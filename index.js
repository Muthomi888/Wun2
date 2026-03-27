'use strict';
const WebSocket = require('ws');

// ===========================================================
// CONFIG — edit these before deploying
// ===========================================================
const CONFIG = {
  API_TOKEN:    'XI3UEVkzS7NbtRH',  // ← paste your token here
  BASE_STAKE:   5.5,
  STOP_LOSS:    130000,
  TAKE_PROFIT:  100000,
  DURATION:     298,                 // contract duration in seconds
  MARKET:       'R_10',             // R_10 | R_25 | R_50 | R_75 | R_100
  MODE:         'HMA_AUTO',         // 'HMA_AUTO' | 'CALL' | 'PUT'
  HMA_PERIOD:   9,                 // Hull MA period (applied to 10-min candles)
  APP_ID:       1089,
};

// ===========================================================
// STATE
// ===========================================================
let ws = null;
let reconnectTimeout = null;
let pingInterval = null;
let connectionMonitor = null;
let errorLogged = false;
let lastMessageTime = Date.now();
let isAuthorized = false;

// Trading
let autoTrading = true;
let isTrading = false;
let activeContractId = null;
let contractExpiry = null;      // epoch seconds when current contract expires
let currentStrategy = null;    // 'CALL' | 'PUT'
let lossStreak = 0;
let maxLossStreak = 0;
let totalProfit = 0;
let lastStake = 0;
let lossStreakStakes = 0;
let activeTradeTimeout = null;
let tradeOpenedAt = null;

// HMA — 10-min candles (signal source)
let hmaCandles = [];           // closed 10-min candles
let hmaCurrentCandle = null;  // live forming candle
let hmaLastValue = null;      // most recent HMA line value
let hmaLastSignal = null;     // 'CALL' | 'PUT' — direction locked at :56

// 5-min candles (execution reference only — confirms boundary)
let execCandles = [];
let execCurrentCandle = null;

// Second-checker state
let stSecondChecker = null;
let st56Fired = false;
let st58Fired = false;

const PING_INTERVAL = 10000;

// ===========================================================
// LOGGING
// ===========================================================
function log(message, type = 'info') {
  const ts = new Date().toISOString();
  const icons = { info: 'ℹ️ ', success: '✅', warning: '⚠️ ', error: '❌', win: '🤑', loss: '☠️ ' };
  console.log(`[${ts}] ${icons[type] || 'ℹ️ '} ${message}`);
}

// ===========================================================
// HULL MOVING AVERAGE ENGINE
// ===========================================================

/**
 * Weighted Moving Average over the last `period` values of `arr`.
 */
function wma(arr, period) {
  if (arr.length < period) return null;
  const slice = arr.slice(-period);
  let num = 0, denom = 0;
  for (let i = 0; i < period; i++) {
    const w = i + 1;
    num += slice[i] * w;
    denom += w;
  }
  return num / denom;
}

/**
 * Hull Moving Average:
 *   HMA(n) = WMA( 2·WMA(n/2) − WMA(n),  floor(√n) )
 *
 * Requires at least  n + floor(√n) − 1  data points.
 */
function computeHMA(closes, period) {
  const halfP  = Math.floor(period / 2);
  const sqrtP  = Math.floor(Math.sqrt(period));
  const needed = period + sqrtP - 1;
  if (closes.length < needed) return null;

  // Build the intermediate diff series for the last sqrtP positions
  const diff = [];
  for (let offset = sqrtP - 1; offset >= 0; offset--) {
    const end   = closes.length - offset;
    const slice = closes.slice(0, end);
    const wHalf = wma(slice, halfP);
    const wFull = wma(slice, period);
    if (wHalf == null || wFull == null) return null;
    diff.push(2 * wHalf - wFull);
  }

  return wma(diff, sqrtP);
}

/**
 * Rebuild HMA from the current 10-min candle array.
 * Updates hmaLastValue and hmaLastSignal.
 */
function refreshHMA() {
  if (!hmaCandles.length) return;

  // Include the live forming candle's close so the value is always up-to-date
  const all    = hmaCurrentCandle
    ? [...hmaCandles, hmaCurrentCandle]
    : [...hmaCandles];

  const closes = all.map(c => c.close);
  const hma    = computeHMA(closes, CONFIG.HMA_PERIOD);
  if (hma == null) return;

  const latestClose = closes[closes.length - 1];
  hmaLastValue  = hma;
  hmaLastSignal = latestClose > hma ? 'CALL' : 'PUT';
}

// ===========================================================
// STUCK-STATE WATCHDOG
// ===========================================================
const STUCK_TIMEOUT_MS = (CONFIG.DURATION + 30) * 1000;

function checkStuckState() {
  const nowSec = Date.now() / 1000;

  // Trade initiated but never confirmed
  if (isTrading && tradeOpenedAt && (Date.now() - tradeOpenedAt > STUCK_TIMEOUT_MS)) {
    log(`Watchdog: trade open >${CONFIG.DURATION + 30}s without confirmation — force-resetting`, 'warning');
    isTrading        = false;
    activeContractId = null;
    tradeOpenedAt    = null;
    contractExpiry   = null;
  }

  // Contract should already have expired
  if (activeContractId && contractExpiry && nowSec > contractExpiry + 30) {
    log(`Watchdog: contract ${activeContractId} expired +30s ago — clearing stale state`, 'warning');
    activeContractId = null;
    isTrading        = false;
    tradeOpenedAt    = null;
    contractExpiry   = null;
    if (activeTradeTimeout) {
      clearTimeout(activeTradeTimeout);
      activeTradeTimeout = null;
    }
  }
}

// ===========================================================
// SECOND WATCHER
//   :56 of a 10-min closing minute → snapshot HMA, lock signal
//   :58 of any 5-min  closing minute → fire trade
//
//   10-min candles close at the end of minutes: 9, 19, 29, 39, 49, 59
//     → min % 10 === 9
//   5-min  candles close at the end of minutes: 4, 9, 14, 19, 24 …
//     → min % 5  === 4
// ===========================================================
function startSecondChecker() {
  if (stSecondChecker) {
    clearInterval(stSecondChecker);
    stSecondChecker = null;
  }
  stSecondChecker = setInterval(() => {
    const now = new Date();
    const min = now.getMinutes();
    const sec = now.getSeconds();

    const on10MinClose = (min % 10 === 9);  // closing minute of 10-min candle
    const on5MinClose  = (min % 5  === 4);  // closing minute of 5-min candle

    // Run watchdog every poll
    checkStuckState();

    // ── :56 on a 10-min boundary — snapshot & lock HMA direction ──
    if (on10MinClose && sec === 56) {
      if (!st56Fired) {
        st56Fired = true;
        onCandleCloseAt56();
      }
    } else {
      st56Fired = false;
    }

    // ── :58 on any 5-min boundary — fire trade ────────────────────
    if (on5MinClose && sec === 58) {
      if (!st58Fired) {
        st58Fired = true;
        onTradeFireAt58();
      }
    } else if (!on5MinClose || sec < 56) {
      st58Fired = false;
    }
  }, 500);
  log('Second-checker started (polls every 500 ms)', 'info');
}

// ===========================================================
// :56 HANDLER — snapshot 10-min candle close, lock HMA signal
// ===========================================================
function onCandleCloseAt56() {
  refreshHMA();
  if (!hmaLastSignal) {
    log('⚠️  :56 — HMA not ready (need more candles)', 'warning');
    return;
  }
  const label = hmaLastSignal === 'CALL' ? '▲ RISE' : '▼ FALL';
  log(`🔒 :56 locked → ${label} | HMA: ${hmaLastValue != null ? hmaLastValue.toFixed(4) : '—'} | Close: ${hmaCurrentCandle ? hmaCurrentCandle.close.toFixed(4) : '—'}`, 'info');

  // Pre-arm direction ready for the next :58
  if (CONFIG.MODE === 'HMA_AUTO' && autoTrading && !isTrading && !activeContractId) {
    currentStrategy = hmaLastSignal;
  }
}

// ===========================================================
// :58 HANDLER — place the trade on a 5-min boundary
// ===========================================================
function onTradeFireAt58() {
  if (!autoTrading) return;
  if (isTrading || activeContractId !== null) {
    log('⏭ :58 — already in a trade, waiting for next cycle', 'warning');
    return;
  }

  if (CONFIG.MODE === 'HMA_AUTO') {
    if (!hmaLastSignal) {
      log('⚡ HMA Auto: no signal locked yet — skipping', 'warning');
      return;
    }
    // Always use the most recent HMA signal (refreshed every 10-min close)
    currentStrategy = hmaLastSignal;
  } else {
    currentStrategy = CONFIG.MODE;
  }

  const dir = currentStrategy === 'CALL' ? 'RISE ▲' : 'FALL ▼';
  log(`⚡ :58 firing → ${dir} | HMA: ${hmaLastValue != null ? hmaLastValue.toFixed(4) : '—'}`, 'info');
  placeTrade(currentStrategy);
}

// ===========================================================
// STAKE / STOP-LOSS / TAKE-PROFIT
// ===========================================================
function calculateNextStake() {
  return Number((CONFIG.BASE_STAKE * Math.pow(2.06, lossStreak)).toFixed(2));
}

function checkStopLoss() {
  if (lossStreakStakes >= CONFIG.STOP_LOSS) {
    log(`Stop loss hit! Streak loss $${lossStreakStakes.toFixed(2)}`, 'error');
    stopBot();
    return true;
  }
  return false;
}

function checkTakeProfit() {
  if (totalProfit >= CONFIG.TAKE_PROFIT) {
    log(`Take profit reached! $${totalProfit.toFixed(2)}`, 'success');
    stopBot();
    return true;
  }
  return false;
}

// ===========================================================
// TRADE EXECUTION
// ===========================================================
function placeTrade(contractType) {
  if (!autoTrading || isTrading || activeContractId !== null) return;
  if (!isAuthorized || !ws || ws.readyState !== WebSocket.OPEN) {
    log('Not connected or not authorised — skipping trade', 'error');
    return;
  }
  const stake = calculateNextStake();
  lastStake    = stake;
  isTrading    = true;
  tradeOpenedAt = Date.now();
  log(`Placing ${contractType === 'CALL' ? 'RISE' : 'FALL'} | ${CONFIG.MARKET} | $${stake} | ${CONFIG.DURATION}s`, 'info');
  try {
    ws.send(JSON.stringify({
      buy: 1,
      price: stake,
      parameters: {
        amount:        stake,
        basis:         'stake',
        contract_type: contractType,
        currency:      'USD',
        duration:      CONFIG.DURATION,
        duration_unit: 's',
        symbol:        CONFIG.MARKET
      },
      passthrough: { priority: 'high', strategy: contractType },
      subscribe: 1
    }));
  } catch (e) {
    log(`Send error: ${e.message}`, 'error');
    isTrading    = false;
    tradeOpenedAt = null;
  }
}

function stopBot() {
  autoTrading      = false;
  isTrading        = false;
  activeContractId = null;
  tradeOpenedAt    = null;
  contractExpiry   = null;
  currentStrategy  = null;
  lossStreak       = 0;
  lossStreakStakes  = 0;
  // maxLossStreak intentionally NOT reset — preserves lifetime maximum
  log('Bot stopped', 'info');
}

// ===========================================================
// CONTRACT MONITORING
// ===========================================================
function monitorActiveTrade(contractId) {
  if (activeTradeTimeout) {
    clearTimeout(activeTradeTimeout);
    activeTradeTimeout = null;
  }
  if (!contractId || !ws || ws.readyState !== WebSocket.OPEN) return;
  ws.send(JSON.stringify({
    proposal_open_contract: 1,
    contract_id: contractId,
    subscribe: 1,
    passthrough: { priority: 'high', force_update: 1 }
  }));
  activeTradeTimeout = setTimeout(() => {
    if (activeContractId === contractId) {
      monitorActiveTrade(contractId);
    } else {
      clearTimeout(activeTradeTimeout);
      activeTradeTimeout = null;
    }
  }, 1000);
}

function subscribeToContractUpdates(contractId) {
  if (ws?.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify({
      proposal_open_contract: 1,
      contract_id: contractId,
      subscribe: 1,
      passthrough: { priority: 'high', force_update: 1 }
    }));
  }
}

// ===========================================================
// CANDLE SUBSCRIPTION
// ===========================================================
function subscribeToCandles() {
  if (!ws || ws.readyState !== WebSocket.OPEN) return;
  ws.send(JSON.stringify({ forget_all: 'candles' }));

  // Reset 10-min HMA state
  hmaCandles       = [];
  hmaCurrentCandle = null;
  hmaLastValue     = null;
  hmaLastSignal    = null;

  // Reset 5-min execution state
  execCandles       = [];
  execCurrentCandle = null;

  // Subscribe to 10-min candles — HMA signal source
  // Need at least HMA_PERIOD + floor(sqrt(HMA_PERIOD)) candles
  const hmaCount = CONFIG.HMA_PERIOD + Math.floor(Math.sqrt(CONFIG.HMA_PERIOD)) + 10;
  ws.send(JSON.stringify({
    ticks_history: CONFIG.MARKET,
    granularity:   600,            // 10 minutes
    style:         'candles',
    count:         Math.max(hmaCount, 50),
    end:           'latest',
    subscribe:     1
  }));

  // Subscribe to 5-min candles — execution boundary reference
  ws.send(JSON.stringify({
    ticks_history: CONFIG.MARKET,
    granularity:   300,            // 5 minutes
    style:         'candles',
    count:         50,
    end:           'latest',
    subscribe:     1
  }));

  log(`Subscribed to ${CONFIG.MARKET} 10-min candles (HMA signal) + 5-min candles (execution)`, 'info');
}

// ===========================================================
// CANDLE HISTORY LOADER
// ===========================================================
function handleCandleHistory(arr, granularity) {
  if (!arr || !arr.length) return;
  const parsed = arr.map(c => ({
    open:  parseFloat(c.open),
    high:  parseFloat(c.high),
    low:   parseFloat(c.low),
    close: parseFloat(c.close),
    epoch: parseInt(c.epoch)
  }));

  if (granularity === 600) {
    // 10-min candles — HMA signal source
    hmaCurrentCandle = parsed[parsed.length - 1];
    hmaCandles       = parsed.slice(0, -1);
    refreshHMA();
    log(`Loaded ${hmaCandles.length} closed 10-min candles | HMA: ${hmaLastValue != null ? hmaLastValue.toFixed(4) : 'pending'} | Signal: ${hmaLastSignal ?? 'pending'}`, 'success');
  } else {
    // 5-min candles — execution reference
    execCurrentCandle = parsed[parsed.length - 1];
    execCandles       = parsed.slice(0, -1);
    log(`Loaded ${execCandles.length} closed 5-min candles`, 'success');
  }
}

// ===========================================================
// WEBSOCKET MESSAGE HANDLER
// ===========================================================
function handleWsMessage(data) {
  // Bulk candle history
  if (data.candles && Array.isArray(data.candles)) {
    const gran = data.echo_req?.granularity ?? 300;
    handleCandleHistory(data.candles, gran);
    return;
  }
  if (data.history?.candles) {
    const gran = data.echo_req?.granularity ?? 300;
    handleCandleHistory(data.history.candles, gran);
    return;
  }

  switch (data.msg_type) {
    case 'pong':
      break;

    case 'authorize':
      if (data.authorize) {
        isAuthorized = true;
        log(`Authorized | ${data.authorize.loginid} | Balance: ${data.authorize.balance} ${data.authorize.currency}`, 'success');
        subscribeToCandles();
        startSecondChecker();
        if (CONFIG.MODE !== 'HMA_AUTO') {
          currentStrategy = CONFIG.MODE;
          log(`Fixed direction: always ${CONFIG.MODE === 'CALL' ? 'RISE' : 'FALL'}`, 'info');
        } else {
          log('HMA Auto active — 10-min close locks signal at :56, fires at :58 on every 5-min boundary', 'info');
        }
        if (activeContractId) {
          subscribeToContractUpdates(activeContractId);
          monitorActiveTrade(activeContractId);
        }
      } else {
        log(`Auth failed: ${JSON.stringify(data.error)}`, 'error');
      }
      break;

    case 'ohlc':
      if (data.ohlc) {
        const o        = data.ohlc;
        const gran     = parseInt(o.granularity ?? 300);
        const newEpoch = parseInt(o.open_time || o.epoch);
        const candle   = {
          open:  parseFloat(o.open),
          high:  parseFloat(o.high),
          low:   parseFloat(o.low),
          close: parseFloat(o.close),
          epoch: newEpoch
        };

        if (gran === 600) {
          // 10-min live candle update
          if (hmaCurrentCandle && hmaCurrentCandle.epoch !== newEpoch) {
            hmaCandles.push({ ...hmaCurrentCandle });
            if (hmaCandles.length > 300) hmaCandles.shift();
          }
          hmaCurrentCandle = candle;
          refreshHMA();
        } else {
          // 5-min live candle update
          if (execCurrentCandle && execCurrentCandle.epoch !== newEpoch) {
            execCandles.push({ ...execCurrentCandle });
            if (execCandles.length > 300) execCandles.shift();
          }
          execCurrentCandle = candle;
        }
      }
      break;

    case 'buy':
      handleBuyResponse(data);
      break;

    case 'proposal_open_contract':
      if (data.proposal_open_contract) handleContractUpdate(data.proposal_open_contract);
      break;

    case 'error':
      log(`API Error: ${data.error.message}`, 'error');
      isTrading    = false;
      tradeOpenedAt = null;
      break;
  }
}

// ===========================================================
// TRADE RESPONSE HANDLERS
// ===========================================================
function handleBuyResponse(data) {
  if (data.buy) {
    activeContractId = data.buy.contract_id;
    lastStake        = data.buy.buy_price;
    contractExpiry   = (data.buy.purchase_time || (tradeOpenedAt / 1000)) + CONFIG.DURATION;
    log(`Trade confirmed | ID: ${activeContractId} | Price: $${lastStake}`, 'success');
    monitorActiveTrade(activeContractId);
    subscribeToContractUpdates(activeContractId);
  } else {
    log(`Trade rejected: ${data.error?.message || 'Unknown'}`, 'error');
    isTrading    = false;
    tradeOpenedAt = null;
  }
}

function handleContractUpdate(contract) {
  if (contract.contract_id !== activeContractId) return;
  if (contract.is_expired || contract.status === 'sold') {
    if (activeTradeTimeout) {
      clearTimeout(activeTradeTimeout);
      activeTradeTimeout = null;
    }
    activeContractId = null;
    isTrading        = false;
    tradeOpenedAt    = null;
    contractExpiry   = null;

    const profit = parseFloat(contract.profit);
    totalProfit += profit;

    if (profit < 0) {
      lossStreak++;
      if (lossStreak > maxLossStreak) maxLossStreak = lossStreak;
      lossStreakStakes += lastStake;
      log(`LOSS -$${Math.abs(profit).toFixed(2)} | Streak: ${lossStreak} | Streak total: $${lossStreakStakes.toFixed(2)} | Max streak: ${maxLossStreak}`, 'loss');
      if (checkStopLoss()) return;
    } else {
      lossStreak       = 0;
      lossStreakStakes  = 0;
      log(`WIN +$${profit.toFixed(2)} | Total P&L: $${totalProfit.toFixed(2)}`, 'win');
      if (checkTakeProfit()) return;
    }
    log('Ready — waiting for next 5-min :58 cycle…', 'info');
  }
}

// ===========================================================
// CONNECTION MANAGEMENT
// ===========================================================
function monitorConnection() {
  if (ws?.readyState === WebSocket.OPEN) {
    if (Date.now() - lastMessageTime > 30000) {
      ws.send(JSON.stringify({ ping: 1 }));
      lastMessageTime = Date.now();
    }
  } else if (ws?.readyState !== WebSocket.CONNECTING) {
    if (!reconnectTimeout) {
      log('Connection lost — reconnecting…', 'warning');
      attemptReconnect();
    }
  }
}

function attemptReconnect() {
  clearTimeout(reconnectTimeout);
  reconnectTimeout = setTimeout(() => initializeWebSocket(), 1000);
}

function initializeWebSocket() {
  if (ws?.readyState === WebSocket.OPEN || ws?.readyState === WebSocket.CONNECTING) return;
  clearInterval(connectionMonitor);
  connectionMonitor = setInterval(monitorConnection, 15000);
  clearInterval(pingInterval);
  log('Connecting to Deriv WebSocket…', 'info');
  ws = new WebSocket(`wss://ws.derivws.com/websockets/v3?app_id=${CONFIG.APP_ID}`);

  ws.on('open', () => {
    errorLogged     = false;
    reconnectTimeout = null;
    log('WebSocket connected', 'success');
    ws.send(JSON.stringify({ authorize: CONFIG.API_TOKEN, passthrough: { priority: 'high' } }));
    pingInterval = setInterval(() => {
      if (ws.readyState === WebSocket.OPEN) {
        ws.send(JSON.stringify({ ping: 1 }));
        lastMessageTime = Date.now();
      }
    }, PING_INTERVAL);
  });

  ws.on('message', (raw) => {
    lastMessageTime = Date.now();
    try {
      handleWsMessage(JSON.parse(raw));
    } catch (e) {
      log(`Parse error: ${e.message}`, 'error');
    }
  });

  ws.on('close', () => {
    clearInterval(pingInterval);
    isAuthorized = false;
    if (!errorLogged) {
      log('Connection closed', 'error');
      errorLogged = true;
    }
    attemptReconnect();
  });

  ws.on('error', (err) => {
    if (!errorLogged) {
      log(`WS error: ${err.message || 'Unknown'}`, 'error');
      errorLogged = true;
    }
    attemptReconnect();
  });
}

// ===========================================================
// BOOT
// ===========================================================
log(`🤖 Deriv HMA Bot starting… [10-min HMA signal / 5-min execution]`, 'info');
log(`Market: ${CONFIG.MARKET} | Mode: ${CONFIG.MODE} | Stake: $${CONFIG.BASE_STAKE}`, 'info');
log(`HMA Period: ${CONFIG.HMA_PERIOD} | Signal TF: 10-min | Execution TF: 5-min`, 'info');
log(`Stop Loss: $${CONFIG.STOP_LOSS} | Take Profit: $${CONFIG.TAKE_PROFIT}`, 'info');

initializeWebSocket();
