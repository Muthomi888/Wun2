'use strict';
const WebSocket = require('ws');

// ===========================================================
// CONFIG — edit these before deploying
// ===========================================================
const CONFIG = {
  API_TOKEN: 'XI3UEVkzS7NbtRH',          // ← paste your token here
  BASE_STAKE: 4.5,
  STOP_LOSS: 130000,
  TAKE_PROFIT: 100000,
  DURATION: 298,                               // contract duration in seconds
  MARKET: 'R_10',                              // R_10 | R_25 | R_50 | R_75 | R_100
  MODE: 'ST_AUTO',                              // 'ST_AUTO' | 'CALL' | 'PUT'
  ST_PERIOD: 1,
  ST_MULTIPLIER: 1.0,
  APP_ID: 1089,
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
let contractExpiry = null;                     // timestamp (seconds) when the current contract expires
let currentStrategy = null;                    // 'CALL' | 'PUT'
let lossStreak = 0;
let maxLossStreak = 0;                          // highest consecutive losses seen
let totalProfit = 0;
let lastStake = 0;
let lossStreakStakes = 0;
let activeTradeTimeout = null;
let tradeOpenedAt = null;                       // timestamp when last trade was placed

// SuperTrend — 5-min candles (execution reference only)
let stCandles = [];
let stCurrentCandle = null;
let stLastDirection = 0;
let stLastValue = null;

// SuperTrend — 15-min candles (signal source)
let st2Candles = [];
let st2CurrentCandle = null;
let st2LastDirection = 0;
let st2LastValue = null;
let st2LastSignal = null;                        // 'CALL' | 'PUT' — drives trade direction

// Aliases for the :56/:58 handlers (always use 2-min signal)
let stLastSignal = null;                         // kept for backward compat — mirrors st2LastSignal
let stSecondChecker = null;
let st56Fired = false;
let st58Fired = false;

const PING_INTERVAL = 10000;

// ===========================================================
// LOGGING
// ===========================================================
function log(message, type = 'info') {
  const ts = new Date().toISOString();
  const icons = { info:'ℹ️ ', success:'✅', warning:'⚠️ ', error:'❌', win:'🤑', loss:'☠️ ' };
  console.log(`[${ts}] ${icons[type] || 'ℹ️ '} ${message}`);
}

// ===========================================================
// SUPERTREND ENGINE (ported 1-to-1 from the HTML bot)
// ===========================================================
function computeSuperTrend(candles, period, multiplier) {
  const n = candles.length;
  if (n < period + 2) return null;
  const trs = [];
  for (let i = 1; i < n; i++) {
    const c = candles[i], p = candles[i - 1];
    trs.push(Math.max(
      c.high - c.low,
      Math.abs(c.high - p.close),
      Math.abs(c.low - p.close)
    ));
  }
  const atrs = new Array(trs.length).fill(0);
  let seed = 0;
  for (let i = 0; i < period; i++) seed += trs[i];
  atrs[period - 1] = seed / period;
  for (let i = period; i < trs.length; i++) {
    atrs[i] = (atrs[i - 1] * (period - 1) + trs[i]) / period;
  }
  const upperBands = [], lowerBands = [], dirs = [];
  for (let i = period - 1; i < trs.length; i++) {
    const ci = i + 1;
    const c = candles[ci];
    const hl2 = (c.high + c.low) / 2;
    const atr = atrs[i];
    const rawUp = hl2 + multiplier * atr;
    const rawDn = hl2 - multiplier * atr;
    let finalUp, finalDn, dir;
    if (upperBands.length === 0) {
      finalUp = rawUp;
      finalDn = rawDn;
      dir = c.close > rawDn ? 1 : -1;
    } else {
      const pUp = upperBands[upperBands.length - 1];
      const pDn = lowerBands[lowerBands.length - 1];
      const pDir = dirs[dirs.length - 1];
      const pClose = candles[ci - 1].close;
      finalUp = (rawUp < pUp || pClose > pUp) ? rawUp : pUp;
      finalDn = (rawDn > pDn || pClose < pDn) ? rawDn : pDn;
      if (pDir === -1) {
        dir = c.close > finalUp ? 1 : -1;
      } else {
        dir = c.close < finalDn ? -1 : 1;
      }
    }
    upperBands.push(finalUp);
    lowerBands.push(finalDn);
    dirs.push(dir);
  }
  if (!dirs.length) return null;
  const lastDir = dirs[dirs.length - 1];
  const lastUp = upperBands[upperBands.length - 1];
  const lastDn = lowerBands[lowerBands.length - 1];
  return {
    direction: lastDir,
    value: lastDir === 1 ? lastDn : lastUp,
    upper: lastUp,
    lower: lastDn
  };
}

function refreshSuperTrend() {
  if (!stCandles.length) return;
  const all = stCurrentCandle ? [...stCandles, stCurrentCandle] : [...stCandles];
  const result = computeSuperTrend(all, CONFIG.ST_PERIOD, CONFIG.ST_MULTIPLIER);
  if (!result) return;
  stLastDirection = result.direction;
  stLastValue = result.value;
}

function refreshSuperTrend2min() {
  if (!st2Candles.length) return;
  const all = st2CurrentCandle ? [...st2Candles, st2CurrentCandle] : [...st2Candles];
  const result = computeSuperTrend(all, CONFIG.ST_PERIOD, CONFIG.ST_MULTIPLIER);
  if (!result) return;
  st2LastDirection = result.direction;
  st2LastValue = result.value;
  st2LastSignal = result.direction === 1 ? 'CALL' : 'PUT';
  stLastSignal = st2LastSignal;                  // keep alias in sync
}

// ===========================================================
// STUCK-STATE WATCHDOG
// ===========================================================
const STUCK_TIMEOUT_MS = (CONFIG.DURATION + 30) * 1000;

function checkStuckState() {
  const nowSec = Date.now() / 1000;

  // Case 1: trade initiated but never confirmed (activeContractId null)
  if (isTrading && tradeOpenedAt && (Date.now() - tradeOpenedAt > STUCK_TIMEOUT_MS)) {
    log(`Watchdog: trade open for >${CONFIG.DURATION + 30}s without confirmation — force-resetting`, 'warning');
    isTrading = false;
    activeContractId = null;
    tradeOpenedAt = null;
    contractExpiry = null;
  }

  // Case 2: contract is active but should have expired already
  if (activeContractId && contractExpiry && nowSec > contractExpiry + 30) {
    log(`Watchdog: contract ${activeContractId} expired +30s ago — clearing stale state`, 'warning');
    activeContractId = null;
    isTrading = false;
    tradeOpenedAt = null;
    contractExpiry = null;
    if (activeTradeTimeout) {
      clearTimeout(activeTradeTimeout);
      activeTradeTimeout = null;
    }
  }
}

// ===========================================================
// SECOND WATCHER — :56 locks signal, :58 fires trade (strictly)
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
    const onCycleMark = (min % 5 === 4); // minutes 4, 9, 14, 19…

    // Run watchdog every poll
    checkStuckState();

    // ── :56 — snapshot candle close, lock direction ───────────
    if (onCycleMark && sec === 56) {
      if (!st56Fired) {
        st56Fired = true;
        onCandleCloseAt56();
      }
    } else {
      st56Fired = false;
    }

    // ── :58 — fire trade (strictly at 58, never at 59) ────────
    if (onCycleMark && sec === 58) {
      if (!st58Fired) {
        st58Fired = true;
        onTradeFireAt58(sec);
      }
    } else if (!onCycleMark || sec < 56) {
      st58Fired = false;
    }
  }, 500);
  log('Second-checker started (polls every 500 ms)', 'info');
}

// ===========================================================
// :56 HANDLER
// ===========================================================
function onCandleCloseAt56() {
  refreshSuperTrend2min();
  if (!st2LastSignal) return;
  const label = st2LastSignal === 'CALL' ? '▲ RISE' : '▼ FALL';
  log(`🔒 :56 locked → ${label} | 15m ST Line: ${st2LastValue != null ? st2LastValue.toFixed(4) : '—'}`, 'info');
  // Pre-set direction ready for :58
  if (CONFIG.MODE === 'ST_AUTO' && autoTrading && !isTrading && !activeContractId) {
    currentStrategy = st2LastSignal;
  }
}

// ===========================================================
// :58 HANDLER — place the trade
// ===========================================================
function onTradeFireAt58(sec) {
  if (!autoTrading) return;
  if (isTrading || activeContractId !== null) {
    log('⏭ :58 — already in a trade, waiting for next cycle', 'warning');
    return;
  }
  if (CONFIG.MODE === 'ST_AUTO') {
    if (!st2LastSignal) {
      log('⚡ ST Auto: no 15-min signal locked this cycle — skipping', 'warning');
      return;
    }
    currentStrategy = st2LastSignal;
  } else {
    currentStrategy = CONFIG.MODE;
  }
  const dir = currentStrategy === 'CALL' ? 'RISE ▲' : 'FALL ▼';
  log(`⚡ :58 firing → ${dir}`, 'info');
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
  lastStake = stake;
  isTrading = true;
  tradeOpenedAt = Date.now();
  log(`Placing ${contractType === 'CALL' ? 'RISE' : 'FALL'} | ${CONFIG.MARKET} | $${stake} | ${CONFIG.DURATION}s`, 'info');
  try {
    ws.send(JSON.stringify({
      buy: 1,
      price: stake,
      parameters: {
        amount: stake,
        basis: 'stake',
        contract_type: contractType,
        currency: 'USD',
        duration: CONFIG.DURATION,
        duration_unit: 's',
        symbol: CONFIG.MARKET
      },
      passthrough: { priority: 'high', strategy: contractType },
      subscribe: 1
    }));
  } catch (e) {
    log(`Send error: ${e.message}`, 'error');
    isTrading = false;
    tradeOpenedAt = null;
  }
}

function stopBot() {
  autoTrading = false;
  isTrading = false;
  activeContractId = null;
  tradeOpenedAt = null;
  contractExpiry = null;
  currentStrategy = null;
  lossStreak = 0;
  lossStreakStakes = 0;
  // maxLossStreak is intentionally NOT reset to preserve lifetime maximum
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

  // Reset 5-min state
  stCandles = [];
  stCurrentCandle = null;
  stLastDirection = 0;
  stLastValue = null;

  // Reset 15-min state
  st2Candles = [];
  st2CurrentCandle = null;
  st2LastDirection = 0;
  st2LastValue = null;
  st2LastSignal = null;
  stLastSignal = null;

  // Subscribe to 5-min candles (trade execution reference)
  ws.send(JSON.stringify({
    ticks_history: CONFIG.MARKET,
    granularity: 300,
    style: 'candles',
    count: 150,
    end: 'latest',
    subscribe: 1
  }));

  // Subscribe to 15-min candles (signal source)
  ws.send(JSON.stringify({
    ticks_history: CONFIG.MARKET,
    granularity: 900,
    style: 'candles',
    count: 150,
    end: 'latest',
    subscribe: 1
  }));

  log(`Subscribed to ${CONFIG.MARKET} 5-min candles (execution) + 15-min candles (signal)`, 'info');
}

function handleCandleHistory(arr, granularity) {
  if (!arr || !arr.length) return;
  const parsed = arr.map(c => ({
    open: parseFloat(c.open),
    high: parseFloat(c.high),
    low: parseFloat(c.low),
    close: parseFloat(c.close),
    epoch: parseInt(c.epoch)
  }));
  if (granularity === 900) {
    // 15-min candles — signal source
    st2CurrentCandle = parsed[parsed.length - 1];
    st2Candles = parsed.slice(0, -1);
    refreshSuperTrend2min();
    log(`Loaded ${st2Candles.length} closed 15-min candles | 15m ST: ${st2LastSignal ?? 'pending'}`, 'success');
  } else {
    // 5-min candles — execution reference
    stCurrentCandle = parsed[parsed.length - 1];
    stCandles = parsed.slice(0, -1);
    refreshSuperTrend();
    log(`Loaded ${stCandles.length} closed 5-min candles`, 'success');
  }
}

// ===========================================================
// WEBSOCKET MESSAGE HANDLER
// ===========================================================
function handleWsMessage(data) {
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
        if (CONFIG.MODE !== 'ST_AUTO') {
          currentStrategy = CONFIG.MODE;
          log(`Fixed direction: always ${CONFIG.MODE === 'CALL' ? 'RISE' : 'FALL'}`, 'info');
        } else {
          log('ST Auto active — 15-min signal locks at :56, fires at :58 on 5-min boundary', 'info');
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
        const o = data.ohlc;
        const gran = parseInt(o.granularity ?? 300);
        const newEpoch = parseInt(o.open_time || o.epoch);
        if (gran === 900) {
          // 15-min live candle update
          if (st2CurrentCandle && st2CurrentCandle.epoch !== newEpoch) {
            st2Candles.push({ ...st2CurrentCandle });
            if (st2Candles.length > 300) st2Candles.shift();
          }
          st2CurrentCandle = {
            open: parseFloat(o.open),
            high: parseFloat(o.high),
            low: parseFloat(o.low),
            close: parseFloat(o.close),
            epoch: newEpoch
          };
          refreshSuperTrend2min();
        } else {
          // 5-min live candle update
          if (stCurrentCandle && stCurrentCandle.epoch !== newEpoch) {
            stCandles.push({ ...stCurrentCandle });
            if (stCandles.length > 300) stCandles.shift();
          }
          stCurrentCandle = {
            open: parseFloat(o.open),
            high: parseFloat(o.high),
            low: parseFloat(o.low),
            close: parseFloat(o.close),
            epoch: newEpoch
          };
          refreshSuperTrend();
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
      isTrading = false;
      tradeOpenedAt = null;
      // autoTrading stays alive — next :58 will retry
      break;
  }
}

// ===========================================================
// TRADE RESPONSE HANDLERS
// ===========================================================
function handleBuyResponse(data) {
  if (data.buy) {
    activeContractId = data.buy.contract_id;
    lastStake = data.buy.buy_price;
    // Use purchase_time from the server (epoch seconds) + DURATION
    contractExpiry = (data.buy.purchase_time || (tradeOpenedAt / 1000)) + CONFIG.DURATION;
    log(`Trade confirmed | ID: ${activeContractId} | Price: $${lastStake}`, 'success');
    monitorActiveTrade(activeContractId);
    subscribeToContractUpdates(activeContractId);
  } else {
    log(`Trade rejected: ${data.error?.message || 'Unknown'}`, 'error');
    isTrading = false;
    tradeOpenedAt = null;
    // Keep autoTrading alive so next cycle retries
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
    isTrading = false;
    tradeOpenedAt = null;
    contractExpiry = null;
    const profit = parseFloat(contract.profit);
    totalProfit += profit;
    if (profit < 0) {
      lossStreak++;
      // Update max loss streak
      if (lossStreak > maxLossStreak) {
        maxLossStreak = lossStreak;
      }
      lossStreakStakes += lastStake;
      log(`LOSS -$${Math.abs(profit).toFixed(2)} | Streak: ${lossStreak} | Total streak: $${lossStreakStakes.toFixed(2)} | Max streak: ${maxLossStreak}`, 'loss');
      if (checkStopLoss()) return;
    } else {
      lossStreak = 0;
      lossStreakStakes = 0;
      log(`WIN +$${profit.toFixed(2)} | Total P&L: $${totalProfit.toFixed(2)}`, 'win');
      if (checkTakeProfit()) return;
    }
    log('Ready — waiting for next :56/:58 cycle…', 'info');
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
    errorLogged = false;
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
log('🤖 Deriv SuperTrend Bot starting… [15m signal / 5m execution]', 'info');
log(`Market: ${CONFIG.MARKET} | Mode: ${CONFIG.MODE} | Stake: $${CONFIG.BASE_STAKE}`, 'info');
log(`ST Period: ${CONFIG.ST_PERIOD} | Multiplier: ${CONFIG.ST_MULTIPLIER} | Signal TF: 15-min | Execution TF: 5-min`, 'info');
log(`Stop Loss: $${CONFIG.STOP_LOSS} | Take Profit: $${CONFIG.TAKE_PROFIT}`, 'info');

initializeWebSocket();
