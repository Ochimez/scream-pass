(function(){
'use strict';
const $ = id => document.getElementById(id);

// <pure>
function rmsOf(b){ let s=0; for(let i=0;i<b.length;i++) s+=b[i]*b[i]; return Math.sqrt(s/b.length); }
function detectPitch(b, sr){
  const N = 1024;
  const minLag = Math.max(2, Math.floor(sr/3000));
  const maxLag = Math.min(Math.floor(sr/150), b.length - N - 1);
  if (maxLag <= minLag + 2) return 0;
  let e0 = 0;
  for (let i=0;i<N;i++) e0 += b[i]*b[i];
  if (e0 < 1e-8) return 0;
  const r = new Float32Array(maxLag + 2);
  let best = 0;
  for (let lag=minLag; lag<=maxLag; lag++){
    let c = 0, e1 = 0;
    for (let i=0;i<N;i++){ const y = b[i+lag]; c += b[i]*y; e1 += y*y; }
    const d = Math.sqrt(e0*e1);
    const v = d > 0 ? c/d : 0;
    r[lag] = v;
    if (v > best) best = v;
  }
  if (best < 0.55) return 0;
  for (let lag=minLag+1; lag<maxLag; lag++){
    if (r[lag] >= 0.92*best && r[lag] >= r[lag-1] && r[lag] >= r[lag+1]){
      const a = r[lag-1], m = r[lag], c2 = r[lag+1];
      const den = a - 2*m + c2;
      const shift = den !== 0 ? 0.5*(a - c2)/den : 0;
      return sr/(lag + shift);
    }
  }
  return 0;
}
function toSemi(f){ return 12*Math.log2(f/440); }
function median(a){
  if (!a.length) return 0;
  const s = a.slice().sort((x,y)=>x-y), m = s.length >> 1;
  return s.length % 2 ? s[m] : (s[m-1] + s[m])/2;
}
function slopeOf(ts, ys){
  const n = ts.length;
  if (n < 2) return 0;
  let st = 0, sy = 0;
  for (let i=0;i<n;i++){ st += ts[i]; sy += ys[i]; }
  const mt = st/n, my = sy/n;
  let num = 0, den = 0;
  for (let i=0;i<n;i++){ num += (ts[i]-mt)*(ys[i]-my); den += (ts[i]-mt)*(ts[i]-mt); }
  return den > 0 ? num/den : 0;
}
function summarize(frames, loudOver){
  const loud = frames.filter(x => x.db >= loudOver);
  if (!loud.length) return null;
  const dur = loud[loud.length-1].t - loud[0].t;
  const voiced = loud.filter(x => x.f > 0);
  if (voiced.length < 6 || dur < 300) return null;
  return {
    pitch: median(voiced.map(x => x.f)),
    slope: slopeOf(voiced.map(x => x.t/1000), voiced.map(x => toSemi(x.f))),
    dur: dur
  };
}
function compare(sig, got, tolSemi){
  const dSemi = toSemi(got.pitch) - toSemi(sig.pitch);
  const slopeTol = Math.max(4, Math.abs(sig.slope)*0.6);
  const dSlope = got.slope - sig.slope;
  const durTol = Math.max(300, sig.dur*0.35);
  const dDur = got.dur - sig.dur;
  return {
    pitchOk: Math.abs(dSemi) <= tolSemi,
    slopeOk: Math.abs(dSlope) <= slopeTol,
    durOk: Math.abs(dDur) <= durTol,
    dSemi: dSemi, dSlope: dSlope, dDur: dDur
  };
}
// </pure>

/* ---------- settings ---------- */
const KEY = 'screampass.cfg.v1';
const DEFAULTS = { mode:'any', overDb:25, holdMs:1200, fLow:400, fHigh:2500, tolSemi:3,
  secret:'Access granted. Replace this message in Settings.', sig:null };
function load(){
  try { const raw = localStorage.getItem(KEY); if (raw) return Object.assign({}, DEFAULTS, JSON.parse(raw)); } catch(e){}
  return Object.assign({}, DEFAULTS);
}
let cfg = load();
function save(){ try { localStorage.setItem(KEY, JSON.stringify(cfg)); } catch(e){} }

/* ---------- elements ---------- */
const chip=$('chip'), hint=$('hint'), scope=$('scope'), go=$('go'), gatesEl=$('gates');
const rdLevel=$('rdLevel'), rdPitch=$('rdPitch'), rdHold=$('rdHold'), rdHoldLabel=$('rdHoldLabel');

/* ---------- state ---------- */
let ctx=null, analyser=null, stream=null, buf=null, raf=0;
let phase='idle';              // idle | calibrating | armed | enrolling | unlocked
let intent='verify';
let phaseStart=0, calib=[], ambientDb=-60, lastT=0;
let hist=[], hold=0, lastBand=-1e9, attempt=null, lastF=0, lastFAt=-1e9;

function running(){ return phase==='calibrating' || phase==='armed' || phase==='enrolling'; }
function setChip(state, text){ chip.dataset.state = state; chip.textContent = text; }
function setHint(t){ hint.textContent = t; }
const clamp01 = v => Math.max(0, Math.min(1, v));

/* ---------- gates ---------- */
let gateRows = [];
function buildGates(){
  const labels = cfg.mode==='match'
    ? ['Pitch matches','Rise or fall matches','Length matches']
    : ['Loud enough','Pitch in range','Held long enough'];
  gatesEl.textContent = '';
  gateRows = labels.map(text => {
    const li = document.createElement('li'); li.dataset.state = 'idle';
    const a = document.createElement('span'); a.className = 'g-label'; a.textContent = text;
    const v = document.createElement('span'); v.className = 'g-val'; v.textContent = '–';
    const bar = document.createElement('div'); bar.className = 'bar';
    const fill = document.createElement('i'); bar.appendChild(fill);
    li.append(a, v, bar); gatesEl.appendChild(li);
    return { li: li, val: v, fill: fill };
  });
}
function setGate(i, o){
  const g = gateRows[i]; if (!g) return;
  g.li.dataset.state = o.state || 'idle';
  g.val.textContent = o.val != null ? o.val : '–';
  g.fill.style.width = Math.round(clamp01(o.fill || 0) * 100) + '%';
}
function resetGates(){ gateRows.forEach((_, i) => setGate(i, {})); }

/* ---------- mode ---------- */
function slopeWord(s){ return Math.abs(s) < 1.5 ? 'steady' : (s > 0 ? 'rising' : 'falling'); }
function renderSig(){
  $('sigText').textContent = cfg.sig
    ? Math.round(cfg.sig.pitch) + ' Hz, ' + slopeWord(cfg.sig.slope) + ', ' + (cfg.sig.dur/1000).toFixed(1) + ' s'
    : 'No scream recorded yet.';
}
function goLabel(){
  if (running()) return 'Stop';
  return (cfg.mode==='match' && !cfg.sig) ? 'Record the pass scream' : 'Start listening';
}
function refreshMode(){
  if (running()) stop();
  $('grpAny').hidden = cfg.mode === 'match';
  $('grpMatch').hidden = cfg.mode !== 'match';
  $('lede').textContent = cfg.mode==='match'
    ? 'Scream the sound you recorded to open the vault.'
    : 'Scream loud, high and long enough to open the vault.';
  rdHoldLabel.textContent = cfg.mode==='match' ? 'Scream' : 'Held';
  buildGates(); renderSig(); go.textContent = goLabel(); draw(performance.now());
}

/* ---------- audio ---------- */
function releaseAudio(){
  if (raf) cancelAnimationFrame(raf); raf = 0;
  if (stream){ stream.getTracks().forEach(t => t.stop()); stream = null; }
  if (ctx){ ctx.close().catch(()=>{}); ctx = null; }
  analyser = null; attempt = null;
}
function stop(msg){
  releaseAudio();
  if (phase !== 'unlocked') phase = 'idle';
  setChip('idle','Locked'); setHint(msg || 'Mic is off');
  go.textContent = goLabel(); resetGates();
  rdLevel.textContent = '–'; rdPitch.textContent = '–'; rdHold.textContent = cfg.mode==='match' ? '–' : '0.0 s';
  hold = 0; draw(performance.now());
}
function showError(text){ setChip('error','Mic problem'); setHint(text); }

async function start(force){
  if (phase !== 'idle') return;
  intent = force || ((cfg.mode==='match' && !cfg.sig) ? 'enroll' : 'verify');
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia){
    showError('This browser only allows the microphone on https pages, localhost, or a local file. Open the page from one of those.');
    return;
  }
  try {
    stream = await navigator.mediaDevices.getUserMedia({ audio:{ echoCancellation:false, noiseSuppression:false, autoGainControl:false } });
  } catch(e){
    showError(e && e.name === 'NotAllowedError'
      ? 'Microphone blocked. Allow it in the browser site settings, then tap Start again.'
      : 'No microphone found or it is in use by another app.');
    return;
  }
  const AC = window.AudioContext || window.webkitAudioContext;
  ctx = new AC();
  try { if (ctx.state === 'suspended') await ctx.resume(); } catch(e){}
  const src = ctx.createMediaStreamSource(stream);
  analyser = ctx.createAnalyser(); analyser.fftSize = 2048; analyser.smoothingTimeConstant = 0;
  src.connect(analyser);
  buf = new Float32Array(analyser.fftSize);
  hist = []; hold = 0; lastBand = -1e9; attempt = null; calib = []; lastT = 0;
  phase = 'calibrating'; phaseStart = performance.now();
  setChip('listening','Calibrating'); setHint('Stay quiet for a second.');
  go.textContent = 'Stop'; resetGates();
  raf = requestAnimationFrame(tick);
}

function tick(now){
  if (!analyser) return;
  raf = requestAnimationFrame(tick);
  analyser.getFloatTimeDomainData(buf);
  const db = 20*Math.log10(Math.max(rmsOf(buf), 1e-7));
  const dt = Math.min(100, lastT ? now - lastT : 16); lastT = now;

  if (phase === 'calibrating'){
    calib.push(db);
    if (now - phaseStart > 1000){
      ambientDb = Math.max(-80, median(calib));
      phase = intent === 'enroll' ? 'enrolling' : 'armed';
      setChip('listening', intent === 'enroll' ? 'Recording' : 'Listening');
      setHint(intent === 'enroll' ? 'Scream the sound you want as your pass.'
        : (cfg.mode==='match' ? 'Scream your pass scream.' : 'Scream now. Loud, high, and hold it.'));
    }
    draw(now); return;
  }

  const over = db - ambientDb;
  const loud = over >= cfg.overDb;
  let f = 0;
  if (over >= 8) f = detectPitch(buf, ctx.sampleRate);
  if (f > 0){ lastF = f; lastFAt = now; }
  const shownF = now - lastFAt < 200 ? lastF : 0;
  hist.push({ t: now, over: over, f: f });
  while (hist.length && now - hist[0].t > 4000) hist.shift();

  rdLevel.textContent = (over >= 0 ? '+' : '') + over.toFixed(0) + ' dB';
  rdPitch.textContent = shownF ? Math.round(shownF) + ' Hz' : '–';

  if (cfg.mode === 'any' && intent === 'verify') stepAny(now, dt, over, f, loud, shownF);
  else stepAttempt(now, over, f, loud);

  draw(now);
}

function stepAny(now, dt, over, f, loud, shownF){
  if (f > 0 && f >= cfg.fLow && f <= cfg.fHigh) lastBand = now;
  const inBand = now - lastBand < 160;
  const ok = loud && inBand;
  hold = ok ? Math.min(cfg.holdMs, hold + dt) : Math.max(0, hold - dt*1.5);
  rdHold.textContent = (hold/1000).toFixed(1) + ' s';
  setGate(0, { val: (over >= 0 ? '+' : '') + over.toFixed(0) + ' / +' + cfg.overDb + ' dB', fill: over/cfg.overDb, state: loud ? 'pass' : 'live' });
  setGate(1, { val: shownF ? Math.round(shownF) + ' Hz' : 'no pitch', fill: inBand ? 1 : 0, state: inBand ? 'pass' : 'live' });
  setGate(2, { val: (hold/1000).toFixed(1) + ' / ' + (cfg.holdMs/1000).toFixed(1) + ' s', fill: hold/cfg.holdMs, state: hold >= cfg.holdMs ? 'pass' : 'live' });
  if (hold >= cfg.holdMs) unlock();
}

function stepAttempt(now, over, f, loud){
  if (!attempt){
    if (!loud) return;
    attempt = { start: now, last: now, frames: [] };
    resetGates();
  }
  if (loud) attempt.last = now;
  attempt.frames.push({ t: now - attempt.start, db: over, f: f });
  rdHold.textContent = ((attempt.last - attempt.start)/1000).toFixed(1) + ' s';
  gateRows.forEach((_, i) => setGate(i, { val: 'recording', fill: 0.5, state: 'live' }));
  if (now - attempt.last > 350){
    const a = attempt; attempt = null; finishAttempt(a);
  }
}

function finishAttempt(a){
  const s = summarize(a.frames, cfg.overDb);
  if (!s){
    resetGates();
    setHint('Too short or too noisy to read. Scream a little longer and try again.');
    return;
  }
  if (phase === 'enrolling'){
    cfg.sig = s; save(); renderSig();
    stop('Saved: ' + Math.round(s.pitch) + ' Hz, ' + slopeWord(s.slope) + ', ' + (s.dur/1000).toFixed(1) + ' s. Tap Start listening to test it.');
    return;
  }
  const c = compare(cfg.sig, s, cfg.tolSemi);
  const sg = n => (n >= 0 ? '+' : '') + n.toFixed(1);
  setGate(0, { val: Math.round(s.pitch) + ' Hz (' + sg(c.dSemi) + ' st)', fill: c.pitchOk ? 1 : 0.2, state: c.pitchOk ? 'pass' : 'fail' });
  setGate(1, { val: slopeWord(s.slope) + ' (' + sg(c.dSlope) + ' st/s)', fill: c.slopeOk ? 1 : 0.2, state: c.slopeOk ? 'pass' : 'fail' });
  setGate(2, { val: (s.dur/1000).toFixed(1) + ' s vs ' + (cfg.sig.dur/1000).toFixed(1) + ' s', fill: c.durOk ? 1 : 0.2, state: c.durOk ? 'pass' : 'fail' });
  if (c.pitchOk && c.slopeOk && c.durOk) unlock();
  else setHint('Not the same scream. Try again.');
}

/* ---------- vault ---------- */
function unlock(){
  phase = 'unlocked'; releaseAudio();
  setChip('open','Unlocked'); setHint('Access granted.');
  go.hidden = true; renderVault();
  try { if (navigator.vibrate) navigator.vibrate([60,40,120]); } catch(e){}
}
function relock(){
  phase = 'idle'; go.hidden = false; renderVault();
  stop('Mic is off');
}
function renderVault(){
  const open = phase === 'unlocked';
  $('vault').dataset.state = open ? 'open' : 'locked';
  $('vaultLocked').hidden = open; $('vaultOpen').hidden = !open;
  const out = $('secretOut'); out.textContent = '';
  if (!open) return;
  const t = (cfg.secret || '').trim();
  if (/^https?:\/\/\S+$/i.test(t)){
    const a = document.createElement('a');
    a.href = t; a.target = '_blank'; a.rel = 'noopener noreferrer'; a.textContent = t;
    out.appendChild(a);
  } else out.textContent = cfg.secret;
}
$('copy').addEventListener('click', () => {
  const btn = $('copy'), done = () => { btn.textContent = 'Copied'; setTimeout(() => btn.textContent = 'Copy', 1500); };
  const fallback = () => { const r = document.createRange(); r.selectNodeContents($('secretOut')); const s = getSelection(); s.removeAllRanges(); s.addRange(r); };
  try { navigator.clipboard.writeText(cfg.secret).then(done, fallback); } catch(e){ fallback(); }
});
$('relock').addEventListener('click', relock);

/* ---------- scope drawing ---------- */
const MONO = "'IBM Plex Mono', ui-monospace, monospace";
const F_MIN = 150, F_MAX = 3000, WINDOW_MS = 4000;
let colors = null;
function readColors(){
  const cs = getComputedStyle(document.documentElement), g = n => cs.getPropertyValue(n).trim();
  colors = { fg:g('--fg'), muted:g('--muted'), line:g('--line'), accent:g('--accent'), surface:g('--surface') };
}
if (window.matchMedia){
  const mq = matchMedia('(prefers-color-scheme: dark)');
  const onTheme = () => { readColors(); draw(performance.now()); };
  if (mq.addEventListener) mq.addEventListener('change', onTheme); else if (mq.addListener) mq.addListener(onTheme);
}
function draw(now){
  if (!colors) readColors();
  const w = scope.clientWidth, h = scope.clientHeight;
  if (!w || !h) return;
  const dpr = Math.min(2, window.devicePixelRatio || 1);
  if (scope.width !== Math.round(w*dpr) || scope.height !== Math.round(h*dpr)){
    scope.width = Math.round(w*dpr); scope.height = Math.round(h*dpr);
  }
  const g = scope.getContext('2d');
  g.setTransform(dpr,0,0,dpr,0,0); g.clearRect(0,0,w,h);
  const padT = 16, gap = 26;
  const levelH = Math.round((h - padT - gap - 14) * 0.5);
  const lvTop = padT, lvBot = lvTop + levelH;
  const pTop = lvBot + gap, pBot = h - 14, pH = pBot - pTop;
  const maxOver = Math.max(50, cfg.overDb + 15);
  const yF = f => pBot - (Math.log(Math.min(F_MAX, Math.max(F_MIN, f))/F_MIN)/Math.log(F_MAX/F_MIN))*pH;

  g.font = '500 10px ' + MONO; g.textBaseline = 'alphabetic';
  g.fillStyle = colors.muted; g.textAlign = 'left';
  g.fillText('LEVEL OVER ROOM', 0, lvTop - 4);
  g.fillText('PITCH', 0, pTop - 8);
  g.strokeStyle = colors.line; g.lineWidth = 1;
  g.beginPath(); g.moveTo(0, lvBot + .5); g.lineTo(w, lvBot + .5); g.moveTo(0, pBot + .5); g.lineTo(w, pBot + .5); g.stroke();

  let bLo = cfg.fLow, bHi = cfg.fHigh;
  if (cfg.mode === 'match'){
    if (cfg.sig){ const k = Math.pow(2, cfg.tolSemi/12); bLo = cfg.sig.pitch/k; bHi = cfg.sig.pitch*k; }
    else { bLo = 0; bHi = 0; }
  }
  if (bHi > 0){
    const y1 = yF(bHi), y2 = yF(bLo);
    g.globalAlpha = .22; g.fillStyle = colors.accent; g.fillRect(0, y1, w, Math.max(2, y2 - y1)); g.globalAlpha = 1;
    g.fillStyle = colors.muted; g.textAlign = 'right';
    g.fillText(Math.round(bLo) + '–' + Math.round(bHi) + ' Hz', w, pTop - 8);
  }

  const barW = Math.max(1.5, w/WINDOW_MS*16.7);
  for (let i = 0; i < hist.length; i++){
    const it = hist[i], x = w - (now - it.t)/WINDOW_MS*w;
    if (x < -barW) continue;
    const bh = clamp01(it.over/maxOver)*levelH;
    const hot = it.over >= cfg.overDb;
    g.globalAlpha = hot ? 1 : .6; g.fillStyle = hot ? colors.accent : colors.muted;
    g.fillRect(x, lvBot - bh, barW, bh);
    if (it.f > 0){
      g.globalAlpha = 1; g.fillStyle = (bHi > 0 && it.f >= bLo && it.f <= bHi) ? colors.accent : colors.fg;
      g.fillRect(x, yF(it.f) - 1.5, barW, 3);
    }
  }
  g.globalAlpha = 1;

  const yT = lvBot - cfg.overDb/maxOver*levelH;
  g.strokeStyle = colors.fg; g.setLineDash([4,4]); g.beginPath(); g.moveTo(0, yT + .5); g.lineTo(w, yT + .5); g.stroke(); g.setLineDash([]);
  g.fillStyle = colors.fg; g.textAlign = 'right';
  g.fillText('NEED +' + cfg.overDb + ' dB', w, yT - 4);
}
window.addEventListener('resize', () => draw(performance.now()));

/* ---------- settings wiring ---------- */
function bindSlider(id, get, set, fmt){
  const el = $(id), out = $(id + 'Out');
  el.value = get(); out.textContent = fmt(get());
  el.addEventListener('input', () => { set(Number(el.value)); out.textContent = fmt(get()); save(); draw(performance.now()); });
}
bindSlider('overDb', () => cfg.overDb, v => { cfg.overDb = v; }, v => '+' + v + ' dB');
bindSlider('holdS', () => cfg.holdMs/1000, v => { cfg.holdMs = Math.round(v*1000); }, v => v.toFixed(1) + ' s');
bindSlider('tolSemi', () => cfg.tolSemi, v => { cfg.tolSemi = v; }, v => '±' + v + ' st');
['fLow','fHigh'].forEach(k => {
  const el = $(k); el.value = cfg[k];
  el.addEventListener('change', () => {
    let v = Number(el.value); if (!isFinite(v)) v = DEFAULTS[k];
    v = k === 'fLow' ? Math.min(Math.max(F_MIN, v), cfg.fHigh - 100) : Math.max(Math.min(F_MAX, v), cfg.fLow + 100);
    cfg[k] = Math.round(v); el.value = cfg[k]; save(); draw(performance.now());
  });
});
document.querySelectorAll('input[name=mode]').forEach(r => {
  r.checked = r.value === cfg.mode;
  r.addEventListener('change', () => { if (r.checked){ cfg.mode = r.value; save(); refreshMode(); } });
});
const secretEl = $('secret'); secretEl.value = cfg.secret;
secretEl.addEventListener('input', () => { cfg.secret = secretEl.value; save(); });
$('enroll').addEventListener('click', () => { if (phase === 'idle') start('enroll'); });
$('reset').addEventListener('click', () => {
  if (running()) stop();
  cfg = Object.assign({}, DEFAULTS); save();
  $('overDb').value = cfg.overDb; $('overDbOut').textContent = '+' + cfg.overDb + ' dB';
  $('holdS').value = cfg.holdMs/1000; $('holdSOut').textContent = (cfg.holdMs/1000).toFixed(1) + ' s';
  $('tolSemi').value = cfg.tolSemi; $('tolSemiOut').textContent = '±' + cfg.tolSemi + ' st';
  $('fLow').value = cfg.fLow; $('fHigh').value = cfg.fHigh; secretEl.value = cfg.secret;
  document.querySelectorAll('input[name=mode]').forEach(r => { r.checked = r.value === cfg.mode; });
  refreshMode();
});
go.addEventListener('click', () => { if (running()) stop('Stopped.'); else start(); });

refreshMode();
})();
