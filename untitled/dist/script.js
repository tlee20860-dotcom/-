/* ============================================================================
 * v7.3：房間連線 / 參數設定 / 盟徽 / 佈兵總覽（含連線圖三佈局）
 * ========================================================================== */
(function(){
'use strict';

const LS_PREFIX = 'slg_sandtable_v70_';
const AI_LS_KEY = 'slg_ai_params';
const HEARTBEAT_INTERVAL = 3000;
const HOST_TIMEOUT = 9000;
const PING_INTERVAL = 5000;
const SIM_CHUNK = 500;
const VIZ_CHUNK_SIZE = 6000;
const VIZ_SNAPSHOT_INTERVAL = 5;
const EDIT_LOCK_TTL = 30000;
const DYN_ROUTE_SAMPLE_SEC = 5;
const COMBAT_TICK = 30;

const MQTT_URI = 'wss://broker.hivemq.com:8884/mqtt';
const TOPIC_PREFIX = 'slg_sandtable/room/';
const PERCENT_OPTIONS = [0, 17, 33, 50, 67, 84, 100];

const ATTACK_RULES = {
  self:['enemy','common_enemy','npc'], ally:['enemy','common_enemy','npc'],
  enemy:['self','ally','npc','common_enemy'], common_enemy:['self','ally','npc','enemy'],
  npc:['self','ally','enemy','common_enemy'],
};
const DEFEND_RULES = { self:['self','ally'], ally:['self','ally'], enemy:[],common_enemy:[],npc:[] };
const SIDE_LABELS = {self:'本方',ally:'同盟',enemy:'敵方',common_enemy:'共同敵方',npc:'NPC'};
const ALLIANCE_SIDE_LABELS = {self:'本方',ally:'同盟',enemy:'敵方'};

const EVT = {
  MEMBERS:'members', LOCKS:'locks', DATA:'data',
  CONN:'conn', PING:'ping', HOST:'host',
  SIM_TRIGGER:'sim:trigger', DEBUG:'debug', VIZ_SNAPSHOTS:'viz:snapshots', VIZ_RESET:'viz:reset',
  DYN_RESULT:'dyn:result',
};

const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2,7);
const nowTime = () => new Date().toTimeString().slice(0,8);
const esc = s => s == null ? '' : String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
const sideLabel = s => SIDE_LABELS[s] || s;
const allianceSideLabel = s => ALLIANCE_SIDE_LABELS[s] || s;
const sideClass = s => (s==='self') ? 'self' : (s==='ally') ? 'ally' : (s==='enemy'||s==='common_enemy') ? 'enemy' : 'npc';
const yieldToMain = () => new Promise(r => queueMicrotask(r));
const logSystem = text => console.log('[系統] ' + text);
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));

function hhmmToMinutes(hhmm){
  if(!hhmm || typeof hhmm !== 'string') return 0;
  const p = hhmm.split(':');
  return (parseInt(p[0],10)||0)*60 + (parseInt(p[1],10)||0);
}
function minutesToHHMM(mins){
  mins = ((mins % 1440) + 1440) % 1440;
  return String(Math.floor(mins/60)).padStart(2,'0') + ':' + String(mins%60).padStart(2,'0');
}
const fmtSimTime = sec => `第 ${Math.floor(sec/60)} 分 ${String(sec%60).padStart(2,'0')} 秒`;

function computeAllocation(city){
  const totalTeams = Number(city.totalTeams) || 0;
  let atkPreSum = 0, defPreSum = 0;
  for(const t of (city.attackTargets || [])) atkPreSum += Math.floor(totalTeams * (Number(t.preWarPercent)||0) / 100);
  for(const t of (city.defendTargets || [])) defPreSum += Math.floor(totalTeams * (Number(t.preWarPercent)||0) / 100);
  const allocated = atkPreSum + defPreSum;
  const reserve = totalTeams - allocated;
  return { totalTeams, atkSum: atkPreSum, defSum: defPreSum, allocated, reserve, over: reserve < 0 };
}
function calcAllianceAvgPower(a){ const mc = Number(a.memberCount)||0; const tp = Number(a.totalPower)||0; return mc>0 ? tp/mc : 0; }
function getAllianceAvgPower(a){ if(typeof a.avgPower === 'number' && a.avgPower > 0) return a.avgPower; return calcAllianceAvgPower(a); }

/* AI 佈兵助手 */
const AI = (() => {
  const DEFAULT_PARAMS = {
    r25: 25, r20: 33, r15: 50, r12: 60, r10: 70, r08: 84, r06: 95, r00: 100,
    teamFactor: 0.4, wallFactor1: 1.10, wallFactor2: 1.15,
    defendFactor: 0.70, minPct: 17,
  };
  let params = { ...DEFAULT_PARAMS };
  const OPTIONS = [17, 33, 50, 67, 84, 100];

  function loadParams(){ try{ const raw = localStorage.getItem(AI_LS_KEY); if (raw) params = { ...DEFAULT_PARAMS, ...JSON.parse(raw) }; }catch(e){} }
  function saveParams(){ try{ localStorage.setItem(AI_LS_KEY, JSON.stringify(params)); }catch(e){} }
  function resetParams(){ params = { ...DEFAULT_PARAMS }; saveParams(); }
  function setParams(p){ params = { ...params, ...p }; }
  function getParams(){ return { ...params }; }

  function calcBaseRatio(myPower, enemyPower){
    const ratio = myPower / Math.max(1, enemyPower);
    if (ratio >= 2.5) return params.r25;
    if (ratio >= 2.0) return params.r20;
    if (ratio >= 1.5) return params.r15;
    if (ratio >= 1.2) return params.r12;
    if (ratio >= 1.0) return params.r10;
    if (ratio >= 0.8) return params.r08;
    if (ratio >= 0.6) return params.r06;
    return params.r00;
  }
  function snapToOption(v){
    let closest = OPTIONS[0], minDiff = Infinity;
    for (const o of OPTIONS){ const diff = Math.abs(o - v); if (diff < minDiff){ minDiff = diff; closest = o; } }
    return closest;
  }
  function suggestForTarget(myCity, targetCity, isAttack){
    const myAvg = myCity.avgPower || 1;
    const tgtAvg = targetCity.avgPower || 1;
    let base = calcBaseRatio(myAvg, tgtAvg);
    const myTeams = myCity.totalTeams || 1;
    const tgtTeams = targetCity.totalTeams || 0;
    const teamRatio = tgtTeams / myTeams;
    if (teamRatio > 1) base = base * (1 + (teamRatio - 1) * params.teamFactor);
    const wallMin = targetCity.wallMin || 0;
    if (wallMin > 30) base *= params.wallFactor1;
    if (wallMin > 60) base *= params.wallFactor2;
    if (!isAttack) base *= params.defendFactor;
    return snapToOption(base);
  }
  function suggestForCity(city, allCities){
    const result = { atk: [], def: [] };
    if (!city.totalTeams) return result;
    let totalPre = 0;
    for (const t of (city.attackTargets || [])){
      const tgt = allCities.find(c => c.id === t.cityId);
      if (!tgt) continue;
      const pre = suggestForTarget(city, tgt, true);
      result.atk.push({ cityId: t.cityId, preWarPercent: pre, postRevivePercent: pre, priority: t.priority || 1 });
      totalPre += pre;
    }
    for (const t of (city.defendTargets || [])){
      const tgt = allCities.find(c => c.id === t.cityId);
      if (!tgt) continue;
      const pre = suggestForTarget(city, tgt, false);
      result.def.push({ cityId: t.cityId, preWarPercent: pre, postRevivePercent: pre, priority: t.priority || 1 });
      totalPre += pre;
    }
    if (totalPre > 100){
      const scale = 100 / totalPre;
      const adjust = arr => arr.forEach(s => {
        const raw = Math.max(s.preWarPercent * scale, params.minPct);
        const snapped = snapToOption(raw);
        s.preWarPercent = snapped;
        s.postRevivePercent = snapped;
      });
      adjust(result.atk);
      adjust(result.def);
    }
    return result;
  }

  loadParams();
  return { suggestForCity, suggestForTarget, loadParams, saveParams, resetParams, setParams, getParams, DEFAULT_PARAMS };
})();

const state = {
  commanderName:'', roomCode:'', isHost:false, hostName:'',
  connected:false, connecting:false, pingMs:null, myClientId:'',
  members:{}, editLocks:{}, isSimulating:false,
  settings:{
    timeLimitMin:120, consumeMinPerMin:10, consumeMaxPerMin:30,
    siegeEfficiency:1, marchTimeSec:0, maxLossRatio:0.9, minLossRatio:0.1
  },
  alliances:[], zones:[], cities:[],
  lamport:0, settingsRev:0,
  entityRev:{ alliance:{}, zone:{}, city:{} },
  dirty:{ settings:false, alliance:new Set(), zone:new Set(), city:new Set(),
    allianceDeleted:new Set(), zoneDeleted:new Set(), cityDeleted:new Set() },
  roomEpoch:'', simBaseMin: 0, dynRows: [], editingAllianceId: null,
  narrativeLines: [],
};

const bus = new Map();
function on(evt, fn){ if(!bus.has(evt)) bus.set(evt, new Set()); bus.get(evt).add(fn); return () => bus.get(evt)?.delete(fn); }
function emit(evt, data){ const s = bus.get(evt); if(!s) return; for(const fn of s){ try{ fn(data); }catch(e){ console.error('[emit]', evt, e); } } }
function tickLamport(r=0){ state.lamport = Math.max(state.lamport, r) + 1; return state.lamport; }
function isNewer(r, l){ return (r||0) > (l||0); }
function markDirty(kind, id){ if(kind==='settings'){ state.dirty.settings=true; return; } state.dirty[kind]?.add(id); }
function clearDirty(){ state.dirty.settings = false; for(const k of ['alliance','zone','city','allianceDeleted','zoneDeleted','cityDeleted']) state.dirty[k].clear(); }

function saveState(){
  try{
    localStorage.setItem(LS_PREFIX+'state', JSON.stringify({
      commanderName:state.commanderName, roomCode:state.roomCode, isHost:state.isHost, hostName:state.hostName,
      settings:state.settings, settingsRev:state.settingsRev, lamport:state.lamport, entityRev:state.entityRev,
      roomEpoch:state.roomEpoch, alliances:state.alliances, zones:state.zones, cities:state.cities,
      dynRows: state.dynRows.slice(-5000),
      narrativeLines: state.narrativeLines.slice(-1000),
    }));
  }catch(e){ console.warn('儲存失敗', e); }
}
function loadState(){
  try{
    const raw = localStorage.getItem(LS_PREFIX+'state');
    if(!raw) return;
    const d = JSON.parse(raw);
    for(const k of ['commanderName','roomCode','isHost','hostName','settingsRev','lamport','roomEpoch']){
      if(d[k]!==undefined) state[k]=d[k];
    }
    if(d.settings) Object.assign(state.settings, d.settings);
    if(typeof state.settings.consumeMinPerMin !== 'number') state.settings.consumeMinPerMin = 10;
    if(typeof state.settings.consumeMaxPerMin !== 'number') state.settings.consumeMaxPerMin = 30;
    delete state.settings.consumePerMin;
    if(typeof state.settings.maxLossRatio !== 'number') state.settings.maxLossRatio = 0.9;
    if(typeof state.settings.minLossRatio !== 'number') state.settings.minLossRatio = 0.1;
    if(typeof state.settings.marchTimeSec !== 'number') state.settings.marchTimeSec = 0;
    if(d.entityRev) state.entityRev = d.entityRev;
    if(Array.isArray(d.alliances)){
      state.alliances = d.alliances.map(a => {
        if(typeof a.memberCount !== 'number') a.memberCount = 100;
        if(typeof a.totalPower !== 'number'){
          if(typeof a.power === 'number') a.totalPower = a.power;
          else if(typeof a.avgPower === 'number') a.totalPower = a.memberCount * a.avgPower;
          else a.totalPower = 20000;
        }
        a.avgPower = a.memberCount > 0 ? (a.totalPower / a.memberCount) : 0;
        if(!['self','ally','enemy'].includes(a.side)) a.side = 'ally';
        if(typeof a.icon !== 'string') a.icon = '';
        return a;
      });
    }
    if(Array.isArray(d.zones)) state.zones = d.zones;
    if(Array.isArray(d.cities)) state.cities = d.cities.map(c => {
      if(!c.defStartTime) c.defStartTime = '19:00';
      const migrate = arr => (arr||[]).map(t => ({
        cityId: t.cityId,
        preWarPercent: t.preWarPercent !== undefined ? t.preWarPercent : (t.teams ? Math.round(t.teams / (c.totalTeams||100) * 100) : 50),
        postRevivePercent: t.postRevivePercent !== undefined ? t.postRevivePercent : 50,
        priority: t.priority !== undefined ? t.priority : 1,
      }));
      c.attackTargets = migrate(c.attackTargets);
      c.defendTargets = migrate(c.defendTargets);
      return c;
    });
    if(Array.isArray(d.dynRows)) state.dynRows = d.dynRows.slice(-5000);
    if(Array.isArray(d.narrativeLines)) state.narrativeLines = d.narrativeLines.slice(-1000);
  }catch(e){ console.warn('讀取失敗', e); }
}

function buildSettingsPatch(){ return { kind:'settings', rev:state.settingsRev, lamport:state.lamport, op:'upsert', data:{...state.settings} }; }
function buildEntityPatch(kind, id){
  const coll = kind==='alliance' ? state.alliances : kind==='zone' ? state.zones : state.cities;
  const entity = coll.find(x => x.id === id);
  if(!entity) return null;
  return { kind, id, rev: state.entityRev[kind][id] || 0, lamport: state.lamport, op:'upsert', data: JSON.parse(JSON.stringify(entity)) };
}
function buildDeletePatch(kind, id){ return { kind, id, rev: state.entityRev[kind][id] || 0, lamport: state.lamport, op:'delete' }; }
function collectDirtyPatches(){
  const patches = [];
  if(state.dirty.settings) patches.push(buildSettingsPatch());
  for(const kind of ['alliance','zone','city']){
    for(const id of state.dirty[kind]){ const p = buildEntityPatch(kind, id); if(p) patches.push(p); }
    for(const id of state.dirty[kind+'Deleted']) patches.push(buildDeletePatch(kind, id));
  }
  return patches;
}
function upsertEntity(kind, entity, {silent=false}={}){
  const coll = kind==='alliance' ? state.alliances : kind==='zone' ? state.zones : state.cities;
  const idx = coll.findIndex(x => x.id === entity.id);
  state.entityRev[kind][entity.id] = (state.entityRev[kind][entity.id] || 0) + 1;
  if(idx>=0) coll[idx] = entity; else coll.push(entity);
  if(!silent){ markDirty(kind, entity.id); tickLamport(); flushPatches(); }
  return entity;
}
function deleteEntity(kind, id, {silent=false}={}){
  const coll = kind==='alliance' ? state.alliances : kind==='zone' ? state.zones : state.cities;
  const idx = coll.findIndex(x => x.id === id);
  if(idx<0) return;
  coll.splice(idx,1);
  state.entityRev[kind][id] = (state.entityRev[kind][id] || 0) + 1;
  if(!silent){ markDirty(kind+'Deleted', id); tickLamport(); flushPatches(); }
}
function updateSettings(patch, {silent=false}={}){
  Object.assign(state.settings, patch); state.settingsRev++;
  if(!silent){ markDirty('settings'); tickLamport(); flushPatches(); }
}
function applyPatch(patch){
  if(!patch || !patch.kind) return false;
  tickLamport(patch.lamport || 0);
  const { kind, id, rev, op, data } = patch;
  if(kind==='settings'){
    if(!isNewer(rev, state.settingsRev)) return false;
    Object.assign(state.settings, data); state.settingsRev = rev; return true;
  }
  const coll = kind==='alliance' ? state.alliances : kind==='zone' ? state.zones : kind==='city' ? state.cities : null;
  if(!coll) return false;
  const localRev = state.entityRev[kind][id] || 0;
  if(!isNewer(rev, localRev)) return false;
  const idx = coll.findIndex(x => x.id === id);
  if(op==='delete'){ if(idx>=0) coll.splice(idx,1); state.entityRev[kind][id] = rev; return true; }
  if(op==='upsert'){ if(idx>=0) coll[idx] = {...coll[idx], ...data}; else coll.push(data); state.entityRev[kind][id] = rev; return true; }
  return false;
}
let sender = null;
function registerSender(fn){ sender = fn; }
let flushTimer = null;
function flushPatches(){
  if(!sender) return;
  clearTimeout(flushTimer);
  flushTimer = setTimeout(() => {
    const patches = collectDirtyPatches();
    if(patches.length === 0) return;
    sender(patches); clearDirty();
  }, 40);
}
function buildFullSnapshot(){
  return { type:'sync_snapshot', epoch: state.roomEpoch, lamport: state.lamport, settingsRev: state.settingsRev,
    settings: {...state.settings}, entityRev: JSON.parse(JSON.stringify(state.entityRev)),
    alliances: JSON.parse(JSON.stringify(state.alliances)), zones: JSON.parse(JSON.stringify(state.zones)),
    cities: JSON.parse(JSON.stringify(state.cities)), clientId: state.myClientId, name: state.commanderName };
}
function applyFullSnapshot(snap){
  if(!snap) return false;
  if(snap.epoch && state.roomEpoch && snap.epoch !== state.roomEpoch) state.roomEpoch = snap.epoch;
  if(isNewer(snap.settingsRev, state.settingsRev)){ Object.assign(state.settings, snap.settings); state.settingsRev = snap.settingsRev; }
  const mergeColl = (kind, incoming) => {
    const coll = kind==='alliance' ? state.alliances : kind==='zone' ? state.zones : state.cities;
    const map = new Map(coll.map(x => [x.id, x]));
    for(const ent of incoming){
      const localRev = state.entityRev[kind][ent.id] || 0;
      const remoteRev = snap.entityRev?.[kind]?.[ent.id] || 0;
      if(isNewer(remoteRev, localRev)){ map.set(ent.id, ent); state.entityRev[kind][ent.id] = remoteRev; }
    }
    const incomingIds = new Set(incoming.map(x => x.id));
    for(const [id] of [...map]){
      if(!incomingIds.has(id)){
        const remoteRev = snap.entityRev?.[kind]?.[id] || 0;
        const localRev = state.entityRev[kind][id] || 0;
        if(isNewer(remoteRev, localRev)) map.delete(id);
      }
    }
    coll.length = 0; for(const ent of map.values()) coll.push(ent);
  };
  mergeColl('alliance', snap.alliances || []);
  mergeColl('zone', snap.zones || []);
  mergeColl('city', snap.cities || []);
  tickLamport(snap.lamport || 0);
  return true;
}

/* ================== Transport ================== */
let client = null;
let heartbeatTimer = null, hostCheckTimer = null, pingTimer = null, reconnectTimer = null;
let lockGCTimer = null, lockRenewTimer = null;
const isConnected = () => state.connected && !!client;

function connectMQTT(roomCode, asHost){
  if(!roomCode || roomCode.length!==6){ emit(EVT.DEBUG, {msg:'❌ 房間碼必須為6位數', err:true}); return; }
  if(!state.commanderName){ emit(EVT.DEBUG, {msg:'❌ 請先填寫指揮官名稱', err:true}); return; }
  if(client){ try{ client.disconnect(); }catch(e){} client = null; }
  state.roomCode = roomCode;
  state.myClientId = 'slg_' + uid();
  state.connecting = true; state.connected = false;
  emit(EVT.CONN); emit(EVT.DEBUG, {msg:'🟡 正在連線至中繼伺服器...'});
  const c = new Paho.MQTT.Client(MQTT_URI, state.myClientId);
  client = c;
  c.onConnectionLost = resp => { state.connected = false; state.connecting = false; emit(EVT.CONN); emit(EVT.DEBUG, {msg:'🔴 連線中斷：'+(resp.errorCode||'unknown'), err:true}); scheduleReconnect(); };
  c.onMessageArrived = msg => { try{ handleIncoming(JSON.parse(msg.payloadString)); }catch(e){ console.warn('訊息解析失敗', e); } };
  c.connect({
    onSuccess: () => {
      state.connected = true; state.connecting = false;
      emit(EVT.CONN); emit(EVT.DEBUG, {msg:'🟢 成功連接中繼伺服器！'});
      c.subscribe(TOPIC_PREFIX + roomCode);
      if(asHost){ state.isHost = true; state.hostName = state.commanderName; state.roomEpoch = uid(); }
      else { state.isHost = false; state.hostName = ''; }
      state.members[state.myClientId] = { name: state.commanderName, joinTime: Date.now(), isHost: state.isHost, lastSeen: Date.now() };
      emit(EVT.MEMBERS); emit(EVT.HOST); saveState();
      startHeartbeat(); startPingCheck(); startEditLockGC();
      if(state.isHost) setTimeout(() => publish(buildFullSnapshot()), 300);
      else publish({ type:'sync_request', clientId:state.myClientId, name:state.commanderName });
    },
    onFailure: err => { state.connected = false; state.connecting = false; emit(EVT.CONN); emit(EVT.DEBUG, {msg:'🔴 連線失敗：'+(err.errorCode||'無法連接'), err:true}); scheduleReconnect(); },
    keepAliveInterval:30, cleanSession:true, reconnect:true, timeout:10, useSSL:true,
  });
}
function scheduleReconnect(){
  clearTimeout(reconnectTimer);
  if(!state.roomCode) return;
  reconnectTimer = setTimeout(() => { if(!state.connected && state.roomCode){ emit(EVT.DEBUG, {msg:'🟡 嘗試重新連線...'}); connectMQTT(state.roomCode, state.isHost); } }, 3000);
}
function disconnectMQTT(){
  clearInterval(heartbeatTimer); clearInterval(hostCheckTimer); clearInterval(pingTimer);
  clearTimeout(reconnectTimer); clearInterval(lockGCTimer); clearInterval(lockRenewTimer);
  if(client){ try{ client.disconnect(); }catch(e){} client = null; }
  state.connected = false; state.connecting = false; state.isHost = false; state.hostName = ''; state.members = {}; state.roomCode = '';
  emit(EVT.CONN); emit(EVT.MEMBERS); emit(EVT.HOST); emit(EVT.DEBUG, {msg:'🔴 已中斷連線'}); saveState();
}
function publish(payload){
  if(!state.connected || !client) return;
  try{ const msg = new Paho.MQTT.Message(JSON.stringify(payload)); msg.destinationName = TOPIC_PREFIX + state.roomCode; client.send(msg); }catch(e){ console.warn('發送失敗', e); }
}
function startHeartbeat(){
  clearInterval(heartbeatTimer);
  heartbeatTimer = setInterval(() => {
    if(!state.connected) return;
    const me = state.members[state.myClientId];
    if(me){ me.lastSeen = Date.now(); me.isHost = state.isHost; me.name = state.commanderName; }
    publish({ type:'heartbeat', clientId:state.myClientId, name:state.commanderName, joinTime: me?.joinTime || Date.now(), isHost: state.isHost, timestamp: Date.now() });
  }, HEARTBEAT_INTERVAL);
  clearInterval(hostCheckTimer);
  hostCheckTimer = setInterval(checkHostHealth, HEARTBEAT_INTERVAL);
}
function checkHostHealth(){
  if(!state.connected) return;
  const now = Date.now();
  let hostAlive = false;
  const online = [];
  for(const cid in state.members){
    const m = state.members[cid];
    if(now - m.lastSeen < HOST_TIMEOUT){ online.push({cid, m}); if(m.isHost) hostAlive = true; }
    else delete state.members[cid];
  }
  emit(EVT.MEMBERS);
  if(!hostAlive && online.length > 0){
    online.sort((a,b) => a.m.joinTime - b.m.joinTime);
    const heir = online[0];
    for(const cid in state.members) state.members[cid].isHost = false;
    state.members[heir.cid].isHost = true;
    state.isHost = (heir.cid === state.myClientId);
    state.hostName = heir.m.name;
    emit(EVT.HOST);
    logSystem(`👑 房主已轉移給 ${heir.m.name}`);
    if(state.isHost){ state.roomEpoch = uid(); setTimeout(() => publish(buildFullSnapshot()), 500); }
    else setTimeout(() => publish({ type:'sync_request', clientId:state.myClientId, name:state.commanderName }), 1500);
  }
}
function startPingCheck(){ clearInterval(pingTimer); pingTimer = setInterval(() => { if(!state.connected || !client) return; publish({ type:'ping', clientId:state.myClientId, t:Date.now() }); }, PING_INTERVAL); }
function startEditLockGC(){
  clearInterval(lockGCTimer);
  lockGCTimer = setInterval(() => {
    const now = Date.now(); let changed = false;
    for(const cityId in state.editLocks){ const lock = state.editLocks[cityId]; if(lock.expiresAt && lock.expiresAt < now){ delete state.editLocks[cityId]; changed = true; } }
    if(changed) emit(EVT.LOCKS);
  }, 10000);
  clearInterval(lockRenewTimer);
  lockRenewTimer = setInterval(() => {
    if(!state.connected) return;
    for(const cityId in state.editLocks){ if(state.editLocks[cityId].clientId === state.myClientId) publish({ type:'edit_lock_renew', cityId, clientId:state.myClientId }); }
  }, 15000);
}
const incomingVizChunks = new Map();
const incomingDynChunks = new Map();

function handleIncoming(payload){
  if(!payload || !payload.type) return;
  if(payload.clientId){
    const m = state.members[payload.clientId];
    if(m){ m.lastSeen = Date.now(); if(payload.name) m.name = payload.name; if(payload.isHost !== undefined) m.isHost = payload.isHost; }
    else if(payload.name && payload.joinTime) state.members[payload.clientId] = { name:payload.name, joinTime:payload.joinTime, isHost:!!payload.isHost, lastSeen:Date.now() };
  }
  switch(payload.type){
    case 'heartbeat': emit(EVT.MEMBERS); break;
    case 'ping': publish({ type:'pong', clientId:state.myClientId, t:payload.t }); break;
    case 'pong': if(payload.t){ state.pingMs = Date.now() - payload.t; emit(EVT.PING); } break;
    case 'sync_patch': {
      if(payload.clientId === state.myClientId) return;
      let changed = false;
      for(const p of payload.patches || []) if(applyPatch(p)) changed = true;
      if(changed){ emit(EVT.DATA); saveState(); }
      break;
    }
    case 'sync_snapshot': {
      if(payload.clientId === state.myClientId) return;
      if(applyFullSnapshot(payload)){ emit(EVT.DATA); saveState(); }
      break;
    }
    case 'sync_request': {
      if(!state.isHost || payload.clientId === state.myClientId) return;
      publish(buildFullSnapshot());
      break;
    }
    case 'edit_lock': state.editLocks[payload.cityId] = { name:payload.name, clientId:payload.clientId, expiresAt: Date.now() + EDIT_LOCK_TTL }; emit(EVT.LOCKS); break;
    case 'edit_unlock': delete state.editLocks[payload.cityId]; emit(EVT.LOCKS); break;
    case 'edit_lock_renew': { const lock = state.editLocks[payload.cityId]; if(lock && lock.clientId === payload.clientId) lock.expiresAt = Date.now() + EDIT_LOCK_TTL; break; }
    case 'trigger_simulate': emit(EVT.SIM_TRIGGER, payload); break;
    case 'viz_chunk': {
      incomingVizChunks.set(payload.part, payload.data);
      if(incomingVizChunks.size === payload.total){
        let full = '';
        for(let i=0;i<payload.total;i++) full += incomingVizChunks.get(i) || '';
        incomingVizChunks.clear();
        try{ const parsed = JSON.parse(full); if(parsed.baseMin !== undefined) state.simBaseMin = parsed.baseMin; for(const [sec, snap] of parsed.snapEntries) viz.ingestSnapshot(sec, snap); viz.finalize(); }catch(e){ console.warn('viz chunk 解析失敗', e); }
      }
      break;
    }
    case 'dyn_chunk': {
      incomingDynChunks.set(payload.part, payload.data);
      if(incomingDynChunks.size === payload.total){
        let full = '';
        for(let i=0;i<payload.total;i++) full += incomingDynChunks.get(i) || '';
        incomingDynChunks.clear();
        try{ state.dynRows = JSON.parse(full); emit(EVT.DYN_RESULT); }catch(e){ console.warn('dyn chunk 解析失敗', e); }
      }
      break;
    }
  }
}
/* ============================================================
   模擬引擎 v7.3
   ============================================================ */
async function runSimulation(cities, settings, opts = {}){
  const { onProgress, shouldAbort, snapshotAt = new Set(), onSnapshot, dynSampleAt = new Set(), onDynSample } = opts;
  const timeLimitSec = settings.timeLimitMin * 60;
  const consumeMin = settings.consumeMinPerMin;
  const consumeMax = settings.consumeMaxPerMin;
  const maxRatio = settings.maxLossRatio;
  const minRatio = settings.minLossRatio;
  const siegeEff = settings.siegeEfficiency;
  const marchSec = Math.max(0, Math.round(settings.marchTimeSec || 0));

  const N = cities.length;
  const defStartMins = cities.map(c => hhmmToMinutes(c.defStartTime || '19:00'));
  const minDefStartMin = Math.min(...defStartMins);
  const defStartRel = defStartMins.map(m => m - minDefStartMin);
  const maxDefStartRel = Math.max(...defStartRel);
  const totalSimSec = (maxDefStartRel * 60) + timeLimitSec;

  const cityId = new Array(N), cityName = new Array(N), cityZoneId = new Array(N);
  const cityAllianceId = new Array(N), citySide = new Array(N);
  const avgPower = new Float64Array(N), wallSec = new Float64Array(N);
  const atHome = new Float64Array(N);
  const totalTeams = new Float64Array(N);
  const fallen = new Uint8Array(N);
  const cooldownSec = new Int32Array(N);
  const cooldownMapLocal = Array.from({length:N}, () => new Map());
  const cooldownMapField = Array.from({length:N}, () => new Map());
  const defLossAcc = new Float64Array(N);
  const defStartSecArr = new Int32Array(N);
  const defenseEndSecArr = new Int32Array(N);
  const capitalByAlliance = new Map();
  const marchingOut = Array.from({length:N}, () => []);
  const marchingBack = Array.from({length:N}, () => []);
  const outbound = Array.from({length:N}, () => []);
  const cityHasBeenWarned = new Uint8Array(N);
  const narrativeLines = [];

  function fmtAbsTime(t) {
    const totalSec = (minDefStartMin * 60) + t;
    const h = Math.floor(totalSec / 3600) % 24;
    const m = Math.floor((totalSec % 3600) / 60);
    const s = totalSec % 60;
    return `${String(h).padStart(2,'0')}:${String(m).padStart(2,'0')}:${String(s).padStart(2,'0')}`;
  }

  for(let i=0;i<N;i++){
    const c = cities[i];
    cityId[i] = c.id; cityName[i] = c.name;
    cityZoneId[i] = c.zoneId || ''; cityAllianceId[i] = c.allianceId || ''; citySide[i] = c.side || 'npc';
    avgPower[i] = c.avgPower || 1;
    wallSec[i] = (c.wallMin || 0) * 60;
    totalTeams[i] = Number(c.totalTeams) || 0;
    cooldownSec[i] = Math.max(1, Math.round((c.cooldownMin || 0) * 60));
    defStartSecArr[i] = defStartRel[i] * 60;
    defenseEndSecArr[i] = defStartSecArr[i] + timeLimitSec;
    if(c.isCapital && c.allianceId && !capitalByAlliance.has(c.allianceId)) capitalByAlliance.set(c.allianceId, i);
  }

  const idxOf = new Map(cityId.map((id, i) => [id, i]));

  for(let i=0;i<N;i++){
    const c = cities[i];
    const total = totalTeams[i];
    atHome[i] = total;
    const routesToAdd = [];
    let preWarTotal = 0;

    const addRoute = (targetId, prePct, postPct, priority, isAttack) => {
      const tIdx = idxOf.get(targetId);
      if(tIdx === undefined) return;
      const pre = clamp(Number(prePct) || 0, 0, 100);
      if(pre <= 0) return;
      const teams = Math.floor(total * pre / 100);
      if(teams <= 0) return;
      preWarTotal += teams;
      routesToAdd.push({ tIdx, teams, prePct: pre, postPct: clamp(Number(postPct)||0,0,100), priority: Number(priority)||99, isAttack });
    };

    for(const t of (c.attackTargets || [])) addRoute(t.cityId, t.preWarPercent, t.postRevivePercent, t.priority, true);
    for(const t of (c.defendTargets || [])) addRoute(t.cityId, t.preWarPercent, t.postRevivePercent, t.priority, false);

    if(preWarTotal > total){
      const scale = total / preWarTotal;
      for(const r of routesToAdd) r.teams = Math.floor(r.teams * scale);
    }

    for(const r of routesToAdd){
      atHome[i] -= r.teams;
      const activeFrom = Math.max(defStartSecArr[i], defStartSecArr[r.tIdx] - marchSec) + marchSec;
      const activeUntil = defStartSecArr[r.tIdx] + timeLimitSec;
      outbound[i].push({
        targetIdx: r.tIdx, count: r.teams, initialCount: r.teams,
        activeFrom, activeUntil, lossAcc: 0, isAttack: r.isAttack,
        postRevivePercent: r.postPct, priority: r.priority,
        consumeThisMin: consumeMin, hasArrived: false,
      });
    }
  }

  const attackersOnCity = Array.from({length:N}, () => []);
  const defendersOnCity = Array.from({length:N}, () => []);
  function rebuildIndexes(){
    for(let i=0;i<N;i++){ attackersOnCity[i].length = 0; defendersOnCity[i].length = 0; }
    for(let i=0;i<N;i++){
      for(let r=0;r<outbound[i].length;r++){
        const route = outbound[i][r];
        if(route.isAttack) attackersOnCity[route.targetIdx].push({ srcIdx:i, routeIdx:r });
        else defendersOnCity[route.targetIdx].push({ srcIdx:i, routeIdx:r });
      }
    }
  }
  rebuildIndexes();

  function findCapitalFor(aid){
    if(!aid) return -1;
    const idx = capitalByAlliance.get(aid);
    if(idx === undefined || fallen[idx]) return -1;
    return idx;
  }

  function sendToFieldCooldown(srcIdx, teams, t){
    if(teams <= 0) return;
    teams = Math.floor(teams);
    if(teams <= 0) return;
    let destIdx = srcIdx;
    if(fallen[srcIdx]){
      const cap = findCapitalFor(cityAllianceId[srcIdx]);
      if(cap < 0) return;
      destIdx = cap;
    }
    if(marchSec > 0){
      marchingBack[destIdx].push({ teams, arrivalAt: t + marchSec });
    } else {
      const alignedT = Math.floor(t / COMBAT_TICK) * COMBAT_TICK;
      const readyAt = alignedT + cooldownSec[destIdx];
      cooldownMapField[destIdx].set(readyAt, (cooldownMapField[destIdx].get(readyAt) || 0) + teams);
    }
  }
  function sendToLocalCooldown(destIdx, teams, t){
    if(teams <= 0) return;
    teams = Math.floor(teams);
    if(teams <= 0) return;
    if(fallen[destIdx]){
      const cap = findCapitalFor(cityAllianceId[destIdx]);
      if(cap < 0) return;
      destIdx = cap;
    }
    const alignedT = Math.floor(t / COMBAT_TICK) * COMBAT_TICK;
    const readyAt = alignedT + cooldownSec[destIdx];
    cooldownMapLocal[destIdx].set(readyAt, (cooldownMapLocal[destIdx].get(readyAt) || 0) + teams);
  }

  function processMarching(t){
    for(let i=0;i<N;i++){
      const q = marchingBack[i];
      for(let k = q.length-1; k >= 0; k--){
        if(t >= q[k].arrivalAt){
          const destIdx = fallen[i] ? (findCapitalFor(cityAllianceId[i]) ?? -1) : i;
          if(destIdx >= 0){
            const readyAt = t + cooldownSec[destIdx];
            cooldownMapField[destIdx].set(readyAt, (cooldownMapField[destIdx].get(readyAt) || 0) + q[k].teams);
          }
          q.splice(k, 1);
        }
      }
    }
    for(let i=0;i<N;i++){
      const q = marchingOut[i];
      for(let k = q.length-1; k >= 0; k--){
        if(t >= q[k].arrivalAt){
          const route = outbound[i][q[k].routeIdx];
          if(route){
            route.count += q[k].teams;
            if(!route.hasArrived){
              route.hasArrived = true;
              narrativeLines.push({ type:'info', text:`【${fmtAbsTime(t)}】${cityName[i]} 的部隊抵達 ${cityName[route.targetIdx]}，戰鬥打響。` });
            }
          }
          q.splice(k, 1);
        }
      }
    }
  }

  function pushMarchingOut(srcIdx, routeIdx, teams, t){
    if(teams <= 0) return;
    if(marchSec > 0){
      marchingOut[srcIdx].push({ teams, arrivalAt: t + marchSec, routeIdx });
    } else {
      outbound[srcIdx][routeIdx].count += teams;
    }
  }

  function processCooldown(t){
    for(let i=0;i<N;i++){
      if(fallen[i]) continue;
      const map = cooldownMapLocal[i];
      let revived = 0;
      for(const [readyAt, teams] of map){ if(t >= readyAt){ revived += teams; map.delete(readyAt); } }
      if(revived > 0) atHome[i] += revived;
    }
    for(let i=0;i<N;i++){
      if(fallen[i]) continue;
      const map = cooldownMapField[i];
      let revived = 0;
      for(const [readyAt, teams] of map){ if(t >= readyAt){ revived += teams; map.delete(readyAt); } }
      if(revived <= 0) continue;
      if(outbound[i].length === 0){ atHome[i] += revived; continue; }
      const sorted = outbound[i].map((route, rIdx) => ({ route, rIdx }))
        .filter(x => (x.route.postRevivePercent || 0) > 0)
        .sort((a, b) => (a.route.priority || 99) - (b.route.priority || 99));
      let remaining = revived;
      for(const item of sorted){
        if(remaining <= 0) break;
        const share = Math.floor(revived * item.route.postRevivePercent / 100);
        const assign = Math.min(share, remaining);
        if(assign > 0){
          pushMarchingOut(i, item.rIdx, assign, t);
          remaining -= assign;
          narrativeLines.push({ type:'revive', text:`【${fmtAbsTime(t)}】${cityName[i]} 的復活部隊集結完畢（${assign} 隊），再次出發前往 ${cityName[item.route.targetIdx]}。` });
        }
      }
      if(remaining > 0) atHome[i] += remaining;
    }
  }

  function combatRound(t){
    for(let dIdx=0; dIdx<N; dIdx++){
      if(fallen[dIdx]) continue;
      if(t < defStartSecArr[dIdx] || t > defenseEndSecArr[dIdx]) continue;
      const activeAttackLines = [];
      for(const {srcIdx, routeIdx} of attackersOnCity[dIdx]){
        if(fallen[srcIdx]) continue;
        const route = outbound[srcIdx][routeIdx];
        if(route.count <= 0) continue;
        if(t < route.activeFrom || t > route.activeUntil) continue;
        activeAttackLines.push({ srcIdx, routeIdx, route, attackerCount: route.count });
      }
      if(activeAttackLines.length === 0) continue;

      if(t % 60 === 0){
        for(const line of activeAttackLines){
          const aP = avgPower[line.srcIdx];
          const dP = avgPower[dIdx];
          const ratio = Math.min(aP, dP) / Math.max(aP, dP);
          const pMax = 0.1 + 0.8 * (1 - ratio);
          const isMax = Math.random() < pMax;
          line.route.consumeThisMin = isMax ? consumeMax : consumeMin;
        }
      }

      let totalDef = atHome[dIdx];
      const defLines = [];
      for(const {srcIdx, routeIdx} of defendersOnCity[dIdx]){
        if(fallen[srcIdx]) continue;
        const route = outbound[srcIdx][routeIdx];
        if(route.count <= 0) continue;
        if(t < route.activeFrom || t > route.activeUntil) continue;
        defLines.push({ srcIdx, routeIdx, route, count: route.count });
        totalDef += route.count;
      }

      if(totalDef === 0 && !fallen[dIdx] && !cityHasBeenWarned[dIdx] && activeAttackLines.length > 0){
        cityHasBeenWarned[dIdx] = 1;
        narrativeLines.push({ type:'warn', text:`【${fmtAbsTime(t)}】⚠️ ${cityName[dIdx]} 的守軍全數陣亡，城牆暴露在敵軍面前！` });
      }

      activeAttackLines.sort((a,b) => b.attackerCount - a.attackerCount);
      let remainingDef = totalDef;
      for(const line of activeAttackLines){
        const assigned = Math.min(remainingDef, line.attackerCount);
        line.defAssigned = assigned;
        remainingDef -= assigned;
      }

      let totalDLoss = 0;
      for(const line of activeAttackLines){
        if(line.defAssigned <= 0) continue;
        const halfConsume = (line.route.consumeThisMin || consumeMin) / 2;
        const aP = avgPower[line.srcIdx];
        const dP = avgPower[dIdx];
        const totAvg = aP + dP;
        let aRatio = clamp(dP / totAvg, minRatio, maxRatio);
        let dRatio = clamp(aP / totAvg, minRatio, maxRatio);
        line.route.lossAcc += halfConsume * aRatio;
        const aKills = Math.floor(line.route.lossAcc);
        if(aKills > 0){
          const actual = Math.min(aKills, line.route.count);
          line.route.lossAcc -= actual;
          line.route.count -= actual;
          sendToFieldCooldown(line.srcIdx, actual, t);
        }
        totalDLoss += halfConsume * dRatio;
      }

      let totalDKills = Math.floor(totalDLoss);
      defLossAcc[dIdx] += totalDLoss - totalDKills;
      if(defLossAcc[dIdx] >= 1){
        const extra = Math.floor(defLossAcc[dIdx]);
        totalDKills += extra;
        defLossAcc[dIdx] -= extra;
      }
      for(const dl of defLines){
        if(totalDKills <= 0) break;
        const deduct = Math.min(dl.route.count, totalDKills);
        dl.route.count -= deduct;
        totalDKills -= deduct;
        sendToFieldCooldown(dl.srcIdx, deduct, t);
      }
      if(totalDKills > 0 && atHome[dIdx] > 0){
        const deduct = Math.min(atHome[dIdx], totalDKills);
        atHome[dIdx] -= deduct;
        totalDKills -= deduct;
        sendToLocalCooldown(dIdx, deduct, t);
      }

      let totalSiege = 0;
      for(const line of activeAttackLines){
        const currentCount = line.route.count;
        const siegeTeams = currentCount - line.defAssigned;
        if(siegeTeams > 0) totalSiege += siegeTeams;
      }
      if(totalSiege > 0 && wallSec[dIdx] > 0){
        wallSec[dIdx] -= totalSiege * siegeEff * COMBAT_TICK;
        if(wallSec[dIdx] <= 0){
          wallSec[dIdx] = 0;
          fallen[dIdx] = 1;
          narrativeLines.push({ type:'capture', text:`【${fmtAbsTime(t)}】💥 ${cityName[dIdx]} 城牆歸零，城池正式淪陷！` });
          atHome[dIdx] = 0;
          const cap = findCapitalFor(cityAllianceId[dIdx]);
          if(cap >= 0){
            for(const [readyAt, teams] of cooldownMapLocal[dIdx]) cooldownMapLocal[cap].set(readyAt, (cooldownMapLocal[cap].get(readyAt) || 0) + teams);
            cooldownMapLocal[dIdx].clear();
            for(const [readyAt, teams] of cooldownMapField[dIdx]) cooldownMapField[cap].set(readyAt, (cooldownMapField[cap].get(readyAt) || 0) + teams);
            cooldownMapField[dIdx].clear();
          } else {
            cooldownMapLocal[dIdx].clear();
            cooldownMapField[dIdx].clear();
          }
          for(let i=0;i<N;i++){
            if(i === dIdx){ outbound[i].length = 0; continue; }
            const keep = [];
            for(let rIdx=0; rIdx<outbound[i].length; rIdx++){
              if(outbound[i][rIdx].targetIdx !== dIdx) keep.push(outbound[i][rIdx]);
            }
            outbound[i] = keep;
          }
          for(const q of marchingOut[dIdx]){ if(cap >= 0) cooldownMapField[cap].set(t + cooldownSec[cap], (cooldownMapField[cap].get(t + cooldownSec[cap]) || 0) + q.teams); }
          marchingOut[dIdx].length = 0;
          for(const q of marchingBack[dIdx]){ if(cap >= 0) cooldownMapField[cap].set(t + cooldownSec[cap], (cooldownMapField[cap].get(t + cooldownSec[cap]) || 0) + q.teams); }
          marchingBack[dIdx].length = 0;
          for(let i=0;i<N;i++){
            if(i === dIdx) continue;
            const q = marchingOut[i];
            for(let k=q.length-1; k>=0; k--){
              if(q[k].targetIdx === dIdx){
                marchingBack[i].push({ teams: q[k].teams, arrivalAt: q[k].arrivalAt });
                q.splice(k, 1);
              }
            }
          }
          rebuildIndexes();
        }
      }
    }
  }

  function emitSnapshot(sec){
    if(!onSnapshot) return;
    const snap = new Array(N);
    for(let i=0;i<N;i++){
      let outCnt = 0; for(const r of outbound[i]) outCnt += r.count;
      let localCd = 0; for(const v of cooldownMapLocal[i].values()) localCd += v;
      let fieldCd = 0; for(const v of cooldownMapField[i].values()) fieldCd += v;
      let mo = 0, mb = 0;
      for(const q of marchingOut[i]) mo += q.teams;
      for(const q of marchingBack[i]) mb += q.teams;
      let siegeTeams = 0, siegeLines = 0;
      if(!fallen[i] && sec >= defStartSecArr[i] && sec <= defenseEndSecArr[i]){
        for(const {srcIdx, routeIdx} of attackersOnCity[i]){
          if(fallen[srcIdx]) continue;
          const r = outbound[srcIdx][routeIdx];
          if(r.count > 0 && sec >= r.activeFrom && sec <= r.activeUntil){ siegeTeams += r.count; siegeLines++; }
        }
      }
      snap[i] = { id: cityId[i], r: atHome[i], o: outCnt, c: localCd + fieldCd, w: wallSec[i], f: fallen[i], si: siegeTeams, sl: siegeLines };
    }
    onSnapshot(sec, snap);
  }

  function emitDynSample(sec){
    if(!onDynSample) return;
    const rows = [];
    for(let sIdx=0; sIdx<N; sIdx++){
      for(let rIdx=0; rIdx<outbound[sIdx].length; rIdx++){
        const route = outbound[sIdx][rIdx];
        const tIdx = route.targetIdx;
        if(sec < route.activeFrom && route.count <= 0) continue;
        let srcFieldCd = 0; for(const v of cooldownMapField[sIdx].values()) srcFieldCd += v;
        let srcMarchBack = 0; for(const q of marchingBack[sIdx]) srcMarchBack += q.teams;
        let tgtLocalCd = 0; for(const v of cooldownMapLocal[tIdx].values()) tgtLocalCd += v;
        let tgtMarchBack = 0; for(const q of marchingBack[tIdx]) tgtMarchBack += q.teams;
        rows.push({
          sec,
          srcCity: cityName[sIdx], srcId: cityId[sIdx], srcSide: citySide[sIdx],
          isAttack: route.isAttack,
          tgtCity: cityName[tIdx], tgtId: cityId[tIdx], tgtSide: citySide[tIdx],
          zoneId: cityZoneId[sIdx],
          consumeThisMin: route.consumeThisMin,
          ownRemain: Math.round(route.count),
          ownCd: Math.round(srcFieldCd),
          ownMarch: Math.round(srcMarchBack),
          tgtRemain: Math.round(atHome[tIdx]),
          tgtCd: Math.round(tgtLocalCd),
          tgtMarch: Math.round(tgtMarchBack),
          wallSec: wallSec[tIdx],
          tgtFallen: !!fallen[tIdx],
        });
      }
    }
    onDynSample(sec, rows);
  }

  let chunkCount = 0;
  const totalTicksEst = totalSimSec + 1;
  const criticalEvents = [];
  let t = 0;

  while(t <= totalSimSec){
    if(shouldAbort && shouldAbort()) return {criticalEvents, aborted:true, minDefStartMin, totalSimSec, narrativeLines};
    if(chunkCount >= SIM_CHUNK){
      chunkCount = 0;
      if(onProgress) onProgress({progress: t / totalTicksEst, t});
      await yieldToMain();
    }
    processMarching(t);
    processCooldown(t);
    if(t > 0 && t % COMBAT_TICK === 0) combatRound(t);
    t++;
    chunkCount++;
    if(snapshotAt.has(t)) emitSnapshot(t);
    if(dynSampleAt.has(t)) emitDynSample(t);
  }

  if(onProgress) onProgress({progress: 1, t});

  const finalStates = [];
  for(let i=0;i<N;i++){
    let outCnt = 0; for(const r of outbound[i]) outCnt += r.count;
    let lc = 0; for(const v of cooldownMapLocal[i].values()) lc += v;
    let fc = 0; for(const v of cooldownMapField[i].values()) fc += v;
    let mb = 0; for(const q of marchingBack[i]) mb += q.teams;
    let mo = 0; for(const q of marchingOut[i]) mo += q.teams;
    finalStates.push({ id: cityId[i], name: cityName[i], atHome: Math.round(atHome[i]), outbound: Math.round(outCnt), cooldown: lc + fc, marchingBack: mb, marchingOut: mo, wallSec: wallSec[i], fallen: !!fallen[i] });
  }
  return { criticalEvents, aborted:false, minDefStartMin, totalSimSec, finalStates, narrativeLines };
}

/* ============ Worker ============ */
const WORKER_SOURCE = `
const hhmmToMinutes = ${hhmmToMinutes.toString()};
const minutesToHHMM = ${minutesToHHMM.toString()};
const computeAllocation = ${computeAllocation.toString()};
const yieldToMain = ${yieldToMain.toString()};
const fmtSimTime = ${fmtSimTime.toString()};
const clamp = ${clamp.toString()};
const COMBAT_TICK = 30;
const runSimulation = ${runSimulation.toString()};
const SIM_CHUNK = 500;
self.onmessage = async (e) => {
  const { type, payload } = e.data || {};
  if(type === 'abort'){ self.__abort = true; return; }
  if(type !== 'run') return;
  const { cities, settings, snapshotsAt, dynSampleAt, runId } = payload;
  const snapSet = new Set(snapshotsAt || []);
  const dynSet = new Set(dynSampleAt || []);
  try {
    const result = await runSimulation(cities, settings, {
      onProgress: ({progress, t}) => self.postMessage({type:'progress', runId, progress, t}),
      shouldAbort: () => self.__abort === true,
      snapshotAt: snapSet,
      onSnapshot: (sec, snap) => self.postMessage({type:'snapshot', runId, sec, snap}),
      dynSampleAt: dynSet,
      onDynSample: (sec, rows) => self.postMessage({type:'dyn_sample', runId, sec, rows}),
    });
    self.postMessage({type:'done', runId, result});
  } catch(err){
    self.postMessage({type:'error', runId, error: String(err && err.stack || err)});
  }
};
`;

let simWorker = null;
let simWorkerAvailable = null;
let simRunId = 0;
function getWorker(){
  if(simWorkerAvailable === false) return null;
  if(simWorker) return simWorker;
  try{
    const blob = new Blob([WORKER_SOURCE], {type:'application/javascript'});
    simWorker = new Worker(URL.createObjectURL(blob));
    simWorkerAvailable = true;
    console.log('%c[Worker] 已啟動', 'color:#22ff88;font-weight:bold');
    return simWorker;
  }catch(e){
    simWorkerAvailable = false; simWorker = null;
    console.warn('%c[Worker] 無法啟動，改用主執行緒同步模式', 'color:#ffcc00;font-weight:bold', e.message);
    return null;
  }
}

/* ============ Viz ============ */
const viz = (() => {
  const NODE_RADIUS = 14;
  let cvStatic, ctxStatic, cvLive, ctxLive, containerEl;
  let layout = { nodes:new Map(), zones:[], bounds:{w:0, h:0} };
  let snapshots = new Map();
  let snapshotSecs = [];
  let currentSec = 0;

  function init(){
    containerEl = document.getElementById('vizContainer');
    if(!containerEl) return;
    cvStatic = document.getElementById('vizStatic');
    cvLive = document.getElementById('vizLive');
    ctxStatic = cvStatic.getContext('2d');
    ctxLive = cvLive.getContext('2d');
    const slider = document.getElementById('vizSlider');
    const timeLabel = document.getElementById('vizTimeLabel');
    slider.addEventListener('input', () => { currentSec = parseInt(slider.value, 10) || 0; renderLive(currentSec); renderClearPanel(currentSec); if(timeLabel) timeLabel.textContent = formatAbsTime(currentSec); });
    window.addEventListener('resize', () => { if(!containerEl.clientWidth) return; computeLayout(); resizeCanvases(); renderStatic(); renderLive(currentSec); });
    on(EVT.DATA, () => { computeLayout(); resizeCanvases(); renderStatic(); renderLive(currentSec); });
    on(EVT.VIZ_SNAPSHOTS, ({snapshots:s, secs}) => {
      snapshots = s; snapshotSecs = secs;
      if(secs.length > 0){
        slider.min = secs[0]; slider.max = secs[secs.length-1]; slider.value = secs[secs.length-1]; currentSec = secs[secs.length-1]; slider.disabled = false;
        computeLayout(); resizeCanvases(); renderStatic(); renderLive(currentSec); renderClearPanel(currentSec);
        if(timeLabel) timeLabel.textContent = formatAbsTime(currentSec);
      }
    });
    on(EVT.VIZ_RESET, () => {
      snapshots = new Map(); snapshotSecs = []; currentSec = 0;
      slider.disabled = true; slider.value = 0;
      if(cvLive) ctxLive.clearRect(0,0,cvLive.width, cvLive.height);
      if(timeLabel) timeLabel.textContent = '尚未推演';
      const panel = document.getElementById('clearPanel');
      if(panel) panel.innerHTML = '<div class="text-dim">尚未推演</div>';
    });
  }
  function activate(){ if(!containerEl) return; computeLayout(); resizeCanvases(); renderStatic(); renderLive(currentSec); renderClearPanel(currentSec); }
  function formatAbsTime(sec){ return minutesToHHMM((state.simBaseMin || 0) + Math.floor(sec/60)); }
  function getSchedule(maxSec){ const set = new Set(); for(let s=0;s<=maxSec;s+=VIZ_SNAPSHOT_INTERVAL) set.add(s); set.add(maxSec); return [...set]; }
  function ingestSnapshot(sec, snap){ snapshots.set(sec, snap); if(!snapshotSecs.includes(sec)){ snapshotSecs.push(sec); snapshotSecs.sort((a,b) => a-b); } }
  function finalize(){ emit(EVT.VIZ_SNAPSHOTS, {snapshots, secs:snapshotSecs}); }
  function reset(){ emit(EVT.VIZ_RESET); snapshots = new Map(); snapshotSecs = []; currentSec = 0; }
  function getAllSnapshots(){ return { snapEntries:[...snapshots.entries()], secs:snapshotSecs, baseMin: state.simBaseMin }; }

  function computeLayout(){
    layout.nodes.clear(); layout.zones = [];
    const zonesById = new Map(state.zones.map(z => [z.id, z]));
    const groups = new Map();
    for(const c of state.cities){
      const key = c.zoneId || '__unassigned__';
      if(!groups.has(key)) groups.set(key, []);
      groups.get(key).push(c);
    }
    const groupArr = [...groups.entries()];
    const cols = Math.max(1, Math.ceil(Math.sqrt(groupArr.length)));
    const cellW = 340, cellH = 340;
    groupArr.forEach(([zoneId, cities], gi) => {
      const col = gi % cols, row = Math.floor(gi / cols);
      const cx = col * cellW + cellW/2, cy = row * cellH + cellH/2;
      layout.zones.push({ zoneId, name: zonesById.get(zoneId)?.name || '未分配', cx, cy });
      const n = cities.length;
      const R = n === 1 ? 0 : Math.min(cellW, cellH) * 0.32;
      cities.forEach((c, i) => {
        const ang = (i/n) * Math.PI * 2 - Math.PI/2;
        layout.nodes.set(c.id, { x: cx + Math.cos(ang)*R, y: cy + Math.sin(ang)*R, zoneId, name:c.name, side:c.side, isCapital:!!c.isCapital });
      });
    });
    layout.bounds.w = cols * cellW;
    layout.bounds.h = Math.ceil(groupArr.length / cols) * cellH;
  }
  function resizeCanvases(){
    if(!containerEl) return;
    const w = containerEl.clientWidth;
    if(!w || w <= 0){ [cvStatic, cvLive].forEach(cv => { cv.width = 320; cv.height = 240; }); return; }
    const scale = Math.min(1, w / Math.max(layout.bounds.w, 320));
    const wS = Math.max(320, layout.bounds.w * scale), hS = Math.max(240, layout.bounds.h * scale);
    [cvStatic, cvLive].forEach(cv => { cv.width = wS; cv.height = hS; cv.style.width = wS + 'px'; cv.style.height = hS + 'px'; });
    ctxStatic.setTransform(scale, 0, 0, scale, 0, 0);
    ctxLive.setTransform(scale, 0, 0, scale, 0, 0);
  }
  function renderStatic(){
    if(!ctxStatic) return;
    ctxStatic.clearRect(0, 0, cvStatic.width, cvStatic.height);
    for(const z of layout.zones){
      const r = 160;
      ctxStatic.beginPath(); ctxStatic.arc(z.cx, z.cy, r, 0, Math.PI*2);
      ctxStatic.strokeStyle = 'rgba(59,130,246,0.2)'; ctxStatic.lineWidth = 1;
      ctxStatic.setLineDash([4,6]); ctxStatic.stroke(); ctxStatic.setLineDash([]);
      ctxStatic.font = '11px sans-serif'; ctxStatic.fillStyle = 'rgba(148,163,184,0.7)';
      ctxStatic.textAlign = 'center'; ctxStatic.fillText(z.name, z.cx, z.cy - r - 6);
    }
    for(const c of state.cities){
      const from = layout.nodes.get(c.id);
      if(!from) continue;
      for(const t of (c.attackTargets || [])){ if((t.preWarPercent||0)<=0) continue; const to = layout.nodes.get(t.cityId); if(!to) continue; drawArrow(ctxStatic, from, to, 'rgba(255,68,102,0.35)', t.preWarPercent); }
      for(const t of (c.defendTargets || [])){ if((t.preWarPercent||0)<=0) continue; const to = layout.nodes.get(t.cityId); if(!to) continue; drawArrow(ctxStatic, from, to, 'rgba(34,255,136,0.28)', t.preWarPercent); }
    }
    for(const c of state.cities){ const p = layout.nodes.get(c.id); if(!p) continue; drawNode(ctxStatic, p, c.side, false); }
  }
  function drawNode(ctx, p, side, fallen){
    const color = side==='self' ? '#3b82f6' : side==='ally' ? '#10b981' : side==='enemy' ? '#ef4444' : side==='common_enemy' ? '#f59e0b' : side==='npc' ? '#a855f7' : '#64748b';
    ctx.beginPath(); ctx.arc(p.x, p.y, NODE_RADIUS, 0, Math.PI*2);
    ctx.fillStyle = fallen ? '#1a1a1a' : color; ctx.fill();
    ctx.strokeStyle = fallen ? '#7f1d1d' : 'rgba(255,255,255,0.25)'; ctx.lineWidth = 2; ctx.stroke();
    if(p.isCapital){ ctx.font = 'bold 12px sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillStyle = '#ffcc00'; ctx.fillText('👑', p.x, p.y - NODE_RADIUS - 10); }
    ctx.font = 'bold 10px sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillStyle = '#fff';
    const label = p.name.length > 6 ? p.name.slice(0,6)+'…' : p.name;
    ctx.fillText(label, p.x, p.y + NODE_RADIUS + 12);
  }
  function drawArrow(ctx, from, to, color, pct){
    const dx = to.x - from.x, dy = to.y - from.y;
    const dist = Math.hypot(dx, dy);
    if(dist < 1) return;
    const ux = dx/dist, uy = dy/dist;
    const sx = from.x + ux*NODE_RADIUS, sy = from.y + uy*NODE_RADIUS;
    const ex = to.x - ux*NODE_RADIUS, ey = to.y - uy*NODE_RADIUS;
    const mx = (sx+ex)/2, my = (sy+ey)/2;
    const co = dist * 0.12;
    const cx = mx - uy*co, cy = my + ux*co;
    ctx.beginPath(); ctx.moveTo(sx, sy); ctx.quadraticCurveTo(cx, cy, ex, ey);
    ctx.strokeStyle = color; ctx.lineWidth = Math.max(1, Math.min(4, pct/25)); ctx.stroke();
    const ang = Math.atan2(ey-cy, ex-cx);
    ctx.beginPath(); ctx.moveTo(ex, ey);
    ctx.lineTo(ex - Math.cos(ang-0.4)*8, ey - Math.sin(ang-0.4)*8);
    ctx.lineTo(ex - Math.cos(ang+0.4)*8, ey - Math.sin(ang+0.4)*8);
    ctx.closePath(); ctx.fillStyle = color; ctx.fill();
  }
  function renderLive(sec){
    if(!ctxLive) return;
    ctxLive.clearRect(0, 0, cvLive.width, cvLive.height);
    const snap = lookupSnapshot(sec);
    if(!snap) return;
    const snapById = new Map(snap.map(s => [s.id, s]));
    for(const c of state.cities){
      const p = layout.nodes.get(c.id);
      if(!p) continue;
      const s = snapById.get(c.id);
      if(!s) continue;
      if(!s.f && s.si > 0){
        ctxLive.beginPath(); ctxLive.arc(p.x, p.y, NODE_RADIUS + 7, 0, Math.PI*2);
        ctxLive.strokeStyle = 'rgba(255,68,102,0.7)'; ctxLive.lineWidth = 2; ctxLive.setLineDash([3,3]); ctxLive.stroke(); ctxLive.setLineDash([]);
      }
      let ringColor = null, ringW = 2;
      if(s.f){ ringColor = '#ef4444'; ringW = 3; }
      else if(s.w < (c.wallMin*60)*0.3){ ringColor = '#f59e0b'; ringW = 2.5; }
      else if(s.r > 0){ ringColor = '#22ff88'; ringW = 1.5; }
      if(ringColor){ ctxLive.beginPath(); ctxLive.arc(p.x, p.y, NODE_RADIUS+4, 0, Math.PI*2); ctxLive.strokeStyle = ringColor; ctxLive.lineWidth = ringW; ctxLive.stroke(); }
      if(!s.f){
        ctxLive.font = 'bold 9px sans-serif'; ctxLive.textAlign = 'center'; ctxLive.textBaseline = 'middle'; ctxLive.fillStyle = '#e2e8f0';
        ctxLive.fillText(`${Math.round(s.r)}/${Math.round(s.r + s.o + s.c)}`, p.x, p.y - NODE_RADIUS - 8);
        if(s.si > 0){ ctxLive.font = 'bold 9px sans-serif'; ctxLive.fillStyle = '#ff4466'; ctxLive.fillText(`⚡${Math.round(s.si)}`, p.x, p.y + NODE_RADIUS + 24); }
      } else {
        ctxLive.font = 'bold 10px sans-serif'; ctxLive.textAlign = 'center'; ctxLive.textBaseline = 'middle'; ctxLive.fillStyle = '#ef4444'; ctxLive.fillText('✕', p.x, p.y);
      }
    }
  }
  function lookupSnapshot(sec){
    if(snapshotSecs.length === 0) return null;
    if(snapshots.has(sec)) return snapshots.get(sec);
    let lo = 0, hi = snapshotSecs.length-1, best = 0;
    while(lo <= hi){ const mid = (lo+hi) >> 1; if(snapshotSecs[mid] <= sec){ best = snapshotSecs[mid]; lo = mid+1; } else hi = mid-1; }
    return snapshots.get(best);
  }
  function renderClearPanel(sec){
    const panel = document.getElementById('clearPanel');
    if(!panel) return;
    const snap = lookupSnapshot(sec);
    if(!snap){ panel.innerHTML = '<div class="text-dim">尚未推演</div>'; return; }
    const absTime = formatAbsTime(sec);
    const snapById = new Map(snap.map(s => [s.id, s]));
    let html = `<div class="clear-panel-title"><span>📊 瞬間清算</span><span class="time">${esc(absTime)}</span></div>`;
    for(const c of state.cities){
      const s = snapById.get(c.id);
      if(!s) continue;
      const fallenCls = s.f ? 'fallen' : '';
      const a = state.alliances.find(al => al.id === c.allianceId);
      const icon = (a && a.icon) ? a.icon + ' ' : '';
      html += `<div class="clear-city ${fallenCls}">
        <div class="name"><span>${c.isCapital ? '👑 ' : ''}${esc(c.name)} <span class="chip ${sideClass(c.side)}" style="font-size:9px;">${esc(icon)}${sideLabel(c.side)}</span></span>${s.f ? '<span style="color:var(--neon-red);font-size:10px;">✕ 已淪陷</span>' : ''}</div>
        <div class="stat-grid">
          <div class="stat-item"><span class="lbl">🛡️ 剩餘可戰</span><span class="val" style="color:#22ff88;">${Math.round(s.r)}</span></div>
          <div class="stat-item"><span class="lbl">⚔️ 外出</span><span class="val" style="color:#44aaff;">${Math.round(s.o)}</span></div>
          <div class="stat-item"><span class="lbl">💤 冷卻</span><span class="val" style="color:#94a3b8;">${Math.round(s.c)}</span></div>
          <div class="stat-item"><span class="lbl">🏰 城牆</span><span class="val" style="color:#ffcc00;">${(s.w/60).toFixed(1)} 分</span></div>
        </div>
      </div>`;
    }
    panel.innerHTML = html;
  }
  return { init, activate, getSchedule, ingestSnapshot, finalize, reset, getAllSnapshots, renderLive, renderClearPanel };
})();

/* ============ R (Render) ============ */
const R = (() => {
  function renderHealth(){
    const dot = document.getElementById('healthDot'), text = document.getElementById('healthText');
    let cls, label;
    if(state.connected){ cls = 'green'; label = '連線成功'; }
    else if(state.connecting){ cls = 'yellow'; label = '連線中...'; }
    else { cls = 'red'; label = '未連線'; }
    dot.className = 'health-dot ' + cls; text.textContent = label;
  }
  function renderHost(){
    const el = document.getElementById('hostDisplay');
    if(el) el.textContent = state.hostName ? `房主：${state.hostName}${state.isHost ? '（你）' : ''}` : '';
  }
  function renderPing(){ const el = document.getElementById('pingDisplay'); if(el) el.textContent = `延遲：${state.pingMs ?? '--'}ms`; }
  function renderDebug({msg, err} = {}){
    const el = document.getElementById('debugLog');
    if(!el || !msg) return;
    const line = document.createElement('div');
    line.className = err ? 'err' : (msg.includes('🟢') ? 'ok' : '');
    line.textContent = `[${nowTime()}] ${msg}`;
    el.appendChild(line);
    while(el.children.length > 6) el.removeChild(el.firstChild);
    el.scrollTop = el.scrollHeight;
  }
  function renderMembers(){
    const el = document.getElementById('onlineMembers');
    if(!el) return;
    const list = Object.values(state.members);
    if(list.length === 0){ el.innerHTML = '<span class="text-dim">尚未連線</span>'; return; }
    el.innerHTML = list.map(m => `<span class="chip ${m.isHost ? 'host' : ''}">${m.isHost ? '👑 ' : ''}${esc(m.name)}</span>`).join('');
  }
  function renderAlliances(){
    const tbody = document.getElementById('allianceTableBody');
    if(!tbody) return;
    if(state.alliances.length === 0){ tbody.innerHTML = '<tr><td colspan="6" class="ally-table-empty">尚無同盟資料</td></tr>'; renderMatrix(); return; }
    tbody.innerHTML = state.alliances.map(a => {
      const cap = state.cities.find(c => c.allianceId === a.id && c.isCapital);
      const tagCls = a.side === 'self' ? 'tag-self' : (a.side === 'ally' ? 'tag-ally' : 'tag-enemy');
      const chipCls = a.side === 'self' ? 'self' : (a.side === 'ally' ? 'ally' : 'enemy');
      const avg = getAllianceAvgPower(a);
      const isEditing = state.editingAllianceId === a.id;
      const icon = a.icon || '';
      return `<tr${isEditing ? ' style="background:rgba(255,204,0,.08);"' : ''}>
        <td class="col-name"><span class="alliance-tag ${tagCls}"></span>${icon ? `<span class="alliance-icon">${icon}</span>` : ''}${esc(a.name)}${isEditing ? '<span class="editing-badge">編輯中</span>' : ''}${cap ? ` <span style="color:var(--neon-yellow);font-size:10px;">👑 ${esc(cap.name)}</span>` : ''}</td>
        <td><span class="chip ${chipCls}">${allianceSideLabel(a.side)}</span></td>
        <td class="col-num">${(a.memberCount||0).toLocaleString()}</td>
        <td class="col-num">${(a.totalPower||0).toLocaleString()}</td>
        <td class="col-num" style="color:var(--neon-green);font-weight:700;">${avg.toLocaleString(undefined,{maximumFractionDigits:2})}</td>
        <td class="col-actions">
          <button class="btn btn-primary btn-sm" data-action="edit-alliance" data-id="${a.id}">✏️ 編輯</button>
          <button class="btn btn-danger btn-sm" data-action="del-alliance" data-id="${a.id}">🗑️ 刪除</button>
        </td>
      </tr>`;
    }).join('');
    renderMatrix();
  }
  function renderMatrix(){
    const wrap = document.getElementById('matrixWrap');
    if(!wrap) return;
    if(state.alliances.length < 2){ wrap.innerHTML = '<div class="text-dim">至少需要 2 個同盟才能生成矩陣</div>'; return; }
    const consume = (state.settings.consumeMinPerMin + state.settings.consumeMaxPerMin) / 2;
    let html = '<table class="matrix-table"><thead><tr><th>發起方 ↓ / 對手 →</th>';
    state.alliances.forEach(a => { const avg = getAllianceAvgPower(a); const icon = a.icon ? a.icon + ' ' : ''; html += `<th>${icon}${esc(a.name)}<br><span style="font-size:9px;color:var(--text-dim);">均戰 ${avg.toLocaleString(undefined,{maximumFractionDigits:2})}</span></th>`; });
    html += '</tr></thead><tbody>';
    state.alliances.forEach(y => {
      const yAvg = getAllianceAvgPower(y);
      const yIcon = y.icon ? y.icon + ' ' : '';
      html += `<tr><td class="row-label">${yIcon}${esc(y.name)}</td>`;
      state.alliances.forEach(x => {
        if(y.id === x.id) html += '<td style="color:#334155;">—</td>';
        else { const xAvg = getAllianceAvgPower(x); const total = yAvg + xAvg; const val = total > 0 ? (xAvg / total) * consume : 0; html += `<td>${val.toFixed(2)}</td>`; }
      });
      html += '</tr>';
    });
    html += '</tbody></table>';
    wrap.innerHTML = html;
  }
  function renderZones(){
    const el = document.getElementById('zoneList');
    if(!el) return;
    el.innerHTML = state.zones.map(z => `<span class="chip">${esc(z.name)} <button class="btn btn-danger btn-sm" style="padding:0 4px;margin-left:4px;" data-action="del-zone" data-id="${z.id}">✕</button></span>`).join('') || '<span class="text-dim">尚無戰區</span>';
    const sim = document.getElementById('simZoneSelect');
    if(sim){ const cur = sim.value; sim.innerHTML = '<option value="all">🌐 全戰區同時推演</option>' + state.zones.map(z => `<option value="${z.id}">${esc(z.name)}</option>`).join(''); sim.value = cur || 'all'; }
  }
  function renderCities(){
    const el = document.getElementById('cityList');
    if(!el) return;
    if(state.cities.length === 0){ el.innerHTML = '<div class="card"><div class="text-dim">尚無城池資料。</div></div>'; return; }
    const grouped = {};
    for(const c of state.cities){ const z = state.zones.find(z => z.id === c.zoneId); const key = z ? z.name : '未分配戰區'; (grouped[key] ||= []).push(c); }
    let html = '';
    for(const zoneName in grouped){
      html += `<div class="card"><div class="card-title">🗺️ ${esc(zoneName)}</div>`;
      for(const c of grouped[zoneName]){
        const lock = state.editLocks[c.id];
        const locked = !!lock && lock.clientId !== state.myClientId;
        const alliance = state.alliances.find(a => a.id === c.allianceId);
        const alloc = computeAllocation(c);
        const overCls = alloc.over ? 'overdraft' : '';
        const capCls = c.isCapital ? 'capital' : '';
        const defStart = c.defStartTime || '19:00';
        const defEnd = minutesToHHMM(hhmmToMinutes(defStart) + state.settings.timeLimitMin);
        const allianceIcon = (alliance && alliance.icon) ? alliance.icon : '';
        html += `<div class="city-card ${locked ? 'locked' : ''} ${overCls} ${capCls}">`;
        html += `<div class="flex-row" style="justify-content:space-between;margin-bottom:6px;"><strong style="font-size:13px;">${c.isCapital ? '👑 ' : ''}${esc(c.name)}</strong><span class="chip ${sideClass(c.side)}">${allianceIcon ? `<span class="alliance-icon">${allianceIcon}</span>` : ''}${sideLabel(c.side)}</span></div>`;
        if(alliance) html += `<div class="text-dim" style="margin-bottom:4px;">同盟：${allianceIcon ? `<span class="alliance-icon">${allianceIcon}</span>` : ''}${esc(alliance.name)}</div>`;
        html += `<div class="flex-row" style="margin-bottom:4px;"><span class="chip time">🕐 ${esc(defStart)} – ${esc(defEnd)}</span></div>`;
        html += `<div class="flex-row" style="font-size:11px;color:var(--text-secondary);gap:12px;"><span>總戰力 ${(c.totalPower||0).toLocaleString()}</span><span>總隊數 ${c.totalTeams}</span><span>均戰 ${c.avgPower}</span></div>`;
        if(alloc.over){ html += `<div class="flex-row" style="font-size:11px;margin-top:4px;"><span class="text-warn">⚠️ 戰前派兵合計 ${alloc.allocated} 隊 ＞ 總隊數 ${alloc.totalTeams} 隊（推演時將按比例縮減）</span></div>`; }
        else { html += `<div class="flex-row" style="font-size:11px;gap:12px;margin-top:4px;"><span style="color:#ff8fa3;">⚔️ 戰前 ${alloc.atkSum} 隊</span><span style="color:#8fffb0;">🛡️ 協防 ${alloc.defSum} 隊</span><span style="color:#8ecbff;">🏰 留守 ${alloc.reserve} 隊</span></div>`; }
        html += `<div class="flex-row" style="font-size:11px;color:var(--text-dim);gap:12px;margin-top:4px;"><span>冷卻 ${c.cooldownMin}分</span><span>城牆 ${c.wallMin}分</span></div>`;
        if(c.attackTargets?.length){
          const list = c.attackTargets.filter(t => (t.preWarPercent||0)>0).map(t => { const tgt = state.cities.find(cc => cc.id === t.cityId); return tgt ? `<span class="chip enemy">${esc(tgt.name)} 戰${t.preWarPercent}% 復${t.postRevivePercent}% #${t.priority}</span>` : null; }).filter(Boolean);
          if(list.length) html += `<div style="margin-top:4px;">⚔️ ${list.join(' ')}</div>`;
        }
        if(c.defendTargets?.length){
          const list = c.defendTargets.filter(t => (t.preWarPercent||0)>0).map(t => { const tgt = state.cities.find(cc => cc.id === t.cityId); return tgt ? `<span class="chip ally">${esc(tgt.name)} 戰${t.preWarPercent}% 復${t.postRevivePercent}% #${t.priority}</span>` : null; }).filter(Boolean);
          if(list.length) html += `<div style="margin-top:4px;">🛡️ ${list.join(' ')}</div>`;
        }
        html += `<div class="flex-row mt-8"><button class="btn btn-primary btn-sm" data-action="edit-city" data-id="${c.id}">✏️ 編輯</button><button class="btn btn-danger btn-sm" data-action="del-city" data-id="${c.id}">🗑️ 刪除</button></div></div>`;
      }
      html += `</div>`;
    }
    el.innerHTML = html;
  }
  function renderNarrative(lines){
    const el = document.getElementById('narrativeOutput');
    if(!el) return;
    if(!lines || lines.length === 0){ el.innerHTML = '<span class="text-dim">尚未推演，或無關鍵事件。</span>'; return; }
    el.innerHTML = lines.map(l => {
      const cls = l.type === 'warn' ? 'event-warn' : l.type === 'capture' ? 'event-capture' : l.type === 'revive' ? 'event-revive' : 'event-info';
      return `<div class="narrative-line ${cls}">${esc(l.text)}</div>`;
    }).join('');
    el.scrollTop = el.scrollHeight;
  }
  function renderProgress(p){ const bar = document.getElementById('simProgress'); if(bar) bar.style.width = Math.round(p*100) + '%'; }
  function renderAll(){ renderHealth(); renderHost(); renderPing(); renderMembers(); renderAlliances(); renderZones(); renderCities(); }
  return { renderHealth, renderHost, renderPing, renderDebug, renderMembers, renderAlliances, renderMatrix, renderZones, renderCities, renderNarrative, renderProgress, renderAll };
})();

/* ============ DYN ============ */
const DYN = (() => {
  let allRows = [];
  function setRows(rows){ allRows = rows || []; renderSummary(); renderTable(); }
  function renderSummary(){
    const el = document.getElementById('dynSummary');
    if(!el) return;
    if(allRows.length === 0){ el.textContent = '尚未推演'; return; }
    const routes = new Set(); allRows.forEach(r => routes.add(`${r.srcId}→${r.tgtId}`));
    el.innerHTML = `共 <b>${allRows.length}</b> 筆 · <b>${routes.size}</b> 條路線`;
  }
  function getFilters(){
    return {
      granularity: parseFloat(document.getElementById('dynGranularity').value) || 5,
      action: document.getElementById('dynAction').value || 'all',
      srcCity: document.getElementById('dynSrcCity').value || 'all',
      tgtCity: document.getElementById('dynTgtCity').value || 'all',
    };
  }
  function formatFullTime(sec) {
    const totalSec = ((state.simBaseMin || 0) * 60) + sec;
    const h = Math.floor(totalSec / 3600) % 24;
    const m = Math.floor((totalSec % 3600) / 60);
    const s = totalSec % 60;
    return `${String(h).padStart(2,'0')}:${String(m).padStart(2,'0')}:${String(s).padStart(2,'0')}`;
  }
  function renderTable(){
    const tbody = document.getElementById('dynTableBody');
    if(!tbody) return;
    if(allRows.length === 0){ tbody.innerHTML = '<tr><td colspan="10" style="text-align:center;color:var(--text-dim);padding:20px;">尚未推演</td></tr>'; return; }
    const f = getFilters();
    const granSec = Math.round(f.granularity * 60);
    const thConsume = document.querySelector('#dynTable thead tr th:nth-child(5)');
    if (thConsume) thConsume.textContent = (granSec === 30) ? '本30秒消耗' : '本分鐘消耗(速率)';
    const filtered = allRows.filter(r => {
      if(f.action === 'attack' && !r.isAttack) return false;
      if(f.action === 'defend' && r.isAttack) return false;
      if(f.srcCity !== 'all' && r.srcId !== f.srcCity) return false;
      if(f.tgtCity !== 'all' && r.tgtId !== f.tgtCity) return false;
      return true;
    });
    const grouped = new Map();
    for(const r of filtered){
      const roundedSec = Math.round(r.sec / granSec) * granSec;
      const key = `${roundedSec}|${r.srcId}|${r.tgtId}|${r.isAttack?1:0}`;
      if(!grouped.has(key)) grouped.set(key, r);
    }
    const rows = [...grouped.values()].sort((a,b) => a.sec - b.sec || a.srcCity.localeCompare(b.srcCity));
    if(rows.length === 0){ tbody.innerHTML = '<tr><td colspan="10" style="text-align:center;color:var(--text-dim);padding:20px;">無資料</td></tr>'; return; }
    tbody.innerHTML = rows.map(r => {
      const timeStr = (granSec === 30) ? formatFullTime(r.sec) : minutesToHHMM((state.simBaseMin || 0) + Math.floor(r.sec / 60));
      const actTxt = r.isAttack ? '⚔️ 進攻' : '🛡️ 協防';
      const wallDisplay = r.tgtFallen ? '🏳️ 城已破' : (r.wallSec / 60).toFixed(1) + ' 分';
      const consumeDisplay = ((r.consumeThisMin||0) * (granSec === 30 ? 0.5 : 1)).toFixed(1);
      return `<tr>
        <td class="time-cell">${esc(timeStr)}</td>
        <td class="atk-cell">${esc(r.srcCity)}城(${sideLabel(r.srcSide)})</td>
        <td class="${r.isAttack ? 'atk' : 'def'}">${actTxt}</td>
        <td class="def-cell">${esc(r.tgtCity)}城(${sideLabel(r.tgtSide)})</td>
        <td class="consumed">${consumeDisplay}</td>
        <td class="num-stay">${r.ownRemain}</td>
        <td class="num-cd">${r.ownCd} + ${r.ownMarch}</td>
        <td class="num-stay">${r.tgtRemain}</td>
        <td class="num-cd">${r.tgtCd} + ${r.tgtMarch}</td>
        <td>${wallDisplay}</td>
      </tr>`;
    }).join('');
  }
  function populateCityFilters(){
    const cities = state.cities;
    const srcSel = document.getElementById('dynSrcCity');
    const tgtSel = document.getElementById('dynTgtCity');
    if(srcSel){ const cur = srcSel.value; srcSel.innerHTML = '<option value="all">全部</option>' + cities.map(c => `<option value="${c.id}">${esc(c.name)}</option>`).join(''); srcSel.value = cur && cities.find(c => c.id === cur) ? cur : 'all'; }
    if(tgtSel){ const cur = tgtSel.value; tgtSel.innerHTML = '<option value="all">全部</option>' + cities.map(c => `<option value="${c.id}">${esc(c.name)}</option>`).join(''); tgtSel.value = cur && cities.find(c => c.id === cur) ? cur : 'all'; }
  }
  function copyAsTSV(){
    const tbody = document.getElementById('dynTableBody');
    if(!tbody) return;
    const headers = ['時間點','進攻方','行動','防守方','本時段消耗','進攻方剩餘','進攻方待復活','防守方剩餘','防守方待復活','城牆剩餘'];
    const lines = [headers.join('\t')];
    tbody.querySelectorAll('tr').forEach(tr => { const cells = [...tr.querySelectorAll('td')].map(td => td.textContent.trim()); if(cells.length === 10) lines.push(cells.join('\t')); });
    navigator.clipboard.writeText(lines.join('\n')).then(() => alert('已複製')).catch(() => {
      const ta = document.createElement('textarea'); ta.value = lines.join('\n'); document.body.appendChild(ta); ta.select(); document.execCommand('copy'); document.body.removeChild(ta); alert('已複製');
    });
  }
  function init(){
    ['dynGranularity','dynAction','dynSrcCity','dynTgtCity'].forEach(id => { const el = document.getElementById(id); if(el) el.addEventListener('change', renderTable); });
    const btn = document.getElementById('btnDynCopy');
    if(btn) btn.addEventListener('click', copyAsTSV);
    on(EVT.DYN_RESULT, () => { setRows(state.dynRows); populateCityFilters(); });
  }
  return { init, setRows, renderTable, populateCityFilters };
})();

/* ============ 同盟表單 ============ */
function updateAllianceAvgPowerPreview(){
  const mc = parseFloat(document.getElementById('allyMemberCount').value) || 0;
  const tp = parseFloat(document.getElementById('allyTotalPower').value) || 0;
  document.getElementById('allyAvgPower').value = mc > 0 ? (tp / mc).toLocaleString(undefined,{maximumFractionDigits:2}) : '0';
}
function resetAllianceForm(){
  state.editingAllianceId = null;
  document.getElementById('allyFormTitle').textContent = '➕ 新增同盟';
  document.getElementById('allyName').value = '';
  document.getElementById('allyIcon').value = '';
  document.getElementById('allySide').value = 'ally';
  document.getElementById('allyMemberCount').value = 100;
  document.getElementById('allyTotalPower').value = 20000;
  document.getElementById('btnCancelAllianceEdit').style.display = 'none';
  document.getElementById('btnSaveAlliance').textContent = '💾 儲存';
  updateAllianceAvgPowerPreview();
  R.renderAlliances();
}
function startEditAlliance(id){
  const a = state.alliances.find(x => x.id === id);
  if(!a) return;
  state.editingAllianceId = id;
  document.getElementById('allyFormTitle').textContent = `✏️ 編輯同盟：${esc(a.name)}`;
  document.getElementById('allyName').value = a.name || '';
  document.getElementById('allyIcon').value = a.icon || '';
  document.getElementById('allySide').value = a.side || 'ally';
  document.getElementById('allyMemberCount').value = a.memberCount || 100;
  document.getElementById('allyTotalPower').value = a.totalPower || 20000;
  document.getElementById('btnCancelAllianceEdit').style.display = 'inline-flex';
  document.getElementById('btnSaveAlliance').textContent = '💾 更新';
  updateAllianceAvgPowerPreview();
  R.renderAlliances();
}

/* ============ AI 參數 UI 同步 ============ */
function syncAIParamsToUI(){
  const p = AI.getParams();
  document.getElementById('aiR25').value = p.r25;
  document.getElementById('aiR20').value = p.r20;
  document.getElementById('aiR15').value = p.r15;
  document.getElementById('aiR12').value = p.r12;
  document.getElementById('aiR10').value = p.r10;
  document.getElementById('aiR08').value = p.r08;
  document.getElementById('aiR06').value = p.r06;
  document.getElementById('aiR00').value = p.r00;
  document.getElementById('aiTeamFactor').value = p.teamFactor;
  document.getElementById('aiWallFactor1').value = p.wallFactor1;
  document.getElementById('aiWallFactor2').value = p.wallFactor2;
  document.getElementById('aiDefendFactor').value = p.defendFactor;
  document.getElementById('aiMinPct').value = p.minPct;
}
function readAIParamsFromUI(){
  return {
    r25: parseFloat(document.getElementById('aiR25').value) || 25,
    r20: parseFloat(document.getElementById('aiR20').value) || 33,
    r15: parseFloat(document.getElementById('aiR15').value) || 50,
    r12: parseFloat(document.getElementById('aiR12').value) || 60,
    r10: parseFloat(document.getElementById('aiR10').value) || 70,
    r08: parseFloat(document.getElementById('aiR08').value) || 84,
    r06: parseFloat(document.getElementById('aiR06').value) || 95,
    r00: parseFloat(document.getElementById('aiR00').value) || 100,
    teamFactor: parseFloat(document.getElementById('aiTeamFactor').value) || 0.4,
    wallFactor1: parseFloat(document.getElementById('aiWallFactor1').value) || 1.10,
    wallFactor2: parseFloat(document.getElementById('aiWallFactor2').value) || 1.15,
    defendFactor: parseFloat(document.getElementById('aiDefendFactor').value) || 0.70,
    minPct: parseFloat(document.getElementById('aiMinPct').value) || 17,
  };
}

/* ============ UI ============ */
let editingCityId = null;
let confirmCb = null;
function showConfirm(title, msg, cb){ document.getElementById('modalTitle').textContent = '⚠️ ' + title; document.getElementById('modalMessage').textContent = msg; document.getElementById('confirmModal').classList.add('show'); confirmCb = cb; }

function validateCrossDay(cities, timeLimitMin){
  if(cities.length === 0) return {ok:true};
  const mins = cities.map(c => hhmmToMinutes(c.defStartTime || '19:00'));
  if((Math.max(...mins) - Math.min(...mins)) + timeLimitMin > 1440) return { ok: false, msg: `時間跨度 + 時長超過 24 小時。` };
  return {ok:true};
}
function updateSectionLabels(){
  const mySide = document.getElementById('cm_side').value;
  const atkSides = (ATTACK_RULES[mySide] || []).map(sideLabel).join(' / ');
  const defSides = (DEFEND_RULES[mySide] || []).map(sideLabel).join(' / ');
  document.getElementById('attackSectionLabel').textContent = `⚔️ 選擇進攻的城池（限 ${atkSides || '無'}）`;
  document.getElementById('defendSectionLabel').textContent = `🛡️ 選擇協防的城池${defSides ? `（限 ${defSides}）` : '（不可協防）'}`;
}
function updateAutoCalcFields(){
  const t = parseFloat(document.getElementById('cm_totalTeams').value)||0;
  const p = parseFloat(document.getElementById('cm_totalPower').value)||0;
  document.getElementById('cm_avgPower').value = t > 0 ? Math.floor(p/t) : 0;
}
function updateAllocPanel(){
  const total = parseFloat(document.getElementById('cm_totalTeams').value) || 0;
  let atkSum = 0, defSum = 0;
  document.querySelectorAll('.atk-cb:checked').forEach(cb => { const sel = document.querySelector(`.atk-pre[data-city="${cb.dataset.city}"]`); atkSum += Math.floor(total * (parseFloat(sel.value)||0) / 100); });
  document.querySelectorAll('.def-cb:checked').forEach(cb => { const sel = document.querySelector(`.def-pre[data-city="${cb.dataset.city}"]`); defSum += Math.floor(total * (parseFloat(sel.value)||0) / 100); });
  const allocated = atkSum + defSum, reserve = total - allocated;
  document.getElementById('cm_allocTotal').textContent = total;
  document.getElementById('cm_allocAtk').textContent = atkSum;
  document.getElementById('cm_allocDef').textContent = defSum;
  const reserveEl = document.getElementById('cm_allocReserve');
  reserveEl.textContent = reserve;
  reserveEl.style.color = reserve < 0 ? 'var(--neon-red)' : 'var(--neon-green)';
  document.getElementById('cm_allocWarning').style.display = reserve < 0 ? 'block' : 'none';
}
function renderTargetSelectors(attackTargets, defendTargets){
  const zoneId = document.getElementById('cm_zone').value, mySide = document.getElementById('cm_side').value;
  const attackEl = document.getElementById('cm_attackList'), defendEl = document.getElementById('cm_defendList');
  const pool = state.cities.filter(c => c.id !== editingCityId);
  const sameZone = zoneId ? pool.filter(c => c.zoneId === zoneId) : pool;
  const attackableSides = ATTACK_RULES[mySide] || [];
  const attackable = sameZone.filter(c => attackableSides.includes(c.side));
  const defendableSides = DEFEND_RULES[mySide] || [];
  const defendable = sameZone.filter(c => defendableSides.includes(c.side));
  const aMap = {}; (attackTargets || []).forEach(t => aMap[t.cityId] = t);
  const dMap = {}; (defendTargets || []).forEach(t => dMap[t.cityId] = t);

  const buildOptions = (selected) => PERCENT_OPTIONS.map(p => `<option value="${p}" ${p===selected?'selected':''}>${p}%</option>`).join('');
  const myCityForAI = {
    avgPower: parseFloat(document.getElementById('cm_avgPower').value) || 1,
    totalTeams: parseFloat(document.getElementById('cm_totalTeams').value) || 0
  };

  if(attackable.length === 0){ attackEl.innerHTML = `<div class="empty-hint">無可進攻目標</div>`; }
  else {
    attackEl.innerHTML = attackable.map(c => {
      const cfg = aMap[c.id] || {};
      const checked = cfg.cityId !== undefined;
      const pre = cfg.preWarPercent !== undefined ? cfg.preWarPercent : 50;
      const post = cfg.postRevivePercent !== undefined ? cfg.postRevivePercent : 50;
      const pr = cfg.priority !== undefined ? cfg.priority : 1;
      const defStart = c.defStartTime || '19:00';
      const aiSuggest = AI.suggestForTarget(myCityForAI, c, true);
      const aiCls = (aiSuggest === 100 && myCityForAI.avgPower < c.avgPower) ? 'ai-hint warn' : 'ai-hint';
      const a = state.alliances.find(al => al.id === c.allianceId);
      const icon = (a && a.icon) ? a.icon + ' ' : '';
      return `<div class="target-item ${checked ? 'checked' : ''}" data-city="${c.id}">
        <input type="checkbox" class="atk-cb" data-city="${c.id}" ${checked ? 'checked' : ''}>
        <span class="tname">${icon}${c.isCapital ? '👑 ' : ''}${esc(c.name)}</span>
        <span class="tside ${sideClass(c.side)}">${sideLabel(c.side)}</span>
        <span class="tside time">${esc(defStart)}</span>
        <span class="${aiCls}">🤖 ${aiSuggest}%</span>
        <div class="target-config-row">
          <span class="cfg-label">戰前</span>
          <select class="atk-pre" data-city="${c.id}" ${checked ? '' : 'disabled'}>${buildOptions(pre)}</select>
          <span class="cfg-label">復活</span>
          <select class="atk-post" data-city="${c.id}" ${checked ? '' : 'disabled'}>${buildOptions(post)}</select>
          <span class="cfg-label">順序</span>
          <input type="number" class="atk-priority" data-city="${c.id}" value="${pr}" min="1" max="99" step="1" ${checked ? '' : 'disabled'}>
        </div>
      </div>`;
    }).join('');
  }
  if(defendable.length === 0){
    defendEl.innerHTML = defendableSides.length === 0 ? '<div class="empty-hint">此陣營不可協防任何城池</div>' : `<div class="empty-hint">無可協防目標</div>`;
  } else {
    defendEl.innerHTML = defendable.map(c => {
      const cfg = dMap[c.id] || {};
      const checked = cfg.cityId !== undefined;
      const pre = cfg.preWarPercent !== undefined ? cfg.preWarPercent : 50;
      const post = cfg.postRevivePercent !== undefined ? cfg.postRevivePercent : 50;
      const pr = cfg.priority !== undefined ? cfg.priority : 1;
      const defStart = c.defStartTime || '19:00';
      const aiSuggest = AI.suggestForTarget(myCityForAI, c, false);
      const a = state.alliances.find(al => al.id === c.allianceId);
      const icon = (a && a.icon) ? a.icon + ' ' : '';
      return `<div class="target-item ${checked ? 'checked' : ''}" data-city="${c.id}">
        <input type="checkbox" class="def-cb" data-city="${c.id}" ${checked ? 'checked' : ''}>
        <span class="tname">${icon}${c.isCapital ? '👑 ' : ''}${esc(c.name)}</span>
        <span class="tside ${sideClass(c.side)}">${sideLabel(c.side)}</span>
        <span class="tside time">${esc(defStart)}</span>
        <span class="ai-hint">🤖 ${aiSuggest}%</span>
        <div class="target-config-row">
          <span class="cfg-label">戰前</span>
          <select class="def-pre" data-city="${c.id}" ${checked ? '' : 'disabled'}>${buildOptions(pre)}</select>
          <span class="cfg-label">復活</span>
          <select class="def-post" data-city="${c.id}" ${checked ? '' : 'disabled'}>${buildOptions(post)}</select>
          <span class="cfg-label">順序</span>
          <input type="number" class="def-priority" data-city="${c.id}" value="${pr}" min="1" max="99" step="1" ${checked ? '' : 'disabled'}>
        </div>
      </div>`;
    }).join('');
  }

  const bindToggle = (cbSelector, itemSelector, selects, priorityEl) => {
    document.querySelectorAll(cbSelector).forEach(cb => cb.addEventListener('change', function(){
      const item = this.closest(itemSelector);
      item.classList.toggle('checked', this.checked);
      item.querySelectorAll(selects).forEach(s => s.disabled = !this.checked);
      item.querySelector(priorityEl).disabled = !this.checked;
      updateAllocPanel();
    }));
  };
  bindToggle('.atk-cb', '.target-item', '.atk-pre,.atk-post', '.atk-priority');
  bindToggle('.def-cb', '.target-item', '.def-pre,.def-post', '.def-priority');
  document.querySelectorAll('.atk-pre,.def-pre').forEach(el => el.addEventListener('change', updateAllocPanel));
  updateAllocPanel();
}
function collectCurrentTargets(){
  const atk = [], def = [];
  document.querySelectorAll('.atk-cb:checked').forEach(cb => {
    const cityId = cb.dataset.city;
    const pre = parseFloat(document.querySelector(`.atk-pre[data-city="${cityId}"]`).value) || 0;
    const post = parseFloat(document.querySelector(`.atk-post[data-city="${cityId}"]`).value) || 0;
    const pr = parseInt(document.querySelector(`.atk-priority[data-city="${cityId}"]`).value) || 1;
    if(pre > 0) atk.push({ cityId, preWarPercent: pre, postRevivePercent: post, priority: pr });
  });
  document.querySelectorAll('.def-cb:checked').forEach(cb => {
    const cityId = cb.dataset.city;
    const pre = parseFloat(document.querySelector(`.def-pre[data-city="${cityId}"]`).value) || 0;
    const post = parseFloat(document.querySelector(`.def-post[data-city="${cityId}"]`).value) || 0;
    const pr = parseInt(document.querySelector(`.def-priority[data-city="${cityId}"]`).value) || 1;
    if(pre > 0) def.push({ cityId, preWarPercent: pre, postRevivePercent: post, priority: pr });
  });
  return {attackTargets:atk, defendTargets:def};
}
function applyAISuggestion(){
  const currentCity = {
    avgPower: parseFloat(document.getElementById('cm_avgPower').value) || 1,
    totalTeams: parseFloat(document.getElementById('cm_totalTeams').value) || 0,
    attackTargets: [],
    defendTargets: [],
  };
  if (!currentCity.totalTeams){ alert('請先輸入總隊數'); return; }
  const currentAtk = [], currentDef = [];
  document.querySelectorAll('.atk-cb:checked').forEach(cb => {
    const cityId = cb.dataset.city;
    const pre = parseFloat(document.querySelector(`.atk-pre[data-city="${cityId}"]`).value) || 0;
    const pr = parseInt(document.querySelector(`.atk-priority[data-city="${cityId}"]`).value) || 1;
    if (pre > 0) currentAtk.push({ cityId, priority: pr });
  });
  document.querySelectorAll('.def-cb:checked').forEach(cb => {
    const cityId = cb.dataset.city;
    const pre = parseFloat(document.querySelector(`.def-pre[data-city="${cityId}"]`).value) || 0;
    const pr = parseInt(document.querySelector(`.def-priority[data-city="${cityId}"]`).value) || 1;
    if (pre > 0) currentDef.push({ cityId, priority: pr });
  });
  if (currentAtk.length === 0 && currentDef.length === 0){
    alert('請先勾選至少一個進攻或協防目標'); return;
  }
  currentCity.attackTargets = currentAtk;
  currentCity.defendTargets = currentDef;
  const suggestion = AI.suggestForCity(currentCity, state.cities);
  for (const s of suggestion.atk){
    const preEl = document.querySelector(`.atk-pre[data-city="${s.cityId}"]`);
    const postEl = document.querySelector(`.atk-post[data-city="${s.cityId}"]`);
    if (preEl) preEl.value = s.preWarPercent;
    if (postEl) postEl.value = s.postRevivePercent;
  }
  for (const s of suggestion.def){
    const preEl = document.querySelector(`.def-pre[data-city="${s.cityId}"]`);
    const postEl = document.querySelector(`.def-post[data-city="${s.cityId}"]`);
    if (preEl) preEl.value = s.preWarPercent;
    if (postEl) postEl.value = s.postRevivePercent;
  }
  updateAllocPanel();
  logSystem('🤖 AI 佈兵建議已套用');
}
function openCityModal(cityId){
  editingCityId = cityId || null;
  const isNew = !editingCityId;
  const city = isNew ? null : state.cities.find(c => c.id === editingCityId);
  if(!isNew && isConnected()) publish({ type:'edit_lock', cityId:editingCityId, name:state.commanderName, clientId:state.myClientId });
  document.getElementById('cityModalTitle').textContent = isNew ? '🏰 新增城池' : `✏️ 編輯城池：${city ? city.name : ''}`;
  const zoneSel = document.getElementById('cm_zone');
  zoneSel.innerHTML = state.zones.map(z => `<option value="${z.id}">${esc(z.name)}</option>`).join('') || '<option value="">（尚未建立戰區）</option>';
  const allianceSel = document.getElementById('cm_alliance');
  allianceSel.innerHTML = '<option value="">（不指定）</option>' + state.alliances.map(a => `<option value="${a.id}">${a.icon ? a.icon + ' ' : ''}${esc(a.name)}（${allianceSideLabel(a.side)}）</option>`).join('');
  if(isNew){
    document.getElementById('cm_name').value = '';
    document.getElementById('cm_side').value = 'self';
    document.getElementById('cm_totalPower').value = 100000;
    document.getElementById('cm_totalTeams').value = 100;
    document.getElementById('cm_cooldownMin').value = 5;
    document.getElementById('cm_wallMin').value = 30;
    document.getElementById('cm_defStartTime').value = '19:00';
    document.getElementById('cm_isCapital').checked = false;
    if(state.zones.length > 0) zoneSel.value = state.zones[0].id;
  } else {
    document.getElementById('cm_name').value = city.name;
    document.getElementById('cm_zone').value = city.zoneId || '';
    document.getElementById('cm_alliance').value = city.allianceId || '';
    document.getElementById('cm_side').value = city.side;
    document.getElementById('cm_totalPower').value = city.totalPower;
    document.getElementById('cm_totalTeams').value = city.totalTeams;
    document.getElementById('cm_cooldownMin').value = city.cooldownMin;
    document.getElementById('cm_wallMin').value = city.wallMin;
    document.getElementById('cm_defStartTime').value = city.defStartTime || '19:00';
    document.getElementById('cm_isCapital').checked = !!city.isCapital;
  }
  updateAutoCalcFields(); updateSectionLabels();
  renderTargetSelectors(city ? (city.attackTargets || []) : [], city ? (city.defendTargets || []) : []);
  document.getElementById('cityModal').classList.add('show');
}
function closeCityModal(){
  if(editingCityId && isConnected()) publish({ type:'edit_unlock', cityId:editingCityId, clientId:state.myClientId });
  delete state.editLocks[editingCityId];
  document.getElementById('cityModal').classList.remove('show');
  editingCityId = null;
  R.renderCities();
  if (document.getElementById('tab-deploy').classList.contains('active')) DEPLOY.render();
}
function saveCityFromModal(){
  const name = document.getElementById('cm_name').value.trim();
  if(!name){ alert('請輸入城池名稱'); return; }
  const zoneId = document.getElementById('cm_zone').value;
  if(!zoneId){ alert('請先建立並選擇戰區'); return; }
  const allianceId = document.getElementById('cm_alliance').value;
  const side = document.getElementById('cm_side').value;
  const totalPower = parseFloat(document.getElementById('cm_totalPower').value) || 0;
  const totalTeams = parseFloat(document.getElementById('cm_totalTeams').value) || 0;
  const cooldownMin = parseFloat(document.getElementById('cm_cooldownMin').value) || 0;
  const wallMin = parseFloat(document.getElementById('cm_wallMin').value) || 0;
  const defStartTime = document.getElementById('cm_defStartTime').value || '19:00';
  const isCapital = document.getElementById('cm_isCapital').checked;
  const {attackTargets, defendTargets} = collectCurrentTargets();
  const avgPower = totalTeams > 0 ? Math.floor(totalPower / totalTeams) : 0;
  const id = editingCityId || uid();
  if(isCapital && allianceId){
    state.cities.forEach(c => { if(c.allianceId === allianceId && c.isCapital && c.id !== id){ c.isCapital = false; state.entityRev.city[c.id] = (state.entityRev.city[c.id] || 0) + 1; markDirty('city', c.id); } });
  }
  const entity = { id, name, zoneId, allianceId, side, totalPower, totalTeams, avgPower, cooldownMin, wallMin, defStartTime, isCapital, attackTargets, defendTargets };
  upsertEntity('city', entity);
  closeCityModal();
  R.renderCities();
  saveState();
}

/* ============ 模擬調度 ============ */
function collectCitiesForSim(zoneId){ return zoneId === 'all' ? state.cities : state.cities.filter(c => c.zoneId === zoneId); }
function executeSimulation(zoneId){
  if(state.isSimulating) return;
  const timeLimitMin = parseInt(document.getElementById('globalTimeLimit').value) || 120;
  const consumeMinPerMin = parseFloat(document.getElementById('globalConsumeMinPerMin').value) || 10;
  const consumeMaxPerMin = parseFloat(document.getElementById('globalConsumeMaxPerMin').value) || 30;
  const siegeEfficiency = parseFloat(document.getElementById('globalSiegeEfficiency').value) || 1;
  const marchTimeSec = parseInt(document.getElementById('globalMarchTimeSec').value) || 0;
  const maxLossRatio = (parseFloat(document.getElementById('globalMaxLossRatio').value) || 90) / 100;
  const minLossRatio = (parseFloat(document.getElementById('globalMinLossRatio').value) || 10) / 100;
  Object.assign(state.settings, { timeLimitMin, consumeMinPerMin, consumeMaxPerMin, siegeEfficiency, marchTimeSec, maxLossRatio, minLossRatio });
  state.settingsRev++;
  saveState();

  const cities = collectCitiesForSim(zoneId);
  if(cities.length === 0){ logSystem('❌ 無城池資料'); return; }
  const v = validateCrossDay(cities, timeLimitMin);
  if(!v.ok){ logSystem('❌ ' + v.msg); return; }
  const defStartMins = cities.map(c => hhmmToMinutes(c.defStartTime || '19:00'));
  state.simBaseMin = Math.min(...defStartMins);
  state.isSimulating = true;
  state.dynRows = []; state.narrativeLines = [];
  document.getElementById('narrativeOutput').innerHTML = '推演中...';
  DYN.setRows([]); viz.reset(); R.renderProgress(0);
  const runId = ++simRunId;
  const maxDefStartRel = Math.max(...defStartMins) - state.simBaseMin;
  const maxSec = maxDefStartRel * 60 + timeLimitMin * 60;
  const snapshotSet = viz.getSchedule(maxSec);
  const dynSet = new Set();
  for(let s=0;s<=maxSec;s+=DYN_ROUTE_SAMPLE_SEC) dynSet.add(s);
  dynSet.add(maxSec);
  const dynRowsBuffer = [];
  const worker = getWorker();
  if(worker){
    const onMessage = (e) => {
      const msg = e.data || {};
      if(msg.runId !== runId) return;
      switch(msg.type){
        case 'progress': R.renderDebug({msg:`⏳ ${Math.round(msg.progress*100)}%`}); R.renderProgress(msg.progress); break;
        case 'snapshot': viz.ingestSnapshot(msg.sec, msg.snap); break;
        case 'dyn_sample': if(msg.rows) for(const r of msg.rows) dynRowsBuffer.push(r); break;
        case 'done': worker.removeEventListener('message', onMessage); state.dynRows = dynRowsBuffer; handleSimulationDone(msg.result); break;
        case 'error': worker.removeEventListener('message', onMessage); logSystem('❌ 推演失敗：' + msg.error); state.isSimulating = false; break;
      }
    };
    worker.addEventListener('message', onMessage);
    worker.postMessage({ type:'run', payload:{ cities: JSON.parse(JSON.stringify(cities)), settings: {...state.settings}, snapshotsAt: snapshotSet, dynSampleAt: [...dynSet], runId } });
    return;
  }
  setTimeout(async () => {
    try{
      const result = await runSimulation(JSON.parse(JSON.stringify(cities)), {...state.settings}, {
        onProgress: ({progress}) => { R.renderProgress(progress); R.renderDebug({msg:`⏳ ${Math.round(progress*100)}%`}); },
        onSnapshot: (sec, snap) => viz.ingestSnapshot(sec, snap),
        snapshotAt: new Set(snapshotSet),
        dynSampleAt: new Set(dynSet),
        onDynSample: (sec, rows) => { for(const r of rows) dynRowsBuffer.push(r); },
      });
      state.dynRows = dynRowsBuffer;
      handleSimulationDone(result);
    }catch(err){ console.error(err); state.isSimulating = false; }
  }, 30);
}
function handleSimulationDone(result){
  R.renderProgress(1);
  setTimeout(() => R.renderProgress(0), 1000);
  if(result.aborted){ logSystem('⛔ 推演已中止'); state.isSimulating = false; return; }
  if(result.minDefStartMin !== undefined) state.simBaseMin = result.minDefStartMin;
  state.narrativeLines = result.narrativeLines || [];
  R.renderNarrative(state.narrativeLines);
  DYN.setRows(state.dynRows);
  DYN.populateCityFilters();
  saveState();
  if(state.isHost && isConnected()){
    const vizPayload = JSON.stringify(viz.getAllSnapshots());
    const totalV = Math.ceil(vizPayload.length / VIZ_CHUNK_SIZE) || 1;
    for(let i=0;i<totalV;i++) publish({ type:'viz_chunk', part:i, total:totalV, data: vizPayload.slice(i*VIZ_CHUNK_SIZE, (i+1)*VIZ_CHUNK_SIZE) });
    const dynPayload = JSON.stringify(state.dynRows);
    const totalD = Math.ceil(dynPayload.length / 6000) || 1;
    for(let i=0;i<totalD;i++) publish({ type:'dyn_chunk', part:i, total:totalD, data: dynPayload.slice(i*6000, (i+1)*6000) });
  }
  viz.finalize();
  state.isSimulating = false;
  logSystem('✅ 推演完成');
}
/* ============ 佈兵總覽 ============ */
const DEPLOY = (() => {
  let currentView = 'attack';

  function init(){
    document.querySelectorAll('.deploy-tab').forEach(tab => {
      tab.addEventListener('click', function(){
        document.querySelectorAll('.deploy-tab').forEach(t => t.classList.remove('active'));
        this.classList.add('active');
        currentView = this.dataset.view;
        const ctrl = document.getElementById('deployLayoutCtrl');
        if (ctrl) ctrl.style.display = (currentView === 'graph') ? '' : 'none';
        render();
      });
    });
    ['deployZone','deploySide','deployFilter','deploySort','deployLayout'].forEach(id => {
      const el = document.getElementById(id);
      if (el) el.addEventListener('change', render);
    });
    const exportBtn = document.getElementById('btnDeployExport');
    if (exportBtn) exportBtn.addEventListener('click', exportCSV);
  }

  function populateZoneFilter(){
    const sel = document.getElementById('deployZone');
    if (!sel) return;
    const cur = sel.value;
    sel.innerHTML = '<option value="all">全部</option>' + state.zones.map(z => `<option value="${z.id}">${esc(z.name)}</option>`).join('');
    if (cur && state.zones.find(z => z.id === cur)) sel.value = cur;
  }

  function getConflictInfo(){
    const map = new Map();
    for(const c of state.cities){
      let incoming = 0;
      for(const o of state.cities){
        (o.attackTargets||[]).forEach(t => {
          if (t.cityId === c.id && (t.preWarPercent||0) > 0) incoming += Math.floor((o.totalTeams||0) * t.preWarPercent / 100);
        });
        (o.defendTargets||[]).forEach(t => {
          if (t.cityId === c.id && (t.preWarPercent||0) > 0) incoming += Math.floor((o.totalTeams||0) * t.preWarPercent / 100);
        });
      }
      const own = c.totalTeams || 0;
      const conflict = own > 0 && incoming > own * 1.2;
      map.set(c.id, { incoming, own, conflict });
    }
    return map;
  }

  function getFilteredCities(){
    const zoneId = document.getElementById('deployZone').value;
    const side = document.getElementById('deploySide').value;
    const filter = document.getElementById('deployFilter').value;
    const conflictMap = getConflictInfo();
    let cities = state.cities.filter(c => {
      if (zoneId !== 'all' && c.zoneId !== zoneId) return false;
      if (side !== 'all' && c.side !== side) return false;
      if (filter === 'hasAction'){
        const hasAtk = (c.attackTargets || []).some(t => (t.preWarPercent||0) > 0);
        const hasDef = (c.defendTargets || []).some(t => (t.preWarPercent||0) > 0);
        const isAttacked = state.cities.some(o => (o.attackTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0) > 0));
        const isDefended = state.cities.some(o => (o.defendTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0) > 0));
        if (!hasAtk && !hasDef && !isAttacked && !isDefended) return false;
      }
      if (filter === 'overdraft'){
        const alloc = computeAllocation(c);
        if (!alloc.over) return false;
      }
      if (filter === 'conflict'){
        const info = conflictMap.get(c.id);
        if (!info || !info.conflict) return false;
      }
      return true;
    });
    const sortBy = document.getElementById('deploySort').value;
    if (sortBy === 'totalTeams') cities.sort((a, b) => (b.totalTeams||0) - (a.totalTeams||0));
    else if (sortBy === 'deployed') cities.sort((a, b) => computeAllocation(b).allocated - computeAllocation(a).allocated);
    else if (sortBy === 'reserve') cities.sort((a, b) => computeAllocation(a).reserve - computeAllocation(b).reserve);
    else if (sortBy === 'incoming') cities.sort((a, b) => (conflictMap.get(b.id)?.incoming||0) - (conflictMap.get(a.id)?.incoming||0));
    return cities;
  }

  function allianceIconOf(city){
    const a = state.alliances.find(al => al.id === city.allianceId);
    return (a && a.icon) ? a.icon : '';
  }

  function renderAttackView(cities, conflictMap){
    let html = `<div class="deploy-table-wrap"><table class="deploy-table">
      <thead><tr>
        <th>出兵城</th><th>陣營</th><th>總隊數</th>
        <th>⚔️ 進攻指示</th><th>🛡️ 協防指示</th>
        <th>留守</th><th>受兵量</th><th>操作</th>
      </tr></thead><tbody>`;
    for(const c of cities){
      const alloc = computeAllocation(c);
      const sideCls = sideClass(c.side);
      const info = conflictMap.get(c.id) || { incoming: 0, conflict: false };
      const icon = allianceIconOf(c);
      const atkChips = (c.attackTargets || []).filter(t => (t.preWarPercent||0) > 0).map(t => {
        const tgt = state.cities.find(cc => cc.id === t.cityId);
        if (!tgt) return '';
        return `<span class="deploy-chip atk">→ ${esc(tgt.name)} <span class="pct">${t.preWarPercent}%</span><span class="pr">#${t.priority}</span></span>`;
      }).join('');
      const defChips = (c.defendTargets || []).filter(t => (t.preWarPercent||0) > 0).map(t => {
        const tgt = state.cities.find(cc => cc.id === t.cityId);
        if (!tgt) return '';
        return `<span class="deploy-chip def">→ ${esc(tgt.name)} <span class="pct">${t.preWarPercent}%</span><span class="pr">#${t.priority}</span></span>`;
      }).join('');
      const reserve = alloc.reserve;
      const reserveCls = alloc.over ? 'warn' : 'ok';
      const reservePct = c.totalTeams > 0 ? Math.round(reserve / c.totalTeams * 100) : 0;
      const conflictIcon = info.conflict ? '<span class="conflict-icon" title="受兵量超過自身兵力">⚠️</span>' : '';
      html += `<tr class="${info.conflict ? 'conflict-row' : ''}">
        <td class="city-name ${c.side==='enemy'?'city-fallen':''}">${icon ? `<span class="alliance-icon">${icon}</span>` : ''}${c.isCapital ? '👑 ' : ''}${esc(c.name)}${conflictIcon}</td>
        <td><span class="chip ${sideCls}">${sideLabel(c.side)}</span></td>
        <td>${c.totalTeams}</td>
        <td>${atkChips || '<span class="deploy-chip none">無</span>'}</td>
        <td>${defChips || '<span class="deploy-chip none">無</span>'}</td>
        <td><span class="deploy-reserve ${reserveCls}">${reserve} 隊 (${reservePct}%)</span></td>
        <td><b style="color:${info.conflict ? 'var(--neon-red)' : (info.incoming > 0 ? 'var(--neon-yellow)' : 'var(--text-dim)')};">${info.incoming} 隊</b></td>
        <td><button class="btn btn-primary btn-sm" data-deploy-edit="${c.id}">✏️</button></td>
      </tr>`;
    }
    html += `</tbody></table></div>`;
    document.getElementById('deployTableWrap').innerHTML = html;
  }

  function renderDefendView(cities, conflictMap){
    let html = `<div class="deploy-table-wrap"><table class="deploy-table">
      <thead><tr>
        <th>目標城</th><th>陣營</th><th>總隊數</th>
        <th>⚔️ 被誰進攻</th><th>🛡️ 被誰協防</th>
        <th>總受兵</th><th>操作</th>
      </tr></thead><tbody>`;
    for(const c of cities){
      const attackerChips = state.cities.filter(o => (o.attackTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0) > 0))
        .map(o => {
          const t = o.attackTargets.find(t => t.cityId === c.id);
          return `<span class="deploy-chip atk">← ${esc(o.name)} <span class="pct">${t.preWarPercent}%</span><span class="pr">#${t.priority}</span></span>`;
        }).join('');
      const defenderChips = state.cities.filter(o => (o.defendTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0) > 0))
        .map(o => {
          const t = o.defendTargets.find(t => t.cityId === c.id);
          return `<span class="deploy-chip def">← ${esc(o.name)} <span class="pct">${t.preWarPercent}%</span><span class="pr">#${t.priority}</span></span>`;
        }).join('');
      const info = conflictMap.get(c.id) || { incoming: 0, conflict: false };
      const sideCls = sideClass(c.side);
      const icon = allianceIconOf(c);
      const conflictIcon = info.conflict ? '<span class="conflict-icon" title="受兵量超過自身兵力">⚠️</span>' : '';
      html += `<tr class="${info.conflict ? 'conflict-row' : ''}">
        <td class="city-name ${c.side==='enemy'?'city-fallen':''}">${icon ? `<span class="alliance-icon">${icon}</span>` : ''}${c.isCapital ? '👑 ' : ''}${esc(c.name)}${conflictIcon}</td>
        <td><span class="chip ${sideCls}">${sideLabel(c.side)}</span></td>
        <td>${c.totalTeams}</td>
        <td>${attackerChips || '<span class="deploy-chip none">無</span>'}</td>
        <td>${defenderChips || '<span class="deploy-chip none">無</span>'}</td>
        <td><b style="color:${info.conflict ? 'var(--neon-red)' : (info.incoming > 0 ? 'var(--neon-yellow)' : 'var(--text-dim)')};">${info.incoming} 隊</b></td>
        <td><button class="btn btn-primary btn-sm" data-deploy-edit="${c.id}">✏️</button></td>
      </tr>`;
    }
    html += `</tbody></table></div>`;
    document.getElementById('deployTableWrap').innerHTML = html;
  }

  function renderMatrixView(cities, conflictMap){
    const activeCities = cities.filter(c => {
      const hasOut = (c.attackTargets||[]).some(t => (t.preWarPercent||0)>0) || (c.defendTargets||[]).some(t => (t.preWarPercent||0)>0);
      const hasIn = state.cities.some(o => 
        (o.attackTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0)>0) || 
        (o.defendTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0)>0)
      );
      return hasOut || hasIn;
    });
    if (activeCities.length === 0){
      document.getElementById('deployTableWrap').innerHTML = '<div class="empty-hint">無任何派兵或受擊關係。</div>';
      return;
    }
    let html = '<div class="deploy-table-wrap"><table class="deploy-matrix"><thead><tr>';
    html += '<th class="row-header">出兵城 \\ 目標城</th>';
    for(const c of activeCities){
      const info = conflictMap.get(c.id) || { conflict: false };
      const conflictIcon = info.conflict ? '<span class="conflict-icon">⚠️</span>' : '';
      const icon = allianceIconOf(c);
      html += `<th>${icon ? `<span class="alliance-icon">${icon}</span>` : ''}${esc(c.name)}${conflictIcon}</th>`;
    }
    html += '</tr></thead><tbody>';
    for(const src of activeCities){
      const srcIcon = allianceIconOf(src);
      html += `<tr><td class="row-header">${srcIcon ? `<span class="alliance-icon">${srcIcon}</span>` : ''}${src.isCapital ? '👑 ' : ''}${esc(src.name)}</td>`;
      for(const tgt of activeCities){
        if (src.id === tgt.id){ html += '<td class="cell-self">—</td>'; continue; }
        const atk = (src.attackTargets||[]).find(t => t.cityId === tgt.id);
        const def = (src.defendTargets||[]).find(t => t.cityId === tgt.id);
        if (atk && (atk.preWarPercent||0) > 0){
          html += `<td class="cell-atk">⚔️ ${atk.preWarPercent}%<br><span style="font-size:9px;color:var(--text-dim);">#${atk.priority}</span></td>`;
        } else if (def && (def.preWarPercent||0) > 0){
          html += `<td class="cell-def">🛡️ ${def.preWarPercent}%<br><span style="font-size:9px;color:var(--text-dim);">#${def.priority}</span></td>`;
        } else {
          html += '<td class="cell-empty">·</td>';
        }
      }
      html += '</tr>';
    }
    html += '</tbody></table></div>';
    document.getElementById('deployTableWrap').innerHTML = html;
  }

  function computeCircleLayout(activeCities){
    const W = 1000, H = 1000, CX = 500, CY = 500;
    const R = Math.min(W, H) * 0.36;
    const N = activeCities.length;
    const pos = new Map();
    activeCities.forEach((c, i) => {
      const ang = (i / N) * Math.PI * 2 - Math.PI / 2;
      pos.set(c.id, { x: CX + Math.cos(ang) * R, y: CY + Math.sin(ang) * R });
    });
    return { pos, zones: [] };
  }

  function fitToCanvas(pos, W, H, padding){
    if (pos.size === 0) return;
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const p of pos.values()){
      minX = Math.min(minX, p.x); maxX = Math.max(maxX, p.x);
      minY = Math.min(minY, p.y); maxY = Math.max(maxY, p.y);
    }
    const contentW = Math.max(maxX - minX, 1);
    const contentH = Math.max(maxY - minY, 1);
    const availW = W - padding * 2;
    const availH = H - padding * 2;
    const scale = Math.min(availW / contentW, availH / contentH, 1.6);
    const offsetX = (W - contentW * scale) / 2 - minX * scale;
    const offsetY = (H - contentH * scale) / 2 - minY * scale;
    for (const [id, p] of pos){
      pos.set(id, { x: p.x * scale + offsetX, y: p.y * scale + offsetY });
    }
  }

  function computeForceLayout(activeCities, allCities){
    const W = 1000, H = 1000, PAD = 120;
    const N = activeCities.length;
    if (N === 0) return { pos: new Map(), zones: [] };
    const area = (W - PAD * 2) * (H - PAD * 2);
    const k = Math.sqrt(area / N) * 0.55;

    const pos = new Map();
    activeCities.forEach((c, i) => {
      const ang = (i / N) * Math.PI * 2 - Math.PI / 2;
      const r = 150 + (i % 3) * 50;
      pos.set(c.id, { x: W/2 + Math.cos(ang) * r, y: H/2 + Math.sin(ang) * r });
    });

    const edges = [];
    for (const src of activeCities){
      for (const t of (src.attackTargets || [])){
        if ((t.preWarPercent||0) <= 0) continue;
        if (!pos.has(t.cityId)) continue;
        edges.push([src.id, t.cityId]);
      }
      for (const t of (src.defendTargets || [])){
        if ((t.preWarPercent||0) <= 0) continue;
        if (!pos.has(t.cityId)) continue;
        edges.push([src.id, t.cityId]);
      }
    }

    const iterations = 300;
    let temp = W / 8;
    const cool = temp / (iterations + 1);

    for (let iter = 0; iter < iterations; iter++){
      const disp = new Map();
      activeCities.forEach(c => disp.set(c.id, { x: 0, y: 0 }));

      for (let i = 0; i < activeCities.length; i++){
        for (let j = i + 1; j < activeCities.length; j++){
          const a = pos.get(activeCities[i].id);
          const b = pos.get(activeCities[j].id);
          let dx = a.x - b.x, dy = a.y - b.y;
          let d = Math.hypot(dx, dy);
          if (d < 0.01){ dx = (Math.random()-0.5)*10; dy = (Math.random()-0.5)*10; d = Math.hypot(dx, dy) || 0.01; }
          const force = (k * k) / d;
          const fx = (dx / d) * force;
          const fy = (dy / d) * force;
          const da = disp.get(activeCities[i].id), db = disp.get(activeCities[j].id);
          da.x += fx; da.y += fy;
          db.x -= fx; db.y -= fy;
        }
      }

      for (const [aId, bId] of edges){
        const pa = pos.get(aId), pb = pos.get(bId);
        let dx = pa.x - pb.x, dy = pa.y - pb.y;
        let d = Math.hypot(dx, dy);
        if (d < 0.01) d = 0.01;
        const force = (d * d) / k * 1.4;
        const fx = (dx / d) * force;
        const fy = (dy / d) * force;
        const da = disp.get(aId), db = disp.get(bId);
        da.x -= fx; da.y -= fy;
        db.x += fx; db.y += fy;
      }

      activeCities.forEach(c => {
        const d = disp.get(c.id);
        const p = pos.get(c.id);
        const len = Math.hypot(d.x, d.y);
        if (len > 0){
          const limit = Math.min(len, temp);
          p.x += (d.x / len) * limit;
          p.y += (d.y / len) * limit;
        }
        p.x = Math.max(PAD, Math.min(W - PAD, p.x));
        p.y = Math.max(PAD, Math.min(H - PAD, p.y));
      });

      temp = Math.max(temp - cool, 0.5);
    }

    fitToCanvas(pos, W, H, 150);
    return { pos, zones: [] };
  }

  function computeZoneLayout(activeCities, allCities){
    const W = 1000, H = 1000, PAD = 40;
    const pos = new Map();
    const zones = [];

    const groups = new Map();
    for (const c of activeCities){
      const key = c.zoneId || '__none__';
      if (!groups.has(key)) groups.set(key, []);
      groups.get(key).push(c);
    }

    const groupArr = [...groups.entries()];
    const numGroups = groupArr.length;
    const cols = numGroups <= 1 ? 1 : numGroups <= 4 ? 2 : numGroups <= 9 ? 3 : 4;
    const rows = Math.ceil(numGroups / cols);
    const gap = 22;
    const cellW = (W - PAD * 2 - gap * (cols - 1)) / cols;
    const cellH = (H - PAD * 2 - gap * (rows - 1)) / rows;

    groupArr.forEach(([zoneId, groupCities], gi) => {
      const col = gi % cols;
      const row = Math.floor(gi / cols);
      const cellX = PAD + col * (cellW + gap);
      const cellY = PAD + row * (cellH + gap);
      const cx = cellX + cellW / 2;
      const cy = cellY + cellH / 2;
      const n = groupCities.length;
      const R = n === 1 ? 0 : Math.min(cellW, cellH) * 0.32;

      const zoneName = zoneId === '__none__' ? '未分配' : (state.zones.find(z => z.id === zoneId)?.name || '未分配');

      zones.push({ zoneId, name: zoneName, x: cellX, y: cellY, w: cellW, h: cellH, cx, cy, count: n });

      groupCities.forEach((c, i) => {
        const ang = (i / n) * Math.PI * 2 - Math.PI / 2;
        pos.set(c.id, { x: cx + Math.cos(ang) * R, y: cy + Math.sin(ang) * R });
      });
    });

    return { pos, zones };
  }

  function makeNodeShape(ns, side, x, y, r){
    const cls = 'graph-node ' + sideClass(side);
    let el;
    if (side === 'ally'){
      el = document.createElementNS(ns, 'rect');
      el.setAttribute('x', x - r);
      el.setAttribute('y', y - r);
      el.setAttribute('width', r * 2);
      el.setAttribute('height', r * 2);
      el.setAttribute('rx', r * 0.35);
      el.setAttribute('ry', r * 0.35);
    } else if (side === 'enemy'){
      const h = r * 1.15;
      el = document.createElementNS(ns, 'polygon');
      el.setAttribute('points', `${x},${y - h} ${x + r * 0.95},${y + h * 0.65} ${x - r * 0.95},${y + h * 0.65}`);
    } else if (side === 'common_enemy'){
      el = document.createElementNS(ns, 'polygon');
      el.setAttribute('points', `${x},${y - r * 1.15} ${x + r * 1.15},${y} ${x},${y + r * 1.15} ${x - r * 1.15},${y}`);
    } else if (side === 'npc'){
      const pts = [];
      for (let i = 0; i < 6; i++){
        const ang = (i / 6) * Math.PI * 2 - Math.PI / 2;
        pts.push(`${x + Math.cos(ang) * r},${y + Math.sin(ang) * r}`);
      }
      el = document.createElementNS(ns, 'polygon');
      el.setAttribute('points', pts.join(' '));
    } else {
      el = document.createElementNS(ns, 'circle');
      el.setAttribute('cx', x);
      el.setAttribute('cy', y);
      el.setAttribute('r', r);
    }
    el.setAttribute('class', cls);
    return el;
  }

  function renderGraphView(cities, conflictMap){
    const wrap = document.getElementById('deployTableWrap');
    const activeCities = cities.filter(c => {
      const hasOut = (c.attackTargets||[]).some(t => (t.preWarPercent||0)>0) || (c.defendTargets||[]).some(t => (t.preWarPercent||0)>0);
      const hasIn = state.cities.some(o => 
        (o.attackTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0)>0) || 
        (o.defendTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0)>0)
      );
      return hasOut || hasIn;
    });

    if (activeCities.length === 0){
      wrap.innerHTML = '<div class="empty-hint">無任何派兵或受擊關係。</div>';
      return;
    }

    const layoutSel = document.getElementById('deployLayout');
    const layoutMode = layoutSel ? layoutSel.value : 'circle';

    let layoutResult;
    if (layoutMode === 'force') layoutResult = computeForceLayout(activeCities, state.cities);
    else if (layoutMode === 'zone') layoutResult = computeZoneLayout(activeCities, state.cities);
    else layoutResult = computeCircleLayout(activeCities);
    const positions = layoutResult.pos;
    const zones = layoutResult.zones || [];

    const W = 1000, H = 1000;

    const maxTeams = Math.max(...activeCities.map(c => c.totalTeams || 1), 1);
    const nodeRadius = (c) => {
      const t = c.totalTeams || 0;
      return 14 + Math.sqrt(t / maxTeams) * 16;
    };

    const ns = 'http://www.w3.org/2000/svg';
    const svg = document.createElementNS(ns, 'svg');
    svg.setAttribute('viewBox', `0 0 ${W} ${H}`);
    svg.setAttribute('preserveAspectRatio', 'xMidYMid meet');

    svg.appendChild(makeDefs(ns));

    if (layoutMode === 'zone' && zones.length > 0){
      const zoneG = document.createElementNS(ns, 'g');
      zoneG.setAttribute('class', 'graph-zones');
      zones.forEach(z => {
        const rect = document.createElementNS(ns, 'rect');
        rect.setAttribute('class', 'graph-zone-box');
        rect.setAttribute('x', z.x);
        rect.setAttribute('y', z.y);
        rect.setAttribute('width', z.w);
        rect.setAttribute('height', z.h);
        zoneG.appendChild(rect);

        const label = document.createElementNS(ns, 'text');
        label.setAttribute('class', 'graph-zone-label');
        label.setAttribute('x', z.cx);
        label.setAttribute('y', z.y + 20);
        label.textContent = z.name;
        zoneG.appendChild(label);

        const sub = document.createElementNS(ns, 'text');
        sub.setAttribute('class', 'graph-zone-sublabel');
        sub.setAttribute('x', z.cx);
        sub.setAttribute('y', z.y + 36);
        sub.textContent = `${z.count} 座城`;
        zoneG.appendChild(sub);
      });
      svg.appendChild(zoneG);
    }

    const edgesG = document.createElementNS(ns, 'g');
    edgesG.setAttribute('class', 'graph-edges');

    const radiusById = new Map();
    activeCities.forEach(c => radiusById.set(c.id, nodeRadius(c)));

    for (const src of activeCities){
      const fromPos = positions.get(src.id);
      if (!fromPos) continue;
      const fromR = radiusById.get(src.id) || 20;

      const addEdge = (targetId, pct, isAttack) => {
        if ((pct||0) <= 0) return;
        const toPos = positions.get(targetId);
        if (!toPos) return;
        const toR = radiusById.get(targetId) || 20;
        const path = document.createElementNS(ns, 'path');
        path.setAttribute('class', 'graph-edge ' + (isAttack ? 'atk' : 'def'));
        path.setAttribute('d', makeCurve(fromPos, toPos, fromR, toR));
        path.setAttribute('marker-end', isAttack ? 'url(#arrow-atk)' : 'url(#arrow-def)');
        path.dataset.src = src.id;
        path.dataset.tgt = targetId;
        edgesG.appendChild(path);
      };

      for (const t of (src.attackTargets || [])) addEdge(t.cityId, t.preWarPercent, true);
      for (const t of (src.defendTargets || [])) addEdge(t.cityId, t.preWarPercent, false);
    }
    svg.appendChild(edgesG);

    const nodesG = document.createElementNS(ns, 'g');
    nodesG.setAttribute('class', 'graph-nodes');

    for (const c of activeCities){
      const pos = positions.get(c.id);
      if (!pos) continue;
      const r = nodeRadius(c);
      const info = conflictMap.get(c.id) || { conflict: false, incoming: 0 };

      const g = document.createElementNS(ns, 'g');
      g.setAttribute('class', 'graph-node-group');
      g.dataset.cityId = c.id;

      if (info.conflict){
        const halo = document.createElementNS(ns, 'circle');
        halo.setAttribute('cx', pos.x);
        halo.setAttribute('cy', pos.y);
        halo.setAttribute('r', r + 6);
        halo.setAttribute('fill', 'none');
        halo.setAttribute('stroke', '#ff4466');
        halo.setAttribute('stroke-width', '2');
        halo.setAttribute('stroke-dasharray', '4 3');
        halo.setAttribute('opacity', '0.8');
        const animate = document.createElementNS(ns, 'animate');
        animate.setAttribute('attributeName', 'opacity');
        animate.setAttribute('values', '0.8;0.3;0.8');
        animate.setAttribute('dur', '1.5s');
        animate.setAttribute('repeatCount', 'indefinite');
        halo.appendChild(animate);
        g.appendChild(halo);
      }

      g.appendChild(makeNodeShape(ns, c.side, pos.x, pos.y, r));

      if (c.isCapital){
        const crown = document.createElementNS(ns, 'text');
        crown.setAttribute('x', pos.x);
        crown.setAttribute('y', pos.y - r - 8);
        crown.setAttribute('text-anchor', 'middle');
        crown.setAttribute('font-size', '14');
        crown.textContent = '👑';
        g.appendChild(crown);
      }

      const label = document.createElementNS(ns, 'text');
      label.setAttribute('class', 'graph-node-label' + (c.name.length > 4 ? ' small' : ''));
      label.setAttribute('x', pos.x);
      label.setAttribute('y', pos.y + r + 16);
      const cIcon = allianceIconOf(c);
      label.textContent = (cIcon ? cIcon + ' ' : '') + (c.name.length > 8 ? c.name.slice(0,8)+'…' : c.name);
      g.appendChild(label);

      const numLabel = document.createElementNS(ns, 'text');
      numLabel.setAttribute('x', pos.x);
      numLabel.setAttribute('y', pos.y + 4);
      numLabel.setAttribute('text-anchor', 'middle');
      numLabel.setAttribute('font-size', Math.min(11, r * 0.7));
      numLabel.setAttribute('font-weight', '700');
      numLabel.setAttribute('fill', '#fff');
      numLabel.setAttribute('pointer-events', 'none');
      numLabel.textContent = c.totalTeams;
      g.appendChild(numLabel);

      nodesG.appendChild(g);
    }
    svg.appendChild(nodesG);

    const infoPanel = document.createElement('div');
    infoPanel.className = 'graph-info-panel';
    infoPanel.style.display = 'none';
    infoPanel.innerHTML = '<div class="title"></div><div class="body"></div>';

    const legend = document.createElement('div');
    legend.className = 'graph-legend';
    legend.innerHTML = `
      <span><span class="dot" style="background:#3b82f6;border-radius:50%;"></span>本方</span>
      <span><span class="dot" style="background:#10b981;border-radius:3px;"></span>同盟</span>
      <span><span class="dot" style="background:#ef4444;clip-path:polygon(50% 0, 100% 100%, 0 100%);"></span>敵方</span>
      <span><span class="dot" style="background:#f59e0b;transform:rotate(45deg);"></span>共同敵</span>
      <span><span class="dot" style="background:#a855f7;clip-path:polygon(50% 0, 93% 25%, 93% 75%, 50% 100%, 7% 75%, 7% 25%);"></span>NPC</span>
      <span><span class="line atk"></span>進攻</span>
      <span><span class="line def"></span>協防</span>
    `;

    const zoomCtrl = document.createElement('div');
    zoomCtrl.className = 'graph-zoom';
    zoomCtrl.innerHTML = `
      <button data-zoom="in">＋</button>
      <button data-zoom="out">－</button>
      <button data-zoom="reset">⟲</button>
    `;

    wrap.innerHTML = '';
    const graphWrap = document.createElement('div');
    graphWrap.className = 'deploy-graph-wrap';
    graphWrap.appendChild(svg);
    graphWrap.appendChild(infoPanel);
    graphWrap.appendChild(legend);
    graphWrap.appendChild(zoomCtrl);
    wrap.appendChild(graphWrap);

    let vb = { x: 0, y: 0, w: W, h: H };
    function applyVB(){ svg.setAttribute('viewBox', `${vb.x} ${vb.y} ${vb.w} ${vb.h}`); }
    zoomCtrl.querySelector('[data-zoom="in"]').addEventListener('click', () => {
      const cx = vb.x + vb.w/2, cy = vb.y + vb.h/2;
      vb.w *= 0.75; vb.h *= 0.75;
      vb.x = cx - vb.w/2; vb.y = cy - vb.h/2; applyVB();
    });
    zoomCtrl.querySelector('[data-zoom="out"]').addEventListener('click', () => {
      const cx = vb.x + vb.w/2, cy = vb.y + vb.h/2;
      vb.w *= 1.33; vb.h *= 1.33;
      vb.x = cx - vb.w/2; vb.y = cy - vb.h/2; applyVB();
    });
    zoomCtrl.querySelector('[data-zoom="reset"]').addEventListener('click', () => {
      vb = { x: 0, y: 0, w: W, h: H }; applyVB();
    });

    let dragging = false, dragStart = null;
    svg.addEventListener('pointerdown', (e) => {
      if (e.target.closest('.graph-node-group')) return;
      dragging = true;
      dragStart = { x: e.clientX, y: e.clientY, vbX: vb.x, vbY: vb.y };
      svg.setPointerCapture(e.pointerId);
    });
    svg.addEventListener('pointermove', (e) => {
      if (!dragging) return;
      const rect = svg.getBoundingClientRect();
      const dx = (e.clientX - dragStart.x) * (vb.w / rect.width);
      const dy = (e.clientY - dragStart.y) * (vb.h / rect.height);
      vb.x = dragStart.vbX - dx;
      vb.y = dragStart.vbY - dy;
      applyVB();
    });
    svg.addEventListener('pointerup', (e) => {
      dragging = false;
      try { svg.releasePointerCapture(e.pointerId); } catch(err){}
    });
    svg.addEventListener('pointercancel', () => { dragging = false; });
    svg.addEventListener('wheel', (e) => {
      e.preventDefault();
      const rect = svg.getBoundingClientRect();
      const mx = (e.clientX - rect.left) / rect.width;
      const my = (e.clientY - rect.top) / rect.height;
      const px = vb.x + vb.w * mx;
      const py = vb.y + vb.h * my;
      const factor = e.deltaY < 0 ? 0.85 : 1.18;
      vb.w *= factor; vb.h *= factor;
      vb.x = px - vb.w * mx;
      vb.y = py - vb.h * my;
      applyVB();
    }, { passive: false });

    const allNodeGroups = nodesG.querySelectorAll('.graph-node-group');
    const allEdges = edgesG.querySelectorAll('.graph-edge');

    function highlightCity(cityId){
      allNodeGroups.forEach(g => {
        if (g.dataset.cityId === cityId){ g.classList.add('highlight'); g.classList.remove('dim'); }
        else g.classList.add('dim');
      });
      allEdges.forEach(edge => {
        if (edge.dataset.src === cityId || edge.dataset.tgt === cityId){
          edge.classList.add('highlight'); edge.classList.remove('dim');
        } else {
          edge.classList.add('dim'); edge.classList.remove('highlight');
        }
      });
    }
    function clearHighlight(){
      allNodeGroups.forEach(g => g.classList.remove('highlight', 'dim'));
      allEdges.forEach(e => e.classList.remove('highlight', 'dim'));
    }

    allNodeGroups.forEach(g => {
      const cityId = g.dataset.cityId;
      const city = state.cities.find(c => c.id === cityId);
      if (!city) return;

      g.addEventListener('mouseenter', () => {
        highlightCity(cityId);
        const info = conflictMap.get(cityId) || { incoming: 0, conflict: false };
        const alloc = computeAllocation(city);
        const title = infoPanel.querySelector('.title');
        const body = infoPanel.querySelector('.body');
        const cIcon = allianceIconOf(city);
        title.textContent = `${cIcon ? cIcon + ' ' : ''}${city.isCapital ? '👑 ' : ''}${city.name}（${sideLabel(city.side)}）`;
        const atkList = (city.attackTargets||[]).filter(t => (t.preWarPercent||0)>0).map(t => {
          const tgt = state.cities.find(cc => cc.id === t.cityId);
          return tgt ? `${tgt.name} ${t.preWarPercent}%` : '';
        }).filter(Boolean).join('、') || '無';
        const defList = (city.defendTargets||[]).filter(t => (t.preWarPercent||0)>0).map(t => {
          const tgt = state.cities.find(cc => cc.id === t.cityId);
          return tgt ? `${tgt.name} ${t.preWarPercent}%` : '';
        }).filter(Boolean).join('、') || '無';
        body.innerHTML = `
          <div class="row"><span>總隊數</span><b>${city.totalTeams}</b></div>
          <div class="row"><span>均戰</span><b>${city.avgPower}</b></div>
          <div class="row"><span>留守</span><b>${alloc.reserve} 隊</b></div>
          <div class="row"><span>受兵量</span><b style="color:${info.conflict?'var(--neon-red)':'var(--text-primary)'};">${info.incoming} 隊</b></div>
          <div class="row" style="flex-direction:column;align-items:flex-start;gap:2px;margin-top:4px;"><span>⚔️ 進攻</span><b style="font-size:10px;">${esc(atkList)}</b></div>
          <div class="row" style="flex-direction:column;align-items:flex-start;gap:2px;"><span>🛡️ 協防</span><b style="font-size:10px;">${esc(defList)}</b></div>
        `;
        infoPanel.style.display = 'block';
      });
      g.addEventListener('mouseleave', () => {
        clearHighlight();
        infoPanel.style.display = 'none';
      });
      g.addEventListener('click', () => openCityModal(cityId));
    });

    svg.addEventListener('click', (e) => {
      if (e.target === svg){ clearHighlight(); infoPanel.style.display = 'none'; }
    });
  }

  function makeCurve(fromPos, toPos, fromR, toR){
    const dx = toPos.x - fromPos.x;
    const dy = toPos.y - fromPos.y;
    const dist = Math.hypot(dx, dy);
    if (dist < 1) return '';
    const ux = dx/dist, uy = dy/dist;
    const sx = fromPos.x + ux * (fromR + 3);
    const sy = fromPos.y + uy * (fromR + 3);
    const ex = toPos.x - ux * (toR + 5);
    const ey = toPos.y - uy * (toR + 5);
    const mx = (sx + ex) / 2;
    const my = (sy + ey) / 2;
    const curvature = Math.min(dist * 0.08, 55);
    const cx = mx - uy * curvature;
    const cy = my + ux * curvature;
    return `M ${sx} ${sy} Q ${cx} ${cy} ${ex} ${ey}`;
  }

  function makeDefs(ns){
    const defs = document.createElementNS(ns, 'defs');
    const mk = (id, color) => {
      const marker = document.createElementNS(ns, 'marker');
      marker.setAttribute('id', id);
      marker.setAttribute('viewBox', '0 0 10 10');
      marker.setAttribute('refX', '8');
      marker.setAttribute('refY', '5');
      marker.setAttribute('markerWidth', '5');
      marker.setAttribute('markerHeight', '5');
      marker.setAttribute('orient', 'auto-start-reverse');
      const path = document.createElementNS(ns, 'path');
      path.setAttribute('d', 'M 0 0 L 10 5 L 0 10 z');
      path.setAttribute('fill', color);
      marker.appendChild(path);
      return marker;
    };
    defs.appendChild(mk('arrow-atk', '#ff4466'));
    defs.appendChild(mk('arrow-def', '#22ff88'));
    return defs;
  }

  function renderSummary(cities, conflictMap){
    const totalCities = cities.length;
    const withAtk = cities.filter(c => (c.attackTargets||[]).some(t => (t.preWarPercent||0)>0)).length;
    const withDef = cities.filter(c => (c.defendTargets||[]).some(t => (t.preWarPercent||0)>0)).length;
    const overdraft = cities.filter(c => computeAllocation(c).over).length;
    const conflict = cities.filter(c => conflictMap.get(c.id)?.conflict).length;
    const totalDeployed = cities.reduce((sum, c) => sum + computeAllocation(c).allocated, 0);
    const totalTeams = cities.reduce((sum, c) => sum + (c.totalTeams || 0), 0);
    document.getElementById('deploySummary').innerHTML = `
      📊 共 <b>${totalCities}</b> 座城 · 
      ⚔️ 有進攻指示 <b>${withAtk}</b> 座 · 
      🛡️ 有協防指示 <b>${withDef}</b> 座 · 
      ⚠️ 超額派兵 <b>${overdraft}</b> 座 · 
      🚨 衝堂警示 <b style="color:var(--neon-red);">${conflict}</b> 座 · 
      總派兵 <b>${totalDeployed}</b> 隊 / 總兵力 <b>${totalTeams}</b> 隊
    `;
  }

  function render(){
    const conflictMap = getConflictInfo();
    const cities = getFilteredCities();
    if (currentView === 'attack') renderAttackView(cities, conflictMap);
    else if (currentView === 'defend') renderDefendView(cities, conflictMap);
    else if (currentView === 'matrix') renderMatrixView(cities, conflictMap);
    else if (currentView === 'graph') renderGraphView(cities, conflictMap);
    renderSummary(cities, conflictMap);
    document.querySelectorAll('[data-deploy-edit]').forEach(btn => {
      btn.addEventListener('click', function(){
        openCityModal(this.dataset.deployEdit);
      });
    });
  }

  function exportCSV(){
    const conflictMap = getConflictInfo();
    const cities = getFilteredCities();
    let headers, rows;
    if (currentView === 'attack'){
      headers = ['出兵城', '陣營', '總隊數', '進攻指示', '協防指示', '留守隊數', '留守%', '受兵量', '衝堂警示'];
      rows = cities.map(c => {
        const alloc = computeAllocation(c);
        const info = conflictMap.get(c.id) || { incoming: 0, conflict: false };
        const atkStr = (c.attackTargets||[]).filter(t => (t.preWarPercent||0)>0).map(t => {
          const tgt = state.cities.find(cc => cc.id === t.cityId);
          return tgt ? `${tgt.name} ${t.preWarPercent}% #${t.priority}` : '';
        }).filter(Boolean).join(' | ');
        const defStr = (c.defendTargets||[]).filter(t => (t.preWarPercent||0)>0).map(t => {
          const tgt = state.cities.find(cc => cc.id === t.cityId);
          return tgt ? `${tgt.name} ${t.preWarPercent}% #${t.priority}` : '';
        }).filter(Boolean).join(' | ');
        const reservePct = c.totalTeams > 0 ? Math.round(alloc.reserve / c.totalTeams * 100) : 0;
        return [c.name, sideLabel(c.side), c.totalTeams, atkStr || '-', defStr || '-', alloc.reserve, `${reservePct}%`, info.incoming, info.conflict ? '⚠️ 警示' : '正常'];
      });
    } else if (currentView === 'defend'){
      headers = ['目標城', '陣營', '總隊數', '被誰進攻', '被誰協防', '總受兵', '衝堂警示'];
      rows = cities.map(c => {
        const info = conflictMap.get(c.id) || { incoming: 0, conflict: false };
        const atkStr = state.cities.filter(o => (o.attackTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0)>0))
          .map(o => { const t = o.attackTargets.find(t => t.cityId === c.id); return `${o.name} ${t.preWarPercent}% #${t.priority}`; }).join(' | ');
        const defStr = state.cities.filter(o => (o.defendTargets||[]).some(t => t.cityId === c.id && (t.preWarPercent||0)>0))
          .map(o => { const t = o.defendTargets.find(t => t.cityId === c.id); return `${o.name} ${t.preWarPercent}% #${t.priority}`; }).join(' | ');
        return [c.name, sideLabel(c.side), c.totalTeams, atkStr || '-', defStr || '-', info.incoming, info.conflict ? '⚠️ 警示' : '正常'];
      });
    } else {
      headers = ['出兵城', '目標城', '行動', '派兵%', '優先順序'];
      rows = [];
      for(const src of cities){
        for(const t of (src.attackTargets||[])){
          if ((t.preWarPercent||0) <= 0) continue;
          const tgt = state.cities.find(cc => cc.id === t.cityId);
          if (!tgt) continue;
          rows.push([src.name, tgt.name, '進攻', t.preWarPercent + '%', t.priority]);
        }
        for(const t of (src.defendTargets||[])){
          if ((t.preWarPercent||0) <= 0) continue;
          const tgt = state.cities.find(cc => cc.id === t.cityId);
          if (!tgt) continue;
          rows.push([src.name, tgt.name, '協防', t.preWarPercent + '%', t.priority]);
        }
      }
    }
    const csv = [headers, ...rows].map(r => r.map(v => `"${String(v).replace(/"/g,'""')}"`).join(',')).join('\n');
    const blob = new Blob(['\uFEFF' + csv], {type: 'text/csv;charset=utf-8;'});
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    const viewName = currentView === 'attack' ? '出兵' : currentView === 'defend' ? '受擊' : currentView === 'graph' ? '連線圖' : '矩陣';
    a.href = url;
    a.download = `佈兵總覽_${viewName}_${new Date().toISOString().slice(0,10)}.csv`;
    document.body.appendChild(a); a.click(); document.body.removeChild(a);
    URL.revokeObjectURL(url);
    logSystem('📥 已匯出 CSV');
  }

  return { init, render, populateZoneFilter };
})();

/* ============ 事件綁定 ============ */
function bindUI(){
  document.querySelectorAll('.top-nav button').forEach(btn => {
    btn.addEventListener('click', function(){
      document.querySelectorAll('.top-nav button').forEach(b => b.classList.remove('active'));
      document.querySelectorAll('.tab-content').forEach(t => t.classList.remove('active'));
      this.classList.add('active');
      const tabId = this.dataset.tab;
      document.getElementById(tabId).classList.add('active');
      if(tabId === 'tab-cities') R.renderCities();
      if(tabId === 'tab-alliances') R.renderAlliances();
      if(tabId === 'tab-dyn'){ DYN.setRows(state.dynRows); DYN.populateCityFilters(); }
      if(tabId === 'tab-narrative'){ R.renderNarrative(state.narrativeLines); }
      if(tabId === 'tab-viz') requestAnimationFrame(() => requestAnimationFrame(() => viz.activate()));
      if(tabId === 'tab-params') syncAIParamsToUI();
      if(tabId === 'tab-deploy'){ DEPLOY.populateZoneFilter(); DEPLOY.render(); }
    });
  });
  const nameInput = document.getElementById('commanderName');
  nameInput.addEventListener('input', function(){ state.commanderName = this.value.trim(); saveState(); });
  document.getElementById('btnCreateRoom').addEventListener('click', () => {
    const name = nameInput.value.trim();
    if(!name){ alert('請先填寫指揮官名稱'); return; }
    state.commanderName = name;
    const code = String(Math.floor(100000 + Math.random()*900000));
    document.getElementById('roomCode').value = code;
    connectMQTT(code, true); saveState();
  });
  document.getElementById('btnJoinRoom').addEventListener('click', () => {
    const name = nameInput.value.trim();
    if(!name){ alert('請先填寫指揮官名稱'); return; }
    const code = document.getElementById('roomCode').value.trim();
    if(code.length !== 6){ alert('請輸入6位數房間碼'); return; }
    state.commanderName = name;
    connectMQTT(code, false); saveState();
  });
  document.getElementById('btnDisconnect').addEventListener('click', () => showConfirm('中斷連線', '確定要中斷與盟友的連線嗎？', () => disconnectMQTT()));
  document.getElementById('btnSaveSettings').addEventListener('click', () => {
    updateSettings({
      timeLimitMin: parseInt(document.getElementById('globalTimeLimit').value) || 120,
      consumeMinPerMin: parseFloat(document.getElementById('globalConsumeMinPerMin').value) || 10,
      consumeMaxPerMin: parseFloat(document.getElementById('globalConsumeMaxPerMin').value) || 30,
      siegeEfficiency: parseFloat(document.getElementById('globalSiegeEfficiency').value) || 1,
      marchTimeSec: parseInt(document.getElementById('globalMarchTimeSec').value) || 0,
      maxLossRatio: (parseFloat(document.getElementById('globalMaxLossRatio').value) || 90) / 100,
      minLossRatio: (parseFloat(document.getElementById('globalMinLossRatio').value) || 10) / 100,
    });
    R.renderMatrix();
    alert('戰鬥參數已儲存');
  });
  document.getElementById('btnResetAll').addEventListener('click', () => {
    showConfirm('重置所有數據', '⚠️ 這將清除所有資料！確定嗎？', () => { localStorage.removeItem(LS_PREFIX + 'state'); localStorage.removeItem(AI_LS_KEY); location.reload(); });
  });
  document.getElementById('btnAISave').addEventListener('click', function(){
    AI.setParams(readAIParamsFromUI());
    AI.saveParams();
    alert('AI 參數已儲存');
  });
  document.getElementById('btnAIReset').addEventListener('click', function(){
    showConfirm('恢復 AI 預設參數', '這會將所有 AI 參數恢復為預設值，確定嗎？', () => {
      AI.resetParams();
      syncAIParamsToUI();
      logSystem('🔄 AI 參數已恢復預設');
    });
  });
  ['aiR25','aiR20','aiR15','aiR12','aiR10','aiR08','aiR06','aiR00','aiTeamFactor','aiWallFactor1','aiWallFactor2','aiDefendFactor','aiMinPct'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.addEventListener('input', () => AI.setParams(readAIParamsFromUI()));
  });
  document.getElementById('allyMemberCount').addEventListener('input', updateAllianceAvgPowerPreview);
  document.getElementById('allyTotalPower').addEventListener('input', updateAllianceAvgPowerPreview);
  document.getElementById('btnSaveAlliance').addEventListener('click', () => {
    const name = document.getElementById('allyName').value.trim();
    if(!name){ alert('請輸入同盟名稱'); return; }
    const icon = document.getElementById('allyIcon').value.trim();
    const side = document.getElementById('allySide').value;
    const memberCount = parseFloat(document.getElementById('allyMemberCount').value) || 0;
    const totalPower = parseFloat(document.getElementById('allyTotalPower').value) || 0;
    if(memberCount <= 0){ alert('總人數必須大於 0'); return; }
    const avgPower = totalPower / memberCount;
    if(side === 'self'){
      state.alliances.forEach(a => { if(a.side === 'self' && a.id !== state.editingAllianceId){ a.side = 'enemy'; state.entityRev.alliance[a.id] = (state.entityRev.alliance[a.id] || 0) + 1; markDirty('alliance', a.id); } });
    }
    const id = state.editingAllianceId || uid();
    upsertEntity('alliance', { id, name, icon, side, memberCount, totalPower, avgPower, power: totalPower });
    resetAllianceForm(); R.renderAlliances(); saveState();
  });
  document.getElementById('btnCancelAllianceEdit').addEventListener('click', resetAllianceForm);
  document.querySelectorAll('.icon-quick').forEach(btn => {
    btn.addEventListener('click', function(){
      document.getElementById('allyIcon').value = this.dataset.icon || '';
    });
  });
  document.getElementById('allianceTableBody').addEventListener('click', e => {
    const editBtn = e.target.closest('[data-action="edit-alliance"]');
    const delBtn = e.target.closest('[data-action="del-alliance"]');
    if(editBtn){ startEditAlliance(editBtn.dataset.id); return; }
    if(delBtn){
      const a = state.alliances.find(x => x.id === delBtn.dataset.id);
      if(!a) return;
      showConfirm('刪除同盟', `確定刪除「${a.name}」？`, () => { if(state.editingAllianceId === a.id) resetAllianceForm(); deleteEntity('alliance', a.id); R.renderAlliances(); saveState(); });
    }
  });
  document.getElementById('btnAddZone').addEventListener('click', () => { const name = document.getElementById('newZoneName').value.trim(); if(!name) return; upsertEntity('zone', {id:uid(), name}); document.getElementById('newZoneName').value = ''; R.renderZones(); R.renderCities(); saveState(); });
  document.getElementById('zoneList').addEventListener('click', e => {
    const btn = e.target.closest('[data-action="del-zone"]');
    if(!btn) return;
    showConfirm('刪除戰區', '確定刪除？', () => { deleteEntity('zone', btn.dataset.id); R.renderZones(); R.renderCities(); saveState(); });
  });
  document.getElementById('btnOpenNewCity').addEventListener('click', () => { if(state.zones.length === 0){ alert('請先新增戰區'); return; } openCityModal(null); });
  document.getElementById('cityList').addEventListener('click', e => {
    const editBtn = e.target.closest('[data-action="edit-city"]');
    const delBtn = e.target.closest('[data-action="del-city"]');
    if(editBtn){ openCityModal(editBtn.dataset.id); return; }
    if(delBtn){ showConfirm('刪除城池', '確定刪除？', () => { deleteEntity('city', delBtn.dataset.id); R.renderCities(); saveState(); }); }
  });
  document.getElementById('cityModalCancel').addEventListener('click', closeCityModal);
  document.getElementById('cityModalSave').addEventListener('click', saveCityFromModal);
  document.getElementById('cityModalAI').addEventListener('click', applyAISuggestion);
  ['cm_totalPower', 'cm_totalTeams'].forEach(id => { document.getElementById(id).addEventListener('input', () => { updateAutoCalcFields(); updateAllocPanel(); }); });
  document.getElementById('cm_side').addEventListener('change', function(){
    const newSide = this.value;
    const validAtk = ATTACK_RULES[newSide] || [];
    const validDef = DEFEND_RULES[newSide] || [];
    const {attackTargets, defendTargets} = collectCurrentTargets();
    const fAtk = attackTargets.filter(t => { const c = state.cities.find(cc => cc.id === t.cityId); return c && validAtk.includes(c.side); });
    const fDef = defendTargets.filter(t => { const c = state.cities.find(cc => cc.id === t.cityId); return c && validDef.includes(c.side); });
    updateSectionLabels();
    renderTargetSelectors(fAtk, fDef);
  });
  document.getElementById('cm_zone').addEventListener('change', () => { const {attackTargets, defendTargets} = collectCurrentTargets(); renderTargetSelectors(attackTargets, defendTargets); });
  document.getElementById('btnSimulate').addEventListener('click', () => {
    const zoneId = document.getElementById('simZoneSelect').value;
    if(!isConnected()){ logSystem('⚠️ 未連線，僅本地推演'); executeSimulation(zoneId); return; }
    publish({ type:'trigger_simulate', zoneId, clientId:state.myClientId, name:state.commanderName });
    logSystem(`⚡ ${state.commanderName} 啟動推演`);
    if(state.isHost) executeSimulation(zoneId);
  });
  document.getElementById('modalCancel').addEventListener('click', () => { document.getElementById('confirmModal').classList.remove('show'); confirmCb = null; });
  document.getElementById('modalConfirm').addEventListener('click', () => { document.getElementById('confirmModal').classList.remove('show'); if(confirmCb) confirmCb(); confirmCb = null; });
  window.addEventListener('beforeunload', saveState);
  DEPLOY.init();
}
function bindEvents(){
  on(EVT.DEBUG, R.renderDebug);
  on(EVT.CONN, () => { R.renderHealth(); R.renderHost(); });
  on(EVT.PING, R.renderPing);
  on(EVT.MEMBERS, R.renderMembers);
  on(EVT.HOST, R.renderHost);
  on(EVT.LOCKS, () => { R.renderCities(); if (document.getElementById('tab-deploy').classList.contains('active')) DEPLOY.render(); });
  on(EVT.DATA, () => {
    R.renderAlliances(); R.renderZones(); R.renderCities();
    document.getElementById('globalTimeLimit').value = state.settings.timeLimitMin;
    document.getElementById('globalConsumeMinPerMin').value = state.settings.consumeMinPerMin;
    document.getElementById('globalConsumeMaxPerMin').value = state.settings.consumeMaxPerMin;
    document.getElementById('globalSiegeEfficiency').value = state.settings.siegeEfficiency;
    document.getElementById('globalMarchTimeSec').value = state.settings.marchTimeSec;
    document.getElementById('globalMaxLossRatio').value = Math.round(state.settings.maxLossRatio * 100);
    document.getElementById('globalMinLossRatio').value = Math.round(state.settings.minLossRatio * 100);
    if (document.getElementById('tab-deploy').classList.contains('active')) DEPLOY.render();
  });
  on(EVT.DYN_RESULT, () => { DYN.setRows(state.dynRows); DYN.populateCityFilters(); });
  on(EVT.SIM_TRIGGER, payload => {
    if(payload.name && payload.clientId !== state.myClientId) logSystem(`⚡ ${payload.name} 啟動推演`);
    if(state.isHost){ document.getElementById('simZoneSelect').value = payload.zoneId || 'all'; executeSimulation(payload.zoneId || 'all'); }
  });
}
function boot(){
  loadState();
  document.getElementById('commanderName').value = state.commanderName || '';
  document.getElementById('roomCode').value = state.roomCode || '';
  document.getElementById('globalTimeLimit').value = state.settings.timeLimitMin;
  document.getElementById('globalConsumeMinPerMin').value = state.settings.consumeMinPerMin;
  document.getElementById('globalConsumeMaxPerMin').value = state.settings.consumeMaxPerMin;
  document.getElementById('globalSiegeEfficiency').value = state.settings.siegeEfficiency;
  document.getElementById('globalMarchTimeSec').value = state.settings.marchTimeSec;
  document.getElementById('globalMaxLossRatio').value = Math.round(state.settings.maxLossRatio * 100);
  document.getElementById('globalMinLossRatio').value = Math.round(state.settings.minLossRatio * 100);
  syncAIParamsToUI();
  registerSender(patches => { if(!state.connected) return; publish({ type:'sync_patch', clientId:state.myClientId, lamport:state.lamport, patches }); });
  bindUI(); bindEvents();
  viz.init(); DYN.init(); resetAllianceForm(); R.renderAll();
  DYN.setRows(state.dynRows); DYN.populateCityFilters();
  R.renderNarrative(state.narrativeLines);
  R.renderProgress(0);
  DEPLOY.populateZoneFilter();
  console.log('%c[沙盤 v7.3] 盟徽 + 三佈局連線圖 + 全部功能就緒', 'color:#22ff88;font-weight:bold;font-size:14px');
}
if(document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
else boot();

})();