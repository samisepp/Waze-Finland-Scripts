// ==UserScript==
// @name         WME MML-katutarkistus
// @namespace    wme-mml-tarkistus
// @version      0.5.2
// @description  Tarkistaa WME-näkymän katunimet MML:n geokoodausrajapinnasta ja korostaa segmentit, joiden katua ei löydy virallisesta tieosoiteaineistosta.
// @author       Sam
// @match        https://www.waze.com/*editor*
// @match        https://beta.waze.com/*editor*
// @exclude      https://www.waze.com/user/editor*
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @connect      avoin-paikkatieto.maanmittauslaitos.fi
// @run-at       document-end
// ==/UserScript==

/*
 * Toimintaperiaate:
 *  1. Tarkistus lukee näkymään ladatut segmentit W.modelista ja suodattaa ne
 *     näkyvälle karttarajaukselle sekä valituille tietyypeille. Tarkistuksen
 *     voi käynnistää napista tai automaattisesti kartan liikkuessa.
 *  2. Jokaisesta segmentistä poimitaan katunimi(en) + kaupunki -parit
 *     (ensisijainen nimi + vaihtoehtoiset nimet, "270 - Nimi" pilkotaan osiin).
 *  3. Uniikit (kaupunki|katu) -parit kysytään MML:n geokoodauksesta
 *     (interpolated-road-addresses) viidellä rinnakkaisella kyselyllä.
 *     Tulokset välimuistiin (30 pv) avaimella kaupunki|katu, joten sama katu
 *     kysytään MML:stä vain kerran riippumatta zoomista ja panoroinnista.
 *  4. Segmentit, joiden yksikään nimi ei löydy MML:stä, korostetaan kartalla
 *     ja listataan sivupaneeliin. Kuntavertailu hyväksyy sekä suomen- että
 *     ruotsinkielisen kuntanimen (kuntanimiFin / kuntanimiSwe).
 *
 * Huom: "ei löydy MML:stä" on vihje, ei tuomio - yksityistiet ja uudet kadut
 * voivat puuttua virallisesta aineistosta vaikka Waze-data on oikein.
 *
 * Versiohistoria:
 *  0.5.2 - Marker segmentin todelliseen keskikohtaan viivaa pitkin, jotta se
 *          ei osu nodeen (2 pisteen segmentillä osui aiemmin päätepisteeseen).
 *  0.5.1 - Markerin klikkaus valitsee kadun segmentit WME:ssä popupin lisäksi.
 *  0.5.0 - Rinnakkaisuus 10:een. Client-tunniste MML-kutsuihin (User-Agent /
 *          X-Client). Markerin klikkaus avaa popupin, joka kertoo ongelman.
 *          Käynnissä-indikaattori (spinner + eteneminen) karttanäkymään.
 *  0.4.2 - Ympyrämarkeri (!) segmentin keskikohtaan korostuksen lisäksi.
 *  0.4.1 - Vikalista näyttää uniikit kadut (yksi rivi per katu+kaupunki);
 *          kaikki kadun segmentit korostetaan ja klikkaus kiertää ne läpi.
 *  0.4.0 - Selkeämpi asetusvalikko (nappimainen avaus, nuoli, valintamäärä).
 *          Valinnainen automaattitarkistus kartan liikkuessa (debounce +
 *          zoomivartija). Nappi säilyy manuaalikäyttöön.
 *  0.3.1 - Lautat (15) ja portaat (16) jätetään aina pois asetusten sijaan.
 *  0.3.0 - Tietyyppiasetukset (on/off per tyyppi). Junaradat (18) aina pois.
 *          Oletuksena pois: jalankulkuväylät, rampit, moottoritiet.
 *  0.2.1 - Näkymäsuodatus: vain kartan rajauksen sisällä olevat segmentit.
 *  0.2.0 - Napit type="button", kuntanimiSwe mukaan, rinnakkaiset kyselyt.
 *  0.1.0 - Ensimmäinen versio.
 */

(function () {
  'use strict';

  const SCRIPT_NAME = 'MML-katutarkistus';
  const SCRIPT_VERSION = '0.5.2';
  const CLIENT_ID = `WME-MML-katutarkistus/${SCRIPT_VERSION} (Tampermonkey userscript; Waze Map Editor)`;
  const MML_BASE = 'https://avoin-paikkatieto.maanmittauslaitos.fi/geocoding/v2/pelias/search';
  const CACHE_KEY = 'mml_katu_cache_v1';
  const APIKEY_KEY = 'mml_api_key';
  const ROADTYPES_KEY = 'mml_roadtypes_v1';
  const AUTOCHECK_KEY = 'mml_autocheck_v1';
  const CACHE_TTL_MS = 30 * 24 * 60 * 60 * 1000; // 30 pv
  const CONCURRENCY = 10;                         // rinnakkaiset MML-kyselyt
  const AUTOCHECK_DEBOUNCE_MS = 1500;             // odotus kartan pysähtymisen jälkeen
  const AUTOCHECK_MIN_ZOOM = 14;                  // automaattitarkistuksen zoomiraja

  // Junaradat, lautat ja portaat ohitetaan aina, eivät näy asetuksissa.
  const ALWAYS_EXCLUDED = new Set([15, 16, 18]);

  // Tietyypit asetuksiin. def = oletusarvo (true = tarkistetaan).
  // Jalankulkuväylät (5, 9, 10), rampit (4) ja moottoritiet (3) oletuksena pois.
  const ROAD_TYPES = [
    { id: 1,  label: 'Katu',                     def: true  },
    { id: 2,  label: 'Pääkatu',                  def: true  },
    { id: 3,  label: 'Moottoritie',              def: false },
    { id: 4,  label: 'Ramppi',                   def: false },
    { id: 5,  label: 'Polku (kävelyreitti)',     def: false },
    { id: 6,  label: 'Valtatie (Major Hwy)',     def: true  },
    { id: 7,  label: 'Seututie (Minor Hwy)',     def: true  },
    { id: 8,  label: 'Maastotie / hiekkatie',    def: true  },
    { id: 9,  label: 'Kävelytie (Walkway)',      def: false },
    { id: 10, label: 'Jalankulkuväylä',          def: false },
    { id: 17, label: 'Yksityistie',              def: true  },
    { id: 19, label: 'Kiitotie',                 def: true  },
    { id: 20, label: 'Pysäköintialueen tie',     def: true  },
    { id: 22, label: 'Kuja / kapea katu',        def: true  },
  ];

  // Tilat: 'found' | 'notfound' | 'wrongcity' | 'error'
  let cache = {};
  let roadTypeSettings = {};
  let autoCheckEnabled = false;
  let highlightLayer = null;
  let panel = { status: null, list: null, keyInput: null, typeCount: null };

  /* ---------------------------------------------------------- apuvälineet */

  const log = (...a) => console.log(`[${SCRIPT_NAME}]`, ...a);

  function loadCache() {
    try {
      const raw = GM_getValue(CACHE_KEY, '{}');
      cache = JSON.parse(raw);
      const now = Date.now();
      let pruned = 0;
      for (const k of Object.keys(cache)) {
        if (!cache[k].ts || now - cache[k].ts > CACHE_TTL_MS) { delete cache[k]; pruned++; }
      }
      if (pruned) saveCache();
      log(`Välimuisti ladattu: ${Object.keys(cache).length} nimeä (${pruned} vanhentunutta poistettu).`);
    } catch (e) {
      log('Välimuistin luku epäonnistui, aloitetaan tyhjästä.', e);
      cache = {};
    }
  }

  function saveCache() {
    GM_setValue(CACHE_KEY, JSON.stringify(cache));
  }

  function loadSettings() {
    let saved = {};
    try {
      saved = JSON.parse(GM_getValue(ROADTYPES_KEY, '{}'));
    } catch (e) { saved = {}; }
    roadTypeSettings = {};
    for (const rt of ROAD_TYPES) {
      roadTypeSettings[rt.id] = (rt.id in saved) ? !!saved[rt.id] : rt.def;
    }
    autoCheckEnabled = !!GM_getValue(AUTOCHECK_KEY, false);
  }

  function saveRoadTypeSettings() {
    GM_setValue(ROADTYPES_KEY, JSON.stringify(roadTypeSettings));
  }

  function isTypeChecked(roadType) {
    if (ALWAYS_EXCLUDED.has(roadType)) return false;
    if (roadType in roadTypeSettings) return roadTypeSettings[roadType];
    return true; // tuntematon uusi tyyppi: tarkistetaan varmuuden vuoksi
  }

  function selectedTypeCount() {
    return ROAD_TYPES.filter(rt => roadTypeSettings[rt.id]).length;
  }

  // "270 - Siikaistentie" -> ["Siikaistentie"], "270" -> [] (pelkkä numero ohitetaan)
  function nameCandidates(rawName) {
    if (!rawName) return [];
    const parts = rawName.split(' - ').map(s => s.trim()).filter(Boolean);
    const out = [];
    for (const p of parts.length ? parts : [rawName.trim()]) {
      if (/^\d+$/.test(p)) continue;          // pelkkä tienumero
      if (/^[EVKS]?\d+$/i.test(p)) continue;  // esim. E12, ohitetaan
      out.push(p);
    }
    return out;
  }

  /* ------------------------------------------------ WME-datamallin luenta */

  function getModel() {
    const W = unsafeWindow.W || window.W;
    if (!W || !W.model || !W.model.segments) return null;
    return W;
  }

  function getOlMap() {
    const W = getModel();
    if (!W || !W.map) return null;
    return typeof W.map.getOLMap === 'function' ? W.map.getOLMap() : W.map;
  }

  function segGeometry(seg) {
    // Uudemmissa WME-versioissa GeoJSON attributeissa, vanhoissa OL-geometria.
    const a = seg.attributes || {};
    if (a.geoJSONGeometry && a.geoJSONGeometry.coordinates) return a.geoJSONGeometry;
    if (typeof seg.getOLGeometry === 'function') {
      try {
        const g = seg.getOLGeometry();
        if (g && g.components) {
          return { type: 'LineString', coordinates: g.components.map(p => [p.x, p.y]) };
        }
      } catch (e) { /* jatketaan */ }
    }
    if (a.geometry && a.geometry.components) {
      return { type: 'LineString', coordinates: a.geometry.components.map(p => [p.x, p.y]) };
    }
    return null;
  }

  // Palauttaa listan { segId, streetName, cityName, candidates:[...] }
  function collectSegments() {
    const W = getModel();
    if (!W) return [];
    const OpenLayers = unsafeWindow.OpenLayers || window.OpenLayers;
    const olMap = getOlMap();
    if (!OpenLayers || !olMap) return [];
    const extent = olMap.getExtent(); // näkymän rajat karttaprojektiossa
    const proj4326 = new OpenLayers.Projection('EPSG:4326');
    const mapProj = olMap.getProjectionObject();

    const segments = W.model.segments.getObjectArray();
    const items = [];
    for (const seg of segments) {
      const a = seg.attributes || {};

      // Tietyyppisuodatus (junaradat/lautat/portaat aina pois, muut asetusten mukaan)
      if (!isTypeChecked(a.roadType)) continue;

      // Näkymäsuodatus: segmentin keskipisteen pitää olla kartan rajauksessa
      const gj = segGeometry(seg);
      if (!gj || !gj.coordinates.length) continue;
      const mid = gj.coordinates[Math.floor(gj.coordinates.length / 2)];
      const pt = new OpenLayers.LonLat(mid[0], mid[1]).transform(proj4326, mapProj);
      if (!extent.containsLonLat(pt)) continue;

      const streetIds = [a.primaryStreetID, ...(a.streetIDs || [])].filter(Boolean);
      for (const sid of streetIds) {
        const street = W.model.streets.getObjectById(sid);
        if (!street) continue;
        const sa = street.attributes || {};
        if (sa.isEmpty || !sa.name) continue;
        const city = W.model.cities.getObjectById(sa.cityID);
        const cityName = city && city.attributes ? city.attributes.name : '';
        if (!cityName) continue; // ilman kaupunkia ei voi verrata MML:ään
        const candidates = nameCandidates(sa.name);
        if (!candidates.length) continue;
        items.push({ seg, segId: a.id, streetName: sa.name, cityName, candidates });
      }
    }
    return items;
  }

  /* --------------------------------------------------------- MML-kyselyt */

  function mmlLookup(street, city, apiKey) {
    return new Promise(resolve => {
      const text = encodeURIComponent(`${street},${city}`);
      const url = `${MML_BASE}?text=${text}&sources=interpolated-road-addresses&size=1&crs=EPSG:4326&api-key=${encodeURIComponent(apiKey)}`;
      GM_xmlhttpRequest({
        method: 'GET',
        url,
        headers: {
          Accept: 'application/json',
          'User-Agent': CLIENT_ID,
          'X-Client': CLIENT_ID,
        },
        onload: resp => {
          try {
            if (resp.status !== 200) {
              log(`MML HTTP ${resp.status} (${street}, ${city})`);
              resolve('error');
              return;
            }
            const data = JSON.parse(resp.responseText);
            const feats = (data && data.features) || [];
            if (!feats.length) { resolve('notfound'); return; }
            const p = feats[0].properties || {};
            const cityLc = city.toLowerCase();
            const nameOk = (p.katunimi || '').toLowerCase() === street.toLowerCase();
            const cityOk = (p.kuntanimiFin || '').toLowerCase() === cityLc
                        || (p.kuntanimiSwe || '').toLowerCase() === cityLc;
            if (nameOk && cityOk) resolve('found');
            else if (nameOk && !cityOk) resolve('wrongcity');
            else resolve('notfound');
          } catch (e) {
            log('MML-vastauksen käsittely epäonnistui', e);
            resolve('error');
          }
        },
        onerror: () => resolve('error'),
        ontimeout: () => resolve('error'),
        timeout: 15000,
      });
    });
  }

  /* ------------------------------------------------------------ korostus */

  function ensureLayer() {
    const W = getModel();
    if (!W) return null;
    const OpenLayers = unsafeWindow.OpenLayers || window.OpenLayers;
    if (!OpenLayers) { log('OpenLayers ei saatavilla - korostus ohitetaan.'); return null; }
    const olMap = getOlMap();
    if (!highlightLayer) {
      highlightLayer = new OpenLayers.Layer.Vector(`${SCRIPT_NAME}`, {
        displayInLayerSwitcher: true,
      });
      olMap.addLayer(highlightLayer);
    }
    return { W, olMap, OpenLayers };
  }

  function clearHighlights() {
    if (highlightLayer) highlightLayer.removeAllFeatures();
    markerIndex.length = 0;
    hideMarkerPopup();
  }

  // Markerien sijainnit ja tiedot popupia varten: { x, y (karttaproj.), html }
  const markerIndex = [];
  let popupDiv = null;
  let popupRegistered = false;

  function hideMarkerPopup() {
    if (popupDiv) popupDiv.style.display = 'none';
  }

  function showMarkerPopup(olMap, pixel, html) {
    if (!popupDiv) {
      popupDiv = document.createElement('div');
      popupDiv.style.cssText =
        'position:absolute;z-index:10001;background:#fff;border:1px solid #666;'
        + 'border-radius:5px;padding:7px 26px 7px 10px;font:12px sans-serif;color:#222;'
        + 'box-shadow:0 2px 8px rgba(0,0,0,.35);max-width:260px;pointer-events:auto;';
      const closeBtn = document.createElement('span');
      closeBtn.textContent = '\u00d7';
      closeBtn.style.cssText =
        'position:absolute;top:2px;right:7px;cursor:pointer;font-size:15px;color:#888;';
      closeBtn.addEventListener('click', hideMarkerPopup);
      popupDiv.appendChild(closeBtn);
      const content = document.createElement('div');
      content.className = 'mml-popup-content';
      popupDiv.appendChild(content);
      olMap.div.appendChild(popupDiv);
    }
    popupDiv.querySelector('.mml-popup-content').innerHTML = html;
    popupDiv.style.left = (pixel.x + 14) + 'px';
    popupDiv.style.top = (pixel.y - 10) + 'px';
    popupDiv.style.display = 'block';
  }

  // Valitsee segmentit WME:ssä ohjelmallisesti (API vaihtelee versioittain)
  function selectSegments(segs) {
    try {
      const W = getModel();
      if (!W || !W.selectionManager || !segs || !segs.length) return;
      if (typeof W.selectionManager.setSelectedModels === 'function') {
        W.selectionManager.setSelectedModels(segs);
      } else if (typeof W.selectionManager.select === 'function') {
        W.selectionManager.select(segs);
      }
    } catch (e) { log('Segmentin valinta epäonnistui', e); }
  }

  // Kartan klikkaus: jos osui markerin lähelle (n. 14 px), näytä popup
  // ja valitse kadun segmentit WME:ssä.
  function registerMarkerPopup() {
    if (popupRegistered) return;
    const olMap = getOlMap();
    if (!olMap || !olMap.events || typeof olMap.events.register !== 'function') return;
    olMap.events.register('click', null, (e) => {
      try {
        if (!markerIndex.length) { hideMarkerPopup(); return; }
        const lonlat = olMap.getLonLatFromPixel(e.xy);
        const res = olMap.getResolution();
        let best = null;
        let bestDist = 14; // osumaraja pikseleinä
        for (const m of markerIndex) {
          const d = Math.hypot((m.x - lonlat.lon) / res, (m.y - lonlat.lat) / res);
          if (d <= bestDist) { bestDist = d; best = m; }
        }
        if (best) {
          showMarkerPopup(olMap, e.xy, best.html);
          selectSegments(best.segs);
        } else {
          hideMarkerPopup();
        }
      } catch (err) { /* ei kaadeta karttaklikkiä */ }
    });
    popupRegistered = true;
    log('Marker-popupin kuuntelija rekisteröity.');
  }

  // Laskee pisteen 50 % matkassa viivaa pitkin - ei osu koskaan
  // päätepisteeseen (nodeen), toisin kuin geometrian keskimmäinen piste.
  function midpointAlong(points) {
    if (points.length === 1) return points[0];
    let total = 0;
    const lens = [];
    for (let i = 1; i < points.length; i++) {
      const l = Math.hypot(points[i].x - points[i - 1].x, points[i].y - points[i - 1].y);
      lens.push(l);
      total += l;
    }
    let target = total / 2;
    for (let i = 0; i < lens.length; i++) {
      if (target <= lens[i] && lens[i] > 0) {
        const t = target / lens[i];
        return {
          x: points[i].x + (points[i + 1].x - points[i].x) * t,
          y: points[i].y + (points[i + 1].y - points[i].y) * t,
        };
      }
      target -= lens[i];
    }
    return points[points.length - 1];
  }

  function highlightSegment(seg, color, infoHtml, groupSegs) {
    const ctx = ensureLayer();
    if (!ctx) return;
    const { OpenLayers, olMap } = ctx;
    const gj = segGeometry(seg);
    if (!gj) return;
    // WGS84 -> karttaprojektio (Web Mercator)
    const proj4326 = new OpenLayers.Projection('EPSG:4326');
    const mapProj = olMap.getProjectionObject();
    const points = gj.coordinates.map(c => {
      const pt = new OpenLayers.Geometry.Point(c[0], c[1]);
      pt.transform(proj4326, mapProj);
      return pt;
    });
    const line = new OpenLayers.Geometry.LineString(points);
    const feat = new OpenLayers.Feature.Vector(line);
    feat.style = { strokeColor: color, strokeWidth: 9, strokeOpacity: 0.65, strokeLinecap: 'round' };

    // Marker segmentin todelliseen keskikohtaan (matkana viivaa pitkin),
    // jotta se ei osu segmentin päätepisteisiin eli nodeihin
    const midPt = midpointAlong(points);
    const marker = new OpenLayers.Feature.Vector(
      new OpenLayers.Geometry.Point(midPt.x, midPt.y)
    );
    marker.style = {
      pointRadius: 11,
      fillColor: color,
      fillOpacity: 0.95,
      strokeColor: '#ffffff',
      strokeWidth: 2.5,
      label: '!',
      fontColor: '#ffffff',
      fontWeight: 'bold',
      fontSize: '13px',
      labelYOffset: 1,
    };

    if (infoHtml) markerIndex.push({ x: midPt.x, y: midPt.y, html: infoHtml, segs: groupSegs || [seg] });

    highlightLayer.addFeatures([feat, marker]);
  }

  function centerOnSegment(seg) {
    const ctx = ensureLayer();
    if (!ctx) return;
    const { OpenLayers, olMap } = ctx;
    const gj = segGeometry(seg);
    if (!gj || !gj.coordinates.length) return;
    const mid = gj.coordinates[Math.floor(gj.coordinates.length / 2)];
    const pt = new OpenLayers.LonLat(mid[0], mid[1]).transform(
      new OpenLayers.Projection('EPSG:4326'),
      olMap.getProjectionObject()
    );
    olMap.setCenter(pt);
  }

  /* --------------------------------------------------------- päälogiikka */

  let running = false;

  async function runCheck(auto) {
    if (running) return;
    const apiKey = (panel.keyInput.value || '').trim();
    if (!apiKey) {
      if (!auto) setStatus('Syötä MML API-avain ennen tarkistusta.');
      return;
    }
    GM_setValue(APIKEY_KEY, apiKey);

    running = true;
    clearHighlights();
    panel.list.innerHTML = '';
    showBusy('MML-tarkistus käynnissä...');

    try {
      const items = collectSegments();
      if (!items.length) {
        setStatus('Näkymässä ei ole nimettyjä segmenttejä valituilla tietyypeillä (tai datamallia ei tavoitettu).');
        return;
      }

      // Uniikit (kaupunki|katu) -parit
      const pairs = new Map(); // key -> {street, city}
      for (const it of items) {
        for (const cand of it.candidates) {
          pairs.set(`${it.cityName}|${cand}`, { street: cand, city: it.cityName });
        }
      }

      // Kysele puuttuvat rinnakkaisella työntekijäpoolilla
      const keys = [...pairs.keys()];
      const toQuery = keys.filter(k => !cache[k]);
      setStatus(`Näkymässä ${keys.length} uniikkia katua, kysytään MML:stä ${toQuery.length} uutta...`);

      let done = 0;
      let index = 0;

      async function worker() {
        while (index < toQuery.length) {
          const k = toQuery[index++];
          const { street, city } = pairs.get(k);
          const status = await mmlLookup(street, city, apiKey);
          if (status !== 'error') {
            cache[k] = { status, ts: Date.now() };
          }
          done++;
          setStatus(`Kysytään MML:stä... ${done}/${toQuery.length}`);
          showBusy(`MML-tarkistus: ${done}/${toQuery.length}`);
        }
      }

      await Promise.all(
        Array.from({ length: Math.min(CONCURRENCY, toQuery.length) }, () => worker())
      );
      if (toQuery.length) saveCache();

      // Arvioi kadut: ryhmittely uniikin (kaupunki|katu) mukaan. OK jos
      // yksikin kandidaatti löytyi. Ongelmakadusta tulee yksi listarivi,
      // mutta kaikki kadun segmentit korostetaan.
      const groups = new Map(); // key -> { streetName, cityName, kind, segs: [] }
      for (const it of items) {
        const statuses = it.candidates.map(c => (cache[`${it.cityName}|${c}`] || {}).status || 'error');
        if (statuses.includes('found')) continue;
        const kind = statuses.includes('wrongcity') ? 'wrongcity'
                   : statuses.every(s => s === 'error') ? 'error'
                   : 'notfound';
        const key = `${it.cityName}|${it.streetName}`;
        if (!groups.has(key)) {
          groups.set(key, { streetName: it.streetName, cityName: it.cityName, kind, segs: [] });
        }
        const g = groups.get(key);
        if (!g.segs.some(s => (s.attributes || {}).id === it.segId)) g.segs.push(it.seg);
      }
      const problems = [...groups.values()];

      // Piirrä ja listaa
      const colors = { notfound: '#e53935', wrongcity: '#fb8c00', error: '#9e9e9e' };
      const labels = { notfound: 'Ei löydy MML:stä', wrongcity: 'Löytyy, mutta eri kunnassa', error: 'Kyselyvirhe' };
      for (const p of problems) {
        const infoHtml = `<b>${p.streetName}</b> (${p.cityName})<br>${labels[p.kind]}`
          + (p.segs.length > 1 ? `<br><span style="color:#777;">${p.segs.length} segmenttiä</span>` : '');
        for (const s of p.segs) highlightSegment(s, colors[p.kind], infoHtml, p.segs);
      }

      if (!problems.length) {
        setStatus(`Valmis: kaikki ${keys.length} katua löytyivät MML:stä.`);
      } else {
        setStatus(`Valmis: ${problems.length} huomiota (${keys.length} katua tarkistettu).`);
        for (const p of problems) {
          const li = document.createElement('li');
          li.style.cssText = 'padding:4px 6px;margin:2px 0;border-left:4px solid ' + colors[p.kind]
            + ';cursor:pointer;background:#fff;';
          const segInfo = p.segs.length > 1 ? ` — ${p.segs.length} segmenttiä` : '';
          li.textContent = `${p.streetName} (${p.cityName}) — ${labels[p.kind]}${segInfo}`;
          li.title = p.segs.length > 1
            ? 'Klikkaa keskittääksesi kartan; toistuvat klikkaukset kiertävät segmentit läpi'
            : 'Klikkaa keskittääksesi kartan segmenttiin';
          let segIndex = 0;
          li.addEventListener('click', () => {
            centerOnSegment(p.segs[segIndex % p.segs.length]);
            segIndex++;
          });
          panel.list.appendChild(li);
        }
      }
    } catch (e) {
      log('Tarkistus kaatui', e);
      setStatus('Tarkistus epäonnistui - katso konsoli (F12).');
    } finally {
      running = false;
      hideBusy();
    }
  }

  function setStatus(text) {
    if (panel.status) panel.status.textContent = text;
  }

  /* --------------------------------------- käynnissä-indikaattori kartalla */

  let busyDiv = null;

  function showBusy(text) {
    const olMap = getOlMap();
    if (!olMap || !olMap.div) return;
    if (!busyDiv) {
      busyDiv = document.createElement('div');
      busyDiv.style.cssText =
        'position:absolute;top:10px;left:50%;transform:translateX(-50%);z-index:10001;'
        + 'background:rgba(40,40,40,.88);color:#fff;padding:6px 14px;border-radius:16px;'
        + 'font:12px sans-serif;display:flex;align-items:center;gap:8px;pointer-events:none;';
      const spinner = document.createElement('span');
      spinner.style.cssText =
        'width:12px;height:12px;border:2px solid rgba(255,255,255,.35);'
        + 'border-top-color:#fff;border-radius:50%;display:inline-block;'
        + 'animation:mml-spin .8s linear infinite;';
      const style = document.createElement('style');
      style.textContent = '@keyframes mml-spin{to{transform:rotate(360deg)}}';
      document.head.appendChild(style);
      const label = document.createElement('span');
      label.className = 'mml-busy-text';
      busyDiv.appendChild(spinner);
      busyDiv.appendChild(label);
      olMap.div.appendChild(busyDiv);
    }
    busyDiv.querySelector('.mml-busy-text').textContent = text;
    busyDiv.style.display = 'flex';
  }

  function hideBusy() {
    if (busyDiv) busyDiv.style.display = 'none';
  }

  /* -------------------------------------------- automaattitarkistus */

  let autoTimer = null;

  function onMapMoved() {
    if (!autoCheckEnabled) return;
    clearTimeout(autoTimer);
    autoTimer = setTimeout(() => {
      const olMap = getOlMap();
      const zoom = olMap && typeof olMap.getZoom === 'function' ? olMap.getZoom() : null;
      if (zoom !== null && zoom < AUTOCHECK_MIN_ZOOM) {
        setStatus(`Automaattitarkistus odottaa: zoomaa lähemmäs (zoom ${zoom} < ${AUTOCHECK_MIN_ZOOM}).`);
        return;
      }
      runCheck(true);
    }, AUTOCHECK_DEBOUNCE_MS);
  }

  function registerAutoCheck() {
    const olMap = getOlMap();
    if (!olMap || !olMap.events || typeof olMap.events.register !== 'function') {
      log('Kartan moveend-tapahtumaa ei voitu rekisteröidä - automaattitila ei käytettävissä.');
      return false;
    }
    olMap.events.register('moveend', null, onMapMoved);
    log('Automaattitarkistuksen kuuntelija rekisteröity.');
    return true;
  }

  /* -------------------------------------------------------------- paneeli */

  function buildRoadTypeSettingsHtml() {
    const rows = ROAD_TYPES.map(rt => `
      <label style="display:flex;align-items:center;gap:6px;margin:3px 0;cursor:pointer;">
        <input type="checkbox" class="mml-roadtype" data-roadtype="${rt.id}"
               ${roadTypeSettings[rt.id] ? 'checked' : ''}>
        <span>${rt.label}</span>
      </label>`).join('');
    return `
      <details id="mml-settings" style="margin-bottom:8px;border:1px solid #ccc;border-radius:4px;background:#fafafa;">
        <summary style="cursor:pointer;user-select:none;list-style:none;display:flex;align-items:center;
                        gap:6px;padding:7px 8px;font-weight:600;color:#333;">
          <span id="mml-chevron" style="display:inline-block;transition:transform .15s;">&#9654;</span>
          <span>Tarkistettavat tietyypit</span>
          <span id="mml-typecount" style="margin-left:auto;font-weight:400;color:#777;"></span>
        </summary>
        <div style="padding:2px 10px 8px 10px;border-top:1px solid #e0e0e0;">
          ${rows}
          <div style="color:#777;font-size:11px;margin-top:4px;">
            Junaratoja, lauttoja ja portaita ei tarkisteta koskaan.
          </div>
        </div>
      </details>`;
  }

  async function buildPanel() {
    const W = unsafeWindow.W || window.W;
    let container;

    if (W && W.userscripts && typeof W.userscripts.registerSidebarTab === 'function') {
      const { tabLabel, tabPane } = W.userscripts.registerSidebarTab('mml-tarkistus');
      tabLabel.innerText = 'MML';
      tabLabel.title = SCRIPT_NAME;
      container = tabPane;
      if (typeof W.userscripts.waitForElementConnected === 'function') {
        await W.userscripts.waitForElementConnected(tabPane);
      }
    } else {
      // Varareitti: kelluva paneeli
      container = document.createElement('div');
      container.style.cssText =
        'position:fixed;top:70px;right:10px;z-index:10000;background:#f4f4f4;'
        + 'border:1px solid #999;border-radius:6px;padding:8px;width:280px;'
        + 'font:12px sans-serif;box-shadow:0 2px 8px rgba(0,0,0,.3);';
      document.body.appendChild(container);
    }

    container.innerHTML = `
      <div style="font:12px sans-serif;padding:6px;">
        <h5 style="margin:0 0 6px;">${SCRIPT_NAME}</h5>
        <label style="display:block;margin-bottom:2px;">MML API-avain</label>
        <input type="password" id="mml-key" style="width:100%;box-sizing:border-box;margin-bottom:8px;">
        ${buildRoadTypeSettingsHtml()}
        <label style="display:flex;align-items:center;gap:6px;margin-bottom:8px;cursor:pointer;">
          <input type="checkbox" id="mml-auto" ${autoCheckEnabled ? 'checked' : ''}>
          <span>Tarkista automaattisesti kartan liikkuessa</span>
        </label>
        <button id="mml-run" type="button" class="btn btn-primary" style="width:100%;margin-bottom:4px;">Tarkista näkymä</button>
        <button id="mml-clear" type="button" class="btn" style="width:100%;margin-bottom:6px;">Tyhjennä korostukset</button>
        <div id="mml-status" style="min-height:2.4em;color:#333;"></div>
        <ul id="mml-list" style="list-style:none;margin:6px 0 0;padding:0;max-height:300px;overflow:auto;"></ul>
        <div style="margin-top:6px;color:#777;font-size:11px;">
          Avain tallentuu vain Tampermonkeyn omaan varastoon ja kulkee ainoastaan
          maanmittauslaitos.fi-kutsuissa. Punainen = katua ei löydy MML:n
          tieosoitteista, oranssi = löytyy mutta eri kunnasta.
        </div>
      </div>`;

    panel.keyInput = container.querySelector('#mml-key');
    panel.status = container.querySelector('#mml-status');
    panel.list = container.querySelector('#mml-list');
    panel.typeCount = container.querySelector('#mml-typecount');
    panel.keyInput.value = GM_getValue(APIKEY_KEY, '');
    container.querySelector('#mml-run').addEventListener('click', () => runCheck(false));
    container.querySelector('#mml-clear').addEventListener('click', () => {
      clearHighlights();
      panel.list.innerHTML = '';
      setStatus('');
    });

    // Asetusvalikon nuoli kääntyy auki/kiinni-tilan mukaan
    const details = container.querySelector('#mml-settings');
    const chevron = container.querySelector('#mml-chevron');
    details.addEventListener('toggle', () => {
      chevron.style.transform = details.open ? 'rotate(90deg)' : 'rotate(0deg)';
    });

    // Valittujen tyyppien määrä otsikkoriville
    const updateTypeCount = () => {
      panel.typeCount.textContent = `${selectedTypeCount()}/${ROAD_TYPES.length} valittu`;
    };
    updateTypeCount();

    // Tietyyppiasetusten tallennus valintaruutujen muuttuessa
    container.querySelectorAll('.mml-roadtype').forEach(cb => {
      cb.addEventListener('change', () => {
        const id = parseInt(cb.dataset.roadtype, 10);
        roadTypeSettings[id] = cb.checked;
        saveRoadTypeSettings();
        updateTypeCount();
      });
    });

    // Automaattitarkistuksen kytkin
    container.querySelector('#mml-auto').addEventListener('change', (e) => {
      autoCheckEnabled = e.target.checked;
      GM_setValue(AUTOCHECK_KEY, autoCheckEnabled);
      if (autoCheckEnabled) {
        setStatus('Automaattitarkistus päällä - tarkistus ajetaan kun kartta pysähtyy.');
        onMapMoved(); // aja heti nykyiselle näkymälle
      } else {
        setStatus('Automaattitarkistus pois päältä.');
      }
    });

    registerAutoCheck();
    registerMarkerPopup();

    setStatus(panel.keyInput.value ? 'Valmiina.' : 'Syötä MML API-avain aloittaaksesi.');
    log('Paneeli alustettu.');
  }

  /* ------------------------------------------------------------ käynnistys */

  function init() {
    loadCache();
    loadSettings();
    buildPanel();
  }

  function waitForWme() {
    const W = unsafeWindow.W || window.W;
    if (W && W.userscripts && W.userscripts.state && W.userscripts.state.isReady) {
      init();
      return;
    }
    if (W && W.model && W.model.segments && W.map) {
      init();
      return;
    }
    setTimeout(waitForWme, 800);
  }

  if (unsafeWindow.W && unsafeWindow.W.userscripts && unsafeWindow.W.userscripts.state
      && unsafeWindow.W.userscripts.state.isReady) {
    init();
  } else {
    document.addEventListener('wme-ready', () => init(), { once: true });
    waitForWme(); // varareitti jos wme-ready ei laukea
  }
})();
