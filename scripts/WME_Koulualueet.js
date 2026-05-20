// ==UserScript==
// @name         WME Koulualueet
// @namespace    https://waze.com
// @version      0.3.5
// @description  Finnish school locations from Statistics Finland INSPIRE OGC API
// @author       Stemmi
// @match        https://*.waze.com/*editor*
// @grant        GM_xmlhttpRequest
// @grant        unsafeWindow
// @connect      geo.stat.fi
// @license      MIT
// @run-at       document-idle
// @require      https://cdnjs.cloudflare.com/ajax/libs/proj4js/2.9.0/proj4.js
// @require      https://greasyfork.org/scripts/24851-wazewrap/code/WazeWrap.js
// ==/UserScript==

(function () {
    'use strict';

    // Prevent multiple initialization
    if (typeof window !== 'undefined' && window.wmeKoulualueetInitialized) {
        console.log('[WME Koulualueet] Already initialized, skipping...');
        return;
    }
    if (typeof window !== 'undefined') {
        window.wmeKoulualueetInitialized = true;
    }

    // ============================================================
    // CONFIGURATION
    // ============================================================

    const SCRIPT_VERSION = GM_info.script.version;
    const SCRIPT_NAME = GM_info.script.name;

    // Debug mode (set to true to enable diagnostic logging)
    const DEBUG_MODE = false;

    // School data configuration from Statistics Finland INSPIRE OGC API
    const SCHOOL_CONFIG = {
        // INSPIRE OGC API endpoint (replaces the failing WFS endpoint)
        baseUrl: 'https://geo.stat.fi/inspire/ogc/api/us/collections/GovernmentalService_Education_EPSG_3067/items',
        timeout: 15000,      // Reduced back to 15s since new endpoint works reliably
        limit: 3000,         // Reduced from 5000 (covers all ~2400 Finnish schools)
        crs: 'EPSG:3067' // ETRS-TM35FIN
    };

    // Cache configuration
    const CACHE_CONFIG = {
        expiryMs: 24 * 60 * 60 * 1000,  // 24 hours
        version: 2  // Bumped to 2 for INSPIRE OGC API migration (invalidates old WFS cache)
    };

    // Circle loading configuration
    const CIRCLE_LOAD_RADIUS_METERS = 15000; // Load circles within this distance (meters) from map center

    // School type mapping (oltyp code -> name and color)
    const SCHOOL_TYPES = {
        11: { name: 'Peruskoulut', color: '#2196F3' },    // Blue
        12: { name: 'Erityiskoulut', color: '#9C27B0' },  // Purple
        15: { name: 'Lukiot', color: '#4CAF50' },         // Green
        19: { name: 'Yhtenäiskoulut', color: '#FF9800' }, // Orange
        21: { name: 'Ammatilliset', color: '#F44336' },  // Red
        31: { name: 'Ammattikorkeakoulut', color: '#00BCD4' }, // Cyan
        41: { name: 'Yliopistot', color: '#3F51B5' }      // Indigo
    };

    // ============================================================
    // PROJ4 PROJECTION DEFINITIONS
    // ============================================================

    // Define EPSG:3067 (ETRS-TM35FIN) - Finnish coordinate system
    if (typeof proj4 !== 'undefined') {
        proj4.defs('EPSG:3067', '+proj=utm +zone=35 +ellps=GRS80 +towgs84=0,0,0,0,0,0,0 +units=m +no_defs +type=crs');
    }

    // Storage keys for localStorage
    const STORAGE_KEYS = {
        showSchools: 'wme-koulualueet-show',
        schoolTypeFilter: 'wme-koulualueet-filter',
        showLabels: 'wme-koulualueet-show-labels',
        circleRadius: 'wme-koulualueet-circle-radius',
        showCircles: 'wme-koulualueet-show-circles',
        floatingButtonPos: 'wme-koulualueet-button-pos',
        minZoomForCircles: 'wme-koulualueet-min-zoom',
        cacheData: 'wme-koulualueet-cache-data'
    };

    // ============================================================
    // GLOBAL STATE
    // ============================================================

    let schoolsData = [];
    let schoolVectorLayer = null;
    let schoolCircleLayer = null;
    let showSchools = true;
    let schoolTypeFilter = 'all'; // 'all' or specific oltyp code
    let showLabels = true;
    let showCircles = true;
    let circleRadius = 200; // meters
    let minZoomForCircles = 15;

    // Floating UI elements
    let floatingButton = null;
    let floatingPanel = null;

    // Circle refresh debouncing and race condition protection
    let refreshCirclesTimeout = null;
    let isRefreshingCircles = false;
    let pendingCircleRefresh = false;

    // ============================================================
    // UTILITY FUNCTIONS
    // ============================================================

    /**
     * Create HTML element with attributes
     */
    function createElem(tag, attrs) {
        const elem = document.createElement(tag);
        Object.entries(attrs).forEach(([key, value]) => {
            if (key === 'style') {
                elem.setAttribute(key, value);
            } else if (key === 'textContent') {
                elem.textContent = value;
            } else if (key === 'innerHTML') {
                elem.innerHTML = value;
            } else {
                elem.setAttribute(key, value);
            }
        });
        return elem;
    }

    /**
     * Calculate destination point given start point, bearing and distance
     * Uses Haversine formula for geodesic calculation (true ground distance)
     * @param {number} lat - Start latitude in degrees
     * @param {number} lon - Start longitude in degrees
     * @param {number} bearing - Bearing in degrees
     * @param {number} distance - Distance in meters
     * @returns {[number, number]} [longitude, latitude] of destination point
     */
    function calculateDestination(lat, lon, bearing, distance) {
        const R = 6371000; // Earth's radius in meters
        const bearingRad = bearing * Math.PI / 180;
        const lat1 = lat * Math.PI / 180;
        const lon1 = lon * Math.PI / 180;

        const lat2 = Math.asin(
            Math.sin(lat1) * Math.cos(distance / R) +
            Math.cos(lat1) * Math.sin(distance / R) * Math.cos(bearingRad)
        );

        const lon2 = lon1 + Math.atan2(
            Math.sin(bearingRad) * Math.sin(distance / R) * Math.cos(lat1),
            Math.cos(distance / R) - Math.sin(lat1) * Math.sin(lat2)
        );

        return [
            lon2 * 180 / Math.PI,
            lat2 * 180 / Math.PI
        ];
    }

    /**
     * Create a geodesic circle polygon in EPSG:3857
     * Uses true ground distance instead of planar projection units
     * @param {OpenLayers.Geometry.Point} center - Center point in EPSG:3857
     * @param {number} radiusMeters - Radius in meters
     * @param {number} sides - Number of points (default 40)
     * @returns {OpenLayers.Geometry.Polygon} Circle polygon
     */
    function createGeodesicCircle(center, radiusMeters, sides = 40) {
        // Convert center from EPSG:3857 to EPSG:4326
        let lon, lat;
        if (typeof proj4 !== 'undefined') {
            const ll = proj4('EPSG:3857', 'EPSG:4326', [center.x, center.y]);
            lon = ll[0];
            lat = ll[1];
        } else {
            // Fallback: approximate conversion (not accurate, should not happen)
            console.warn('[WME Koulualueet] proj4 not available, using approximate conversion');
            lon = center.x / 111319.49;
            lat = center.y / 111319.49;
        }

        const points = [];
        for (let i = 0; i < sides; i++) {
            const bearing = (i / sides) * 360;
            const dest = calculateDestination(lat, lon, bearing, radiusMeters);

            // Convert destination back to EPSG:3857
            let xy;
            if (typeof proj4 !== 'undefined') {
                xy = proj4('EPSG:4326', 'EPSG:3857', dest);
            } else {
                xy = [
                    dest[0] * 111319.49,
                    dest[1] * 111319.49
                ];
            }

            points.push(new OpenLayers.Geometry.Point(xy[0], xy[1]));
        }

        // Close the ring
        points.push(points[0].clone());

        const ring = new OpenLayers.Geometry.LinearRing(points);
        return new OpenLayers.Geometry.Polygon([ring]);
    }

    /**
     * Debounced save preferences to localStorage
     */
    let saveTimeout;
    function savePreferences() {
        clearTimeout(saveTimeout);
        saveTimeout = setTimeout(() => {
            try {
                localStorage.setItem(STORAGE_KEYS.showSchools, JSON.stringify(showSchools));
                localStorage.setItem(STORAGE_KEYS.schoolTypeFilter, JSON.stringify(schoolTypeFilter));
                localStorage.setItem(STORAGE_KEYS.showLabels, JSON.stringify(showLabels));
                localStorage.setItem(STORAGE_KEYS.showCircles, JSON.stringify(showCircles));
                localStorage.setItem(STORAGE_KEYS.circleRadius, JSON.stringify(circleRadius));
                localStorage.setItem(STORAGE_KEYS.minZoomForCircles, JSON.stringify(minZoomForCircles));

                // Save button position
                if (floatingButton) {
                    const pos = {
                        top: floatingButton.style.top,
                        left: floatingButton.style.left
                    };
                    localStorage.setItem(STORAGE_KEYS.floatingButtonPos, JSON.stringify(pos));
                }
            } catch (error) {
                console.warn('[WME Koulualueet] Failed to save preferences:', error);
            }
        }, 500);
    }

    /**
     * Load preferences from localStorage
     */
    function loadPreferences() {
        try {
            const savedShow = localStorage.getItem(STORAGE_KEYS.showSchools);
            if (savedShow !== null) {
                showSchools = JSON.parse(savedShow);
            }

            const savedFilter = localStorage.getItem(STORAGE_KEYS.schoolTypeFilter);
            if (savedFilter !== null) {
                schoolTypeFilter = JSON.parse(savedFilter);
            }

            const savedShowLabels = localStorage.getItem(STORAGE_KEYS.showLabels);
            if (savedShowLabels !== null) {
                showLabels = JSON.parse(savedShowLabels);
            }

            const savedShowCircles = localStorage.getItem(STORAGE_KEYS.showCircles);
            if (savedShowCircles !== null) {
                showCircles = JSON.parse(savedShowCircles);
            }

            const savedRadius = localStorage.getItem(STORAGE_KEYS.circleRadius);
            if (savedRadius !== null) {
                const parsed = parseInt(JSON.parse(savedRadius), 10);
                if (!isNaN(parsed) && parsed > 0) {
                    circleRadius = parsed;
                }
            }

            const savedMinZoom = localStorage.getItem(STORAGE_KEYS.minZoomForCircles);
            if (savedMinZoom !== null) {
                const parsed = parseInt(JSON.parse(savedMinZoom), 10);
                if (!isNaN(parsed) && parsed >= 0) {
                    minZoomForCircles = parsed;
                }
            }
        } catch (error) {
            console.warn('[WME Koulualueet] Failed to load preferences:', error);
        }
    }

    /**
     * Load saved button position
     */
    function loadButtonPosition() {
        try {
            const savedPos = localStorage.getItem(STORAGE_KEYS.floatingButtonPos);
            if (savedPos && floatingButton) {
                const pos = JSON.parse(savedPos);
                if (pos.top && pos.left) {
                    floatingButton.style.top = pos.top;
                    floatingButton.style.left = pos.left;
                }
            }
        } catch (error) {
            console.warn('[WME Koulualueet] Failed to load button position:', error);
        }
    }

    // ============================================================
    // COORDINATE TRANSFORMATION
    // ============================================================

    /**
     * Convert WGS84 to ETRS-TM35FIN (EPSG:3067)
     */
    function wgs84ToETRSTM35FIN(lat, lon) {
        if (typeof proj4 !== 'undefined') {
            const coords = proj4('EPSG:4326', 'EPSG:3067', [lon, lat]);
            return { x: coords[0], y: coords[1] };
        }
        // Fallback approximation
        return { x: lon * 100000, y: lat * 100000 };
    }

    /**
     * Convert ETRS-TM35FIN (EPSG:3067) to WGS84
     */
    function etrsTm35FinToWgs84(x, y) {
        if (typeof proj4 !== 'undefined') {
            const coords = proj4('EPSG:3067', 'EPSG:4326', [x, y]);
            return { lon: coords[0], lat: coords[1] };
        }
        // Fallback approximation if proj4 not available
        return { lon: x / 10000, lat: y / 10000 };
    }

    /**
     * Calculate distance between two points in EPSG:3067 (meters)
     * @param {number} x1 - First point X coordinate
     * @param {number} y1 - First point Y coordinate
     * @param {number} x2 - Second point X coordinate
     * @param {number} y2 - Second point Y coordinate
     * @returns {number} Distance in meters
     */
    function distanceIn3067(x1, y1, x2, y2) {
        const dx = x2 - x1;
        const dy = y2 - y1;
        return Math.sqrt(dx * dx + dy * dy);
    }

    /**
     * Get current map center in EPSG:3067 coordinates
     * @returns {{x: number, y: number}} Center point in EPSG:3067
     */
    function getMapCenterIn3067() {
        const center = W.map.getCenter();
        if (typeof proj4 !== 'undefined') {
            const coords = proj4('EPSG:3857', 'EPSG:3067', [center.lon, center.lat]);
            return { x: coords[0], y: coords[1] };
        }
        // Fallback (won't be accurate)
        return { x: center.lon, y: center.lat };
    }

    // ============================================================
    // CACHE FUNCTIONS
    // ============================================================

    /**
     * Save schools data to cache
     */
    function saveToCache(schools) {
        try {
            const cacheData = {
                version: CACHE_CONFIG.version,
                timestamp: Date.now(),
                schools: schools
            };
            localStorage.setItem(STORAGE_KEYS.cacheData, JSON.stringify(cacheData));
            console.log('[WME Koulualueet] Cached', schools.length, 'schools');
        } catch (e) {
            console.warn('[WME Koulualueet] Failed to cache data:', e);
        }
    }

    /**
     * Load schools data from cache
     * @returns {Array|null} Cached schools or null if expired/invalid
     */
    function loadFromCache() {
        try {
            const cachedJson = localStorage.getItem(STORAGE_KEYS.cacheData);
            if (!cachedJson) return null;

            const cached = JSON.parse(cachedJson);

            // Check version compatibility
            if (cached.version !== CACHE_CONFIG.version) {
                console.log('[WME Koulualueet] Cache version mismatch, ignoring');
                return null;
            }

            // Check expiry
            const age = Date.now() - cached.timestamp;
            if (age > CACHE_CONFIG.expiryMs) {
                console.log('[WME Koulualueet] Cache expired (', Math.round(age / 3600000), 'h old)');
                return null;
            }

            console.log('[WME Koulualueet] Loaded from cache:', cached.schools.length, 'schools');
            return cached.schools;
        } catch (e) {
            console.warn('[WME Koulualueet] Failed to load from cache:', e);
            return null;
        }
    }

    /**
     * Clear cache (for manual refresh)
     */
    function clearCache() {
        localStorage.removeItem(STORAGE_KEYS.cacheData);
        console.log('[WME Koulualueet] Cache cleared');
    }

    // ============================================================
    // OGC API DATA FETCHING
    // ============================================================

    /**
     * Fetch school data from Statistics Finland INSPIRE OGC API
     * @param {boolean} forceRefresh - Force refresh from API, bypassing cache
     */
    function fetchSchools(forceRefresh = false) {
        return new Promise((resolve, reject) => {
            // Check cache first (unless force refresh)
            if (!forceRefresh) {
                const cached = loadFromCache();
                if (cached) {
                    resolve(cached);
                    return;
                }
            }

            // Build OGC API URL (uses 'f' and 'limit' parameters, not WFS format)
            const params = new URLSearchParams({
                f: 'json',
                limit: SCHOOL_CONFIG.limit.toString()
            });

            const url = `${SCHOOL_CONFIG.baseUrl}?${params.toString()}`;

            console.log('[WME Koulualueet] Fetching schools from:', url);

            if (typeof GM_xmlhttpRequest !== 'undefined') {
                GM_xmlhttpRequest({
                    method: 'GET',
                    url: url,
                    timeout: SCHOOL_CONFIG.timeout,
                    onload: function(response) {
                        if (response.status !== 200) {
                            reject(new Error(`HTTP ${response.status}: ${response.statusText}`));
                            return;
                        }
                        try {
                            const data = JSON.parse(response.responseText);
                            const schools = parseSchoolData(data);

                            // Save to cache on success
                            saveToCache(schools);

                            console.log(`[WME Koulualueet] Loaded ${schools.length} schools from API`);
                            resolve(schools);
                        } catch (e) {
                            reject(new Error('Invalid JSON response'));
                        }
                    },
                    onerror: function() {
                        reject(new Error('Network error'));
                    },
                    ontimeout: function() {
                        reject(new Error('Request timeout'));
                    }
                });
            } else {
                fetch(url)
                    .then(r => {
                        if (!r.ok) throw new Error(`HTTP ${r.status}`);
                        return r.json();
                    })
                    .then(data => {
                        const schools = parseSchoolData(data);
                        saveToCache(schools);
                        resolve(schools);
                    })
                    .catch(reject);
            }
        });
    }

    /**
     * Extract type code from INSPIRE URL
     * URL format: ".../EducationalInstituteType/15"
     * @param {string} typeUrl - The type URL from INSPIRE data
     * @returns {number|null} The type code or null if not found
     */
    function extractTypeCode(typeUrl) {
        if (!typeUrl) return null;
        const match = typeUrl.match(/EducationalInstituteType\/(\d+)$/);
        return match ? parseInt(match[1], 10) : null;
    }

    /**
     * Parse school data from INSPIRE OGC API GeoJSON response
     */
    function parseSchoolData(geoJson) {
        if (!geoJson || !geoJson.features || !Array.isArray(geoJson.features)) {
            return [];
        }

        const schools = [];

        geoJson.features.forEach(feature => {
            const props = feature.properties;
            if (!props) return;

            // INSPIRE data uses URL for status - active schools have status ending with "/0"
            const isActive = props.status?.endsWith('/0');
            if (!isActive) {
                return;
            }

            // Extract type code from URL
            const typeCode = extractTypeCode(props.type);
            if (!typeCode) {
                return;
            }

            // Get coordinates from geometry (EPSG:3067 in INSPIRE data)
            let x, y;
            if (feature.geometry && feature.geometry.coordinates && feature.geometry.coordinates.length >= 2) {
                x = feature.geometry.coordinates[0];
                y = feature.geometry.coordinates[1];
            } else {
                return; // No valid coordinates
            }

            const school = {
                id: props.inspireId_localId || feature.id,
                name: props.name_fi || 'Nimetön koulu',
                typeCode: typeCode,
                typeName: SCHOOL_TYPES[typeCode]?.name || 'Muu',
                x: x,
                y: y
            };

            // Validate coordinates
            if (school.x && school.y) {
                schools.push(school);

                // Diagnostic: track all unique type codes (only in debug mode)
                if (DEBUG_MODE) {
                    if (!window.wmeKouluTypesSeen) {
                        window.wmeKouluTypesSeen = new Set();
                    }
                    window.wmeKouluTypesSeen.add(school.typeCode);
                }
            }
        });

        // Log diagnostic information about school types found (only in debug mode)
        if (DEBUG_MODE && schools.length > 0 && window.wmeKouluTypesSeen) {
            const sortedTypes = Array.from(window.wmeKouluTypesSeen).sort((a, b) => a - b);
            console.log('[WME Koulualueet] Found type codes:', sortedTypes);
            console.log('[WME Koulualueet] School types with names:');
            sortedTypes.forEach(code => {
                const typeName = SCHOOL_TYPES[code]?.name || 'Unknown';
                const count = schools.filter(s => s.typeCode === code).length;
                console.log(`  ${code}: ${typeName} (${count} schools)`);
            });
        }

        return schools;
    }

    // ============================================================
    // VECTOR LAYER CREATION
    // ============================================================

    /**
     * Create style map for school features with labels
     */
    function createSchoolStyleMap() {
        // Build label template based on showLabels setting
        const labelTemplate = showLabels ? '${name}' : '';
        const fontSize = showLabels ? '11px' : '0px';

        return new OpenLayers.StyleMap({
            'default': new OpenLayers.Style({
                fillColor: '${color}',
                fillOpacity: 0.8,
                strokeColor: '#FFFFFF',
                strokeWidth: 2,
                pointRadius: 12,
                label: labelTemplate,
                labelAlign: 'lt',
                labelXOffset: 8,
                labelYOffset: -8,
                fontColor: '#333333',
                fontFamily: 'Arial, sans-serif',
                fontSize: fontSize,
                fontWeight: 'bold',
                labelOutlineColor: 'white',
                labelOutlineWidth: 2
            }),
            'select': new OpenLayers.Style({
                fillColor: '${color}',
                fillOpacity: 1,
                strokeColor: '#FFD700',
                strokeWidth: 3,
                pointRadius: 16,
                label: labelTemplate,
                labelAlign: 'lt',
                labelXOffset: 8,
                labelYOffset: -8,
                fontColor: '#333333',
                fontFamily: 'Arial, sans-serif',
                fontSize: fontSize,
                fontWeight: 'bold',
                labelOutlineColor: 'white',
                labelOutlineWidth: 2
            }),
            'hover': new OpenLayers.Style({
                fillColor: '${color}',
                fillOpacity: 1,
                strokeColor: '#FFD700',
                strokeWidth: 3,
                pointRadius: 16,
                label: labelTemplate,
                labelAlign: 'lt',
                labelXOffset: 8,
                labelYOffset: -8,
                fontColor: '#333333',
                fontFamily: 'Arial, sans-serif',
                fontSize: fontSize,
                fontWeight: 'bold',
                labelOutlineColor: 'white',
                labelOutlineWidth: 2
            })
        });
    }

    /**
     * Create style map for school circles
     */
    function createCircleStyleMap() {
        return new OpenLayers.StyleMap({
            'default': new OpenLayers.Style({
                fillColor: '${color}',
                fillOpacity: 0.15,
                strokeColor: '${color}',
                strokeWidth: 1,
                strokeOpacity: 0.5
            })
        });
    }

    /**
     * Create vector layer for schools
     */
    function createSchoolVectorLayer() {
        // Remove existing layer if any
        if (schoolVectorLayer) {
            try {
                W.map.getOLMap().removeLayer(schoolVectorLayer);
                schoolVectorLayer.destroy();
            } catch (e) {
                // Ignore
            }
        }

        const vectorLayer = new OpenLayers.Layer.Vector(
            'Koulualueet (Schools)',
            {
                displayInLayerSwitcher: false,
                styleMap: createSchoolStyleMap(),
                projection: new OpenLayers.Projection('EPSG:3857')
            }
        );

        // Filter schools by type
        const filteredSchools = schoolTypeFilter === 'all'
            ? schoolsData
            : schoolsData.filter(s => s.typeCode.toString() === schoolTypeFilter.toString());

        console.log(`[WME Koulualueet] Creating layer with ${filteredSchools.length} schools (filter: ${schoolTypeFilter})`);

        const features = [];

        filteredSchools.forEach(school => {
            try {
                // Ensure coordinates are numbers
                const x = parseFloat(school.x);
                const y = parseFloat(school.y);

                if (isNaN(x) || isNaN(y)) {
                    console.warn('[WME Koulualueet] Invalid coordinates for school:', school.name, { x: school.x, y: school.y });
                    return;
                }

                // Transform from EPSG:3067 to EPSG:3857
                let point;
                if (typeof proj4 !== 'undefined') {
                    const t = proj4('EPSG:3067', 'EPSG:3857', [x, y]);
                    point = new OpenLayers.Geometry.Point(t[0], t[1]);
                } else {
                    // Fallback - won't be accurate
                    point = new OpenLayers.Geometry.Point(x, y);
                }

                const typeConfig = SCHOOL_TYPES[school.typeCode] || { color: '#757575' };

                const feature = new OpenLayers.Feature.Vector(point, {
                    name: school.name,
                    type: school.typeName,
                    typeCode: school.typeCode,
                    color: typeConfig.color,
                    schoolId: school.id
                });

                feature.schoolData = school;
                features.push(feature);
            } catch (e) {
                console.warn('[WME Koulualueet] Failed to create point for school:', school.name, e.message, e);
            }
        });

        if (features.length > 0) {
            vectorLayer.addFeatures(features);
        }

        schoolVectorLayer = vectorLayer;

        if (showSchools) {
            W.map.getOLMap().addLayer(vectorLayer);
        }

        return vectorLayer;
    }

    /**
     * Create circle polygons around schools
     */
    function createSchoolCirclesLayer() {
        // Remove existing circle layer if any
        if (schoolCircleLayer) {
            try {
                W.map.getOLMap().removeLayer(schoolCircleLayer);
                schoolCircleLayer.destroy();
            } catch (e) {
                // Ignore
            }
        }

        const circleLayer = new OpenLayers.Layer.Vector(
            'Koulualueet (School Zones)',
            {
                displayInLayerSwitcher: false,
                styleMap: createCircleStyleMap(),
                projection: new OpenLayers.Projection('EPSG:3857')
            }
        );

        // Get map center for distance filtering
        const mapCenter = getMapCenterIn3067();

        // Filter by type AND distance from map center
        let filteredSchools = schoolTypeFilter === 'all'
            ? schoolsData
            : schoolsData.filter(s => s.typeCode.toString() === schoolTypeFilter.toString());

        // Apply distance filter
        filteredSchools = filteredSchools.filter(school => {
            const dist = distanceIn3067(mapCenter.x, mapCenter.y, school.x, school.y);
            return dist <= CIRCLE_LOAD_RADIUS_METERS;
        });

        const loadRadiusKm = (CIRCLE_LOAD_RADIUS_METERS / 1000).toFixed(0);
        console.log(`[WME Koulualueet] Loading ${filteredSchools.length} circles within ${loadRadiusKm}km of center`);

        const features = [];

        filteredSchools.forEach(school => {
            try {
                const x = parseFloat(school.x);
                const y = parseFloat(school.y);

                if (isNaN(x) || isNaN(y)) {
                    return;
                }

                // Transform from EPSG:3067 to EPSG:3857
                let centerPoint;
                if (typeof proj4 !== 'undefined') {
                    const t = proj4('EPSG:3067', 'EPSG:3857', [x, y]);
                    centerPoint = new OpenLayers.Geometry.Point(t[0], t[1]);
                } else {
                    centerPoint = new OpenLayers.Geometry.Point(x, y);
                }

                const typeConfig = SCHOOL_TYPES[school.typeCode] || { color: '#757575' };

                // Create circle polygon using geodesic calculation
                // This ensures the radius represents true ground distance, not planar units
                const radiusInMeters = circleRadius;
                const circlePolygon = createGeodesicCircle(
                    centerPoint,
                    radiusInMeters,
                    40  // Number of points (more = smoother circle)
                );

                const feature = new OpenLayers.Feature.Vector(circlePolygon, {
                    name: school.name,
                    type: school.typeName,
                    typeCode: school.typeCode,
                    color: typeConfig.color,
                    schoolId: school.id
                });

                features.push(feature);
            } catch (e) {
                console.warn('[WME Koulualueet] Failed to create circle for school:', school.name, e.message);
            }
        });

        if (features.length > 0) {
            circleLayer.addFeatures(features);
        }

        schoolCircleLayer = circleLayer;

        // Add layer and set initial visibility based on zoom
        if (showCircles) {
            W.map.getOLMap().addLayer(circleLayer);
            updateCircleVisibility();
        }

        return circleLayer;
    }

    /**
     * Update circle visibility based on zoom level and master switch
     */
    function updateCircleVisibility() {
        if (!schoolCircleLayer) return;

        const currentZoom = W.map.getZoom();
        // Circle layer requires: master switch ON + circles checkbox ON + sufficient zoom
        const shouldShow = showSchools && showCircles && currentZoom >= minZoomForCircles;

        if (shouldShow) {
            schoolCircleLayer.setVisibility(true);
        } else {
            schoolCircleLayer.setVisibility(false);
        }
    }

    /**
     * Recreate circles when radius or filter changes
     * Includes race condition protection to prevent overlapping refreshes
     */
    function refreshCircles() {
        if (isRefreshingCircles) {
            // Already refreshing, mark that another refresh is pending
            pendingCircleRefresh = true;
            return;
        }

        isRefreshingCircles = true;
        pendingCircleRefresh = false;

        console.log('[WME Koulualueet] Refreshing school circles...');

        createSchoolCirclesLayer();

        // Mark refresh as complete and trigger pending refresh if any
        setTimeout(() => {
            isRefreshingCircles = false;
            if (pendingCircleRefresh) {
                refreshCircles();
            }
        }, 100);
    }

    /**
     * Debounced circle refresh for map movement
     */
    function debouncedRefreshCircles() {
        if (refreshCirclesTimeout) {
            clearTimeout(refreshCirclesTimeout);
        }
        refreshCirclesTimeout = setTimeout(() => {
            refreshCirclesTimeout = null;
            refreshCircles();
        }, 300); // 300ms delay to prevent excessive reloads during dragging
    }

    // ============================================================
    // FLOATING UI PANEL
    // ============================================================

    /**
     * Create floating button and panel
     */
    function createFloatingUI() {
        // Create floating button
        floatingButton = createElem('button', {
            id: 'koulu-toggle-btn',
            style: `
                position: fixed;
                top: 64px;
                left: 10px;
                z-index: 10000;
                width: 40px;
                height: 40px;
                padding: 0;
                background: #0052A5;
                color: white;
                border: 2px solid #333;
                border-radius: 6px;
                cursor: grab;
                font-size: 22px;
                box-shadow: 0 3px 8px rgba(0,0,0,0.4);
                transition: all 0.2s;
                display: flex;
                align-items: center;
                justify-content: center;
            `,
            innerHTML: '🏫',
            title: 'Näytä/piilota Koulualueet'
        });

        // Create floating panel
        floatingPanel = createElem('div', {
            id: 'koulu-floating-panel',
            style: `
                position: fixed;
                top: 125px;
                left: 10px;
                background: white;
                border: 2px solid #0052A5;
                border-radius: 8px;
                padding: 12px;
                z-index: 10000;
                box-shadow: 0 4px 12px rgba(0,0,0,0.3);
                max-width: 280px;
                display: none;
                font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
                font-size: 13px;
            `
        });

        setupFloatingButtonEvents();

        document.body.appendChild(floatingButton);
        document.body.appendChild(floatingPanel);

        // Load saved button position
        loadButtonPosition();
    }

    /**
     * Setup floating button events (drag, hover, click)
     */
    function setupFloatingButtonEvents() {
        let isDragging = false;
        let mouseMoveHandler = null;
        let mouseUpHandler = null;

        floatingButton.addEventListener('mouseenter', function () {
            if (!isDragging) {
                this.style.transform = 'scale(1.1)';
                this.style.boxShadow = '0 4px 12px rgba(0,0,0,0.5)';
            }
        });

        floatingButton.addEventListener('mouseleave', function () {
            if (!isDragging) {
                this.style.transform = 'scale(1)';
                this.style.boxShadow = '0 3px 8px rgba(0,0,0,0.4)';
            }
        });

        // Toggle panel visibility
        floatingButton.addEventListener('click', function () {
            if (isDragging) return;

            if (floatingPanel.style.display === 'none' || floatingPanel.style.display === '') {
                // Position panel relative to button
                const buttonTop = parseInt(floatingButton.style.top) || 64;
                floatingPanel.style.left = floatingButton.style.left;
                floatingPanel.style.top = (buttonTop + 45) + 'px';
                floatingPanel.style.display = 'block';
                this.style.borderColor = '#0052A5';
                this.style.borderWidth = '3px';
            } else {
                floatingPanel.style.display = 'none';
                this.style.borderColor = '#333';
                this.style.borderWidth = '2px';
            }
        });

        // Drag functionality
        floatingButton.addEventListener('mousedown', function (e) {
            e.preventDefault();
            isDragging = false;

            const shiftX = e.clientX - floatingButton.getBoundingClientRect().left;
            const shiftY = e.clientY - floatingButton.getBoundingClientRect().top;

            function moveAt(pageX, pageY) {
                isDragging = true;
                floatingButton.style.left = (pageX - shiftX) + 'px';
                floatingButton.style.top = (pageY - shiftY) + 'px';
                // Panel follows if visible
                if (floatingPanel.style.display === 'block') {
                    floatingPanel.style.left = floatingButton.style.left;
                    const buttonTop = parseInt(floatingButton.style.top) || 64;
                    floatingPanel.style.top = (buttonTop + 45) + 'px';
                }
            }

            mouseMoveHandler = function (e) {
                moveAt(e.pageX, e.pageY);
            };

            mouseUpHandler = function () {
                document.removeEventListener('mousemove', mouseMoveHandler);
                document.removeEventListener('mouseup', mouseUpHandler);
                mouseMoveHandler = null;
                mouseUpHandler = null;

                // Save button position after dragging
                if (isDragging) {
                    savePreferences();
                    setTimeout(() => isDragging = false, 100);
                }
            };

            document.addEventListener('mousemove', mouseMoveHandler);
            document.addEventListener('mouseup', mouseUpHandler);
        });

        floatingButton.addEventListener('dragstart', () => false);
    }

    /**
     * Update floating panel content
     */
    function updateFloatingPanelContent() {
        if (!floatingPanel) return;

        floatingPanel.innerHTML = '';

        // Header
        const header = createElem('div', {
            style: 'font-weight: bold; margin-bottom: 8px; font-size: 14px; color: #0052A5; border-bottom: 1px solid #0052A5; padding-bottom: 4px; display: flex; align-items: center; justify-content: space-between;',
            innerHTML: '<span>🏫 Koulualueet</span><span style="font-size: 10px; color: #999;">v' + SCRIPT_VERSION + '</span>'
        });
        floatingPanel.appendChild(header);

        // Refresh button
        const refreshButton = createElem('button', {
            id: 'wme-koulu-refresh',
            style: 'width: 100%; padding: 6px; background: #0052A5; color: white; border: none; border-radius: 4px; cursor: pointer; font-size: 12px; margin-bottom: 10px;',
            textContent: 'Päivitä koulutiedot'
        });
        refreshButton.addEventListener('click', function() {
            this.disabled = true;
            this.textContent = 'Ladataan...';
            fetchSchools(true)  // Force refresh
                .then(schools => {
                    schoolsData = schools;
                    refreshSchoolLayer();
                    refreshCircles();
                    updateFloatingPanelContent();
                })
                .catch(error => {
                    console.error('[WME Koulualueet] Refresh failed:', error);
                    this.disabled = false;
                    this.textContent = 'Päivitys epäonnistui - yritä uudelleen';
                    setTimeout(() => {
                        this.disabled = false;
                        this.textContent = 'Päivitä koulutiedot';
                    }, 1000);
                });
        });
        floatingPanel.appendChild(refreshButton);

        // Show/hide checkbox
        const showContainer = createElem('div', { style: 'margin-bottom: 10px;' });
        const showCheckbox = createElem('input', {
            type: 'checkbox',
            id: 'wme-koulu-show',
            checked: showSchools,
            style: 'margin-right: 6px; accent-color: #2E7D32; width: 18px; height: 18px;'  // Green, larger
        });
        showCheckbox.addEventListener('change', (e) => {
            const newShowSchools = e.target.checked;

            showSchools = newShowSchools;
            savePreferences();
            refreshSchoolLayer();

            // Update dependent checkbox visual state and enabled state
            const labelsCheckbox = document.getElementById('wme-koulu-labels');
            const circlesCheckbox = document.getElementById('wme-koulu-circles');

            if (labelsCheckbox && circlesCheckbox) {
                if (showSchools) {
                    // Enable and restore internal state
                    labelsCheckbox.disabled = false;
                    labelsCheckbox.checked = showLabels;
                    circlesCheckbox.disabled = false;
                    circlesCheckbox.checked = showCircles;
                } else {
                    // Disable and visually uncheck (but keep internal state)
                    labelsCheckbox.disabled = true;
                    labelsCheckbox.checked = false;
                    circlesCheckbox.disabled = true;
                    circlesCheckbox.checked = false;
                }
            }

            // Update circle visibility based on zoom and state
            updateCircleVisibility();
        });

        const showLabel = createElem('label', {
            htmlFor: 'wme-koulu-show',
            style: 'cursor: pointer; font-size: 13px; font-weight: 600; color: #2E7D32;'  // Bold, larger, green
        });
        showLabel.textContent = 'Näytä koulut kartalla';

        showContainer.appendChild(showCheckbox);
        showContainer.appendChild(showLabel);
        floatingPanel.appendChild(showContainer);

        // Labels checkbox
        const labelsContainer = createElem('div', { style: 'margin-bottom: 10px;' });
        const labelsCheckbox = createElem('input', {
            type: 'checkbox',
            id: 'wme-koulu-labels',
            checked: showLabels,
            style: 'margin-right: 6px; accent-color: #0052A5; width: 16px; height: 16px;'
        });
        labelsCheckbox.addEventListener('change', (e) => {
            if (e.target.disabled) {
                e.preventDefault();
                return;
            }
            showLabels = e.target.checked;
            savePreferences();
            refreshSchoolLayer();
        });

        const labelsLabel = createElem('label', {
            htmlFor: 'wme-koulu-labels',
            style: 'cursor: pointer; font-size: 12px;'
        });
        labelsLabel.textContent = 'Näytä koulujen nimet';

        labelsContainer.appendChild(labelsCheckbox);
        labelsContainer.appendChild(labelsLabel);
        floatingPanel.appendChild(labelsContainer);

        // School type filter
        const filterContainer = createElem('div', { style: 'margin-bottom: 10px;' });
        const filterLabel = createElem('label', {
            style: 'font-size: 11px; color: #666; margin-bottom: 4px; display: block;',
            textContent: 'Koulutyyppi:'
        });
        filterContainer.appendChild(filterLabel);

        const typeFilter = createElem('select', {
            style: 'width: 100%; padding: 6px 8px; border: 1px solid #ddd; border-radius: 4px; font-size: 12px; background: white;'
        });

        // Add "All" option
        const allOption = createElem('option', {
            value: 'all',
            textContent: 'Kaikki koulut'
        });
        typeFilter.appendChild(allOption);

        // Add school type options
        Object.entries(SCHOOL_TYPES).forEach(([code, config]) => {
            const option = createElem('option', {
                value: code,
                textContent: config.name
            });
            typeFilter.appendChild(option);
        });

        typeFilter.value = schoolTypeFilter;
        typeFilter.addEventListener('change', (e) => {
            schoolTypeFilter = e.target.value;
            savePreferences();
            refreshSchoolLayer();
            refreshCircles();

            // Update the count display directly without rebuilding entire UI
            const filteredCount = schoolTypeFilter === 'all'
                ? schoolsData.length
                : schoolsData.filter(s => s.typeCode.toString() === schoolTypeFilter.toString()).length;

            const countDiv = document.getElementById('wme-koulu-count');
            if (countDiv) {
                countDiv.textContent = `${filteredCount} koulua näkyvissä`;
            }
        });

        filterContainer.appendChild(typeFilter);
        floatingPanel.appendChild(filterContainer);

        // School count
        const filteredCount = schoolTypeFilter === 'all'
            ? schoolsData.length
            : schoolsData.filter(s => s.typeCode.toString() === schoolTypeFilter.toString()).length;

        const countDiv = createElem('div', {
            id: 'wme-koulu-count',  // Add ID for direct DOM access
            style: 'padding: 8px; background: #f5f5f5; border-radius: 4px; margin-bottom: 10px; text-align: center; font-size: 12px; color: #666;',
            textContent: `${filteredCount} koulua näkyvissä`
        });
        floatingPanel.appendChild(countDiv);

        // Circles section
        const circlesSection = createElem('div', {
            style: 'margin-bottom: 10px; padding: 8px; background: #f9f9f9; border-radius: 4px; border: 1px solid #e0e0e0;'
        });

        const circlesHeader = createElem('div', {
            style: 'font-weight: 500; font-size: 12px; margin-bottom: 8px; color: #0052A5;',
            textContent: 'Koulualueet ympyrät'
        });
        circlesSection.appendChild(circlesHeader);

        // Show circles checkbox
        const circlesShowContainer = createElem('div', { style: 'margin-bottom: 8px;' });
        const circlesShowCheckbox = createElem('input', {
            type: 'checkbox',
            id: 'wme-koulu-circles',
            checked: showCircles,
            style: 'margin-right: 6px; accent-color: #0052A5; width: 16px; height: 16px;'
        });
        circlesShowCheckbox.addEventListener('change', (e) => {
            if (e.target.disabled) {
                e.preventDefault();
                return;
            }
            showCircles = e.target.checked;
            savePreferences();
            if (showCircles) {
                if (!schoolCircleLayer) {
                    refreshCircles();
                }
                updateCircleVisibility();
            } else {
                if (schoolCircleLayer) {
                    schoolCircleLayer.setVisibility(false);
                }
            }
        });

        const circlesShowLabel = createElem('label', {
            htmlFor: 'wme-koulu-circles',
            style: 'cursor: pointer; font-size: 12px;'
        });
        circlesShowLabel.textContent = 'Näytä ympyrät';

        circlesShowContainer.appendChild(circlesShowCheckbox);
        circlesShowContainer.appendChild(circlesShowLabel);
        circlesSection.appendChild(circlesShowContainer);

        // Circle radius input
        const radiusContainer = createElem('div', { style: 'margin-bottom: 6px;' });
        const radiusLabel = createElem('label', {
            style: 'font-size: 11px; color: #666; margin-right: 8px;',
            textContent: 'Säde (m):'
        });
        const radiusInput = createElem('input', {
            type: 'number',
            id: 'wme-koulu-radius',
            value: circleRadius.toString(),
            min: '50',
            max: '2000',
            step: '50',
            style: 'width: 70px; padding: 4px 6px; border: 1px solid #ddd; border-radius: 4px; font-size: 12px;'
        });
        radiusInput.addEventListener('change', (e) => {
            const value = parseInt(e.target.value, 10);
            if (!isNaN(value) && value >= 50 && value <= 2000) {
                circleRadius = value;
                savePreferences();
                refreshCircles();
            }
        });
        radiusContainer.appendChild(radiusLabel);
        radiusContainer.appendChild(radiusInput);
        circlesSection.appendChild(radiusContainer);

        // Min zoom input
        const zoomContainer = createElem('div', {});
        const zoomLabel = createElem('label', {
            style: 'font-size: 11px; color: #666; margin-right: 8px;',
            textContent: 'Zoom-taso:'
        });
        const zoomInput = createElem('input', {
            type: 'number',
            id: 'wme-koulu-zoom',
            value: minZoomForCircles.toString(),
            min: '0',
            max: '22',
            step: '1',
            style: 'width: 70px; padding: 4px 6px; border: 1px solid #ddd; border-radius: 4px; font-size: 12px;'
        });
        zoomInput.addEventListener('change', (e) => {
            const value = parseInt(e.target.value, 10);
            if (!isNaN(value) && value >= 0 && value <= 22) {
                minZoomForCircles = value;
                savePreferences();
                updateCircleVisibility();
            }
        });
        zoomContainer.appendChild(zoomLabel);
        zoomContainer.appendChild(zoomInput);
        circlesSection.appendChild(zoomContainer);

        floatingPanel.appendChild(circlesSection);

        // School count by type
        const byTypeContainer = createElem('div', { style: 'margin-bottom: 10px;' });
        const byTypeLabel = createElem('div', {
            style: 'font-size: 11px; color: #666; margin-bottom: 6px; font-weight: 500;',
            textContent: 'Koulujen määrä tyypeittäin:'
        });
        byTypeContainer.appendChild(byTypeLabel);

        const typeCounts = {};
        schoolsData.forEach(school => {
            const typeCode = school.typeCode.toString();
            typeCounts[typeCode] = (typeCounts[typeCode] || 0) + 1;
        });

        Object.entries(SCHOOL_TYPES).forEach(([code, config]) => {
            const count = typeCounts[code] || 0;
            if (count > 0) {
                const typeRow = createElem('div', {
                    style: 'display: flex; align-items: center; padding: 3px 0; font-size: 11px;'
                });

                const colorDot = createElem('span', {
                    style: `display: inline-block; width: 10px; height: 10px; border-radius: 50%; background: ${config.color}; margin-right: 8px;`
                });

                const label = createElem('span', {
                    style: 'flex: 1;'
                });
                label.textContent = config.name;

                const countLabel = createElem('span', {
                    style: 'color: #666; font-weight: 500;'
                });
                countLabel.textContent = count;

                typeRow.appendChild(colorDot);
                typeRow.appendChild(label);
                typeRow.appendChild(countLabel);
                byTypeContainer.appendChild(typeRow);
            }
        });

        floatingPanel.appendChild(byTypeContainer);

        // Data source info
        const sourceDiv = createElem('div', {
            style: 'margin-top: 10px; padding-top: 8px; border-top: 1px solid #eee; font-size: 10px; color: #999; line-height: 1.4;',
            innerHTML: 'Tietolähde: Tilastokeskus INSPIRE<br>© Statistics Finland'
        });
        floatingPanel.appendChild(sourceDiv);

        // Set initial state of dependent checkboxes based on showSchools
        const labelsCheckboxEl = document.getElementById('wme-koulu-labels');
        const circlesCheckboxEl = document.getElementById('wme-koulu-circles');

        if (labelsCheckboxEl && circlesCheckboxEl) {
            if (showSchools) {
                // Enable and use internal state
                labelsCheckboxEl.disabled = false;
                labelsCheckboxEl.checked = showLabels;
                circlesCheckboxEl.disabled = false;
                circlesCheckboxEl.checked = showCircles;
            } else {
                // Disable and visually uncheck (internal state is preserved)
                labelsCheckboxEl.disabled = true;
                labelsCheckboxEl.checked = false;
                circlesCheckboxEl.disabled = true;
                circlesCheckboxEl.checked = false;
            }
        }
    }

    /**
     * Refresh school layer with current filter settings
     */
    function refreshSchoolLayer() {
        console.log('[WME Koulualueet] Refreshing school layer...');

        if (schoolVectorLayer) {
            try {
                W.map.getOLMap().removeLayer(schoolVectorLayer);
                schoolVectorLayer.destroy();
            } catch (e) {
                // Ignore
            }
            schoolVectorLayer = null;
        }

        if (showSchools && schoolsData.length > 0) {
            createSchoolVectorLayer();
        }
    }

    // ============================================================
    // INITIALIZATION
    // ============================================================

    /**
     * Poll for WazeWrap.Ready
     */
    function waitForWazeWrap(retryCount) {
        const MAX_RETRIES = 40;

        if (typeof WazeWrap !== 'undefined' && WazeWrap.Ready) {
            // Initialize script
            initializeScript();
        } else if (retryCount < MAX_RETRIES) {
            retryCount++;
            setTimeout(() => waitForWazeWrap(retryCount), 250);
        } else {
            // WazeWrap failed to load, try to initialize anyway
            initializeScript();
        }
    }

    /**
     * Initialize the script
     */
    function initializeScript() {
        console.log('[WME Koulualueet] Initializing...');

        // Load saved preferences
        loadPreferences();

        // Create floating UI
        createFloatingUI();

        // Fetch school data
        fetchSchools()
            .then(schools => {
                schoolsData = schools;

                // Create vector layer
                if (showSchools) {
                    createSchoolVectorLayer();
                }

                // Create circles layer
                if (showCircles) {
                    createSchoolCirclesLayer();
                }

                // Update floating panel content
                updateFloatingPanelContent();

                console.log(`[WME Koulualueet] Initialized with ${schools.length} schools`);
            })
            .catch(error => {
                console.error('[WME Koulualueet] Failed to fetch schools:', error);
                // Still show panel with error state
                updateFloatingPanelContent();
            });

        // Setup zoom event listener for circle visibility
        W.map.getOLMap().events.register('zoomend', null, function() {
            updateCircleVisibility();
        });

        // Reload circles when map moves (pan/zoom) - with debouncing
        W.map.getOLMap().events.register('moveend', null, function() {
            if (showSchools && showCircles) {
                debouncedRefreshCircles();
            }
        });
    }

    // ============================================================
    // STARTUP
    // ============================================================

    // Start initialization
    waitForWazeWrap(0);

})();
