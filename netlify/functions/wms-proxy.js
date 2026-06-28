exports.handler = async function(event) {
  const params = event.queryStringParameters || {};
  const service = params.service || 'ekon';
  const w = Math.min(parseInt(params.w) || 512, 1024);
  const h = Math.min(parseInt(params.h) || 512, 1024);

  const bboxRaw = params.bbox || '';
  const parts = bboxRaw.split(',').map(Number);
  const [minLon, minLat, maxLon, maxLat] = parts;
  const bbox130 = `${minLat},${minLon},${maxLat},${maxLon}`;

  const LM_USER = process.env.LM_USER || '';
  const LM_PASS = process.env.LM_PASS || '';
  const LM_KEY  = process.env.LM_API_KEY || '';
  const BASE_EKON = 'https://ext-geodata-raster.lansstyrelsen.se/arcgis/services/RasterNationellt/lst_ext_ekonomiska_kartan/ImageServer/WMSServer';
  const BASE_HIST = 'https://maps.lantmateriet.se/historiska-ortofoton/wms/v1';

  let url, authHeader = null;

  if (service === 'ekon_cap') {
    url = `${BASE_EKON}?SERVICE=WMS&REQUEST=GetCapabilities&VERSION=1.3.0`;
  } else if (service === 'ekon') {
    url = `${BASE_EKON}?SERVICE=WMS&REQUEST=GetMap&VERSION=1.3.0&LAYERS=lst_ext_ekonomiska_kartan&STYLES=&CRS=EPSG:4326&FORMAT=image/png&TRANSPARENT=FALSE&WIDTH=${w}&HEIGHT=${h}&BBOX=${bbox130}`;
  } else if (service === 'ortho60') {
    // Use Basic Auth with LM credentials
    if (!LM_USER || !LM_PASS) return { statusCode: 403, body: 'LM_USER/LM_PASS not set in Netlify env' };
    url = `${BASE_HIST}?SERVICE=WMS&REQUEST=GetMap&VERSION=1.1.1&LAYERS=OI.Histortho_60&STYLES=&SRS=EPSG:4326&FORMAT=image/jpeg&WIDTH=${w}&HEIGHT=${h}&BBOX=${bboxRaw}`;
    authHeader = 'Basic ' + Buffer.from(LM_USER + ':' + LM_PASS).toString('base64');
  } else if (service === 'hist_cap') {
    if (!LM_USER || !LM_PASS) return { statusCode: 403, body: 'LM_USER/LM_PASS not set' };
    url = `${BASE_HIST}?SERVICE=WMS&REQUEST=GetCapabilities&VERSION=1.1.1`;
    authHeader = 'Basic ' + Buffer.from(LM_USER + ':' + LM_PASS).toString('base64');
  } else {
    return { statusCode: 400, body: 'Unknown service: ' + service };
  }

  try {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 20000);
    const fetchOpts = { signal: controller.signal };
    if (authHeader) fetchOpts.headers = { 'Authorization': authHeader };
    const response = await fetch(url, fetchOpts);
    clearTimeout(timeout);

    const ct = response.headers.get('content-type') || '';

    if (ct.includes('xml') || service.includes('cap')) {
      const text = await response.text();
      const layers = [];
      const re = /<Layer[^>]*>\s*<Name>([^<]+)<\/Name>/g;
      let m;
      while ((m = re.exec(text)) !== null) layers.push(m[1]);
      return {
        statusCode: 200,
        headers: { 'Content-Type': 'text/plain', 'Access-Control-Allow-Origin': '*' },
        body: `Status: ${response.status}\nURL: ${url}\n` + (layers.length ? 'Layers:\n' + layers.join('\n') + '\n\n' : '') + text.substring(0, 2000),
      };
    }

    if (!response.ok) {
      const text = await response.text();
      return {
        statusCode: 500,
        headers: { 'Content-Type': 'text/plain', 'Access-Control-Allow-Origin': '*' },
        body: `WMS ${response.status}\nURL: ${url}\n\n${text.substring(0, 500)}`,
      };
    }

    const buffer = await response.arrayBuffer();
    const base64 = Buffer.from(buffer).toString('base64');
    return {
      statusCode: 200,
      headers: {
        'Content-Type': ct,
        'Cache-Control': 'public, max-age=86400',
        'Access-Control-Allow-Origin': '*',
      },
      body: base64,
      isBase64Encoded: true,
    };
  } catch (e) {
    return {
      statusCode: 500,
      headers: { 'Content-Type': 'text/plain', 'Access-Control-Allow-Origin': '*' },
      body: 'Proxy error: ' + e.message,
    };
  }
};
