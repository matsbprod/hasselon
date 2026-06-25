exports.handler = async function(event) {
  const params = event.queryStringParameters || {};
  const service = params.service || 'ekon';
  const w = params.w || '512';
  const h = params.h || '512';

  const bboxRaw = params.bbox || '';
  const parts = bboxRaw.split(',').map(Number);
  const [minLon, minLat, maxLon, maxLat] = parts;
  // WMS 1.3.0 + EPSG:4326: axis order is lat,lon
  const bbox130 = `${minLat},${minLon},${maxLat},${maxLon}`;

  const LM_KEY = process.env.LM_API_KEY || '';
  const BASE = 'https://ext-geodata-raster.lansstyrelsen.se/arcgis/services/RasterNationellt/lst_ext_ekonomiska_kartan/ImageServer/WMSServer';

  let url;
  if (service === 'ekon_cap') {
    url = `${BASE}?SERVICE=WMS&REQUEST=GetCapabilities&VERSION=1.3.0`;
  } else if (service === 'ekon') {
    // Try layer name = service name (ArcGIS ImageServer convention)
    const layer = params.layer || 'lst_ext_ekonomiska_kartan';
    url = `${BASE}?SERVICE=WMS&REQUEST=GetMap&VERSION=1.3.0&LAYERS=${layer}&STYLES=&CRS=EPSG:4326&FORMAT=image/png&TRANSPARENT=FALSE&WIDTH=${w}&HEIGHT=${h}&BBOX=${bbox130}`;
  } else if (service === 'ortho60') {
    if (!LM_KEY) return { statusCode: 403, body: 'LM_API_KEY not set' };
    url = `https://api.lantmateriet.se/historiska-ortofoton/wms/v1/token/${LM_KEY}/?SERVICE=WMS&REQUEST=GetMap&VERSION=1.1.1&LAYERS=OI.Histortho_60&STYLES=&SRS=EPSG:4326&FORMAT=image/jpeg&WIDTH=${w}&HEIGHT=${h}&BBOX=${bboxRaw}`;
  } else if (service === 'ortho75') {
    if (!LM_KEY) return { statusCode: 403, body: 'LM_API_KEY not set' };
    url = `https://api.lantmateriet.se/historiska-ortofoton/wms/v1/token/${LM_KEY}/?SERVICE=WMS&REQUEST=GetMap&VERSION=1.1.1&LAYERS=OI.Histortho_75&STYLES=&SRS=EPSG:4326&FORMAT=image/jpeg&WIDTH=${w}&HEIGHT=${h}&BBOX=${bboxRaw}`;
  } else {
    return { statusCode: 400, body: 'Unknown service' };
  }

  try {
    const response = await fetch(url);
    const ct = response.headers.get('content-type') || '';

    if (ct.includes('xml') || service.includes('cap')) {
      const text = await response.text();
      // Extract just Layer names from capabilities
      const layers = [];
      const re = /<Layer[^>]*>\s*<Name>([^<]+)<\/Name>/g;
      let m;
      while ((m = re.exec(text)) !== null) layers.push(m[1]);
      const summary = layers.length
        ? 'Layer names found:\n' + layers.join('\n') + '\n\n---\n' + text.substring(0, 3000)
        : text.substring(0, 4000);
      return {
        statusCode: 200,
        headers: { 'Content-Type': 'text/plain', 'Access-Control-Allow-Origin': '*' },
        body: `Status: ${response.status}\nURL: ${url}\n\n${summary}`,
      };
    }

    if (!response.ok) {
      const text = await response.text();
      return {
        statusCode: 500,
        headers: { 'Content-Type': 'text/plain', 'Access-Control-Allow-Origin': '*' },
        body: `WMS error ${response.status}\nURL: ${url}\n\n${text.substring(0, 1000)}`,
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
      body: 'Proxy error: ' + e.message + '\nURL: ' + url,
    };
  }
};
