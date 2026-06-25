exports.handler = async function(event) {
  const params = event.queryStringParameters || {};
  const service = params.service || 'ekon';
  
  const LM_KEY = process.env.LM_API_KEY || '';
  
  let url;
  const bbox  = params.bbox  || '';
  const w     = params.w     || '512';
  const h     = params.h     || '512';
  
  if (service === 'ekon') {
    url = `https://ext-geodata-raster.lansstyrelsen.se/arcgis/services/RasterNationellt/lst_ext_ekonomiska_kartan/ImageServer/WMSServer?SERVICE=WMS&REQUEST=GetMap&VERSION=1.3.0&LAYERS=0&STYLES=&CRS=EPSG:4326&FORMAT=image/png&TRANSPARENT=FALSE&WIDTH=${w}&HEIGHT=${h}&BBOX=${bbox}`;
  } else if (service === 'ortho60') {
    if (!LM_KEY) return { statusCode: 403, body: 'LM_API_KEY not set' };
    url = `https://api.lantmateriet.se/historiska-ortofoton/wms/v1/token/${LM_KEY}/?SERVICE=WMS&REQUEST=GetMap&VERSION=1.1.1&LAYERS=OI.Histortho_60&STYLES=&SRS=EPSG:4326&FORMAT=image/jpeg&WIDTH=${w}&HEIGHT=${h}&BBOX=${bbox}`;
  } else if (service === 'ortho75') {
    if (!LM_KEY) return { statusCode: 403, body: 'LM_API_KEY not set' };
    url = `https://api.lantmateriet.se/historiska-ortofoton/wms/v1/token/${LM_KEY}/?SERVICE=WMS&REQUEST=GetMap&VERSION=1.1.1&LAYERS=OI.Histortho_75&STYLES=&SRS=EPSG:4326&FORMAT=image/jpeg&WIDTH=${w}&HEIGHT=${h}&BBOX=${bbox}`;
  } else {
    return { statusCode: 400, body: 'Unknown service' };
  }

  try {
    const response = await fetch(url);
    if (!response.ok) return { statusCode: response.status, body: `WMS error: ${response.status}` };
    const buffer = await response.arrayBuffer();
    const base64 = Buffer.from(buffer).toString('base64');
    const ct = response.headers.get('content-type') || 'image/png';
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
    return { statusCode: 500, body: 'Proxy error: ' + e.message };
  }
};
