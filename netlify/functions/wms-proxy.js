exports.handler = async function(event) {
  const params = event.queryStringParameters || {};
  const service = params.service || 'ekon';
  const w = params.w || '512';
  const h = params.h || '512';
  
  // bbox arrives as minLon,minLat,maxLon,maxLat (from our JS)
  const bboxRaw = params.bbox || '';
  const [minLon, minLat, maxLon, maxLat] = bboxRaw.split(',').map(Number);
  
  // WMS 1.3.0 + EPSG:4326 needs minLat,minLon,maxLat,maxLon (axis order flipped)
  const bbox130 = `${minLat},${minLon},${maxLat},${maxLon}`;
  // WMS 1.1.1 + EPSG:4326 uses normal lon,lat order
  const bbox111 = bboxRaw;

  const LM_KEY = process.env.LM_API_KEY || '';

  let url;

  if (service === 'ekon') {
    // Länsstyrelsen ArcGIS WMS — get capabilities first to confirm layer name
    // Layer name varies — try 'lst_ext_ekonomiska_kartan' or just default layer
    url = `https://ext-geodata-raster.lansstyrelsen.se/arcgis/services/RasterNationellt/lst_ext_ekonomiska_kartan/ImageServer/WMSServer?SERVICE=WMS&REQUEST=GetMap&VERSION=1.3.0&LAYERS=lst_ext_ekonomiska_kartan&STYLES=&CRS=EPSG:4326&FORMAT=image/png&TRANSPARENT=FALSE&WIDTH=${w}&HEIGHT=${h}&BBOX=${bbox130}`;
  } else if (service === 'ekon_cap') {
    // GetCapabilities to discover correct layer name
    url = `https://ext-geodata-raster.lansstyrelsen.se/arcgis/services/RasterNationellt/lst_ext_ekonomiska_kartan/ImageServer/WMSServer?SERVICE=WMS&REQUEST=GetCapabilities&VERSION=1.3.0`;
  } else if (service === 'ortho60') {
    if (!LM_KEY) return { statusCode: 403, body: 'LM_API_KEY not set' };
    url = `https://api.lantmateriet.se/historiska-ortofoton/wms/v1/token/${LM_KEY}/?SERVICE=WMS&REQUEST=GetMap&VERSION=1.1.1&LAYERS=OI.Histortho_60&STYLES=&SRS=EPSG:4326&FORMAT=image/jpeg&WIDTH=${w}&HEIGHT=${h}&BBOX=${bbox111}`;
  } else if (service === 'ortho75') {
    if (!LM_KEY) return { statusCode: 403, body: 'LM_API_KEY not set' };
    url = `https://api.lantmateriet.se/historiska-ortofoton/wms/v1/token/${LM_KEY}/?SERVICE=WMS&REQUEST=GetMap&VERSION=1.1.1&LAYERS=OI.Histortho_75&STYLES=&SRS=EPSG:4326&FORMAT=image/jpeg&WIDTH=${w}&HEIGHT=${h}&BBOX=${bbox111}`;
  } else {
    return { statusCode: 400, body: 'Unknown service' };
  }

  try {
    const response = await fetch(url);
    const ct = response.headers.get('content-type') || '';
    
    // If XML error or capabilities, return as text
    if (ct.includes('xml') || !response.ok) {
      const text = await response.text();
      return {
        statusCode: response.ok ? 200 : 500,
        headers: { 'Content-Type': 'text/plain', 'Access-Control-Allow-Origin': '*' },
        body: `Status: ${response.status}\nURL: ${url}\n\n${text.substring(0, 2000)}`,
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
