const { useState, useRef, useEffect, useCallback, useMemo } = React;
// THREE from CDN

/* ═══ GEDCOM PARSER ═══════════════════════════════════════════ */
function cleanText(s){if(!s)return"";return s.replace(/\r/g,"").replace(/\xe8O/g,"Ö").replace(/\xe8o/g,"ö").replace(/\xe8A/g,"Ä").replace(/\xe8a/g,"ä").replace(/\xea/g,"å").replace(/\xeaA/g,"Å").replace(/\xe8U/g,"Ü").replace(/\xe8u/g,"ü").trim();}
function parseNameLine(v){var val=cleanText(v),g="",s="";var m=val.match(/\/([^/]*)\//);if(m){s=m[1].trim();g=val.replace(/\/[^/]*\//,"").trim();}else g=val.replace(/\//g,"").trim();return{given:g.replace(/\*/g,"").trim(),surname:s};}
function parseGedcom(text){var individuals={},families={},ent=null,sub=null,lines=text.split(/\r?\n/);for(var i=0;i<lines.length;i++){var line=lines[i].replace(/\r$/,"");var m=line.match(/^(\d+)\s+(@[^@]+@)?\s*(\w+)\s*(.*)?$/);if(!m)continue;var lv=parseInt(m[1]),id=m[2],tag=m[3],v=(m[4]||"").replace(/\r/g,"").trim();if(lv===0){sub=null;if(tag==="INDI"&&id){ent={type:"INDI",id:id,givenName:"",surname:"",rawName:"",sex:"",birthDate:"",birthPlace:"",deathDate:"",deathPlace:"",occupation:"",events:[],familySpouse:[],familyChild:[]};individuals[id]=ent;}else if(tag==="FAM"&&id){ent={type:"FAM",id:id,husband:null,wife:null,children:[]};families[id]=ent;}else ent=null;}else if(lv===1&&ent){sub=tag;if(ent.type==="INDI"){if(tag==="NAME"){var p=parseNameLine(v);if(!ent.rawName){ent.rawName=v;if(p.given)ent.givenName=p.given;if(p.surname)ent.surname=p.surname;}}if(tag==="SEX")ent.sex=v;if(tag==="FAMS")ent.familySpouse.push(v);if(tag==="FAMC")ent.familyChild.push(v);if(tag==="OCCU"&&v)ent.occupation=cleanText(v);if(tag==="RESI"||tag==="BIRT"||tag==="DEAT"||tag==="EMIG"||tag==="IMMI"||tag==="CHR"){if(!ent._curEvent)ent._curEvent={type:tag,date:"",place:""};ent._curEvent.type=tag;ent._curEvent.date="";ent._curEvent.place="";}}if(ent.type==="FAM"){if(tag==="HUSB")ent.husband=v;if(tag==="WIFE")ent.wife=v;if(tag==="CHIL")ent.children.push(v);}}else if(lv===2&&ent&&ent.type==="INDI"){if(sub==="NAME"&&tag==="GIVN"&&v)ent.givenName=cleanText(v);if(sub==="NAME"&&tag==="SURN"&&v)ent.surname=cleanText(v);if(sub==="BIRT"&&tag==="DATE")ent.birthDate=cleanText(v);if(sub==="BIRT"&&tag==="PLAC")ent.birthPlace=cleanText(v);if(sub==="DEAT"&&tag==="DATE")ent.deathDate=cleanText(v);if(sub==="DEAT"&&tag==="PLAC")ent.deathPlace=cleanText(v);if(sub==="OCCU"&&tag==="DATE")ent.occupation=ent.occupation||"";if(tag==="DATE"&&(sub==="RESI"||sub==="EMIG"||sub==="IMMI"||sub==="CHR")){if(!ent.events)ent.events=[];if(!ent._curEvent)ent._curEvent={type:sub,date:"",place:""};ent._curEvent.date=cleanText(v);}if(tag==="PLAC"&&(sub==="RESI"||sub==="EMIG"||sub==="IMMI"||sub==="CHR")){if(!ent.events)ent.events=[];if(!ent._curEvent)ent._curEvent={type:sub,date:"",place:""};ent._curEvent.place=cleanText(v);if(ent._curEvent.place){ent.events.push({type:ent._curEvent.type,date:ent._curEvent.date,place:ent._curEvent.place});ent._curEvent=null;}}}}for(var iid in individuals){var ind=individuals[iid];var dn="";if(ind.givenName&&ind.surname)dn=ind.givenName+" "+ind.surname;else if(ind.givenName)dn=ind.givenName;else if(ind.surname)dn=ind.surname;ind.name=dn.replace(/\//g,"").trim()||"Unknown";}return{individuals:individuals,families:families};}

/* ═══ LAYOUT — proper tree style ══════════════════════════════
   Like reference image: spouses side-by-side with horizontal line,
   vertical drop to horizontal bar, then vertical to each child.
   Family branches separated by gaps.
   ═════════════════════════════════════════════════════════════ */
function computeLayout(individuals, families) {
  var nodes=[], idToNode={}, childToParents={}, parentToChildren={}, childToFamily={}, personToSpouseFam={};
  for (var fid in families) { var f=families[fid];
    for (var ci=0;ci<f.children.length;ci++) { var c=f.children[ci]; if(!childToParents[c])childToParents[c]=[]; if(f.husband)childToParents[c].push(f.husband); if(f.wife)childToParents[c].push(f.wife); childToFamily[c]=fid; }
    var pp=[f.husband,f.wife].filter(Boolean);
    for(var pi=0;pi<pp.length;pi++){if(!parentToChildren[pp[pi]])parentToChildren[pp[pi]]=[];for(var cci=0;cci<f.children.length;cci++){var kid=f.children[cci];if(parentToChildren[pp[pi]].indexOf(kid)<0)parentToChildren[pp[pi]].push(kid);}
      if(!personToSpouseFam[pp[pi]])personToSpouseFam[pp[pi]]=[];personToSpouseFam[pp[pi]].push(fid);}
  }
  // BFS generations
  var roots=Object.keys(individuals).filter(function(id){return !childToParents[id]||!childToParents[id].length;});
  var gen={},queue=roots.slice();for(var ri=0;ri<roots.length;ri++)gen[roots[ri]]=0;
  while(queue.length){var cur=queue.shift();var kids=parentToChildren[cur]||[];for(var ki=0;ki<kids.length;ki++){if(gen[kids[ki]]===undefined||gen[kids[ki]]<gen[cur]+1){gen[kids[ki]]=gen[cur]+1;queue.push(kids[ki]);}}}
  for(var iid in individuals)if(gen[iid]===undefined)gen[iid]=0;

  // Align married-in spouses
  for(var fid2 in families){var fm=families[fid2];var h=fm.husband&&individuals[fm.husband]?fm.husband:null;var w=fm.wife&&individuals[fm.wife]?fm.wife:null;
    if(h&&w){var hP=childToParents[h]&&childToParents[h].length>0;var wP=childToParents[w]&&childToParents[w].length>0;if(hP&&!wP)gen[w]=gen[h];else if(wP&&!hP)gen[h]=gen[w];}}

  var placed={}, rowSp=22, spouseSp=8, minUnitW=12, siblingGap=6;

  function mkNode(id,x,g){
    var ind=individuals[id];
    var nd={id:id,x:x,z:g*rowSp,name:ind.name,sex:ind.sex,givenName:ind.givenName,surname:ind.surname,birthDate:ind.birthDate,birthPlace:ind.birthPlace,deathDate:ind.deathDate,deathPlace:ind.deathPlace,generation:g};
    nodes.push(nd);idToNode[id]=nd;placed[id]=true;return nd;
  }

  function getSpouse(pid,famId){var f=families[famId];if(!f)return null;if(f.husband===pid)return f.wife&&individuals[f.wife]?f.wife:null;if(f.wife===pid)return f.husband&&individuals[f.husband]?f.husband:null;return null;}

  // Bottom-up: measure how much width each person's subtree needs
  var widthCache={};
  function measureSubtree(personId, g){
    if(widthCache[personId]!==undefined)return widthCache[personId];
    var spFams=personToSpouseFam[personId]||[];
    if(!spFams.length){widthCache[personId]=minUnitW;return minUnitW;}
    var maxW=minUnitW;
    for(var fi=0;fi<spFams.length;fi++){
      var fam=families[spFams[fi]];if(!fam)continue;
      var sp=getSpouse(personId,spFams[fi]);
      var coupleW=sp?spouseSp:0;
      var kids=fam.children.filter(function(c){return individuals[c];});
      if(!kids.length){maxW=Math.max(maxW,Math.max(coupleW,minUnitW));continue;}
      var childrenW=0;
      for(var ki=0;ki<kids.length;ki++){
        if(ki>0)childrenW+=siblingGap;
        childrenW+=measureSubtree(kids[ki],g+1);
      }
      maxW=Math.max(maxW, Math.max(coupleW, childrenW), minUnitW);
    }
    widthCache[personId]=maxW;
    return maxW;
  }

  // Top-down: place person at center of allocated slot, then fan children below
  function placeUnit(personId, centerX, g){
    if(placed[personId])return;
    var spFams=personToSpouseFam[personId]||[];
    var spouse=null;
    for(var fi=0;fi<spFams.length;fi++){
      var sp=getSpouse(personId,spFams[fi]);
      if(sp&&individuals[sp]&&!placed[sp]){spouse=sp;break;}
    }
    if(spouse){
      mkNode(personId,centerX-spouseSp/2,g);
      mkNode(spouse,centerX+spouseSp/2,g);
    } else {
      mkNode(personId,centerX,g);
    }
    // Place children for all families this person parents
    for(var fi2=0;fi2<spFams.length;fi2++){
      var fam=families[spFams[fi2]];if(!fam)continue;
      var kids=fam.children.filter(function(c){return individuals[c]&&!placed[c];});
      if(!kids.length)continue;
      var childWidths=[];var totalChildW=0;
      for(var ki=0;ki<kids.length;ki++){
        var cw=measureSubtree(kids[ki],g+1);
        childWidths.push(cw);totalChildW+=cw;
        if(ki>0)totalChildW+=siblingGap;
      }
      var x=centerX-totalChildW/2;
      for(var ki2=0;ki2<kids.length;ki2++){
        if(ki2>0)x+=siblingGap;
        var childCenter=x+childWidths[ki2]/2;
        placeUnit(kids[ki2],childCenter,g+1);
        x+=childWidths[ki2];
      }
    }
  }

  // Find root families
  var rootFams=[];
  for(var ff in families){
    var fam=families[ff];
    var pars=[fam.husband,fam.wife].filter(function(p){return p&&individuals[p];});
    if(!pars.length)continue;
    var isRoot=true;
    for(var pi2=0;pi2<pars.length;pi2++){if(childToParents[pars[pi2]]&&childToParents[pars[pi2]].length>0){isRoot=false;break;}}
    if(isRoot){
      var primary=fam.husband&&individuals[fam.husband]?fam.husband:fam.wife;
      rootFams.push({fid:ff,primary:primary,gen:gen[primary]});
    }
  }
  rootFams.sort(function(a,b){return a.gen-b.gen;});

  var globalX=0;
  for(var rfi=0;rfi<rootFams.length;rfi++){
    var rf=rootFams[rfi];
    var w=measureSubtree(rf.primary,rf.gen);
    var cx=globalX+w/2;
    placeUnit(rf.primary,cx,rf.gen);
    var maxNodeX=-Infinity;for(var ni=0;ni<nodes.length;ni++)if(nodes[ni].x>maxNodeX)maxNodeX=nodes[ni].x;
    globalX=maxNodeX+minUnitW*2;
  }

  // Place remaining unplaced individuals
  for(var rid in individuals){if(!placed[rid]){var g3=gen[rid];mkNode(rid,globalX,g3);globalX+=siblingGap;}}

  var maxGen=0;for(var ndi=0;ndi<nodes.length;ndi++)if(nodes[ndi].generation>maxGen)maxGen=nodes[ndi].generation;
  // Center entire tree (not per-generation, which would break parent-child alignment)
  if(nodes.length){var minX=Infinity,maxX2=-Infinity;for(var gi=0;gi<nodes.length;gi++){if(nodes[gi].x<minX)minX=nodes[gi].x;if(nodes[gi].x>maxX2)maxX2=nodes[gi].x;}var cx=(minX+maxX2)/2;for(var gi2=0;gi2<nodes.length;gi2++)nodes[gi2].x-=cx;}

  return{nodes:nodes,idToNode:idToNode,families:families,maxGeneration:maxGen};
}

/* ═══ GEOCODING — All of Sweden + key international ═════════ */
var GEOCODE={
  // === Göteborg city parishes/areas ===
  "göteborg":{lat:57.7089,lon:11.9746},"gbg":{lat:57.7089,lon:11.9746},"masthugget":{lat:57.6970,lon:11.9380},"masthugg":{lat:57.6970,lon:11.9380},"haga":{lat:57.6975,lon:11.9540},"karl johan":{lat:57.7010,lon:11.9600},"annedal":{lat:57.7000,lon:11.9470},"lundby":{lat:57.7150,lon:11.9400},"johanneberg":{lat:57.6890,lon:11.9780},"örgryte":{lat:57.6930,lon:12.0050},"härlanda":{lat:57.7100,lon:12.0200},"vasa":{lat:57.6970,lon:11.9750},"angered":{lat:57.7920,lon:12.0490},"oskar fredrik":{lat:57.6910,lon:11.9490},"oscar fredrik":{lat:57.6910,lon:11.9490},"domkyrko":{lat:57.7047,lon:11.9668},"backa":{lat:57.7500,lon:11.9600},"gamlestad":{lat:57.7240,lon:12.0050},"nylöse":{lat:57.7240,lon:12.0050},"västra frölunda":{lat:57.6490,lon:11.9130},"högsbo":{lat:57.6580,lon:11.9350},"tynnered":{lat:57.6450,lon:11.8850},"biskopsgård":{lat:57.7280,lon:11.9100},"brämaregård":{lat:57.7150,lon:11.9200},"kortedala":{lat:57.7530,lon:12.0430},"kristine":{lat:57.7050,lon:11.9670},"sankt pauli":{lat:57.7000,lon:11.9600},"älvsborg":{lat:57.6890,lon:11.9100},
  // === Exakta adresser Göteborg ===
  "biskopsgatan 7":{lat:57.7175,lon:11.9345},"biskopsgatan":{lat:57.7175,lon:11.9345},
  "lundby (o)":{lat:57.7175,lon:11.9345},"lundby (göteborg)":{lat:57.7175,lon:11.9345},
  // === Orust island ===
  "myckleby":{lat:58.1100,lon:11.6800},"torp":{lat:58.1400,lon:11.6200},"tölläs":{lat:58.1300,lon:11.6400},"töllås":{lat:58.1300,lon:11.6400},"röra":{lat:58.1000,lon:11.7200},"långelanda":{lat:58.0700,lon:11.7100},"stenshult":{lat:58.1350,lon:11.6300},"gåre":{lat:58.1200,lon:11.6100},"resteröd":{lat:58.0700,lon:11.7400},"ottestala":{lat:58.1050,lon:11.6900},"syltenäs":{lat:58.1150,lon:11.6750},"buvenäs":{lat:58.1080,lon:11.6600},"grindsby":{lat:58.1000,lon:11.6500},"krogane":{lat:58.1000,lon:11.6900},"naddebacken":{lat:58.1250,lon:11.6350},"brunnefjäll":{lat:58.0950,lon:11.6700},"skörbo":{lat:58.0900,lon:11.6800},"hogen":{lat:58.1450,lon:11.6150},"ström":{lat:58.1350,lon:11.6100},"blibrä":{lat:58.1380,lon:11.6250},"söbben":{lat:58.1200,lon:11.6500},"medstugan":{lat:58.1300,lon:11.6200},"höggeröd":{lat:58.1100,lon:11.6300},"andenäs":{lat:58.1050,lon:11.6600},"krogeröd":{lat:58.0950,lon:11.6900},"bogane":{lat:58.1000,lon:11.6700},"hasselö":{lat:58.0300,lon:11.5800},"morlanda":{lat:58.0850,lon:11.5400},"tegneby":{lat:58.0920,lon:11.6200},"stala":{lat:58.0700,lon:11.5700},"gullholmen":{lat:58.1750,lon:11.3950},"fidjie":{lat:58.0800,lon:11.7300},"fidji":{lat:58.0800,lon:11.7300},
  // === Bohuslän coast & nearby ===
  "ödsmål":{lat:58.0300,lon:11.8100},"norum":{lat:58.1400,lon:11.8000},"forshälla":{lat:58.2900,lon:11.7600},"västerby":{lat:58.2800,lon:11.7500},"uddevalla":{lat:58.3530,lon:11.9380},"bäve":{lat:58.3400,lon:11.9000},"lysekil":{lat:58.2740,lon:11.4360},"grundsund":{lat:58.2130,lon:11.3180},"skaftö":{lat:58.2200,lon:11.3500},"fiskebäckskil":{lat:58.2430,lon:11.4500},"skredsvik":{lat:58.3100,lon:11.7800},"bokenäs":{lat:58.2500,lon:11.6500},"brastad":{lat:58.3800,lon:11.5600},"smögen":{lat:58.3540,lon:11.2260},"kville":{lat:58.5700,lon:11.2800},"svarteborg":{lat:58.5200,lon:11.4200},"marstrand":{lat:57.8880,lon:11.5820},"kungälv":{lat:57.8710,lon:11.9710},"herrestad":{lat:58.3300,lon:11.8600},"grinneröd":{lat:58.3200,lon:11.7900},"stenkyrka":{lat:58.0350,lon:11.4850},"foss":{lat:58.4200,lon:11.8200},"munkedal":{lat:58.4700,lon:11.6700},"lane ryr":{lat:58.4300,lon:11.9100},"hjärtum":{lat:58.1700,lon:11.9200},
  // === Västra Götaland inland ===
  "vänersborg":{lat:58.3810,lon:12.3230},"trollhättan":{lat:58.2837,lon:12.2886},"alingsås":{lat:57.9305,lon:12.5337},"nödinge":{lat:57.8670,lon:12.0670},"lerum":{lat:57.7710,lon:12.2690},"mölnlycke":{lat:57.6580,lon:12.1180},"borås":{lat:57.7210,lon:12.9401},"fritsla":{lat:57.5500,lon:12.7600},"ljung":{lat:57.7400,lon:12.5800},"skallsjö":{lat:57.7600,lon:12.3600},"skara":{lat:58.3869,lon:13.4384},"falköping":{lat:58.1734,lon:13.5513},"västerlanda":{lat:58.1200,lon:11.9200},"färgelanda":{lat:58.5700,lon:12.0900},"magra":{lat:58.0500,lon:12.3500},"hemsjö":{lat:57.8400,lon:12.3300},"agnetorp":{lat:58.3800,lon:13.6200},"höga":{lat:58.1100,lon:11.6300},"vättlösa":{lat:58.5300,lon:13.3200},"vänersnäs":{lat:58.4200,lon:12.2600},"ödenäs":{lat:58.0100,lon:12.4700},
  // === Other Swedish cities/regions ===
  "stockholm":{lat:59.3293,lon:18.0686},"malmö":{lat:55.6050,lon:13.0038},"uppsala":{lat:59.8586,lon:17.6389},"linköping":{lat:58.4108,lon:15.6214},"norrköping":{lat:58.5942,lon:16.1826},"halmstad":{lat:56.6745,lon:12.8577},"söndrum":{lat:56.6400,lon:12.8200},"växjö":{lat:56.8770,lon:14.8059},"jönköping":{lat:57.7826,lon:14.1618},"örebro":{lat:59.2753,lon:15.2134},"karlstad":{lat:59.3793,lon:13.5036},"gävle":{lat:60.6749,lon:17.1413},"sundsvall":{lat:62.3908,lon:17.3069},"lund":{lat:55.7047,lon:13.1910},"umeå":{lat:63.8258,lon:20.2630},"luleå":{lat:65.5848,lon:22.1547},"kiruna":{lat:67.8558,lon:20.2253},"visby":{lat:57.6348,lon:18.2948},"kalmar":{lat:56.6634,lon:16.3566},"karlskrona":{lat:56.1612,lon:15.5869},"kristianstad":{lat:56.0294,lon:14.1567},"helsingborg":{lat:56.0465,lon:12.6945},"västerås":{lat:59.6099,lon:16.5448},"eskilstuna":{lat:59.3666,lon:16.5077},"ludvika":{lat:60.1486,lon:15.1886},"norrbärke":{lat:60.1500,lon:15.1900},"degerfors":{lat:59.2400,lon:14.4300},"tuna":{lat:62.7400,lon:17.0700},"tranås":{lat:58.0372,lon:14.9761},"säby":{lat:57.9000,lon:14.0800},"rödeby":{lat:56.2600,lon:15.6200},"lövestad":{lat:55.5900,lon:13.7400},"lösen":{lat:56.1900,lon:15.6400},"lyckeby":{lat:56.1800,lon:15.6500},
  "norra åsum":{lat:55.8600,lon:14.2700},"bygdeå":{lat:64.3600,lon:21.3700},"rickleå":{lat:64.3800,lon:21.2700},"dals ed":{lat:58.8100,lon:11.5900},
  "kristinehamn":{lat:59.3099,lon:14.1083},"oskarshamn":{lat:57.2648,lon:16.4482},"karlskoga":{lat:59.3267,lon:14.5208},"filipstad":{lat:59.7125,lon:14.1686},"arvika":{lat:59.6553,lon:12.5853},"säffle":{lat:59.1319,lon:12.9283},"mariestad":{lat:58.7094,lon:13.8236},"lidköping":{lat:58.5053,lon:13.1578},"skövde":{lat:58.3864,lon:13.8458},"motala":{lat:58.5372,lon:15.0364},"västervik":{lat:57.7583,lon:16.6367},"vimmerby":{lat:57.6658,lon:15.8556},"eksjö":{lat:57.6667,lon:14.9667},"vetlanda":{lat:57.4289,lon:15.0786},"nässjö":{lat:57.6531,lon:14.6967},"mjölby":{lat:58.3256,lon:15.1314},"katrineholm":{lat:58.9958,lon:16.2058},"nyköping":{lat:58.7530,lon:17.0086},"strängnäs":{lat:59.3792,lon:17.0306},"enköping":{lat:59.6358,lon:17.0767},"sala":{lat:59.9200,lon:16.6069},"köping":{lat:59.5147,lon:15.9928},"arboga":{lat:59.3939,lon:15.8386},"borlänge":{lat:60.4858,lon:15.4364},"falun":{lat:60.6065,lon:15.6355},"mora":{lat:61.0036,lon:14.5450},"avesta":{lat:60.1458,lon:16.1694},"sandviken":{lat:60.6167,lon:16.7758},"hudiksvall":{lat:61.7270,lon:17.1056},"härnösand":{lat:62.6323,lon:17.9379},"örnsköldsvik":{lat:63.2909,lon:18.7152},"skellefteå":{lat:64.7507,lon:20.9528},"piteå":{lat:65.3174,lon:21.4797},"boden":{lat:66.0000,lon:21.6886},"kramfors":{lat:62.9314,lon:17.7758},"sollefteå":{lat:63.1672,lon:17.2681},"ånge":{lat:62.5247,lon:15.6600},"östersund":{lat:63.1792,lon:14.6357},"sveg":{lat:62.0350,lon:14.3539},"gällivare":{lat:67.1333,lon:20.6500},"haparanda":{lat:65.8353,lon:24.1369},
  // === Norway / International ===
  "grimstad":{lat:58.3405,lon:8.5930},"norge":{lat:59.0,lon:10.0},"usa":{lat:40.7128,lon:-74.0060},"minnesota":{lat:44.9778,lon:-93.2650},"amerika":{lat:40.7128,lon:-74.0060},
};


// Build timeline of locations for a person
// Combines: 1) extraLocs (locations.json), 2) GEDCOM RESI events, 3) birth/death geocoding
function buildPersonLocations(ind, extraLocs){
  if(!ind)return [];
  var locs=[];
  var id=ind.id||ind.rawId;
  
  // 1. Explicit locations from locations.json (highest priority)
  if(extraLocs&&extraLocs[id]){
    return extraLocs[id]; // already formatted [{lat,lon,from,to,place,type}]
  }
  
  // 2. Parse year from date string
  function yr(d){if(!d)return null;var m=d.match(/\d{4}/);return m?parseInt(m[0]):null;}
  
  var birthY=yr(ind.birthDate), deathY=yr(ind.deathDate);
  
  // 3. Birth place
  if(ind.birthPlace){
    var bloc=lookupLocation(ind.birthPlace);
    if(bloc)locs.push({lat:bloc.lat,lon:bloc.lon,from:birthY,to:birthY,place:ind.birthPlace,type:"birth"});
  }
  
  // 4. RESI events from GEDCOM
  if(ind.events){
    ind.events.forEach(function(ev){
      var eloc=lookupLocation(ev.place);
      if(eloc){
        var ey=yr(ev.date);
        locs.push({lat:eloc.lat,lon:eloc.lon,from:ey,to:ey,place:ev.place,type:ev.type.toLowerCase(),date:ev.date});
      }
    });
  }
  
  // 5. Death place (if different from birth)
  if(ind.deathPlace&&ind.deathPlace!==ind.birthPlace){
    var dloc=lookupLocation(ind.deathPlace);
    if(dloc)locs.push({lat:dloc.lat,lon:dloc.lon,from:deathY,to:deathY,place:ind.deathPlace,type:"death"});
  }
  
  // Sort by year
  locs.sort(function(a,b){return (a.from||0)-(b.from||0);});
  return locs;
}

function kartbildUrl(lat,lon,layer,zoom){
  if(!lat||!lon)return null;
  return 'https://kartbild.com/#'+(zoom||15)+'/'+lat.toFixed(4)+'/'+lon.toFixed(4)+'/'+layer;
}
function placeZoom(place){
  // Returns appropriate kartbild zoom level based on place name
  if(!place) return 15;
  var p=place.toLowerCase();
  // Specific address → zoom in close
  if(p.match(/gatan|vägen|torget|platsen|allén|\d+,/)) return 16;
  // Farm/homestead names
  if(p.match(/gård|säteri|torp|husegård|husegård/)) return 16;
  // Small hamlet/village
  if(p.match(/by\b|näs\b|udde\b|backe\b|vik\b|dal\b/)) return 15;
  // Parish/socken
  if(p.match(/socken|församling|\(o\)|\(n\)|\(p\)|\(r\)|\(s\)/)) return 14;
  // City district
  if(p.indexOf("göteborg")>=0||p.indexOf("stockholm")>=0||p.indexOf("malmö")>=0) return 13;
  // Island
  if(p.indexOf("orust")>=0||p.indexOf("tjörn")>=0) return 11;
  return 15;
}

function lookupLocation(place){
  if(!place)return null;
  var p=place.toLowerCase();
  for(var ki=0;ki<GEOCODE_KEYS.length;ki++){if(p.indexOf(GEOCODE_KEYS[ki])>=0)return GEOCODE[GEOCODE_KEYS[ki]];}
  return null;
}

function normalizePlaceName(place){
  if(!place) return "";
  return place.toLowerCase()
    .replace(/[åä]/g,"a").replace(/ö/g,"o")
    .replace(/[^a-z0-9]+/g,"_")
    .replace(/^_+|_+$/g,"")
    .replace(/_+/g,"_");
}

function lookupPlacePhotos(place, placeUrls){
  if(!place||!placeUrls) return [];
  var norm=normalizePlaceName(place);
  // 1. Exact match
  if(placeUrls[norm]) return placeUrls[norm];
  // 2. norm starts with placeId (place name is more specific than file)
  // e.g. "biskopsgatan_7_lundby_goteborg" starts with "biskopsgatan_7_lundby"
  var keys=Object.keys(placeUrls);
  for(var i=0;i<keys.length;i++){
    if(norm.indexOf(keys[i])===0) return placeUrls[keys[i]];
  }
  return [];
}

// Pre-sort keys longest first so "kristinehamn" matches before "kristine"
var GEOCODE_KEYS=Object.keys(GEOCODE).sort(function(a,b){return b.length-a.length;});

function geocodePlace(ps){
  if(!ps)return null;
  var lw=ps.toLowerCase().replace(/\(.\)/g,"").replace(/\([a-z]+\)/g,"").trim();
  for(var i=0;i<GEOCODE_KEYS.length;i++){var k=GEOCODE_KEYS[i];if(lw.indexOf(k)>=0)return GEOCODE[k];}
  // Try with ANSEL remnants stripped
  var a=lw.replace(/[èêëé]/g,"");
  for(var i2=0;i2<GEOCODE_KEYS.length;i2++){var k2=GEOCODE_KEYS[i2];var ak=k2.replace(/[öäå]/g,function(c){return{ö:"o",ä:"a",å:"a"}[c]||c;});if(a.indexOf(ak)>=0)return GEOCODE[k2];}
  // Try first word
  var first=lw.split(/[\s,]/)[0];
  if(first.length>3){for(var i3=0;i3<GEOCODE_KEYS.length;i3++){var k3=GEOCODE_KEYS[i3];if(k3.indexOf(first)>=0||first.indexOf(k3)>=0)return GEOCODE[k3];}}
  return null;
}
function parseYear(d){if(!d)return null;var m=d.match(/(\d{4})/);return m?parseInt(m[1]):null;}

/* ═══ SAMPLE DATA ═════════════════════════════════════════════ */
var PM={"@I1@":{i:"JS",s:"M",h:"#8B7355",k:"#D08B5B",t:"#3c4f5c"},"@I2@":{i:"MJ",s:"F",h:"#4A312C",k:"#EDB98A",t:"#929598"},"@I3@":{i:"RS",s:"M",h:"#5C4033",k:"#D08B5B",t:"#25557c"},"@I4@":{i:"ES",s:"F",h:"#6B3A2E",k:"#EDB98A",t:"#c44a7a"},"@I5@":{i:"SW",s:"F",h:"#A0522D",k:"#FFDBB4",t:"#7a6a9e"},"@I6@":{i:"JS",s:"M",h:"#3B2F2F",k:"#D08B5B",t:"#3c4f5c"},"@I7@":{i:"ES",s:"F",h:"#B58143",k:"#EDB98A",t:"#6a8a6a"},"@I8@":{i:"TB",s:"M",h:"#4E3B31",k:"#FFDBB4",t:"#25557c"},"@I9@":{i:"CB",s:"F",h:"#7B3F00",k:"#FFDBB4",t:"#c44a7a"},"@I10@":{i:"WB",s:"M",h:"#2F1E0E",k:"#FFDBB4",t:"#3c4f5c"},"@I11@":{i:"AD",s:"F",h:"#8B4513",k:"#EDB98A",t:"#7a6a9e"},"@I12@":{i:"OS",s:"M",h:"#3B2F2F",k:"#D08B5B",t:"#25557c"},"@I13@":{i:"CS",s:"F",h:"#B58143",k:"#EDB98A",t:"#c44a7a"}};
function genAvatar(m){var s=128,c=document.createElement("canvas");c.width=s;c.height=s;var x=c.getContext("2d"),cx=s/2;x.beginPath();x.arc(cx,cx,60,0,Math.PI*2);x.fillStyle=m.s==="M"?"#1a3a5c":"#4a1a3a";x.fill();x.fillStyle=m.k;x.fillRect(cx-8,78,16,16);x.fillStyle=m.t;x.beginPath();x.ellipse(cx,115,38,24,0,Math.PI,0,true);x.fill();x.fillStyle=m.k;x.beginPath();x.ellipse(cx,52,22,26,0,0,Math.PI*2);x.fill();x.fillStyle=m.h;if(m.s==="M"){x.beginPath();x.ellipse(cx,42,23,18,0,Math.PI,0,true);x.fill();x.fillRect(cx-22,38,5,14);x.fillRect(cx+17,38,5,14);}else{x.beginPath();x.ellipse(cx,42,25,20,0,Math.PI,0,true);x.fill();x.beginPath();x.moveTo(cx-25,42);x.quadraticCurveTo(cx-30,65,cx-26,85);x.lineTo(cx-20,85);x.quadraticCurveTo(cx-22,65,cx-22,45);x.fill();x.beginPath();x.moveTo(cx+25,42);x.quadraticCurveTo(cx+30,65,cx+26,85);x.lineTo(cx+20,85);x.quadraticCurveTo(cx+22,65,cx+22,45);x.fill();}x.fillStyle="#fff";x.beginPath();x.ellipse(cx-8,50,4.5,3.5,0,0,Math.PI*2);x.fill();x.beginPath();x.ellipse(cx+8,50,4.5,3.5,0,0,Math.PI*2);x.fill();x.fillStyle="#2c1810";x.beginPath();x.arc(cx-7,50,2.2,0,Math.PI*2);x.fill();x.beginPath();x.arc(cx+9,50,2.2,0,Math.PI*2);x.fill();x.strokeStyle="#c06050";x.lineWidth=1.8;x.beginPath();x.arc(cx,64,6,0.15*Math.PI,0.85*Math.PI);x.stroke();x.beginPath();x.arc(cx,cx,60,0,Math.PI*2);x.strokeStyle=m.s==="M"?"#4a9eff":"#ff6b9d";x.lineWidth=3;x.stroke();return c;}
function genPhotoTex(pid){var m=PM[pid];if(!m||typeof THREE==='undefined')return null;return new THREE.CanvasTexture(genAvatar(m));}
var GEDCOM=["0 HEAD","1 SOUR SAMPLE","0 @I1@ INDI","1 NAME John /Smith/","2 GIVN John","2 SURN Smith","1 SEX M","1 BIRT","2 DATE 15 JAN 1920","2 PLAC Göteborg","1 DEAT","2 DATE 3 MAR 1995","2 PLAC Uddevalla","1 FAMS @F1@","0 @I2@ INDI","1 NAME Mary /Johnson/","2 GIVN Mary","2 SURN Johnson","1 SEX F","1 BIRT","2 DATE 22 JUN 1925","2 PLAC Lysekil","1 DEAT","2 DATE 10 NOV 2001","2 PLAC Uddevalla","1 FAMS @F1@","0 @I3@ INDI","1 NAME Robert /Smith/","2 GIVN Robert","2 SURN Smith","1 SEX M","1 BIRT","2 DATE 5 MAR 1948","2 PLAC Uddevalla","1 FAMC @F1@","1 FAMS @F2@","0 @I4@ INDI","1 NAME Elizabeth /Smith/","2 GIVN Elizabeth","2 SURN Smith","1 SEX F","1 BIRT","2 DATE 12 SEP 1950","2 PLAC Uddevalla","1 FAMC @F1@","1 FAMS @F3@","0 @I5@ INDI","1 NAME Susan /Williams/","2 GIVN Susan","2 SURN Williams","1 SEX F","1 BIRT","2 DATE 8 AUG 1952","2 PLAC Myckleby","1 FAMS @F2@","0 @I6@ INDI","1 NAME James /Smith/","2 GIVN James","2 SURN Smith","1 SEX M","1 BIRT","2 DATE 20 DEC 1975","2 PLAC Göteborg","1 FAMC @F2@","1 FAMS @F4@","0 @I7@ INDI","1 NAME Emma /Smith/","2 GIVN Emma","2 SURN Smith","1 SEX F","1 BIRT","2 DATE 3 FEB 1978","2 PLAC Göteborg","1 FAMC @F2@","0 @I8@ INDI","1 NAME Thomas /Brown/","2 GIVN Thomas","2 SURN Brown","1 SEX M","1 BIRT","2 DATE 14 JUL 1948","2 PLAC Torp","1 FAMS @F3@","0 @I9@ INDI","1 NAME Catherine /Brown/","2 GIVN Catherine","2 SURN Brown","1 SEX F","1 BIRT","2 DATE 1 APR 1972","2 PLAC Torp","1 FAMC @F3@","0 @I10@ INDI","1 NAME William /Brown/","2 GIVN William","2 SURN Brown","1 SEX M","1 BIRT","2 DATE 17 OCT 1974","2 PLAC Torp","1 FAMC @F3@","0 @I11@ INDI","1 NAME Alice /Davis/","2 GIVN Alice","2 SURN Davis","1 SEX F","1 BIRT","2 DATE 5 MAY 1977","2 PLAC Forshälla","1 FAMS @F4@","0 @I12@ INDI","1 NAME Oliver /Smith/","2 GIVN Oliver","2 SURN Smith","1 SEX M","1 BIRT","2 DATE 12 SEP 2003","2 PLAC Göteborg","1 FAMC @F4@","0 @I13@ INDI","1 NAME Charlotte /Smith/","2 GIVN Charlotte","2 SURN Smith","1 SEX F","1 BIRT","2 DATE 28 NOV 2006","2 PLAC Göteborg","1 FAMC @F4@","0 @F1@ FAM","1 HUSB @I1@","1 WIFE @I2@","1 CHIL @I3@","1 CHIL @I4@","0 @F2@ FAM","1 HUSB @I3@","1 WIFE @I5@","1 CHIL @I6@","1 CHIL @I7@","0 @F3@ FAM","1 HUSB @I8@","1 WIFE @I4@","1 CHIL @I9@","1 CHIL @I10@","0 @F4@ FAM","1 HUSB @I6@","1 WIFE @I11@","1 CHIL @I12@","1 CHIL @I13@","0 TRLR"].join("\n");

/* ═══ COLORS ══════════════════════════════════════════════════ */
var C={bg:"#080c14",ground:"#0f1520",gridCol:"#1a2540",male:"#4a9eff",female:"#ff6b9d",unknown:"#a0aec0",spouse:"#ffd700",parent:"#66d9a0",highlight:"#ffdd57",text:"#e2e8f0",dim:"#556677",panel:"#0d1420",border:"#1e2d44",accent:"#4a9eff"};
var GL=["Gen I","Gen II","Gen III","Gen IV","Gen V","Gen VI","Gen VII","Gen VIII"];
var GC=["#ff6b6b","#ffa94d","#ffd43b","#69db7c","#4dabf7","#9775fa","#f783ac","#20c997"];

/* ═══ 3D HELPERS ══════════════════════════════════════════════ */
var _silhCache={};
function mkSilhouette(sex){
  var key=sex||"U";
  if(_silhCache[key])return _silhCache[key];
  var cv=document.createElement("canvas");cv.width=256;cv.height=320;
  var x=cv.getContext("2d");
  // Card background
  x.fillStyle="#f4f1ea";
  if(x.roundRect){x.beginPath();x.roundRect(4,4,248,312,14);x.fill();}else{x.fillRect(4,4,248,312);}
  // Frame
  x.strokeStyle=sex==="M"?"#4a8ab0":sex==="F"?"#c75a8a":"#999";x.lineWidth=6;
  if(x.roundRect){x.beginPath();x.roundRect(7,7,242,306,12);x.stroke();}else{x.strokeRect(7,7,242,306);}
  // Silhouette (head + shoulders, like ArkivDigital)
  x.fillStyle="#1a1a1a";
  x.beginPath();x.arc(128,120,58,0,Math.PI*2);x.fill();
  x.beginPath();x.moveTo(40,290);x.quadraticCurveTo(45,195,128,192);x.quadraticCurveTo(211,195,216,290);x.closePath();x.fill();
  _silhCache[key]=cv;
  return cv;
}
function mkSilhTex(sex){
  var cv=mkSilhouette(sex);
  if(!cv||typeof THREE==='undefined')return null;
  var key=(sex||'U')+'_tex';
  if(_silhCache[key])return _silhCache[key];
  var tex=new THREE.CanvasTexture(cv);
  _silhCache[key]=tex;
  return tex;
}
function mkLabel(n,dt,hl){
  var cv=document.createElement("canvas");cv.width=400;cv.height=120;
  var x=cv.getContext("2d");x.textAlign="center";x.textBaseline="top";
  x.shadowColor="rgba(0,0,0,0.9)";x.shadowBlur=8;
  // Word wrap name if too long
  x.font="bold 20px Arial";x.fillStyle=hl?C.highlight:"#fff";
  var maxW=380,words=n.split(" "),lines2=[],cur="";
  for(var wi=0;wi<words.length;wi++){var test=cur?cur+" "+words[wi]:words[wi];if(x.measureText(test).width>maxW&&cur){lines2.push(cur);cur=words[wi];}else cur=test;}
  if(cur)lines2.push(cur);
  var y=4;
  for(var li=0;li<lines2.length;li++){x.fillText(lines2[li],200,y);y+=22;}
  if(dt){x.font="13px Arial";x.fillStyle=hl?"#ffe88a":"#8899aa";x.shadowBlur=4;x.fillText(dt,200,y+2);}
  if(typeof THREE==="undefined")return cv;return new THREE.SpriteMaterial({map:new THREE.CanvasTexture(cv),transparent:true,depthTest:false});
}

/* ═══ MAP with zoom/pan — realistic colors ════════════════════ */

// === PEDIGREE VIEW (ancestor chart) ===
function PedigreeView(props){
  var cvRef=useRef(null);
  var viewRef=useRef({cx:0,cy:0,zoom:1,dragging:false,sx:0,sy:0,scx:0,scy:0});
  var cardsRef=useRef([]);
  var individuals=props.individuals,families=props.families,selectedId=props.selectedId,onSelect=props.onSelect,photoUrls=props.photoUrls||{},mode=props.mode||"ancestors";

  var drawPedigree=useCallback(function(){
    var cv=cvRef.current;if(!cv)return;
    var ct=cv.parentElement;cv.width=ct.clientWidth*2;cv.height=ct.clientHeight*2;
    cv.style.width=ct.clientWidth+"px";cv.style.height=ct.clientHeight+"px";
    var ctx=cv.getContext("2d");ctx.scale(2,2);
    var W=ct.clientWidth,H=ct.clientHeight,v=viewRef.current;

    ctx.fillStyle="#0d1117";ctx.fillRect(0,0,W,H);
    var _cards=[];
    if(!individuals||!selectedId||!individuals[selectedId])return;

    // Build ancestor tree from selected person
    var childToFam={};
    for(var fid in families){var f=families[fid];for(var ci=0;ci<f.children.length;ci++)childToFam[f.children[ci]]=fid;}

    function getParents(pid){
      var fid=childToFam[pid];if(!fid)return null;
      var f=families[fid];
      return{father:f.husband&&individuals[f.husband]?f.husband:null,mother:f.wife&&individuals[f.wife]?f.wife:null};
    }

    function getChildren(pid){var kids=[];for(var fid in families){var f=families[fid];if((f.husband===pid||f.wife===pid)&&f.children){for(var ci=0;ci<f.children.length;ci++){if(individuals[f.children[ci]]&&kids.indexOf(f.children[ci])<0)kids.push(f.children[ci]);}}}return kids;}


    var colW=185*v.zoom, startX=20+v.cx, startY=H/2+v.cy;
    var maxDepth=7;
    // Count leaves for proportional spacing
    function cntLeaves(pid,d){
      if(!pid||!individuals[pid]||d>=maxDepth)return 1;
      if(mode==="ancestors"){var p=getParents(pid);if(!p)return 1;return (p.father?cntLeaves(p.father,d+1):1)+(p.mother?cntLeaves(p.mother,d+1):1);}
      else{var k=getChildren(pid);if(!k.length)return 1;var s=0;for(var ki=0;ki<k.length;ki++)s+=cntLeaves(k[ki],d+1);return s;}
    }
    var totalLeaves=cntLeaves(selectedId,0);
    var minRowH=28*v.zoom;
    var totalNeeded=totalLeaves*minRowH;
    var availH=H*0.92;
    var leafH=Math.max(minRowH,availH/totalLeaves);

    var bwBase=170*v.zoom;

    function drawPerson(pid,x,y,depth,slotH){
      if(!pid||!individuals[pid]||depth>maxDepth)return;
      var ind=individuals[pid];
      var bw=170*v.zoom,bh=Math.min(34*v.zoom,Math.max(16*v.zoom,slotH*0.65)),fs=Math.max(7,Math.min(11,bh/(3*v.zoom)))*v.zoom;
      var isSel=pid===selectedId;
      ctx.fillStyle=isSel?"#1a2744":ind.sex==="M"?"#162030":"#251525";
      ctx.strokeStyle=isSel?"#4a9eff":ind.sex==="M"?"#2a5080":"#802a50";
      ctx.lineWidth=isSel?2:1;
      ctx.beginPath();ctx.roundRect(x,y-bh/2,bw,bh,4*v.zoom);ctx.fill();ctx.stroke();
      _cards.push({pid:pid,x:x,y:y-bh/2,w:bw,h:bh});
      ctx.fillStyle=isSel?"#fff":"#ccd";ctx.font="bold "+fs+"px Arial";ctx.textBaseline="middle";
      var name=ind.name||"Unknown";
      if(ctx.measureText(name).width>bw-8*v.zoom)name=name.substring(0,Math.floor(bw/(fs*0.55)))+"..";
      ctx.fillText(name,x+5*v.zoom,bh>24*v.zoom?y-bh*0.15:y);
      var dates="";if(ind.birthDate){var by=ind.birthDate.match(/\d{4}/);dates+=by?by[0]:"?";}if(ind.deathDate){var dy=ind.deathDate.match(/\d{4}/);dates+=" - "+(dy?dy[0]:"?");}
      if(dates&&bh>22*v.zoom){ctx.fillStyle="#778";ctx.font=Math.max(6,fs*0.75)+"px Arial";ctx.fillText(dates,x+5*v.zoom,y+bh*0.22);}
      if(photoUrls[pid]&&photoUrls[pid].length>0){ctx.fillStyle="#66d9a0";ctx.beginPath();ctx.arc(x+bw-8*v.zoom,y-bh/2+8*v.zoom,3*v.zoom,0,Math.PI*2);ctx.fill();}
      if(mode==="ancestors"){
        var parents=getParents(pid);
        if(parents){var nextX=x+colW;
          var fLeaves=parents.father?cntLeaves(parents.father,depth+1):0;
          var mLeaves=parents.mother?cntLeaves(parents.mother,depth+1):0;
          var tLeaves2=Math.max(1,fLeaves+mLeaves);
          var fSlot=slotH*fLeaves/tLeaves2,mSlot=slotH*mLeaves/tLeaves2;
          if(parents.father){var fy=y-slotH/2+fSlot/2;ctx.strokeStyle="#2a5080";ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(x+bw,y);ctx.lineTo(x+bw+8*v.zoom,y);ctx.lineTo(x+bw+8*v.zoom,fy);ctx.lineTo(nextX,fy);ctx.stroke();drawPerson(parents.father,nextX,fy,depth+1,fSlot);}
          if(parents.mother){var my2=y+slotH/2-mSlot/2;ctx.strokeStyle="#802a50";ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(x+bw,y);ctx.lineTo(x+bw+8*v.zoom,y);ctx.lineTo(x+bw+8*v.zoom,my2);ctx.lineTo(nextX,my2);ctx.stroke();drawPerson(parents.mother,nextX,my2,depth+1,mSlot);}
        }
      } else {
        var kids=getChildren(pid);
        if(kids.length>0){var prevX=x-colW;
          var kidLeaves=[];var tKL=0;for(var kli=0;kli<kids.length;kli++){var kl=cntLeaves(kids[kli],depth+1);kidLeaves.push(kl);tKL+=kl;}
          var curY=y-slotH/2;
          for(var ki=0;ki<kids.length;ki++){var kidSlot=slotH*kidLeaves[ki]/tKL;var ky=curY+kidSlot/2;ctx.strokeStyle="#ff6b9d";ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(x,y);ctx.lineTo(x-8*v.zoom,y);ctx.lineTo(x-8*v.zoom,ky);ctx.lineTo(prevX+bw,ky);ctx.stroke();drawPerson(kids[ki],prevX,ky,depth+1,kidSlot);curY+=kidSlot;}
        }
      }
    }

    var startXD=mode==="descendants"?W-bwBase-20+v.cx:20+v.cx;
    drawPerson(selectedId,startXD,startY,0,Math.max(availH,totalNeeded));

    cardsRef.current=_cards;

    // HUD
    ctx.fillStyle="#8899aa";ctx.font="11px Arial";ctx.textBaseline="top";
    ctx.fillText((mode==="descendants"?"Descendants":"Pedigree")+" \u00b7 "+((individuals[selectedId]||{}).name||""),10,10);
    ctx.fillStyle="#556";ctx.font="9px Arial";
    ctx.fillText("Select a person in 3D view",10,26);
  },[individuals,families,selectedId,photoUrls,mode]);

  useEffect(function(){drawPedigree();},[drawPedigree]);

  useEffect(function(){
    var cv=cvRef.current;if(!cv)return;
    function onW(e){e.preventDefault();var v=viewRef.current;v.zoom=Math.max(0.3,Math.min(3,v.zoom+e.deltaY*-0.001));drawPedigree();}
    function onD(e){var v=viewRef.current;v.dragging=true;v.sx=e.clientX;v.sy=e.clientY;v.scx=v.cx;v.scy=v.cy;}
    function onM(e){var v=viewRef.current;if(v.dragging){v.cx=v.scx+(e.clientX-v.sx);v.cy=v.scy+(e.clientY-v.sy);drawPedigree();}}
    function onU(){viewRef.current.dragging=false;}
    function onClick(e){
      var v2=viewRef.current;var dx2=Math.abs(e.clientX-(v2.sx||0))+Math.abs(e.clientY-(v2.sy||0));if(dx2>5)return;
      var rect=cv.getBoundingClientRect();var mx=e.clientX-rect.left,my=e.clientY-rect.top;
      var cards=cardsRef.current;
      for(var ci2=0;ci2<cards.length;ci2++){var cd=cards[ci2];if(mx>=cd.x&&mx<=cd.x+cd.w&&my>=cd.y&&my<=cd.y+cd.h){if(props.onInspect)props.onInspect(cd.pid);return;}}
    }
    cv.addEventListener("wheel",onW,{passive:false});cv.addEventListener("mousedown",onD);cv.addEventListener("click",onClick);
    window.addEventListener("mousemove",onM);window.addEventListener("mouseup",onU);
    return function(){cv.removeEventListener("wheel",onW);cv.removeEventListener("mousedown",onD);cv.removeEventListener("click",onClick);window.removeEventListener("mousemove",onM);window.removeEventListener("mouseup",onU);};
  },[drawPedigree]);

  return <canvas ref={cvRef} style={{width:"100%",height:"100%",display:"block",cursor:"grab"}}/>;
}

// === FAN CHART VIEW ===
function FanView(props){
  var cvRef=useRef(null);
  var viewRef=useRef({zoom:1,cx:0,cy:0,dragging:false,sx:0,sy:0,scx:0,scy:0});
  var individuals=props.individuals,families=props.families,selectedId=props.selectedId,onSelect=props.onSelect,photoUrls=props.photoUrls||{},mode=props.mode||"ancestors";

  // Build lookup
  var childToFam=useMemo(function(){
    var m={};if(!families)return m;
    for(var fid in families){var f=families[fid];if(f.children)for(var ci=0;ci<f.children.length;ci++)m[f.children[ci]]=fid;}
    return m;
  },[families]);

  var getParents=useCallback(function(pid){
    var fid=childToFam[pid];if(!fid||!families[fid])return null;
    var f=families[fid];
    return{father:f.husband&&individuals[f.husband]?f.husband:null,mother:f.wife&&individuals[f.wife]?f.wife:null};
  },[childToFam,families,individuals]);

  var getChildren=useCallback(function(pid){
    var kids=[];if(!families)return kids;
    for(var fid in families){var f=families[fid];
      if((f.husband===pid||f.wife===pid)&&f.children){
        for(var ci=0;ci<f.children.length;ci++){if(individuals[f.children[ci]]&&kids.indexOf(f.children[ci])<0)kids.push(f.children[ci]);}
      }
    }
    return kids;
  },[families,individuals]);

  // Store arc hit regions for click detection
  var arcsRef=useRef([]);

  var drawFan=useCallback(function(){
    var cv=cvRef.current;if(!cv)return;
    var ct=cv.parentElement;cv.width=ct.clientWidth*2;cv.height=ct.clientHeight*2;
    cv.style.width=ct.clientWidth+"px";cv.style.height=ct.clientHeight+"px";
    var ctx=cv.getContext("2d");ctx.scale(2,2);
    var W=ct.clientWidth,H=ct.clientHeight,z=viewRef.current.zoom;
    var vv=viewRef.current;

    ctx.fillStyle="#0d1117";ctx.fillRect(0,0,W,H);
    if(!individuals||!selectedId||!individuals[selectedId])return;

    var selInd=individuals[selectedId];
    var maxGen=7;
    var baseR=45*z,ringW=50*z;
    var cx=W/2+vv.cx,cy=H/2+vv.cy;

    // Arc sweep: 270 degrees, gap at bottom (like Gramps)
    var gapAngle=Math.PI*0.5; // 90 degree gap at bottom
    var startAngle=Math.PI/2+gapAngle/2; // start just past bottom-right
    var sweepAngle=Math.PI*2-gapAngle;
    var endAngle=startAngle+sweepAngle;

    var colors=[
      ["#c75a5a","#a84646"],["#e8913d","#c77830"],["#c4a632","#a89028"],
      ["#4ea85a","#3a8a46"],["#4a8ab0","#3670a0"],["#7a5eb0","#6248a0"],
      ["#c75a8a","#a84672"]
    ];

    // Build levels via BFS
    var levels=[];
    levels[0]=[{pid:selectedId,sa:startAngle,ea:endAngle}];

    var arcs=[];

    for(var d=0;d<maxGen;d++){
      levels[d+1]=[];
      for(var i=0;i<levels[d].length;i++){
        var entry=levels[d][i];
        if(mode==="ancestors"){
          var parents=entry.pid?getParents(entry.pid):null;
          var mid=(entry.sa+entry.ea)/2;
          levels[d+1].push({pid:parents?parents.father:null,sa:entry.sa,ea:mid});
          levels[d+1].push({pid:parents?parents.mother:null,sa:mid,ea:entry.ea});
        } else {
          var dK=entry.pid?getChildren(entry.pid):[];
          if(dK.length>0){
            var sl=(entry.ea-entry.sa)/dK.length;
            for(var dki=0;dki<dK.length;dki++)
              levels[d+1].push({pid:dK[dki],sa:entry.sa+dki*sl,ea:entry.sa+(dki+1)*sl});
          } else {
            levels[d+1].push({pid:null,sa:entry.sa,ea:entry.ea});
          }
        }
      }
    }

    // Draw arcs from outer to inner
    for(var d2=maxGen;d2>=1;d2--){
      var r1=baseR+d2*ringW-ringW+3;
      var r2=baseR+d2*ringW;
      for(var i2=0;i2<levels[d2].length;i2++){
        var e=levels[d2][i2];
        var col=colors[(d2-1)%colors.length];
        var hasPerson=e.pid&&individuals[e.pid];

        // Fill arc
        ctx.fillStyle=hasPerson?col[0]+"88":col[0]+"15";
        ctx.strokeStyle=hasPerson?col[0]:col[0]+"44";
        ctx.lineWidth=1;
        ctx.beginPath();ctx.arc(cx,cy,r2,e.sa,e.ea);ctx.arc(cx,cy,r1,e.ea,e.sa,true);ctx.closePath();ctx.fill();ctx.stroke();

        // No-data marker
        if(!hasPerson&&(e.ea-e.sa)>0.05){
          var mAngle=(e.sa+e.ea)/2,mRad=(r1+r2)/2;
          var mx=cx+mRad*Math.cos(mAngle),my=cy+mRad*Math.sin(mAngle);
          ctx.fillStyle=col[0]+"66";ctx.font="bold "+Math.max(8,12*z)+"px Arial";ctx.textAlign="center";ctx.textBaseline="middle";
          ctx.fillText("+",mx,my);
        }

        if(hasPerson){
          var ind=individuals[e.pid];
          var arcAngle=e.ea-e.sa;
          var midR=(r1+r2)/2;
          var rWidth=r2-r1;

          // Store for click hit testing
          arcs.push({pid:e.pid,r1:r1,r2:r2,sa:e.sa,ea:e.ea});


          // Text along arc - characters follow the curve
          var arcLen=arcAngle*midR;
          if(arcLen>12){
            var fs=Math.min(rWidth*0.3, arcLen*0.11)*Math.max(1,z*0.3+0.7);
            fs=Math.max(6,Math.min(fs,22*z));

            // Build display text
            var fullNm=ind.name||"Unknown";
            var givenNm=ind.givenName||fullNm.split(" ")[0]||"?";
            var surNm=ind.surname||"";
            var by=ind.birthDate?(ind.birthDate.match(/\d{4}/)||[""])[0]:"";
            var dy=ind.deathDate?(ind.deathDate.match(/\d{4}/)||[""])[0]:"";
            var dateStr=by?"f."+by+(dy?" - "+dy:""):"";

            // Helper: draw text curved along an arc at given radius
            function drawArcText(text,radius,fontSize,bold,color){
              ctx.font=(bold?"bold ":"")+fontSize+"px Arial";
              ctx.fillStyle=color;ctx.textAlign="center";ctx.textBaseline="middle";
              var textW=ctx.measureText(text).width;
              var availArc=arcAngle*0.88; // leave some padding
              var textAngle=textW/radius;
              if(textAngle>availArc){
                // Truncate text to fit
                while(text.length>1&&ctx.measureText(text+"..").width/radius>availArc)text=text.slice(0,-1);
                text=text+"..";
                textW=ctx.measureText(text).width;
                textAngle=textW/radius;
              }
              var ma2=(e.sa+e.ea)/2;
              // Determine if text should go clockwise or counter-clockwise
              // Top half: text goes left-to-right (clockwise)  
              // Bottom half: text goes right-to-left to stay readable
              var isBottom=Math.sin(ma2)>0;
              var charAngleStart;
              if(isBottom){
                // Read right-to-left along arc (counter-clockwise from perspective)
                charAngleStart=ma2+textAngle/2;
              } else {
                charAngleStart=ma2-textAngle/2;
              }
              for(var ci2=0;ci2<text.length;ci2++){
                var ch=text[ci2];
                var chW=ctx.measureText(ch).width;
                var chAngle=chW/radius;
                var a2;
                if(isBottom){
                  a2=charAngleStart-chAngle/2;
                  charAngleStart-=chAngle;
                } else {
                  a2=charAngleStart+chAngle/2;
                  charAngleStart+=chAngle;
                }
                var tx2=cx+radius*Math.cos(a2),ty2=cy+radius*Math.sin(a2);
                ctx.save();ctx.translate(tx2,ty2);
                if(isBottom){ctx.rotate(a2-Math.PI/2);}
                else{ctx.rotate(a2+Math.PI/2);}
                ctx.fillText(ch,0,0);
                ctx.restore();
              }
            }

            // Decide layout based on ring width
            var lineH=fs*1.2;
            var numLines=Math.floor(rWidth/(lineH));
            numLines=Math.max(1,Math.min(numLines,3));

            if(numLines>=2&&arcLen>30){
              // Line 1: name at inner radius, Line 2: date or surname at outer
              var nameR=midR-lineH*0.4;
              var dateR=midR+lineH*0.4;
              ctx.font="bold "+fs+"px Arial";
              var nm=fullNm;
              if(ctx.measureText(nm).width/(arcAngle*0.88*nameR)>1){nm=givenNm+(surNm?" "+surNm.charAt(0)+".":"");}
              if(ctx.measureText(nm).width/(arcAngle*0.88*nameR)>1){nm=givenNm;}
              drawArcText(nm,nameR,fs,true,"#fff");
              if(dateStr)drawArcText(dateStr,dateR,Math.max(5,fs*0.78),false,"#dde");
            } else if(numLines>=3&&arcLen>50){
              var r_1=midR-lineH*0.7;
              var r_2=midR;
              var r_3=midR+lineH*0.7;
              drawArcText(givenNm,r_1,fs,true,"#fff");
              if(surNm)drawArcText(surNm,r_2,fs*0.9,false,"#fff");
              if(dateStr)drawArcText(dateStr,r_3,Math.max(5,fs*0.75),false,"#dde");
            } else {
              // Single line
              ctx.font="bold "+fs+"px Arial";
              var nm3=fullNm;
              if(ctx.measureText(nm3).width/(arcAngle*0.88*midR)>1){nm3=givenNm;}
              if(ctx.measureText(nm3).width/(arcAngle*0.88*midR)>1){nm3=nm3.substring(0,Math.max(1,Math.floor(arcLen/(fs*0.65))));}
              drawArcText(nm3,midR,fs,true,"#fff");
            }
          }
        }
      }
    }

    arcsRef.current=arcs;

    // Center circle
    ctx.fillStyle="#1a2744";ctx.strokeStyle="#4a9eff";ctx.lineWidth=2.5;
    ctx.beginPath();ctx.arc(cx,cy,baseR,0,Math.PI*2);ctx.fill();ctx.stroke();
    if(selInd){
      ctx.fillStyle="#fff";ctx.font="bold "+Math.max(11,14*z)+"px Arial";ctx.textAlign="center";ctx.textBaseline="middle";
      var sn=(selInd.givenName||selInd.name||"").split(" ");
      ctx.fillText(sn[0]||"",cx,cy-10*z);
      if(sn[1])ctx.fillText(sn[1],cx,cy+6*z);
      var sby=selInd.birthDate?(selInd.birthDate.match(/\d{4}/)||[""])[0]:"";
      if(sby){ctx.fillStyle="#99a";ctx.font=Math.max(9,10*z)+"px Arial";ctx.fillText("f."+sby,cx,cy+22*z);}
    }

    // HUD
    ctx.fillStyle="#8899aa";ctx.font="11px Arial";ctx.textBaseline="top";ctx.textAlign="left";
    ctx.fillText((mode==="descendants"?"Descendants":"Fan Chart")+" \u00b7 "+(selInd?selInd.name:""),10,10);
    ctx.fillStyle="#556";ctx.font="9px Arial";
    ctx.fillText("Click arc to inspect \u00b7 Scroll to zoom \u00b7 Drag to pan",10,26);
  },[individuals,families,selectedId,photoUrls,mode,getParents,getChildren]);

  useEffect(function(){drawFan();},[drawFan]);

  useEffect(function(){
    var cv=cvRef.current;if(!cv)return;
    function onW(e){e.preventDefault();var v=viewRef.current;v.zoom=Math.max(0.3,Math.min(5.0,v.zoom+e.deltaY*-0.002));drawFan();}
    function onD(e){var v=viewRef.current;v.dragging=true;v.sx=e.clientX;v.sy=e.clientY;v.scx=v.cx;v.scy=v.cy;v.clickX=e.clientX;v.clickY=e.clientY;}
    function onM(e){var v=viewRef.current;if(v.dragging){v.cx=v.scx+(e.clientX-v.sx);v.cy=v.scy+(e.clientY-v.sy);drawFan();}}
    function onU(){viewRef.current.dragging=false;}
    function onClick(e){
      var v=viewRef.current;
      var movedDist=Math.abs(e.clientX-(v.clickX||0))+Math.abs(e.clientY-(v.clickY||0));
      if(movedDist>5)return;
      var rect=cv.getBoundingClientRect();
      var mx=e.clientX-rect.left,my=e.clientY-rect.top;
      var cxC=cv.clientWidth/2+v.cx;
      var cyC=cv.clientHeight/2+v.cy;
      var dx=mx-cxC,dy=my-cyC;
      var dist=Math.sqrt(dx*dx+dy*dy);
      var angle=Math.atan2(dy,dx);if(angle<0)angle+=Math.PI*2;
      var z2=v.zoom,baseR2=45*z2;
      if(dist<baseR2){if(props.onInspect)props.onInspect(selectedId);return;}
      var arcs=arcsRef.current;
      var best=null,bestDist=999;
      for(var ai=0;ai<arcs.length;ai++){
        var a=arcs[ai];
        if(dist>=a.r1&&dist<=a.r2){
          var sa2=a.sa%(Math.PI*2);if(sa2<0)sa2+=Math.PI*2;
          var ea2=a.ea%(Math.PI*2);if(ea2<0)ea2+=Math.PI*2;
          var inArc=false;
          if(ea2>sa2){inArc=angle>=sa2&&angle<=ea2;}
          else{inArc=angle>=sa2||angle<=ea2;}
          if(inArc){if(props.onInspect)props.onInspect(a.pid);return;}
          var midA=(a.sa+a.ea)/2%(Math.PI*2);if(midA<0)midA+=Math.PI*2;
          var aDiff=Math.abs(angle-midA);if(aDiff>Math.PI)aDiff=Math.PI*2-aDiff;
          if(aDiff<bestDist){bestDist=aDiff;best=a.pid;}
        }
      }
      if(best){if(props.onInspect)props.onInspect(best);return;}
      
    }
    cv.addEventListener("wheel",onW,{passive:false});cv.addEventListener("mousedown",onD);
    window.addEventListener("mousemove",onM);window.addEventListener("mouseup",onU);
    cv.addEventListener("click",onClick);
    return function(){cv.removeEventListener("wheel",onW);cv.removeEventListener("mousedown",onD);window.removeEventListener("mousemove",onM);window.removeEventListener("mouseup",onU);cv.removeEventListener("click",onClick);};
  },[drawFan,selectedId]);

  return (<div style={{width:"100%",height:"100%",position:"relative"}}>
    <canvas ref={cvRef} style={{width:"100%",height:"100%",display:"block",cursor:"grab"}}/>
    </div>);
}

function MapView(props) {
  var cvRef=useRef(null), clickAreas=useRef([]), wmsDebounceRef=useRef(null), wmsAbortRef=useRef(null);
  var viewRef=useRef({cx:11.75,cy:58.15,zoom:9,dragging:false,sx:0,sy:0,scx:0,scy:0});
  var tileCache=useRef({});
  var layerRef=useRef("osm");
  var tileErrRef=useRef({ok:0,err:0});
  var individuals=props.individuals,year=props.year,selId=props.selectedId,onSelect=props.onSelect,extraLocs=props.extraLocs||{},buildPersonLocations=props.buildPersonLocations,focusLat=props.focusLat,focusLon=props.focusLon,focusZoom=props.focusZoom,followPersonId=props.followPersonId,followYear=props.followYear,photoUrls=props.photoUrls||{},placeUrls=props.placeUrls||{},onPhotoClick=props.onPhotoClick;
  var s13=useState("osm"),mapLayer=s13[0],setMapLayer=s13[1];
  var s14=useState(null),hoverPerson=s14[0],setHoverPerson=s14[1]; // {id,name,x,y,photos}
  var hoverRef=useRef(null);
  var overTooltipRef=useRef(false);

  // Tile sources
  var lmKeyInit=function(){try{var r=localStorage.getItem('slakttrads_lmkey');return r||"";}catch(e){return "";}};
  var sLM=useState(lmKeyInit()),lmKey=sLM[0],setLmKey=sLM[1];
  var sLMconf=useState(false),showLMConf=sLMconf[0],setShowLMConf=sLMconf[1];

  // WMS BBOX: unproject the four canvas corners to get exact geographic extent
  function wmsBbox(v,W,H){
    var tl=unproject(0,0,W,H,v);     // top-left pixel
    var br=unproject(W,H,W,H,v);     // bottom-right pixel
    var minLon=tl.lon,maxLon=br.lon;
    var minLat=br.lat,maxLat=tl.lat;
    minLat=Math.max(-85,minLat);maxLat=Math.min(85,maxLat);
    return minLon.toFixed(6)+","+minLat.toFixed(6)+","+maxLon.toFixed(6)+","+maxLat.toFixed(6);
  }

  var TILE_SOURCES={
    osm:{name:"Standard",url:function(z,x,y){var s=["a","b","c"][(x+y)%3];return"https://"+s+".tile.openstreetmap.org/"+z+"/"+x+"/"+y+".png";},attr:"© OpenStreetMap"},
    topo:{name:"Topo",url:function(z,x,y){var s=["a","b","c"][(x+y)%3];return"https://"+s+".tile.opentopomap.org/"+z+"/"+x+"/"+y+".png";},attr:"© OpenTopoMap"},
    cycle:{name:"Terrain",url:function(z,x,y){return"https://tile.thunderforest.com/landscape/"+z+"/"+x+"/"+y+".png?apikey=6170aad10dfd42a38d4d8c709a536f38";},attr:"© Thunderforest"},
    ekon:{name:"Ekon.karta",type:"wms",
      wmsUrl:function(bbox,W,H){var pr=Math.min(window.devicePixelRatio||1,2);var mw=Math.min(Math.round(W*pr),1024),mh=Math.min(Math.round(H*pr),1024);return"/api/wms-proxy?service=ekon&bbox="+encodeURIComponent(bbox)+"&w="+mw+"&h="+mh;},
      attr:"© Lantmäteriet CC0"},
    ortho60:{name:"Flygfoto 1960",type:"wms",
      wmsUrl:function(bbox,W,H){var pr=Math.min(window.devicePixelRatio||1,2);var mw=Math.min(Math.round(W*pr),1024),mh=Math.min(Math.round(H*pr),1024);return"/api/wms-proxy?service=ortho60&bbox="+encodeURIComponent(bbox)+"&w="+mw+"&h="+mh;},
      attr:"© Lantmäteriet"},
    ortho75:{name:"Flygfoto 1975",type:"wms",
      wmsUrl:function(bbox,W,H){var pr=Math.min(window.devicePixelRatio||1,2);var mw=Math.min(Math.round(W*pr),1024),mh=Math.min(Math.round(H*pr),1024);return"/api/wms-proxy?service=ortho75&bbox="+encodeURIComponent(bbox)+"&w="+mw+"&h="+mh;},
      attr:"© Lantmäteriet"},

  };

  // Slippy map math (Web Mercator)
  function lon2tileX(lon,z){return((lon+180)/360)*Math.pow(2,z);}
  function lat2tileY(lat,z){return(1-Math.log(Math.tan(lat*Math.PI/180)+1/Math.cos(lat*Math.PI/180))/Math.PI)/2*Math.pow(2,z);}
  function tileX2lon(x,z){return x/Math.pow(2,z)*360-180;}
  function tileY2lat(y,z){var n=Math.PI-2*Math.PI*y/Math.pow(2,z);return 180/Math.PI*Math.atan(0.5*(Math.exp(n)-Math.exp(-n)));}

  function project(lat,lon,W,H,v){var z=v.zoom;var cxT=lon2tileX(v.cx,z),cyT=lat2tileY(v.cy,z);return{x:W/2+(lon2tileX(lon,z)-cxT)*256,y:H/2+(lat2tileY(lat,z)-cyT)*256};}
  function unproject(px,py,W,H,v){var z=v.zoom;var cxT=lon2tileX(v.cx,z),cyT=lat2tileY(v.cy,z);return{lon:tileX2lon(cxT+(px-W/2)/256,z),lat:tileY2lat(cyT+(py-H/2)/256,z)};}

  var alive=useMemo(function(){if(!individuals)return[];var res=[];for(var id in individuals){var ind=individuals[id];var by=parseYear(ind.birthDate),dy=parseYear(ind.deathDate);if(!by)continue;if(year<by||(dy&&year>dy))continue;
    // Use buildPersonLocations if available for accurate timeline positions
    var loc=null,pl="";
    if(buildPersonLocations&&extraLocs!==undefined){
      ind.id=id;
      var personLocs=buildPersonLocations(ind,extraLocs||{});
      // Find best loc for this year
      var best=null;
      for(var pi=0;pi<personLocs.length;pi++){
        var pl2=personLocs[pi];
        if(!pl2.lat||!pl2.lon)continue;
        var pFrom=pl2.from||by,pTo=pl2.to||(dy||year+1);
        if(year>=pFrom&&year<=pTo){best=pl2;break;}
        if(!best&&year>=pFrom)best=pl2; // fallback: most recent past loc
      }
      if(!best&&personLocs.length>0){
        // use first with coords
        for(var pi2=0;pi2<personLocs.length;pi2++){if(personLocs[pi2].lat){best=personLocs[pi2];break;}}
      }
      if(best){loc={lat:best.lat,lon:best.lon};pl=best.place||"";}
    }
    // Fallback to geocoding
    if(!loc){
      if(dy&&year>=dy-5&&ind.deathPlace){loc=geocodePlace(ind.deathPlace);pl=ind.deathPlace;}
      if(!loc&&ind.birthPlace){loc=geocodePlace(ind.birthPlace);pl=ind.birthPlace;}
    }
    if(!loc)continue;
    res.push({id:id,name:ind.name,sex:ind.sex,lat:loc.lat,lon:loc.lon,place:pl,age:year-by});}return res;},[individuals,year,extraLocs,buildPersonLocations]);

  function loadTile(z,tx,ty,layer,cb){
    var key=layer+"/"+z+"/"+tx+"/"+ty;
    if(tileCache.current[key]){if(tileCache.current[key].loaded)cb(tileCache.current[key]);return;}
    var src=TILE_SOURCES[layer];
    var img=new Image();if(!(src&&src.noCors))img.crossOrigin="anonymous";img.loaded=false;
    tileCache.current[key]=img;
    img.onload=function(){img.loaded=true;tileErrRef.current.ok++;cb(img);};
    img.onerror=function(){tileErrRef.current.err++;cb(null);};
    if(src)img.src=src.url(z,tx,ty);
  }

  var drawMap=useCallback(function(){
    var cv=cvRef.current;if(!cv)return;
    var ct=cv.parentElement,W=ct.clientWidth,H=ct.clientHeight;
    cv.width=W*2;cv.height=H*2;cv.style.width=W+"px";cv.style.height=H+"px";
    var ctx=cv.getContext("2d");ctx.scale(2,2);
    var v=viewRef.current,areas=[];
    var z=Math.round(v.zoom);
    var layer=layerRef.current;

    var cxTile=lon2tileX(v.cx,z),cyTile=lat2tileY(v.cy,z);
    var tilesX=Math.ceil(W/256)+2,tilesY=Math.ceil(H/256)+2;
    var startTX=Math.floor(cxTile-tilesX/2),startTY=Math.floor(cyTile-tilesY/2);
    var maxTile=Math.pow(2,z);

    ctx.fillStyle="#a8d5f2";ctx.fillRect(0,0,W,H);

    var srcDef=TILE_SOURCES[layer];
    if(srcDef&&srcDef.type==="wms"){
      var bbox=wmsBbox(v,W,H);
      var wmsUrl=srcDef.wmsUrl(bbox,W,H);
      if(!wmsUrl){
        ctx.fillStyle="rgba(40,40,40,0.85)";ctx.fillRect(0,0,W,H);
        ctx.fillStyle="#ffa94d";ctx.font="bold 12px Arial";ctx.textAlign="center";ctx.textBaseline="middle";
        ctx.fillText("Lantmäteriets flygfoton kräver API-nyckel",W/2,H/2);
      } else {
        var wmsKey=layer+"/wms/"+bbox;
        var wmsCache=tileCache.current[wmsKey];
        // Find most recent loaded image to show while loading
        var fallbackImg=null;
        for(var fk in tileCache.current){
          var fe=tileCache.current[fk];
          if(fe&&fe.loaded&&fk.indexOf(layer+"/wms/")===0){fallbackImg=fe;break;}
        }
        if(wmsCache&&wmsCache.loaded){
          ctx.drawImage(wmsCache,0,0,W,H);
        } else {
          // Show fallback (old zoom level) while loading
          if(fallbackImg){ctx.drawImage(fallbackImg,0,0,W,H);}
          else{ctx.fillStyle="#dce8dc";ctx.fillRect(0,0,W,H);}
          ctx.fillStyle="rgba(0,0,0,0.3)";ctx.fillRect(W-110,4,106,18);
          ctx.fillStyle="#fff";ctx.font="10px Arial";ctx.textAlign="right";ctx.textBaseline="top";
          ctx.fillText("Laddar "+srcDef.name+"...",W-6,7);
          if(wmsCache!=="loading"){
            tileCache.current[wmsKey]="loading";
            // Safety: clear stuck loading entry after 10s so it can retry
            setTimeout(function(){if(tileCache.current[wmsKey]==="loading")delete tileCache.current[wmsKey];},10000);
            // Debounce: wait 250ms after last pan/zoom before fetching
            if(wmsDebounceRef.current)clearTimeout(wmsDebounceRef.current);
            wmsDebounceRef.current=setTimeout(function(){
              wmsDebounceRef.current=null;
              if(wmsAbortRef.current)wmsAbortRef.current.abort();
              wmsAbortRef.current=new AbortController();
              var signal=wmsAbortRef.current.signal;
              fetch(wmsUrl,{signal:signal}).then(function(resp){
                var ct=resp.headers.get("content-type")||"";
                if(!resp.ok||ct.indexOf("image")<0){
                  return resp.text().then(function(txt){
                    delete tileCache.current[wmsKey];
                    console.error("WMS error:",resp.status,txt.substring(0,200));
                  });
                }
                return resp.blob().then(function(blob){
                  var url2=URL.createObjectURL(blob);
                  var img2=new Image();img2.loaded=false;
                  img2.onload=function(){
                    img2.loaded=true;
                    tileCache.current[wmsKey]=img2;
                    // Keep only 5 WMS images to avoid memory bloat
                    var wmsKeys=Object.keys(tileCache.current).filter(function(k){return k.indexOf('/wms/')>=0&&tileCache.current[k]&&tileCache.current[k].loaded;});
                    if(wmsKeys.length>5){delete tileCache.current[wmsKeys[0]];}
                    drawMap();
                  };
                  img2.src=url2;
                });
              }).catch(function(e){if(e.name!=="AbortError"){delete tileCache.current[wmsKey];console.error("WMS:",e);}});
            },250);
          }
        }
      }
    } else {
    var scale=Math.pow(2,v.zoom-z);
    for(var tx=startTX;tx<startTX+tilesX+1;tx++){
      for(var ty=startTY;ty<startTY+tilesY+1;ty++){
        if(ty<0||ty>=maxTile)continue;
        var wrappedTX=((tx%maxTile)+maxTile)%maxTile;
        var px=W/2+(tx-cxTile)*256*scale;
        var py=H/2+(ty-cyTile)*256*scale;
        var tileSize=256*scale;
        var key=layer+"/"+z+"/"+wrappedTX+"/"+ty;
        var cached=tileCache.current[key];
        if(cached&&cached.loaded){ctx.drawImage(cached,px,py,tileSize,tileSize);}
        else{ctx.fillStyle="#c8e6c0";ctx.fillRect(px,py,tileSize,tileSize);ctx.strokeStyle="#b0d8a0";ctx.strokeRect(px,py,tileSize,tileSize);loadTile(z,wrappedTX,ty,layer,function(){drawMap();});}
      }
    }
    } // end tile branch

    // Attribution
    var srcInfo=TILE_SOURCES[layer]||TILE_SOURCES.osm;
    ctx.fillStyle="rgba(255,255,255,0.7)";ctx.fillRect(W-160,H-16,160,16);
    ctx.fillStyle="#333";ctx.font="9px Arial";ctx.textAlign="right";ctx.textBaseline="bottom";
    ctx.fillText(srcInfo.attr+" contributors",W-4,H-3);
    if(tileErrRef.current.err>0&&tileErrRef.current.ok===0){ctx.fillStyle="rgba(200,40,40,0.9)";ctx.font="bold 11px Arial";ctx.textAlign="center";ctx.fillText("Kartlagret saknas ("+tileErrRef.current.err+" tiles) \u2014 tiles_ekon/ beh\u00f6ver deployas med appen",W/2,40);}

    // Project function for markers
    function p(lat,lon){return project(lat,lon,W,H,v);}

    // Group people by location
    var locG={};
    for(var ai=0;ai<alive.length;ai++){var pr=alive[ai];var lk=Math.round(pr.lat*100)+","+Math.round(pr.lon*100);if(!locG[lk])locG[lk]=[];locG[lk].push(pr);}

    var dotR=Math.max(4,3+v.zoom*0.5);
    for(var gk in locG){var grp=locG[gk];
      var bp=p(grp[0].lat,grp[0].lon);
      if(bp.x<-50||bp.x>W+50||bp.y<-50||bp.y>H+50)continue;

      // Cluster if too many at low zoom
      if(grp.length>8&&v.zoom<12){
        ctx.beginPath();ctx.arc(bp.x,bp.y,14,0,Math.PI*2);
        ctx.fillStyle="rgba(74,158,255,0.85)";ctx.fill();
        ctx.strokeStyle="#fff";ctx.lineWidth=2;ctx.stroke();
        ctx.fillStyle="#fff";ctx.font="bold 10px Arial";ctx.textAlign="center";ctx.textBaseline="middle";
        ctx.fillText(grp.length+"",bp.x,bp.y);
        ctx.fillStyle="rgba(0,0,0,0.6)";ctx.font="bold 8px Arial";ctx.textBaseline="top";
        ctx.fillText(grp[0].place.split(",")[0].split("(")[0].trim(),bp.x,bp.y+17);
        for(var gi=0;gi<grp.length;gi++)areas.push({x:bp.x,y:bp.y,r:16,id:grp[gi].id,place:grp[gi].place||""});
        continue;
      }

      for(var gi2=0;gi2<grp.length;gi2++){
        var pp=grp[gi2],pt=p(pp.lat,pp.lon);
        var ang=(gi2/Math.max(grp.length,1))*Math.PI*2;
        var oR=grp.length>1?(dotR*2.5+gi2*dotR*0.6):0;
        var px2=pt.x+Math.cos(ang)*oR,py2=pt.y+Math.sin(ang)*oR;
        var isSel=pp.id===selId;
        var col=pp.sex==="M"?C.male:pp.sex==="F"?C.female:C.unknown;
        var r=isSel?dotR+3:dotR;

        // Shadow
        ctx.beginPath();ctx.arc(px2+1,py2+1,r+1,0,Math.PI*2);ctx.fillStyle="rgba(0,0,0,0.2)";ctx.fill();
        // Dot
        ctx.beginPath();ctx.arc(px2,py2,r,0,Math.PI*2);ctx.fillStyle=isSel?C.highlight:col;ctx.fill();
        ctx.strokeStyle=isSel?"#333":"#fff";ctx.lineWidth=isSel?2.5:1.5;ctx.stroke();

        // Initials (always show)
        ctx.fillStyle="#fff";ctx.font="bold "+Math.max(7,Math.min(11,dotR*1.2))+"px Arial";ctx.textAlign="center";ctx.textBaseline="middle";
        ctx.fillText(pp.name.split(" ").map(function(w){return w[0]||"";}).join("").substring(0,2),px2,py2);

        // Name label at higher zoom
        if(v.zoom>=11){
          ctx.fillStyle=isSel?"#333":"rgba(0,0,0,0.7)";
          ctx.font=(isSel?"bold ":"")+"10px Arial";ctx.textAlign="center";ctx.textBaseline="top";
          ctx.fillText(pp.name.split(" ")[0],px2,py2+r+3);
        }
        // Age at even higher zoom
        if(v.zoom>=13){
          ctx.fillStyle="rgba(0,0,0,0.4)";ctx.font="8px Arial";
          ctx.fillText("age "+pp.age,px2,py2+r+15);
        }

        areas.push({x:px2,y:py2,r:r+4,id:pp.id,place:pp.place||""});
      }
      // Place label at medium zoom
      if(grp.length>0&&grp.length<=8&&v.zoom>=10&&v.zoom<13){
        var gpt=p(grp[0].lat,grp[0].lon);
        ctx.fillStyle="rgba(0,0,0,0.5)";ctx.font="bold 8px Arial";ctx.textAlign="center";
        ctx.fillText(grp[0].place.split(",")[0].split("(")[0].trim(),gpt.x,gpt.y+dotR*2+grp.length*dotR+10);
      }
    }

    // HUD
    ctx.fillStyle="rgba(255,255,255,0.9)";
    ctx.beginPath();ctx.roundRect(8,8,96,56,6);ctx.fill();
    ctx.strokeStyle="#ddd";ctx.lineWidth=0.5;ctx.stroke();
    ctx.fillStyle="#222";ctx.font="bold 24px Arial";ctx.textAlign="left";ctx.textBaseline="top";ctx.fillText(year+"",16,14);
    ctx.fillStyle="#666";ctx.font="11px Arial";ctx.fillText(alive.length+" alive",16,40);

    // Zoom level
    ctx.fillStyle="rgba(255,255,255,0.8)";
    ctx.beginPath();ctx.roundRect(W-56,8,48,22,4);ctx.fill();
    ctx.fillStyle="#555";ctx.font="10px Arial";ctx.textAlign="center";ctx.fillText("z"+v.zoom.toFixed(1),W-32,22);

    clickAreas.current=areas;
  },[alive,year,selId]);

  useEffect(function(){layerRef.current=mapLayer;drawMap();},[mapLayer]);
  useEffect(function(){drawMap();},[drawMap]);
  useEffect(function(){
    if(focusLat&&focusLon){
      var v=viewRef.current;
      v.cx=focusLon;v.cy=focusLat;v.zoom=focusZoom||11;
      drawMap();
    }
  },[focusLat,focusLon,focusZoom]);

  // Follow selected person as year slider moves
  useEffect(function(){
    if(!followPersonId||!individuals||!buildPersonLocations) return;
    var ind=individuals[followPersonId];
    if(!ind) return;
    ind.id=followPersonId;
    var locs=buildPersonLocations(ind,extraLocs);
    if(!locs||!locs.length) return;
    // Find best location for this year — use .from field (buildPersonLocations uses from/to not year)
    var best=null;
    for(var i=0;i<locs.length;i++){
      var loc=locs[i];
      if(loc.lat&&loc.lon){
        if(!best) best=loc;
        var locYear=loc.from?parseInt(loc.from):(loc.year?parseInt(loc.year):null);
        if(locYear&&locYear<=followYear) best=loc;
      }
    }
    if(best&&best.lat&&best.lon){
      var v=viewRef.current;
      // Only pan if not manually dragged recently
      v.cx=best.lon;v.cy=best.lat;
      if(!v.zoom||v.zoom<9) v.zoom=11;
      drawMap();
    }
  },[followYear,followPersonId]);

  // Interaction
  useEffect(function(){
    var cv=cvRef.current;if(!cv)return;
    var v=viewRef.current;
    function clearWmsCache(){
      if(wmsDebounceRef.current){clearTimeout(wmsDebounceRef.current);wmsDebounceRef.current=null;}
      // Abort any in-flight WMS fetch
      if(wmsAbortRef.current){wmsAbortRef.current.abort();wmsAbortRef.current=null;}
      var tc=tileCache.current;
      Object.keys(tc).forEach(function(k){if(k.indexOf('/wms/')>=0)delete tc[k];});
    }
    function onWheel(e){
      e.preventDefault();
      var ct=cv.parentElement,W=ct.clientWidth,H=ct.clientHeight;
      var rect=cv.getBoundingClientRect();
      var mx=e.clientX-rect.left,my=e.clientY-rect.top;
      var before=unproject(mx,my,W,H,v);
      v.zoom=Math.max(6,Math.min(17,v.zoom+(e.deltaY<0?0.3:-0.3)));clearWmsCache();
      var after=unproject(mx,my,W,H,v);
      v.cx-=(after.lon-before.lon);v.cy-=(after.lat-before.lat);
      drawMap();
    }
    function onDown(e){if(e.button===0){v.dragging=true;v.sx=e.clientX;v.sy=e.clientY;v.scx=v.cx;v.scy=v.cy;}}
    function onMove(e){
      var r=cv.getBoundingClientRect(),mx=e.clientX-r.left,my=e.clientY-r.top;
      if(v.dragging){
        var ct=cv.parentElement,W=ct.clientWidth,H=ct.clientHeight;
        var z=v.zoom;
        var dx=(e.clientX-v.sx)/256,dy=(e.clientY-v.sy)/256;
        var scale=Math.pow(2,z-Math.round(z));
        var cxT=lon2tileX(v.scx,z),cyT=lat2tileY(v.scy,z);
        v.cx=tileX2lon(cxT-dx/scale,z);
        v.cy=tileY2lat(cyT-dy/scale,z);
        drawMap();
        if(!overTooltipRef.current) setHoverPerson(null);
        return;
      }
      // Hover detection
      var found=null;
      for(var hi=0;hi<clickAreas.current.length;hi++){
        var a=clickAreas.current[hi],hdx=mx-a.x,hdy=my-a.y;
        if(hdx*hdx+hdy*hdy<(a.r+6)*(a.r+6)){found=a;break;}
      }
      if(found){
        var ind=individuals&&individuals[found.id];
        if(ind){
          var photos=photoUrls[found.id]||[];
          // Place comes directly from the map marker position (already correct for current year)
          var currentPlace=found.place||"";
          var placePhotosForLoc=lookupPlacePhotos(currentPlace,placeUrls);
          var mainPhoto=null;
          if(placePhotosForLoc.length>0){
            mainPhoto=placePhotosForLoc[0];
          } else {
            var placePhotoP=photos.find(function(p){return p.type==="place";});
            var portraitPhoto=photos.find(function(p){return p.type==="portrait";});
            mainPhoto=placePhotoP||portraitPhoto||photos[0]||null;
          }
          setHoverPerson({id:found.id,name:ind.name,x:found.x,y:found.y,photo:mainPhoto,photoCount:photos.length,place:currentPlace,placePhotos:placePhotosForLoc});
        }
      } else {
        if(!overTooltipRef.current) setHoverPerson(null);
      }
    }
    function onUp(){v.dragging=false;drawMap();}
    function onClick(e){
      if(Math.abs(e.clientX-(v.sx||0))>4||Math.abs(e.clientY-(v.sy||0))>4)return;
      var r=cv.getBoundingClientRect(),mx=e.clientX-r.left,my=e.clientY-r.top;
      for(var i=0;i<clickAreas.current.length;i++){var a=clickAreas.current[i],dx=mx-a.x,dy=my-a.y;if(dx*dx+dy*dy<a.r*a.r){onSelect(a.id);return;}}
      onSelect(null);
    }
    function onCtx(e){e.preventDefault();}
    // Touch
    var lastD=0;
    function tS(e){if(e.touches.length===1){v.dragging=true;v.sx=e.touches[0].clientX;v.sy=e.touches[0].clientY;v.scx=v.cx;v.scy=v.cy;}else if(e.touches.length===2){v.dragging=false;lastD=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);}}
    function tM(e){e.preventDefault();
      if(e.touches.length===1&&v.dragging){
        var ct=cv.parentElement,W=ct.clientWidth,H=ct.clientHeight;
        var dx=(e.touches[0].clientX-v.sx)/256,dy=(e.touches[0].clientY-v.sy)/256;
        var cxT=lon2tileX(v.scx,v.zoom),cyT=lat2tileY(v.scy,v.zoom);
        v.cx=tileX2lon(cxT-dx,v.zoom);v.cy=tileY2lat(cyT-dy,v.zoom);
        drawMap();
      }else if(e.touches.length===2){
        var d=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);
        v.zoom=Math.max(6,Math.min(17,v.zoom+Math.log2(d/lastD)));lastD=d;drawMap();
      }
    }
    function tE(){v.dragging=false;drawMap();}
    cv.addEventListener("wheel",onWheel,{passive:false});cv.addEventListener("mousedown",onDown);cv.addEventListener("mousemove",onMove);cv.addEventListener("mouseup",onUp);cv.addEventListener("click",onClick);cv.addEventListener("contextmenu",onCtx);
    cv.addEventListener("touchstart",tS,{passive:false});cv.addEventListener("touchmove",tM,{passive:false});cv.addEventListener("touchend",tE);
    return function(){cv.removeEventListener("wheel",onWheel);cv.removeEventListener("mousedown",onDown);cv.removeEventListener("mousemove",onMove);cv.removeEventListener("mouseup",onUp);cv.removeEventListener("click",onClick);cv.removeEventListener("contextmenu",onCtx);cv.removeEventListener("touchstart",tS);cv.removeEventListener("touchmove",tM);cv.removeEventListener("touchend",tE);};
  },[drawMap,onSelect]);

  useEffect(function(){function r(){drawMap();}window.addEventListener("resize",r);return function(){window.removeEventListener("resize",r);};},[drawMap]);

  function fitAll(){
    if(!alive.length)return;
    var mnLat=90,mxLat=-90,mnLon=180,mxLon=-180;
    for(var i=0;i<alive.length;i++){if(alive[i].lat<mnLat)mnLat=alive[i].lat;if(alive[i].lat>mxLat)mxLat=alive[i].lat;if(alive[i].lon<mnLon)mnLon=alive[i].lon;if(alive[i].lon>mxLon)mxLon=alive[i].lon;}
    var v=viewRef.current;
    v.cx=(mnLon+mxLon)/2;v.cy=(mnLat+mxLat)/2;
    var latSpan=Math.max(mxLat-mnLat,0.1)+0.5;var lonSpan=Math.max(mxLon-mnLon,0.1)+0.5;
    v.zoom=Math.max(4,Math.min(13,Math.min(Math.log2(180/latSpan),Math.log2(360/lonSpan))));
    drawMap();
  }

  return (<div style={{width:"100%",height:"100%",position:"relative"}}>
    <canvas ref={cvRef} style={{width:"100%",height:"100%",display:"block",cursor:"grab"}}/>
    {hoverPerson&&(function(){
      var cvEl=cvRef.current;
      var W=cvEl?cvEl.parentElement.clientWidth:800;
      var H=cvEl?cvEl.parentElement.clientHeight:600;
      var tx=hoverPerson.x+20,ty=hoverPerson.y-10;
      if(tx+190>W)tx=hoverPerson.x-210;
      if(ty+180>H)ty=H-184;
      if(ty<4)ty=4;
      var hphotos=photoUrls[hoverPerson.id]||[];
      return(<div style={{position:"absolute",left:tx,top:ty,width:190,background:"rgba(22,27,34,0.97)",borderRadius:10,border:"1px solid #30363d",boxShadow:"0 4px 20px rgba(0,0,0,0.5)",pointerEvents:"all",overflow:"hidden",zIndex:50,cursor:"default"}}
        onMouseEnter={function(){overTooltipRef.current=true;}}
        onMouseLeave={function(){overTooltipRef.current=false;setHoverPerson(null);}}>
        {hoverPerson.photo
          ?<img src={hoverPerson.photo.url} style={{width:"100%",height:220,objectFit:"cover",display:"block",cursor:"pointer"}}
              onClick={function(){if(onPhotoClick&&hphotos.length)onPhotoClick(hphotos,Math.max(0,hphotos.indexOf(hoverPerson.photo)));}}
              onError={function(e){e.target.style.display="none";}}/>
          :<div style={{height:40,display:"flex",alignItems:"center",justifyContent:"center",color:"#8b949e",fontSize:18}}>📷</div>}
        <div style={{padding:"7px 9px 6px"}}>
          <div style={{fontSize:12,fontWeight:600,color:"#c9d1d9",marginBottom:2,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{hoverPerson.name}</div>
          {hoverPerson.place&&<div style={{fontSize:10,color:"#8b949e",marginBottom:3,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{hoverPerson.place}</div>}
          {(function(){
            var galleryPhotos=hoverPerson.placePhotos&&hoverPerson.placePhotos.length>0?hoverPerson.placePhotos:hphotos;
            if(galleryPhotos.length>1) return(<div style={{display:"flex",gap:3,overflowX:"auto",paddingBottom:2}}>
              {galleryPhotos.map(function(ph,pi){return(<img key={pi} src={ph.url} style={{width:32,height:32,borderRadius:3,objectFit:"cover",border:"2px solid #66d9a0",flexShrink:0,cursor:"pointer"}}
                onClick={function(){if(onPhotoClick)onPhotoClick(galleryPhotos,pi);}}
                onError={function(e){e.target.style.display="none";}}/>);})}
            </div>);
          })()}
        </div>
      </div>);
    })()}
    <div style={{position:"absolute",top:8,right:8,display:"flex",gap:2,background:"rgba(255,255,255,0.9)",borderRadius:6,padding:2,boxShadow:"0 1px 4px rgba(0,0,0,0.2)"}}>
      {Object.keys(TILE_SOURCES).map(function(k){var sdef=TILE_SOURCES[k];return(<button key={k} onClick={function(){tileErrRef.current={ok:0,err:0};Object.keys(tileCache.current).forEach(function(tk){if(tk.indexOf('/wms/')>=0)delete tileCache.current[tk];});setMapLayer(k);}} style={{padding:"3px 8px",fontSize:9,fontWeight:mapLayer===k?700:400,border:"none",borderRadius:4,cursor:"pointer",background:mapLayer===k?"#4a9eff":"transparent",color:mapLayer===k?(sdef.needsKey&&!lmKey?"#ffa94d":"#fff"):(sdef.needsKey&&!lmKey?"#ffa94d55":"#555")}}>{sdef.name}{sdef.needsKey&&!lmKey?" 🔑":""}</button>);})}

      {showLMConf&&(<div style={{position:"absolute",top:32,right:4,background:"#161b22",border:"1px solid #30363d",borderRadius:8,padding:"10px 12px",zIndex:50,minWidth:280,boxShadow:"0 4px 20px rgba(0,0,0,0.5)"}}>
        <div style={{fontSize:10,color:"#8b949e",marginBottom:6,fontWeight:700,letterSpacing:1,textTransform:"uppercase"}}>Lantmäteriet API-nyckel</div>
        <input type="password" value={lmKey} placeholder="Klistra in din LM-nyckel..."
          onChange={function(e){setLmKey(e.target.value);try{localStorage.setItem('slakttrads_lmkey',e.target.value);}catch(ex){}}}
          style={{width:"100%",boxSizing:"border-box",background:"rgba(255,255,255,0.05)",border:"1px solid #30363d",borderRadius:5,padding:"5px 8px",color:"#c9d1d9",fontSize:11,outline:"none"}}/>
        <div style={{fontSize:9,color:"#8b949e",marginTop:4}}>Krävs för Flygfoto 1960/1975. Hämta på opendata.lantmateriet.se</div>
        {lmKey&&<div style={{fontSize:9,color:"#66d9a0",marginTop:3}}>✓ Nyckel sparad</div>}
      </div>)}
      <button onClick={fitAll} style={{padding:"3px 8px",fontSize:9,fontWeight:600,border:"none",borderRadius:4,cursor:"pointer",background:"#66d9a0",color:"#fff"}} title="Zoom to show all people">Fit All</button>
      {selId&&<button onClick={function(){
        var sel2=alive.find(function(a){return a.id===selId;});
        if(!sel2) return;
        var v=viewRef.current;
        v.cx=sel2.lon;v.cy=sel2.lat;v.zoom=14;
        Object.keys(tileCache.current).forEach(function(k){if(k.indexOf('/wms/')>=0)delete tileCache.current[k];});
        drawMap();
      }} style={{padding:"3px 8px",fontSize:9,fontWeight:600,border:"none",borderRadius:4,cursor:"pointer",background:"#4a9eff",color:"#fff"}} title="Zooma in på vald person">Zoom till vald</button>}
    </div>
  </div>);
}

/* ═══ MAIN APP ════════════════════════════════════════════════ */
// ═══ PLACES LEAFLET MAP ══════════════════════════════════
function PlacesLeafletMap({locs,editIdx,onCoords}){
  const {useRef,useEffect}=React;
  var mapRef=useRef(null);
  var leafRef=useRef(null);
  var markerRef=useRef([]);
  var clickMarkerRef=useRef(null);

  useEffect(function(){
    if(!mapRef.current)return;
    if(typeof L==='undefined'){
      // Leaflet not loaded - show fallback
      mapRef.current.innerHTML='<div style="display:flex;align-items:center;justify-content:center;height:100%;color:#888;font-size:12px;">Laddar karta...</div>';
      return;
    }
    // Init map once
    if(!leafRef.current){
      var clat=58.08,clon=11.58;
      var withCoords=(locs||[]).filter(function(l){return l.lat&&l.lon;});
      if(withCoords.length>0){
        clat=withCoords.reduce(function(s,l){return s+l.lat;},0)/withCoords.length;
        clon=withCoords.reduce(function(s,l){return s+l.lon;},0)/withCoords.length;
      }
      var m=L.map(mapRef.current).setView([clat,clon],12);
      L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',{
        attribution:'© OpenStreetMap',maxZoom:19
      }).addTo(m);
      // Click to set coordinates
      m.on('click',function(e){
        var lat=parseFloat(e.latlng.lat.toFixed(4)),lon=parseFloat(e.latlng.lng.toFixed(4));
        if(clickMarkerRef.current)m.removeLayer(clickMarkerRef.current);
        clickMarkerRef.current=L.marker([lat,lon],{
          icon:L.divIcon({className:'',html:'<div style="background:#ffd060;width:16px;height:16px;border-radius:50%;border:3px solid #fff;box-shadow:0 2px 6px rgba(0,0,0,0.6)"><div style="position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);color:#000;font-size:10px;font-weight:bold">+</div></div>',iconSize:[16,16],iconAnchor:[8,8]})
        }).addTo(m).bindPopup('<b>'+lat+', '+lon+'</b><br><small>Öppna en plats för att koppla dessa koordinater</small>',{maxWidth:200}).openPopup();
        window._pendingCoords={lat:lat,lon:lon};
        if(typeof window._placesSetCoords==='function'){
          window._placesSetCoords(lat,lon);
          window._pendingCoords=null;
          if(clickMarkerRef.current)clickMarkerRef.current.closePopup();
        }
      });
      leafRef.current=m;
    }
    // Update markers
    var map=leafRef.current;
    markerRef.current.forEach(function(mk){map.removeLayer(mk);});
    markerRef.current=[];
    var typeColors2={birth:'#2ecc71',death:'#e74c3c',resi:'#3498db',residence:'#3498db',emig:'#f39c12',immi:'#9b59b6',chr:'#95a5a6'};
    var withC=(locs||[]).filter(function(l){return l.lat&&l.lon;});
    withC.forEach(function(loc,i){
      var col=typeColors2[loc.type]||'#3498db';
      var isEditing=editIdx===i;
      var mk=L.marker([loc.lat,loc.lon],{
        icon:L.divIcon({className:'',html:'<div style="background:'+col+';width:'+(isEditing?18:12)+'px;height:'+(isEditing?18:12)+'px;border-radius:50%;border:2px solid #fff;box-shadow:0 1px 3px rgba(0,0,0,0.5);'+(isEditing?'outline:2px solid #ffd060;outline-offset:2px':'')+'"></div>',iconSize:[isEditing?18:12,isEditing?18:12],iconAnchor:[isEditing?9:6,isEditing?9:6]})
      }).addTo(map);
      mk.bindTooltip((loc.place||'')+(loc.from?' ('+loc.from+')':''),{permanent:false,direction:'top'});
      markerRef.current.push(mk);
    });
    if(withC.length>0){
      var bounds=L.latLngBounds(withC.map(function(l){return[l.lat,l.lon];}));
      map.fitBounds(bounds,{padding:[20,20],maxZoom:14});
    }
    setTimeout(function(){if(leafRef.current)leafRef.current.invalidateSize();},100);
  },[locs,editIdx]);

  return <div ref={mapRef} style={{height:800,borderRadius:8,overflow:"hidden",border:"1px solid #30363d",marginBottom:12}}/>;
}

// ═══ PLACES EDITOR ═══════════════════════════════════════

/* ═══ PHOTO MANAGER ════════════════════════════════════════════ */
var PHOTO_TYPES=[
  {id:"portrait",label:"Portr\u00e4tt",icon:"\uD83E\uDDD1",color:"#4a9eff"},
  {id:"wedding",label:"Br\u00f6llop",icon:"\uD83D\uDC8D",color:"#ff6b9d"},
  {id:"place",label:"Plats/Hus",icon:"\uD83C\uDFE0",color:"#66d9a0"},
  {id:"group",label:"Grupphoto",icon:"\uD83D\uDC68\u200D\uD83D\uDC69\u200D\uD83D\uDC67",color:"#ffa94d"},
  {id:"document",label:"Dokument",icon:"\uD83D\uDCC4",color:"#9775fa"},
  {id:"other",label:"\u00D6vrigt",icon:"\uD83D\uDCF7",color:"#8899aa"},
];

function PhotoManager(props){
  var individuals=props.individuals,photoUrls=props.photoUrls,setPhotoUrls=props.setPhotoUrls,setPhotoTex=props.setPhotoTex,selectedId=props.selectedId,hasParsedData=props.hasParsedData;
  var _s=useState;
  var s1=_s(selectedId||null),editId=s1[0],setEditId=s1[1];
  var s2=_s(""),search=s2[0],setSearch=s2[1];
  var s3=_s(null),lightbox=s3[0],setLightbox=s3[1];
  var s4=_s(false),dragging=s4[0],setDragging=s4[1];
  var s5=_s(false),uploading=s5[0],setUploading=s5[1];
  var s6=_s(null),uploadErr=s6[0],setUploadErr=s6[1];
  var s7=_s(null),editPhoto=s7[0],setEditPhoto=s7[1];
  var s8=_s(false),showGHConfig=s8[0],setShowGHConfig=s8[1];
  var GH_KEY="hasselon2025";
  var GH_T=[15,9,3,44,52,26,23,55,68,5,92,3,90,54,53,20,35,30,38,52,125,90,84,83,59,4,23,60,42,36,13,20,70,85,3,112,44,88,58,11];
  var GH_R=[5,0,7,0,7,28,29,1,86,31,90,84,27,18,22,31,10,2];
  function xorDec(arr,key){return arr.map(function(c,i){return String.fromCharCode(c^key.charCodeAt(i%key.length));}).join("");}
  var ghInit=function(){
    try{var r=localStorage.getItem('slakttrads_gh');if(r){var p=JSON.parse(r);if(p.token&&p.repo)return p;}}catch(e){}
    return{token:xorDec(GH_T,GH_KEY),repo:xorDec(GH_R,GH_KEY),branch:"main"};
  };
  var s9=_s(ghInit()),ghConfig=s9[0],setGhConfig=s9[1];
  var s10=_s(false),syncing=s10[0],setSyncing=s10[1];
  var s11=_s(null),syncMsg=s11[0],setSyncMsg=s11[1];
  var ghReady=!!(ghConfig.token&&ghConfig.repo);

  useEffect(function(){if(selectedId)setEditId(selectedId);},[selectedId]);

  // Auto-sync once on mount if config is ready
  var didAutoSync=useRef(false);
  useEffect(function(){
    if(ghReady&&!didAutoSync.current){
      didAutoSync.current=true;
      syncFromGitHub(ghConfig);
      syncPlacePhotos(ghConfig);
    }
  },[]);

  function parsePhotoMeta(filename){
    var base=filename.replace(/\.[^.]+$/,"");
    var parts=base.split("_");
    if(parts.length<2) return {gedcomId:null,type:"other",label:base};
    var gedcomId="@"+parts[0]+"@";
    // Format: I2158_01_description or I2158_foto_barn_1_description (legacy)
    var seq=1,descStart=1;
    if(!isNaN(parts[1])&&parts[1].length<=3){
      seq=parseInt(parts[1]);descStart=2;
    } else {
      // Legacy format: find first numeric part as seq
      for(var li=2;li<parts.length;li++){if(!isNaN(parts[li])&&parts[li].length<4){seq=parseInt(parts[li]);descStart=li+1;break;}}
    }
    var descParts=parts.slice(descStart);
    var label=descParts.join(" ").replace(/_/g," ").trim()||base;
    // Detect type from all description words
    var dl=(parts.slice(1).join(" ")).toLowerCase();
    var type="other";
    if(dl.indexOf("brollop")>=0||dl.indexOf("wedding")>=0||dl.indexOf("vigsel")>=0) type="wedding";
    else if(dl.indexOf("plats")>=0||dl.indexOf("hus")>=0||dl.indexOf("gard")>=0||dl.indexOf("torp")>=0||dl.indexOf("gatan")>=0||dl.indexOf("vagen")>=0) type="place";
    else if(dl.indexOf("kyrkbok")>=0||dl.indexOf("husforh")>=0||dl.indexOf("fod")>=0||dl.indexOf("dod")>=0||dl.indexOf("document")>=0) type="document";
    else if(dl.indexOf("grupp")>=0||dl.indexOf("group")>=0||dl.indexOf("familj")>=0) type="group";
    else type="portrait";
    var yearMatch=base.match(/_(1[0-9]{3}|2[0-9]{3})/);
    var year=yearMatch?yearMatch[1]:"";
    return {gedcomId:gedcomId,type:type,label:label,year:year,seq:seq};
  }

  var syncInProgressRef=useRef(false);

  function syncPlacePhotos(cfg){
    if(!cfg||!cfg.token||!cfg.repo) return;
    var headers={"Authorization":"token "+cfg.token,"Accept":"application/vnd.github.v3+json"};
    var branch=cfg.branch||"main";
    fetch("https://api.github.com/repos/"+cfg.repo+"/git/trees/"+branch+"?recursive=1",{headers:headers})
      .then(function(r){return r.ok?r.json():Promise.reject(r.status);})
      .then(function(data){
        var items=(data.tree||[]).filter(function(f){
          return f.type==="blob"&&f.path.indexOf("photos/places/")===0&&f.path.match(/\.(jpg|jpeg|png|webp|svg|gif)$/i);
        });
        if(!items.length) return;
        var newPlaceUrls={};
        items.forEach(function(item){
          var filename=item.path.split("/").pop();
          var base=filename.replace(/\.[^.]+$/,"");
          // Format: PLACE_husegardet_torp_01_exteriör.jpg
          // or simpler: husegardet_torp_01.jpg
          // PlaceId = everything before the sequence number
          var parts=base.split("_");
          // Sequence number must be exactly 2 digits (01-99) to avoid matching
          // numbers in place names like "biskopsgatan_7"
          var seqIdx=-1;
          for(var i=1;i<parts.length;i++){
            if(/^[0-9]{2}$/.test(parts[i])){seqIdx=i;break;}
          }
          if(seqIdx<0) seqIdx=parts.length; // no seq found, whole name is place id
          // Remove PLACE_ prefix if present
          var idParts=parts.slice(0,seqIdx);
          if(idParts[0]&&idParts[0].toUpperCase()==="PLACE") idParts=idParts.slice(1);
          var placeId=idParts.join("_").toLowerCase();
          if(!placeId) return;
          var seq=parseInt(parts[seqIdx])||1;
          var descParts=parts.slice(seqIdx+1);
          var label=descParts.join(" ").trim()||placeId.replace(/_/g," ");
          var yearMatch=base.match(/_(1[0-9]{3}|2[0-9]{3})/);
          var year=yearMatch?yearMatch[1]:"";
          var rawUrl="https://raw.githubusercontent.com/"+cfg.repo+"/"+branch+"/"+item.path;
          if(!newPlaceUrls[placeId])newPlaceUrls[placeId]=[];
          newPlaceUrls[placeId].push({url:rawUrl,label:label,year:year,seq:seq,placeId:placeId});
        });
        // Sort each place's photos by seq
        Object.keys(newPlaceUrls).forEach(function(k){
          newPlaceUrls[k].sort(function(a,b){return a.seq-b.seq;});
        });
        try{localStorage.setItem('slakttrads_place_photos',JSON.stringify(newPlaceUrls));}catch(e){}
        setPlaceUrls(newPlaceUrls);
        console.log("Place photos synced:",Object.keys(newPlaceUrls).length,"places");
      })
      .catch(function(e){console.warn("Place photo sync failed:",e);});
  }

  var syncInProgressRef=useRef(false);
  function syncFromGitHub(cfg){
    if(!cfg||!cfg.token||!cfg.repo) return;
    if(syncInProgressRef.current){console.log("Sync already in progress, skipping");return;}
    syncInProgressRef.current=true;
    setSyncing(true);setSyncMsg(null);
    // Clear stale localStorage so old entries don't interfere
    try{localStorage.removeItem('slakttrads_photos');}catch(e){}
    setPhotoUrls({});
    var headers={"Authorization":"token "+cfg.token,"Accept":"application/vnd.github.v3+json"};
    var branch=cfg.branch||"main";
    // Use git trees API to list all files under photos/ recursively
    fetch("https://api.github.com/repos/"+cfg.repo+"/git/trees/"+branch+"?recursive=1",{headers:headers})
      .then(function(r){return r.ok?r.json():Promise.reject(r.status);})
      .then(function(data){
        var items=(data.tree||[]).filter(function(f){
          return f.type==="blob"&&f.path.indexOf("photos/")===0&&f.path.match(/\.(jpg|jpeg|png|webp|svg|gif)$/i);
        });
        var truncated=data.truncated?" (repo för stor, kan vara ofullständigt)":"";
        if(!items.length){setSyncing(false);setSyncMsg("Inga bilder hittades i photos/"+truncated);return;}
        var newUrls={};
        items.forEach(function(item){
          var filename=item.path.split("/").pop();
          var meta=parsePhotoMeta(filename);
          if(!meta.gedcomId) return;
          var rawUrl="https://raw.githubusercontent.com/"+cfg.repo+"/"+branch+"/"+item.path;
          if(!newUrls[meta.gedcomId])newUrls[meta.gedcomId]=[];
          // Avoid duplicates
          var exists=newUrls[meta.gedcomId].some(function(p){return p.url===rawUrl;});
          if(!exists) newUrls[meta.gedcomId].push({url:rawUrl,label:meta.label,type:meta.type,year:meta.year,source:"GitHub: "+item.path,_seq:meta.seq});
        });
        // Sort each person's photos by seq
        Object.keys(newUrls).forEach(function(k){
          newUrls[k].sort(function(a,b){return (a._seq||0)-(b._seq||0);});
        });
        // Replace all — don't merge with old localStorage, use GitHub as source of truth
        var merged={};
        Object.keys(newUrls).forEach(function(k){merged[k]=newUrls[k];});
        console.log("Setting photoUrls:",Object.keys(merged).map(function(k){return k+":"+merged[k].length+" foton";}));
        try{localStorage.setItem('slakttrads_photos',JSON.stringify(merged));}catch(e){}
        setPhotoUrls(merged);
        var total=items.length;
        var persons=Object.keys(newUrls).length;
        var idList=Object.keys(newUrls).slice(0,6).join(", ");
        var fileList=items.map(function(f){return f.path.split("/").pop();}).join(", ");
        console.log("Sync found files:",fileList);
        syncInProgressRef.current=false;
        setSyncing(false);setSyncMsg("\u2713 "+total+" bilder | "+persons+" pers: "+idList+truncated);
      })
      .catch(function(e){
        syncInProgressRef.current=false;
        setSyncing(false);
        setSyncMsg("Fel: "+(typeof e==="string"?e:e.message||"okänt fel")+" — kontrollera token och repo");
      });
  }

  if(!hasParsedData) return React.createElement('div',{style:{flex:1,display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",color:"#8899aa",fontSize:13,gap:12,height:"100%",background:"#0d1117"}},
    React.createElement('div',{style:{fontSize:40}},"\uD83D\uDCF7"),
    React.createElement('div',{style:{fontWeight:600,color:"#c9d1d9"}},"Fotogalleriet"),
    React.createElement('div',{style:{fontSize:12,textAlign:"center",maxWidth:280,lineHeight:1.7}},"Ladda en GEDCOM-fil f\u00f6rst, sedan kan du l\u00e4gga till foton f\u00f6r varje person.")
  );

  var pids=individuals?Object.keys(individuals):[];
  var pidList=pids.filter(function(p){return individuals[p]&&individuals[p].name;}).sort(function(a,b){return(individuals[a].name||"").localeCompare(individuals[b].name||"","sv");});
  var filteredPids=search.trim()?pidList.filter(function(p){return individuals[p].name.toLowerCase().indexOf(search.toLowerCase())>=0;}):pidList;
  var ind=editId&&individuals?individuals[editId]:null;
  var photos=editId&&photoUrls[editId]?photoUrls[editId]:[];
  var C2={bg:"#0d1117",panel:"#161b22",border:"#30363d",text:"#c9d1d9",dim:"#8b949e",accent:"#4a9eff"};

  function saveGhConfig(cfg){
    setGhConfig(cfg);
    try{localStorage.setItem('slakttrads_gh',JSON.stringify(cfg));}catch(e){}
  }

  function savePhotos(next){
    setPhotoUrls(next);
    try{localStorage.setItem('slakttrads_photos',JSON.stringify(next));}catch(e){}
    var arr=next[editId]||[];
    var first=arr.find(function(p){return p.type==="portrait"&&p.label&&(p.label.indexOf("vuxen")>=0||p.label.indexOf("adult")>=0);})||arr.find(function(p){return p.type==="portrait";})||arr[0];
    if(first&&first.url&&typeof THREE!=="undefined"){
      var loader2=new THREE.TextureLoader();loader2.crossOrigin="anonymous";
      loader2.load(first.url,function(tex2){
        setPhotoTex(function(prev){var n={};for(var k in prev)n[k]=prev[k];n[editId]=tex2;return n;});
      });
    }
  }

  function readFileAsBase64(file){
    return new Promise(function(resolve,reject){
      var r=new FileReader();
      r.onload=function(ev){resolve(ev.target.result.split(",")[1]);};
      r.onerror=reject;
      r.readAsDataURL(file);
    });
  }

  function uploadToGitHub(file,personId){
    var cfg=ghConfig;
    if(!cfg.token||!cfg.repo) return Promise.resolve(null);
    var ext=(file.name.split(".").pop()||"jpg").toLowerCase();
    var ts=Date.now();
    var safeName=personId.replace(/@/g,"").replace(/[^a-zA-Z0-9]/g,"_");
    var path="photos/"+safeName+"/"+ts+"."+ext;
    var apiBase="https://api.github.com/repos/"+cfg.repo+"/contents/"+path;
    var headers={"Authorization":"token "+cfg.token,"Accept":"application/vnd.github.v3+json","Content-Type":"application/json"};
    return readFileAsBase64(file).then(function(b64){
      return fetch(apiBase,{headers:headers})
        .then(function(r){return r.ok?r.json():null;})
        .catch(function(){return null;})
        .then(function(existing){
          var body={message:"Add photo for "+personId,content:b64,branch:cfg.branch||"main"};
          if(existing&&existing.sha) body.sha=existing.sha;
          return fetch(apiBase,{method:"PUT",headers:headers,body:JSON.stringify(body)});
        })
        .then(function(resp){
          if(!resp.ok) return resp.json().then(function(e){throw new Error(e.message||resp.status);});
          return resp.json();
        })
        .then(function(data){
          return data.content&&data.content.download_url
            ? data.content.download_url
            : "https://raw.githubusercontent.com/"+cfg.repo+"/"+(cfg.branch||"main")+"/"+path;
        });
    });
  }

  function deleteFromGitHub(url){
    var cfg=ghConfig;
    if(!cfg.token||!cfg.repo||!url) return;
    var m=url.match(/raw\.githubusercontent\.com\/[^/]+\/[^/]+\/[^/]+\/(.+)/);
    if(!m) return;
    var path=m[1];
    var apiBase="https://api.github.com/repos/"+cfg.repo+"/contents/"+path;
    var headers={"Authorization":"token "+cfg.token,"Accept":"application/vnd.github.v3+json","Content-Type":"application/json"};
    fetch(apiBase,{headers:headers})
      .then(function(r){return r.ok?r.json():null;})
      .then(function(cd){
        if(!cd||!cd.sha) return;
        return fetch(apiBase,{method:"DELETE",headers:headers,body:JSON.stringify({message:"Delete photo",sha:cd.sha,branch:cfg.branch||"main"})});
      })
      .catch(function(e){console.warn("GitHub delete failed:",e);});
  }

  function processFiles(files){
    if(!files||!files.length) return;
    if(!ghReady){setUploadErr("Konfigurera GitHub-token och repo f\u00f6rst (\u2699\uFE0F ovan).");return;}
    setUploading(true);setUploadErr(null);
    var arr=Array.from(files).filter(function(f){return f.type.match(/image\//);});
    var idx=0;
    var errors=[];
    function next(){
      if(idx>=arr.length){setUploading(false);if(errors.length)setUploadErr("Fel: "+errors.join("; "));return;}
      var file=arr[idx++];
      uploadToGitHub(file,editId)
        .then(function(url){
          if(url){
            var label=file.name.replace(/\.[^.]+$/,"").replace(/[_-]/g," ");
            setPhotoUrls(function(prev){
              var next2=Object.assign({},prev);
              if(!next2[editId])next2[editId]=[];
              next2[editId]=next2[editId].concat([{url:url,label:label,type:"portrait",year:"",source:""}]);
              try{localStorage.setItem('slakttrads_photos',JSON.stringify(next2));}catch(e){}
              return next2;
            });
          }
        })
        .catch(function(e){errors.push(file.name+": "+e.message);})
        .then(next);
    }
    next();
  }

  function deletePhoto(idx){
    if(!window.confirm("Ta bort bilden?")) return;
    var ph=photos[idx];
    var next=Object.assign({},photoUrls);
    next[editId]=photos.filter(function(_,i){return i!==idx;});
    if(!next[editId].length)delete next[editId];
    savePhotos(next);
    if(ph&&ph.url&&ph.url.indexOf("raw.githubusercontent")>=0)deleteFromGitHub(ph.url);
  }

  function savePhotoMeta(idx,patch){
    var next=Object.assign({},photoUrls);
    next[editId]=photos.map(function(p,i){return i===idx?Object.assign({},p,patch):p;});
    savePhotos(next);
    setEditPhoto(null);
  }

  var personList=filteredPids.map(function(pid){
    var p=individuals[pid];
    var phCount=(photoUrls[pid]||[]).length;
    return React.createElement('div',{key:pid,onClick:function(){setEditId(pid);setSearch("");},
      style:{padding:"7px 10px",cursor:"pointer",borderBottom:"1px solid "+C2.border+"44",background:editId===pid?"rgba(74,158,255,0.12)":"transparent",display:"flex",alignItems:"center",gap:7}},
      photoUrls[pid]&&photoUrls[pid][0]
        ?React.createElement('img',{src:photoUrls[pid][0].url,style:{width:28,height:28,borderRadius:4,objectFit:"cover",flexShrink:0,border:"1px solid "+C2.border}})
        :React.createElement('div',{style:{width:28,height:28,borderRadius:4,background:"rgba(255,255,255,0.05)",flexShrink:0,display:"flex",alignItems:"center",justifyContent:"center",fontSize:12,color:C2.dim}},p.sex==="F"?"\u2640":"\u2642"),
      React.createElement('div',{style:{flex:1,minWidth:0}},
        React.createElement('div',{style:{fontSize:11,fontWeight:editId===pid?600:400,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap",color:editId===pid?C2.accent:C2.text}},p.name),
        phCount>0&&React.createElement('div',{style:{fontSize:9,color:"#66d9a0"}},phCount+" foto"+(phCount!==1?"n":""))
      )
    );
  });

  var photoGrid=photos.map(function(ph,idx){
    var pt=PHOTO_TYPES.find(function(t){return t.id===ph.type;})||PHOTO_TYPES[PHOTO_TYPES.length-1];
    return React.createElement('div',{key:idx,style:{background:C2.panel,borderRadius:8,border:"1px solid "+C2.border,overflow:"hidden",position:"relative",cursor:"pointer"},
      onClick:function(){setLightbox({photos:photos,idx:idx});}},
      React.createElement('img',{src:ph.url,style:{width:"100%",aspectRatio:"1",objectFit:"cover",display:"block"},onError:function(e){e.target.style.display="none";}}),
      React.createElement('div',{style:{padding:"5px 7px"}},
        React.createElement('div',{style:{fontSize:9,color:pt.color,fontWeight:600,marginBottom:1}},pt.icon+" "+pt.label),
        React.createElement('div',{style:{fontSize:10,color:C2.text,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}},ph.label||"\u2014"),
        ph.year&&React.createElement('div',{style:{fontSize:9,color:C2.dim}},ph.year)
      ),
      React.createElement('div',{style:{position:"absolute",top:4,right:4,display:"flex",gap:3}},
        React.createElement('button',{onClick:function(e){e.stopPropagation();setEditPhoto({idx:idx,label:ph.label||"",type:ph.type||"portrait",year:ph.year||"",source:ph.source||""});},
          style:{width:22,height:22,borderRadius:4,background:"rgba(0,0,0,0.75)",border:"none",color:"#fff",fontSize:11,cursor:"pointer"}},"\u270F\uFE0F"),
        React.createElement('button',{onClick:function(e){e.stopPropagation();deletePhoto(idx);},
          style:{width:22,height:22,borderRadius:4,background:"rgba(180,0,0,0.75)",border:"none",color:"#fff",fontSize:11,cursor:"pointer"}},"\u2715")
      )
    );
  });

  return React.createElement('div',{style:{flex:1,display:"flex",height:"100%",overflow:"hidden",background:C2.bg,color:C2.text,fontFamily:"'Segoe UI',sans-serif"}},
    /* Person list */
    React.createElement('div',{style:{width:200,flexShrink:0,borderRight:"1px solid "+C2.border,display:"flex",flexDirection:"column",overflow:"hidden"}},
      React.createElement('div',{style:{padding:"8px 10px",borderBottom:"1px solid "+C2.border,flexShrink:0}},
        React.createElement('input',{type:"text",placeholder:"\uD83D\uDD0D S\u00f6k person...",value:search,onChange:function(e){setSearch(e.target.value);},
          style:{width:"100%",background:"rgba(255,255,255,0.05)",border:"1px solid "+C2.border,borderRadius:6,padding:"5px 8px",color:C2.text,fontSize:11,outline:"none",boxSizing:"border-box"}})
      ),
      React.createElement('div',{style:{flex:1,overflowY:"auto"}},personList)
    ),
    /* Main area */
    React.createElement('div',{style:{flex:1,display:"flex",flexDirection:"column",overflow:"hidden"}},
      /* Header */
      React.createElement('div',{style:{padding:"8px 12px",borderBottom:"1px solid "+C2.border,flexShrink:0,display:"flex",alignItems:"center",gap:8}},
        ind
          ?React.createElement('div',{style:{flex:1}},
            React.createElement('div',{style:{fontSize:13,fontWeight:600}},ind.name),
            React.createElement('div',{style:{fontSize:10,color:C2.dim}},(ind.birthDate?ind.birthDate+" \u00b7 ":"")+photos.length+" foto"+(photos.length!==1?"n":""))
          )
          :React.createElement('div',{style:{flex:1,fontSize:12,color:C2.dim}},"V\u00e4lj en person till v\u00e4nster"),
        syncing&&React.createElement('div',{style:{fontSize:10,color:"#4a9eff",display:"flex",alignItems:"center",gap:4}},
          React.createElement('span',{style:{display:"inline-block",animation:"spin 1s linear infinite"}},"\u23F3")," Synkar..."
        ),
        React.createElement('button',{onClick:function(){setShowGHConfig(!showGHConfig);},title:"GitHub-inst\u00e4llningar",
          style:{padding:"4px 8px",background:ghReady?"rgba(102,217,160,0.15)":"rgba(255,165,0,0.15)",border:"1px solid "+(ghReady?"#66d9a0":"#ffa94d"),borderRadius:6,color:ghReady?"#66d9a0":"#ffa94d",cursor:"pointer",fontSize:11,fontWeight:600}},
          "\u2699\uFE0F GitHub"+(ghReady?" \u2713":""))
      ),
      /* GitHub config */
      showGHConfig&&React.createElement('div',{style:{padding:"10px 12px",borderBottom:"1px solid "+C2.border,background:"rgba(74,158,255,0.06)",flexShrink:0}},
        React.createElement('div',{style:{fontSize:10,fontWeight:700,letterSpacing:1,color:C2.dim,textTransform:"uppercase",marginBottom:6}},"GitHub-konfiguration"),
        [["token","Token (ghp_...)","password"],["repo","Repo (user/repo)","text"],["branch","Branch","text"]].map(function(f){
          return React.createElement('div',{key:f[0],style:{display:"flex",alignItems:"center",gap:6,marginBottom:5}},
            React.createElement('label',{style:{fontSize:10,color:C2.dim,width:52,flexShrink:0}},f[0]==="branch"?"Branch":"token"===f[0]?"Token":"Repo"),
            React.createElement('input',{type:f[2],placeholder:f[1],value:ghConfig[f[0]]||"",
              onChange:function(key){return function(e){var n=Object.assign({},ghConfig);n[key]=e.target.value;saveGhConfig(n);};}(f[0]),
              style:{flex:1,background:"rgba(255,255,255,0.05)",border:"1px solid "+C2.border,borderRadius:5,padding:"4px 7px",color:C2.text,fontSize:11,outline:"none"}})
          );
        }),
        React.createElement('div',{style:{fontSize:9,color:C2.dim,marginTop:4}},
          "Token beh\u00f6ver repo-scope. Bilder sparas i photos/. SVG, JPG, PNG st\u00f6ds."
        ),
        ghReady&&React.createElement('button',{
          onClick:function(){syncFromGitHub(ghConfig);syncPlacePhotos(ghConfig);},
          disabled:syncing,
          style:{marginTop:6,padding:"5px 12px",background:syncing?"rgba(255,255,255,0.05)":"rgba(74,158,255,0.15)",border:"1px solid "+(syncing?C2.border:"#4a9eff"),borderRadius:6,color:syncing?C2.dim:"#4a9eff",cursor:syncing?"default":"pointer",fontSize:10,fontWeight:600,width:"100%"}},
          syncing?"\u23F3 H\u00e4mtar bilder fr\u00e5n GitHub...":"\uD83D\uDD04 Synka bilder fr\u00e5n GitHub"
        ),
        syncMsg&&React.createElement('div',{style:{fontSize:10,color:syncMsg.indexOf("Fel")===0?"#ff6b6b":"#66d9a0",marginTop:4}},syncMsg)
      ),
      /* Upload error */
      uploadErr&&React.createElement('div',{style:{padding:"6px 12px",background:"rgba(255,80,80,0.15)",borderBottom:"1px solid rgba(255,80,80,0.3)",fontSize:11,color:"#ff6b6b",flexShrink:0}},
        uploadErr,
        React.createElement('button',{onClick:function(){setUploadErr(null);},style:{background:"none",border:"none",color:"#ff6b6b",cursor:"pointer",marginLeft:8,fontSize:13}},"\u2715")
      ),
      ind&&React.createElement('div',{style:{flex:1,display:"flex",flexDirection:"column",overflow:"hidden"}},
        /* Drop zone */
        React.createElement('label',{
          style:{margin:"10px 12px 0",padding:"12px",border:"2px dashed "+(dragging?"#4a9eff":C2.border),borderRadius:8,textAlign:"center",
            background:dragging?"rgba(74,158,255,0.08)":uploading?"rgba(102,217,160,0.06)":"rgba(255,255,255,0.02)",transition:"all 0.15s",flexShrink:0,display:"block",cursor:"pointer"},
          onDragOver:function(e){e.preventDefault();setDragging(true);},
          onDragLeave:function(){setDragging(false);},
          onDrop:function(e){e.preventDefault();setDragging(false);processFiles(Array.from(e.dataTransfer.files));}},
          uploading
            ?React.createElement('div',{style:{color:"#66d9a0",fontSize:11}},"\u23F3 Laddar upp till GitHub\u2026")
            :React.createElement('div',null,
              React.createElement('div',{style:{fontSize:20,marginBottom:4}},dragging?"\uD83D\uDCC2":"\uD83D\uDCF7"),
              React.createElement('div',{style:{fontSize:11,color:dragging?C2.accent:C2.dim}},dragging?"Sl\u00e4pp h\u00e4r!":"Dra & sl\u00e4pp bilder, eller klicka f\u00f6r att v\u00e4lja"),
              React.createElement('div',{style:{fontSize:9,color:C2.dim,marginTop:2}},"JPG, PNG, WEBP \u2014 sparas p\u00e5 GitHub")
            ),
          React.createElement('input',{type:"file",accept:"image/*",multiple:true,style:{display:"none"},
            onChange:function(e){processFiles(Array.from(e.target.files));e.target.value="";}})
        ),
        /* Grid */
        React.createElement('div',{style:{flex:1,overflowY:"auto",padding:"10px 12px"}},
          photos.length===0&&React.createElement('div',{style:{textAlign:"center",color:C2.dim,fontSize:12,marginTop:20}},"Inga foton \u00e4nnu \u2014 ladda upp via rutan ovan."),
          React.createElement('div',{style:{display:"grid",gridTemplateColumns:"repeat(auto-fill,minmax(130px,1fr))",gap:8}},photoGrid)
        )
      )
    ),
    /* Edit modal */
    editPhoto&&React.createElement('div',{style:{position:"fixed",inset:0,background:"rgba(0,0,0,0.75)",display:"flex",alignItems:"center",justifyContent:"center",zIndex:1000},
      onClick:function(){setEditPhoto(null);}},
      React.createElement('div',{style:{background:C2.panel,borderRadius:12,border:"1px solid "+C2.border,padding:20,minWidth:280,maxWidth:340},
        onClick:function(e){e.stopPropagation();}},
        React.createElement('div',{style:{fontSize:13,fontWeight:600,marginBottom:10}},"Redigera fotoinformation"),
        photos[editPhoto.idx]&&React.createElement('img',{src:photos[editPhoto.idx].url,style:{width:"100%",height:130,objectFit:"cover",borderRadius:6,marginBottom:10,border:"1px solid "+C2.border}}),
        React.createElement('div',{style:{marginBottom:8}},
          React.createElement('div',{style:{fontSize:10,color:C2.dim,marginBottom:4}},"Typ"),
          React.createElement('div',{style:{display:"flex",flexWrap:"wrap",gap:4}},
            PHOTO_TYPES.map(function(pt){
              return React.createElement('button',{key:pt.id,onClick:function(){setEditPhoto(function(ep){return Object.assign({},ep,{type:pt.id});});},
                style:{padding:"3px 8px",borderRadius:5,border:"1px solid "+(editPhoto.type===pt.id?pt.color:C2.border),background:editPhoto.type===pt.id?"rgba(74,158,255,0.15)":"transparent",color:editPhoto.type===pt.id?pt.color:C2.dim,fontSize:10,cursor:"pointer"}},
                pt.icon+" "+pt.label);
            })
          )
        ),
        [["label","Bildtext","t.ex. Br\u00f6llopsdag 1923"],["year","\u00c5r (ca)","t.ex. 1923"],["source","K\u00e4lla","t.ex. Familjearkiv"]].map(function(f){
          return React.createElement('div',{key:f[0],style:{marginBottom:8}},
            React.createElement('div',{style:{fontSize:10,color:C2.dim,marginBottom:3}},f[1]),
            React.createElement('input',{type:"text",value:editPhoto[f[0]],placeholder:f[2],
              onChange:function(key){return function(e){setEditPhoto(function(ep){var n=Object.assign({},ep);n[key]=e.target.value;return n;});};}(f[0]),
              style:{width:"100%",boxSizing:"border-box",background:"rgba(255,255,255,0.05)",border:"1px solid "+C2.border,borderRadius:5,padding:"5px 8px",color:C2.text,fontSize:11,outline:"none"}})
          );
        }),
        React.createElement('div',{style:{display:"flex",gap:8,justifyContent:"flex-end",marginTop:6}},
          React.createElement('button',{onClick:function(){setEditPhoto(null);},style:{padding:"6px 14px",background:"transparent",border:"1px solid "+C2.border,borderRadius:6,color:C2.dim,cursor:"pointer",fontSize:11}},"Avbryt"),
          React.createElement('button',{onClick:function(){savePhotoMeta(editPhoto.idx,{label:editPhoto.label,type:editPhoto.type,year:editPhoto.year,source:editPhoto.source});},
            style:{padding:"6px 14px",background:"#4a9eff",border:"none",borderRadius:6,color:"#fff",cursor:"pointer",fontSize:11,fontWeight:600}},"Spara")
        )
      )
    ),
    /* Lightbox */
    lightbox&&React.createElement('div',{style:{position:"fixed",inset:0,background:"rgba(0,0,0,0.92)",display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",zIndex:2000},
      onClick:function(){setLightbox(null);}},
      React.createElement('button',{onClick:function(){setLightbox(null);},style:{position:"absolute",top:16,right:16,background:"rgba(255,255,255,0.1)",border:"none",color:"#fff",fontSize:20,width:36,height:36,borderRadius:8,cursor:"pointer"}},"\u2715"),
      lightbox.idx>0&&React.createElement('button',{onClick:function(e){e.stopPropagation();setLightbox(function(lb){return{photos:lb.photos,idx:lb.idx-1};});},
        style:{position:"absolute",left:16,top:"50%",transform:"translateY(-50%)",background:"rgba(255,255,255,0.1)",border:"none",color:"#fff",fontSize:28,width:44,height:44,borderRadius:8,cursor:"pointer"}},"\u2039"),
      lightbox.idx<lightbox.photos.length-1&&React.createElement('button',{onClick:function(e){e.stopPropagation();setLightbox(function(lb){return{photos:lb.photos,idx:lb.idx+1};});},
        style:{position:"absolute",right:16,top:"50%",transform:"translateY(-50%)",background:"rgba(255,255,255,0.1)",border:"none",color:"#fff",fontSize:28,width:44,height:44,borderRadius:8,cursor:"pointer"}},"\u203a"),
      React.createElement('img',{src:lightbox.photos[lightbox.idx].url,style:{maxWidth:"90vw",maxHeight:"75vh",objectFit:"contain",borderRadius:8},onClick:function(e){e.stopPropagation();}}),
      React.createElement('div',{style:{marginTop:12,textAlign:"center"},onClick:function(e){e.stopPropagation();}},
        React.createElement('div',{style:{color:"#fff",fontSize:13,fontWeight:600}},lightbox.photos[lightbox.idx].label||"Foto "+(lightbox.idx+1)),
        lightbox.photos[lightbox.idx].year&&React.createElement('div',{style:{color:"#8899aa",fontSize:11,marginTop:2}},lightbox.photos[lightbox.idx].year),
        lightbox.photos[lightbox.idx].source&&React.createElement('div',{style:{color:"#8899aa",fontSize:10,marginTop:1}},"K\u00e4lla: "+lightbox.photos[lightbox.idx].source),
        React.createElement('div',{style:{color:"#555",fontSize:10,marginTop:4}},(lightbox.idx+1)+" / "+lightbox.photos.length)
      )
    )
  );
}

function PlacesEditor({individuals,families,extraLocs,setExtraLocs,selectedId,buildPersonLocations,lookupLocation,hasParsedData}){
  const {useState,useRef,useEffect,useCallback}=React;
  if(!hasParsedData)return <div style={{flex:1,display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",color:"#8899aa",fontSize:13,gap:12,height:"100%",background:"#0d1117"}}>
    <div style={{fontSize:40}}>📍</div>
    <div style={{fontWeight:600,color:"#c9d1d9"}}>Platseditorn</div>
    <div style={{fontSize:12,textAlign:"center",maxWidth:280,lineHeight:1.7}}>Ladda en GEDCOM-fil först via uppladdningsskärmen (3D-vyn), sedan kan du redigera och lägga till platser för varje person.</div>
    <button onClick={function(){window.dispatchEvent(new CustomEvent('showUpload'));}} style={{padding:"8px 16px",background:"rgba(74,158,255,0.15)",border:"1px solid #4a9eff",color:"#4a9eff",borderRadius:6,fontSize:12,cursor:"pointer"}}>Öppna uppladdning</button>
  </div>;
  var pids=individuals?Object.keys(individuals):[];
  var _s=useState;
  var s1=_s(selectedId||pids[0]||null),editId=s1[0],setEditId=s1[1];
  var s2=_s(null),editIdx=s2[0],setEditIdx=s2[1];
  var s3=_s(""),search=s3[0],setSearch=s3[1];
  var mapRef=useRef(null);
  var clickModeRef=useRef(false);
  var s4=_s(false),clickMode=s4[0],setClickMode=s4[1];

  // Reset form when switching person
  useEffect(function(){setEditIdx(null);},[editId]);

  var ind=editId&&individuals?individuals[editId]:null;
  var locs=ind?buildPersonLocations(ind,extraLocs):[];
  var manualLocs=extraLocs[editId]||null;

  // Save a location entry
  function saveLoc(idx,entry){
    var cur=extraLocs[editId]?[...extraLocs[editId]]:[...locs];
    if(idx===-1){cur.push(entry);}else{cur[idx]=entry;}
    var next=Object.assign({},extraLocs);
    next[editId]=cur;
    setExtraLocs(next);
    try{localStorage.setItem('slakttrads_locations',JSON.stringify(next));}catch(e){}
    pushLocsToGitHub(next);
    setEditIdx(null);
  }

  function deleteLoc(idx){
    var cur=extraLocs[editId]?[...extraLocs[editId]]:[...locs];
    cur.splice(idx,1);
    var next=Object.assign({},extraLocs);
    next[editId]=cur.length>0?cur:undefined;
    if(!next[editId])delete next[editId];
    setExtraLocs(next);
    try{localStorage.setItem('slakttrads_locations',JSON.stringify(next));}catch(e){}
    pushLocsToGitHub(next);
    setEditIdx(null);
  }

  function exportJson(){
    var blob=new Blob([JSON.stringify(extraLocs,null,2)],{type:"application/json"});
    var url=URL.createObjectURL(blob);
    var a=document.createElement("a");a.href=url;a.download="locations.json";a.click();
    URL.revokeObjectURL(url);
  }

  function pushLocsToGitHub(data){
    // Read GitHub config - use same XOR-decoded defaults as PhotoManager
    var ghRaw=null;
    try{ghRaw=JSON.parse(localStorage.getItem('slakttrads_gh')||'{}');}catch(e){}
    var GH_KEY="hasselon2025";
    var GH_T=[15,9,3,44,52,26,23,55,68,5,92,3,90,54,53,20,35,30,38,52,125,90,84,83,59,4,23,60,42,36,13,20,70,85,3,112,44,88,58,11];
    var GH_R=[5,0,7,0,7,28,29,1,86,31,90,84,27,18,22,31,10,2];
    function xd(arr,key){return arr.map(function(c,i){return String.fromCharCode(c^key.charCodeAt(i%key.length));}).join("");}
    var token=(ghRaw&&ghRaw.token)||xd(GH_T,GH_KEY);
    var repo=(ghRaw&&ghRaw.repo)||xd(GH_R,GH_KEY);
    var branch=(ghRaw&&ghRaw.branch)||"main";
    if(!token||!repo) return;
    var path="slakttrads/locations.json";
    var apiUrl="https://api.github.com/repos/"+repo+"/contents/"+path;
    var headers={"Authorization":"token "+token,"Accept":"application/vnd.github.v3+json","Content-Type":"application/json"};
    var body=JSON.stringify(data,null,2);
    var b64=btoa(unescape(encodeURIComponent(body)));
    // Get current SHA first
    fetch(apiUrl,{headers:headers})
      .then(function(r){return r.ok?r.json():null;})
      .catch(function(){return null;})
      .then(function(existing){
        var req={message:"Uppdatera platser",content:b64,branch:branch};
        if(existing&&existing.sha) req.sha=existing.sha;
        return fetch(apiUrl,{method:"PUT",headers:headers,body:JSON.stringify(req)});
      })
      .then(function(r){
        if(r&&r.ok) console.log("Platser sparade till GitHub");
        else r&&r.text().then(function(t){console.warn("GitHub push failed:",t);});
      })
      .catch(function(e){console.warn("GitHub push error:",e);});
  }

  // Navigate to prev/next person
  var pidList=pids.filter(function(p){return individuals[p]&&individuals[p].name;}).sort(function(a,b){return (individuals[a].name||"").localeCompare(individuals[b].name||"");});
  var curIdx=pidList.indexOf(editId);
  function navPrev(){if(curIdx>0){setEditId(pidList[curIdx-1]);setEditIdx(null);}}
  function navNext(){if(curIdx<pidList.length-1){setEditId(pidList[curIdx+1]);setEditIdx(null);}}

  // Filter for search
  var filteredPids=search.trim()?pidList.filter(function(p){return individuals[p].name.toLowerCase().indexOf(search.toLowerCase())>=0;}):[];

  // Draw map using our existing OSM tiles
  useEffect(function(){
    var cv=mapRef.current;if(!cv)return;
    var ctx=cv.getContext("2d");
    var W=cv.parentElement.clientWidth||400,H=200;
    cv.width=W*2;cv.height=H*2;cv.style.width=W+"px";cv.style.height=H+"px";
    ctx.scale(2,2);
    ctx.fillStyle="#e8f0e8";ctx.fillRect(0,0,W,H);
    ctx.fillStyle="#aaa";ctx.font="12px Arial";ctx.textAlign="center";
    ctx.fillText("Klicka 'Välj på karta' för att öppna OSM-karta",W/2,H/2-8);
    ctx.fillStyle="#888";ctx.font="11px Arial";
    ctx.fillText("och ange koordinater manuellt",W/2,H/2+12);

    // Draw location dots
    if(!locs.length)return;
    // Simple projection centered on Orust area
    var clat=58.1,clon=11.6,scale=W/3;
    locs.forEach(function(loc,i){
      if(!loc.lat||!loc.lon)return;
      var x=W/2+(loc.lon-clon)*scale*Math.cos(clat*Math.PI/180)*2;
      var y=H/2-(loc.lat-clat)*scale*2;
      var col=loc.type==="birth"?"#2ecc71":loc.type==="death"?"#e74c3c":"#3498db";
      ctx.fillStyle=col;
      ctx.beginPath();ctx.arc(x,y,6,0,Math.PI*2);ctx.fill();
      ctx.fillStyle="#fff";ctx.strokeStyle=col;ctx.lineWidth=1;
      ctx.strokeText((loc.from||"?")+"",x,y-10);
    });
  },[locs,editId]);

  var C2={bg:"#0d1117",panel:"#161b22",border:"#30363d",text:"#c9d1d9",dim:"#8899aa",accent:"#4a9eff"};
  var typeColors={birth:"#2ecc71",death:"#e74c3c",resi:"#3498db",residence:"#3498db",emig:"#f39c12",immi:"#9b59b6"};
  var typeLabels={birth:"Födelse",death:"Död",resi:"Bostad",residence:"Bostad",emig:"Emigration",immi:"Immigration",chr:"Dop"};

  var EditForm=function({loc,idx,onSave,onCancel,onDelete}){
    var _es=useState;
    var ef1=_es(loc.place||""),eplace=ef1[0],setEplace=ef1[1];
    var ef2=_es(loc.from||""),efrom=ef2[0],setEfrom=ef2[1];
    var ef3=_es(loc.to||""),eto=ef3[0],setEto=ef3[1];
    var ef4=_es(loc.type||"resi"),etype=ef4[0],setEtype=ef4[1];
    var ef5=_es(loc.lat||""),elat=ef5[0],setElat=ef5[1];
    var ef6=_es(loc.lon||""),elon=ef6[0],setElon=ef6[1];
    useEffect(function(){
      window._placesSetCoords=function(lat,lon){setElat(lat.toFixed(4));setElon(lon.toFixed(4));};
      return function(){if(window._placesSetCoords)delete window._placesSetCoords;};
    },[]);

    function tryGeocode(){
      var found=lookupLocation(eplace);
      if(found){setElat(found.lat.toFixed(4));setElon(found.lon.toFixed(4));}
      else alert("Platsen '"+eplace+"' hittades inte i geocoding-registret. Ange koordinater manuellt.");
    }

    return <div style={{background:"rgba(74,158,255,0.08)",border:"1px solid "+C2.accent,borderRadius:8,padding:12,marginTop:8}}>
      <div style={{display:"flex",gap:8,marginBottom:8}}>
        <div style={{flex:1}}>
          <div style={{fontSize:10,color:C2.dim,marginBottom:3}}>Platsnamn</div>
          <input value={eplace} onChange={function(e){setEplace(e.target.value);}} style={{width:"100%",background:"#0d1117",border:"1px solid "+C2.border,color:C2.text,borderRadius:4,padding:"4px 8px",fontSize:12,boxSizing:"border-box"}}/>
        </div>
        <button onClick={tryGeocode} style={{marginTop:16,padding:"4px 8px",background:"rgba(74,158,255,0.15)",border:"1px solid "+C2.accent,color:C2.accent,borderRadius:4,fontSize:11,cursor:"pointer",whiteSpace:"nowrap"}}>Geocoda</button>
      </div>
      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr 1fr",gap:8,marginBottom:8}}>
        <div>
          <div style={{fontSize:10,color:C2.dim,marginBottom:3}}>Från år</div>
          <input type="number" value={efrom} onChange={function(e){setEfrom(e.target.value);}} style={{width:"100%",background:"#0d1117",border:"1px solid "+C2.border,color:C2.text,borderRadius:4,padding:"4px 8px",fontSize:12,boxSizing:"border-box"}}/>
        </div>
        <div>
          <div style={{fontSize:10,color:C2.dim,marginBottom:3}}>Till år</div>
          <input type="number" value={eto} onChange={function(e){setEto(e.target.value);}} style={{width:"100%",background:"#0d1117",border:"1px solid "+C2.border,color:C2.text,borderRadius:4,padding:"4px 8px",fontSize:12,boxSizing:"border-box"}}/>
        </div>
        <div>
          <div style={{fontSize:10,color:C2.dim,marginBottom:3}}>Typ</div>
          <select value={etype} onChange={function(e){setEtype(e.target.value);}} style={{width:"100%",background:"#0d1117",border:"1px solid "+C2.border,color:C2.text,borderRadius:4,padding:"4px 6px",fontSize:12,boxSizing:"border-box"}}>
            <option value="birth">Födelse</option>
            <option value="resi">Bostad</option>
            <option value="emig">Emigration</option>
            <option value="immi">Immigration</option>
            <option value="chr">Dop</option>
            <option value="death">Död</option>
          </select>
        </div>
      </div>
      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:8,marginBottom:10}}>
        <div>
          <div style={{fontSize:10,color:C2.dim,marginBottom:3}}>Latitud</div>
          <input type="number" step="0.0001" value={elat} onChange={function(e){setElat(e.target.value);}} style={{width:"100%",background:"#0d1117",border:"1px solid "+C2.border,color:C2.text,borderRadius:4,padding:"4px 8px",fontSize:12,boxSizing:"border-box"}}/>
        </div>
        <div>
          <div style={{fontSize:10,color:C2.dim,marginBottom:3}}>Longitud</div>
          <input type="number" step="0.0001" value={elon} onChange={function(e){setElon(e.target.value);}} style={{width:"100%",background:"#0d1117",border:"1px solid "+C2.border,color:C2.text,borderRadius:4,padding:"4px 8px",fontSize:12,boxSizing:"border-box"}}/>
        </div>
      </div>
      <div style={{display:"flex",gap:6}}>
        {idx>=0&&<button onClick={function(){onDelete(idx);}} style={{padding:"5px 10px",background:"rgba(255,107,107,0.15)",border:"1px solid rgba(255,107,107,0.4)",color:"#ff6b6b",borderRadius:4,fontSize:11,cursor:"pointer"}}>Ta bort</button>}
        <button onClick={onCancel} style={{flex:1,padding:"5px 10px",background:"rgba(255,255,255,0.05)",border:"1px solid "+C2.border,color:C2.dim,borderRadius:4,fontSize:11,cursor:"pointer"}}>Avbryt</button>
        <button onClick={function(){onSave(idx,{place:eplace,from:efrom?parseInt(efrom):null,to:eto?parseInt(eto):null,type:etype,lat:elat?parseFloat(elat):null,lon:elon?parseFloat(elon):null});}} style={{flex:2,padding:"5px 10px",background:"rgba(74,158,255,0.2)",border:"1px solid "+C2.accent,color:C2.accent,borderRadius:4,fontSize:11,cursor:"pointer",fontWeight:600}}>Spara</button>
      </div>
      <div style={{marginTop:8,fontSize:10,color:C2.dim}}>
        Tips: Öppna <a href={"https://www.openstreetmap.org/search?query="+encodeURIComponent(eplace)} target="_blank" style={{color:C2.accent}}>OSM ↗</a> i ny flik → navigera till platsen → kopiera URL:en och klistra in här (fungerar även med Google Maps-URL):
        <br/><input placeholder="Klistra in: 58.1234,11.5678" onChange={function(e){
  var v=e.target.value.trim();
  // OSM URL: #map=18/58.233635/11.698288
  var osmHash=v.match(/#map=\d+\/([\d.-]+)\/([\d.-]+)/);
  if(osmHash){setElat(parseFloat(osmHash[1]).toFixed(4));setElon(parseFloat(osmHash[2]).toFixed(4));return;}
  // Google Maps: @58.2336,11.6982
  var gm=v.match(/@([\d.-]+),([\d.-]+)/);
  if(gm){setElat(parseFloat(gm[1]).toFixed(4));setElon(parseFloat(gm[2]).toFixed(4));return;}
  // Plain: 58.1234, 11.5678 or 58.1234 11.5678
  var p=v.split(/[,\s]+/);
  if(p.length>=2&&!isNaN(p[0])&&!isNaN(p[1])){setElat(parseFloat(p[0]).toFixed(4));setElon(parseFloat(p[1]).toFixed(4));}
}} style={{width:"100%",marginTop:4,background:"#0d1117",border:"1px solid #4a9eff",color:"#c9d1d9",borderRadius:4,padding:"3px 8px",fontSize:11,boxSizing:"border-box"}} placeholder="Klistra OSM-URL, Google Maps-URL eller: 58.1234, 11.5678"/>
      </div>
    </div>;
  };

  return <div style={{width:"100%",height:"100%",display:"flex",flexDirection:"column",background:C2.bg,color:C2.text,overflow:"hidden"}}>
    <div style={{flexShrink:0,padding:"10px 14px",borderBottom:"1px solid "+C2.border,display:"flex",gap:8,alignItems:"center"}}>
      <div style={{position:"relative",flex:1}}>
        <input value={search} onChange={function(e){setSearch(e.target.value);}} placeholder="Sök person..." style={{width:"100%",background:"rgba(255,255,255,0.05)",border:"1px solid "+C2.border,color:C2.text,borderRadius:6,padding:"6px 10px",fontSize:12,boxSizing:"border-box"}}/>
        {search&&filteredPids.length>0&&<div style={{position:"absolute",top:"100%",left:0,right:0,background:C2.panel,border:"1px solid "+C2.border,borderRadius:6,zIndex:50,maxHeight:160,overflowY:"auto"}}>
          {filteredPids.slice(0,10).map(function(p){return <div key={p} onClick={function(){setEditId(p);setSearch("");setEditIdx(null);}} style={{padding:"6px 10px",cursor:"pointer",fontSize:12,borderBottom:"1px solid "+C2.border}}>{individuals[p].name}</div>;})}
        </div>}
      </div>
      <button onClick={navPrev} disabled={curIdx<=0} style={{padding:"6px 10px",background:"rgba(255,255,255,0.05)",border:"1px solid "+C2.border,color:C2.dim,borderRadius:6,cursor:"pointer",fontSize:14}}>←</button>
      <button onClick={navNext} disabled={curIdx>=pidList.length-1} style={{padding:"6px 10px",background:"rgba(255,255,255,0.05)",border:"1px solid "+C2.border,color:C2.dim,borderRadius:6,cursor:"pointer",fontSize:14}}>→</button>
      <button onClick={exportJson} style={{padding:"6px 12px",background:"rgba(74,158,255,0.15)",border:"1px solid "+C2.accent,color:C2.accent,borderRadius:6,cursor:"pointer",fontSize:11,fontWeight:600}}>Exportera JSON</button>
    </div>

    {ind&&<div style={{flex:1,overflow:"auto",padding:"12px 14px"}}>
      <div style={{display:"flex",alignItems:"center",gap:10,marginBottom:12}}>
        <div style={{width:36,height:36,borderRadius:"50%",background:ind.sex==="M"?"rgba(74,158,255,0.2)":"rgba(255,107,157,0.2)",border:"1px solid "+(ind.sex==="M"?"#4a9eff":"#ff6b9d"),display:"flex",alignItems:"center",justifyContent:"center",fontSize:14,fontWeight:600,color:ind.sex==="M"?"#4a9eff":"#ff6b9d",flexShrink:0}}>
          {(ind.givenName||ind.name||"?").charAt(0)}
        </div>
        <div>
          <div style={{fontWeight:600,fontSize:14}}>{ind.name}</div>
          <div style={{fontSize:11,color:C2.dim}}>{ind.birthDate||"?"} · {ind.birthPlace||"okänd ort"}{manualLocs?"  ✎ manuell data":""}</div>
        </div>
        <div style={{marginLeft:"auto",fontSize:11,color:C2.dim}}>{curIdx+1} / {pidList.length}</div>
      </div>

    <PlacesLeafletMap locs={locs} editIdx={editIdx} onCoords={function(lat,lon){
        if(typeof window._placesSetCoords==='function')window._placesSetCoords(lat,lon);
      }}/>
    <div style={{display:"flex",alignItems:"center",justifyContent:"space-between",marginBottom:8}}>
        <div style={{fontSize:11,color:C2.dim,letterSpacing:1,textTransform:"uppercase"}}>Platser ({locs.length})</div>
        <button onClick={function(){setEditIdx(-1);}} style={{padding:"4px 10px",background:"rgba(74,158,255,0.15)",border:"1px solid "+C2.accent,color:C2.accent,borderRadius:4,fontSize:11,cursor:"pointer"}}>+ Lägg till</button>
      </div>

      {editIdx===-1&&<EditForm loc={{}} idx={-1} onSave={saveLoc} onCancel={function(){setEditIdx(null);}} onDelete={deleteLoc}/>}

      <div style={{display:"flex",flexDirection:"column",gap:6}}>
        {locs.map(function(loc,i){
          var col=typeColors[loc.type]||"#888";
          var label=typeLabels[loc.type]||loc.type||"";
          var isManual=manualLocs&&manualLocs[i];
          return <div key={i}>
            <div
              draggable={true}
              onDragStart={function(){window._dragIdx=i;}}
              onDragOver={function(e){e.preventDefault();window._dragOver=i;}}
              onDrop={function(e){e.preventDefault();
                var from=window._dragIdx,to=window._dragOver;
                if(from!==undefined&&to!==undefined&&from!==to){
                  var cur=extraLocs[editId]?[...extraLocs[editId]]:[...locs];
                  var item=cur.splice(from,1)[0];cur.splice(to,0,item);
                  var next=Object.assign({},extraLocs);next[editId]=cur;
                  setExtraLocs(next);
                  try{localStorage.setItem('slakttrads_locations',JSON.stringify(next));}catch(ex){}
                }
                window._dragIdx=undefined;window._dragOver=undefined;
              }}
              style={{background:editIdx===i?"rgba(74,158,255,0.08)":"rgba(255,255,255,0.03)",border:"1px solid "+(editIdx===i?C2.accent:C2.border),borderRadius:8,padding:"8px 12px",display:"flex",alignItems:"center",gap:10,cursor:"grab"}}>
              <div style={{color:C2.dim,fontSize:14,cursor:"grab",userSelect:"none"}} title="Dra för att ändra ordning">⠿</div>
              <div style={{width:10,height:10,borderRadius:"50%",background:col,flexShrink:0}}/>
              <div onClick={function(){setEditIdx(editIdx===i?null:i);}} style={{flex:1,cursor:"pointer"}}>
                <div style={{fontSize:13,fontWeight:500}}>{loc.place||"Okänd plats"}</div>
                <div style={{fontSize:11,color:C2.dim}}>{loc.from||"?"}{loc.to&&loc.to!==loc.from?" – "+loc.to:""} · {label}{!loc.lat?" · ⚠ saknar koordinater":""}</div>
              </div>
              <div style={{display:"flex",gap:4,alignItems:"center"}}>
                {window._pendingCoords&&editIdx!==i&&<button onClick={function(e){e.stopPropagation();var p=window._pendingCoords;saveLoc(i,Object.assign({},loc,{lat:p.lat,lon:p.lon}));window._pendingCoords=null;if(clickMarkerRef2&&clickMarkerRef2.current){}}} style={{fontSize:10,padding:"3px 7px",background:"rgba(255,208,96,0.2)",border:"1px solid #ffd060",color:"#ffd060",borderRadius:4,cursor:"pointer",whiteSpace:"nowrap"}}>📍 Sätt här</button>}
                <div onClick={function(){setEditIdx(editIdx===i?null:i);}} style={{fontSize:10,color:isManual?"#2ecc71":"#4a9eff",cursor:"pointer"}}>{isManual?"✎ manuell":"✎ redigera"}</div>
              </div>
            </div>
            {editIdx===i&&<EditForm loc={loc} idx={i} onSave={saveLoc} onCancel={function(){setEditIdx(null);}} onDelete={deleteLoc}/>}
          </div>;
        })}
      </div>

      {locs.length===0&&<div style={{textAlign:"center",color:C2.dim,fontSize:12,padding:"30px 0"}}>
        Inga platser hittade. Klicka "+ Lägg till" för att lägga till manuellt.<br/>
        <span style={{fontSize:11}}>Automatiska platser hämtas från GEDCOM-filen (BIRT PLAC, RESI PLAC, DEAT PLAC).</span>
      </div>}

    </div>}

    {!ind&&<div style={{flex:1,display:"flex",alignItems:"center",justifyContent:"center",color:C2.dim,fontSize:13}}>Välj en person ovan för att redigera platser</div>}
  </div>;
}


function GenealogyApp(){
  var _s=useState;var s1=_s(null),layout=s1[0],setLayout=s1[1];var s2=_s(null),sel=s2[0],setSel=s2[1];var sInsp=_s(null),inspPerson=sInsp[0],setInspPerson=sInsp[1];var sLB=_s(null),panelLightbox=sLB[0],setPanelLightbox=sLB[1];var s3=_s(""),search=s3[0],setSearch=s3[1];var s4=_s(new Set()),hlIds=s4[0],setHlIds=s4[1];var s5=_s(true),showUp=s5[0],setShowUp=s5[1];var s6=_s({}),photoTex=s6[0],setPhotoTex=s6[1];var s7=_s(true),isSample=s7[0],setIsSample=s7[1];var s8=_s(null),parsedData=s8[0],setParsedData=s8[1];var sGL=_s(false),gedcomLoading=sGL[0],setGedcomLoading=sGL[1];var sGE=_s(null),gedcomError=sGE[0],setGedcomError=sGE[1];var s9=_s(1970),sliderYear=s9[0],setSliderYear=s9[1];var s10=_s(false),isPlaying=s10[0],setIsPlaying=s10[1];var s11=_s(null),rangeStart=s11[0],setRangeStart=s11[1];var s12=_s(null),rangeEnd=s12[0],setRangeEnd=s12[1];
  var s14=_s(function(){try{var r=localStorage.getItem('slakttrads_photos');return r?JSON.parse(r):{};}catch(e){return {};}}()),photoUrls=s14[0],setPhotoUrls=s14[1];
  var sPlU=useState(function(){try{var r=localStorage.getItem('slakttrads_place_photos');return r?JSON.parse(r):{};}catch(e){return {};}}()),placeUrls=sPlU[0],setPlaceUrls=sPlU[1];
  var s15=_s(0),photoCount=s15[0],setPhotoCount=s15[1];
  useEffect(function(){
    var c=0;
    var toLoad=[];
    for(var k in photoUrls){
      var arr2=photoUrls[k]||[];
      c+=arr2.length;
      var first2=arr2.find(function(p){return p.type==="portrait"&&p.label&&(p.label.indexOf("vuxen")>=0||p.label.indexOf("adult")>=0);})||arr2.find(function(p){return p.type==="portrait";})||arr2[0];
      if(first2&&first2.url) toLoad.push({id:k,src:first2.url});
    }
    setPhotoCount(c);
    if(!toLoad.length) return;
    // Use THREE.TextureLoader if available (works with SVG + avoids canvas taint)
    function loadOne(id,src){
      if(typeof THREE!=="undefined"){
        var loader=new THREE.TextureLoader();
        loader.crossOrigin="anonymous";
        loader.load(src,function(tex){
          setPhotoTex(function(prev){var n={};for(var k2 in prev)n[k2]=prev[k2];n[id]=tex;return n;});
        },undefined,function(){
          // fallback canvas for data: URLs
          var img=new Image();
          img.onload=function(){
            var cv=document.createElement("canvas");cv.width=128;cv.height=128;
            var ctx=cv.getContext("2d");
            var sz=Math.min(img.width,img.height),sx=(img.width-sz)/2,sy=(img.height-sz)/2;
            ctx.beginPath();ctx.arc(64,64,60,0,Math.PI*2);ctx.clip();
            ctx.drawImage(img,sx,sy,sz,sz,0,0,128,128);
            if(typeof THREE!=="undefined") setPhotoTex(function(prev){var n={};for(var k3 in prev)n[k3]=prev[k3];n[id]=new THREE.CanvasTexture(cv);return n;});
          };
          img.src=src;
        });
      }
    }
    // Retry until THREE is available (scene may not be active yet)
    function tryLoad(attempts){
      if(typeof THREE!=="undefined"){
        toLoad.forEach(function(item){loadOne(item.id,item.src);});
      } else if(attempts>0){
        setTimeout(function(){tryLoad(attempts-1);},500);
      }
    }
    tryLoad(20); // retry up to 10s
  },[photoUrls]);
  var s16=_s(0),viewTrigger=s16[0],setViewTrigger=s16[1];
  var s17=_s("3d"),rightView=s17[0],setRightView=s17[1];
  // Auto-compute layout when parsedData arrives
  useEffect(function(){
    if(parsedData&&!layout){
      setLayout(computeLayout(parsedData.individuals,parsedData.families));
      setShowUp(false);
    }
  },[parsedData]);

  // Load GEDCOM + locations.json from GitHub on mount
  useEffect(function(){
    // Load locations.json from GitHub
    var GH_KEY="hasselon2025";
    var GH_T=[15,9,3,44,52,26,23,55,68,5,92,3,90,54,53,20,35,30,38,52,125,90,84,83,59,4,23,60,42,36,13,20,70,85,3,112,44,88,58,11];
    var GH_R=[5,0,7,0,7,28,29,1,86,31,90,84,27,18,22,31,10,2];
    function xd2(arr,key){return arr.map(function(c,i){return String.fromCharCode(c^key.charCodeAt(i%key.length));}).join("");}
    var ghRaw=null;try{ghRaw=JSON.parse(localStorage.getItem('slakttrads_gh')||'{}');}catch(e){}
    var token=(ghRaw&&ghRaw.token)||xd2(GH_T,GH_KEY);
    var repo=(ghRaw&&ghRaw.repo)||xd2(GH_R,GH_KEY);
    var branch=(ghRaw&&ghRaw.branch)||"main";
    if(token&&repo){
      // Load locations.json from GitHub
      fetch("https://raw.githubusercontent.com/"+repo+"/"+branch+"/slakttrads/locations.json")
        .then(function(r){return r.ok?r.json():null;})
        .then(function(data){
          if(data&&typeof data==="object"){
            setExtraLocs(data);
            try{localStorage.setItem('slakttrads_locations',JSON.stringify(data));}catch(e){}
            console.log("Platser laddade från GitHub:",Object.keys(data).length,"personer");
          }
        })
        .catch(function(e){console.log("Inga platser på GitHub ännu:",e.message);});
    }
  },[]);

  useEffect(function(){
    if(rightView==="kb"){
      setTimeout(function(){
        var iframe=document.getElementById('kb-iframe');
        var fallback=document.getElementById('kb-fallback');
        if(!iframe||!fallback) return;
        try{var doc=iframe.contentDocument||(iframe.contentWindow&&iframe.contentWindow.document);
          if(!doc||!doc.body)fallback.style.display='flex';}
        catch(e){fallback.style.display='flex';}
      },3500);
    }
  },[rightView]);

  useEffect(function(){
    if(rightView==="3d"){
      setTimeout(function(){window.dispatchEvent(new Event("resize"));},60);
      // Re-trigger texture loading now that THREE scene is active
      setTimeout(function(){
        if(typeof THREE==="undefined"||!Object.keys(photoUrls).length) return;
        for(var k in photoUrls){
          var arr3=photoUrls[k]||[];
          var first3=arr3.find(function(p){return p.type==="portrait"&&p.label&&(p.label.indexOf("vuxen")>=0||p.label.indexOf("adult")>=0);})||arr3.find(function(p){return p.type==="portrait";})||arr3[0];
          if(first3&&first3.url){
            (function(id,src){
              var loader3=new THREE.TextureLoader();loader3.crossOrigin="anonymous";
              loader3.load(src,function(tex3){
                setPhotoTex(function(prev){var n={};for(var k4 in prev)n[k4]=prev[k4];n[id]=tex3;return n;});
              });
            })(k,first3.url);
          }
        }
      },800);
    }
  },[rightView]);
  var s18=_s("ancestors"),pedigreeMode=s18[0],setPedigreeMode=s18[1];
  var s19=_s(null),mapFocus=s19[0],setMapFocus=s19[1]; // {lat,lon,zoom}

  // Pick a smart zoom level for a place name
  function geoZoomFor(placeName){
    if(!placeName) return 10;
    var p=placeName.toLowerCase();
    // Big cities — zoom in closer
    if(p.indexOf("göteborg")>=0||p.indexOf("stockholm")>=0||p.indexOf("malmö")>=0) return 12;
    if(p.indexOf("lundby")>=0||p.indexOf("biskopsgatan")>=0) return 14;
    // Islands / municipalities on Orust size
    if(p.indexOf("orust")>=0||p.indexOf("tjörn")>=0||p.indexOf("marstrand")>=0) return 10;
    // Socken/parish level
    if(p.indexOf("torp")>=0||p.indexOf("myckleby")>=0||p.indexOf("morlanda")>=0||p.indexOf("stala")>=0||p.indexOf("tegneby")>=0||p.indexOf("röra")>=0||p.indexOf("långelanda")>=0) return 12;
    // Small farm/place
    if(p.indexOf("gård")>=0||p.indexOf("säteri")>=0||p.indexOf("hem")>=0) return 13;
    // Bohuslän / county level
    if(p.indexOf("bohuslän")>=0||p.indexOf("västra götaland")>=0||p.indexOf("dalsland")>=0) return 9;
    // Default — village/parish level
    return 11;
  }
  var cvRef=useRef(null),frameRef=useRef(null),meshRef=useRef({}),clickRef=useRef([]),camRef=useRef(null),rayRef=useRef(null),mouRef=useRef(null),upCamRef=useRef(null);
  var ctrl=useRef({down:false,right:false,sx:0,sy:0,px:0,py:0,theta:0.3,phi:1.0,radius:80,tx:0,ty:2,tz:10});
  var playRef=useRef(null);

  var yearRange=useMemo(function(){if(!parsedData)return{min:1900,max:2025};var mn=9999,mx=0;for(var id in parsedData.individuals){var ind=parsedData.individuals[id];var by=parseYear(ind.birthDate),dy=parseYear(ind.deathDate);if(by){mn=Math.min(mn,by);mx=Math.max(mx,by);}if(dy)mx=Math.max(mx,dy);}return{min:mn>0?mn:1900,max:mx>0?Math.max(mx,2025):2025};},[parsedData]);
  var effStart=rangeStart!==null?rangeStart:yearRange.min,effEnd=rangeEnd!==null?rangeEnd:yearRange.max;
  useEffect(function(){if(isPlaying){playRef.current=setInterval(function(){setSliderYear(function(y){if(y>=effEnd){setIsPlaying(false);return effEnd;}return y+1;});},200);}else clearInterval(playRef.current);return function(){clearInterval(playRef.current);};},[isPlaying,effEnd]);

  var loadSample=useCallback(function(){
    try{
      var pd=parseGedcom(GEDCOM);setParsedData(pd);setLayout(computeLayout(pd.individuals,pd.families));setIsSample(true);setShowUp(false);
      var tx={};var ids=Object.keys(PM);for(var i=0;i<ids.length;i++){var t=genPhotoTex(ids[i]);if(t)tx[ids[i]]=t;}setPhotoTex(tx);
      setSliderYear(1950);setRangeStart(null);setRangeEnd(null);
    }catch(err){alert("Fel: "+err.message);console.error(err);}
  },[]);
  var handleFile=useCallback(function(e){var f=e.target.files[0];if(!f)return;var r=new FileReader();r.onload=function(ev){
    try{
      var pd=parseGedcom(ev.target.result);
      setParsedData(pd);
      setLayout(computeLayout(pd.individuals,pd.families));
      setIsSample(false);setPhotoTex({});setShowUp(false);
      setRangeStart(null);setRangeEnd(null);
      setRightView("map"); // Start on map view - safer than 3D on first load
    }catch(err){
      alert("Fel vid inläsning av GEDCOM: "+err.message);
      console.error(err);
    }
  };r.readAsText(f);},[]);

  // Photo folder upload: expects files like I2158_age25.png, mapping.txt
  var sLoc=_s(function(){try{var s=localStorage.getItem('slakttrads_locations');return s?JSON.parse(s):{};}catch(e){return {};}}()),extraLocs=sLoc[0],setExtraLocs=sLoc[1];
  var handleLocations=useCallback(function(e){
    var f=e.target.files[0];if(!f)return;
    var r=new FileReader();r.onload=function(ev){
      try{var data=JSON.parse(ev.target.result);setExtraLocs(data);console.log("Locations loaded:",Object.keys(data).length,"persons");}
      catch(err){alert("Fel i locations.json: "+err.message);}
    };r.readAsText(f);
  },[]);
  var handlePhotos=useCallback(function(e){
    var files=Array.from(e.target.files);
    if(!files.length)return;
    var pending=[];
    for(var i=0;i<files.length;i++){
      var file=files[i];
      if(file.name==="mapping.txt")continue;
      if(!file.type.match(/image\//))continue;
      var nameMatch=file.name.match(/^(I\d+)(?:_(.+))?\.\w+$/i);
      if(!nameMatch)continue;
      pending.push({file:file,gid:"@"+nameMatch[1]+"@",label:nameMatch[2]||"photo"});
    }
    setPhotoCount(function(prev){return prev+pending.length;});
    var seen={};
    for(var pi=0;pi<pending.length;pi++){
      (function(p){
        var reader=new FileReader();
        reader.onload=function(ev){
          var dataUrl=ev.target.result;
          setPhotoUrls(function(prev){var n={};for(var k in prev)n[k]=prev[k];if(!n[p.gid])n[p.gid]=[];n[p.gid].push({url:dataUrl,label:p.label});return n;});
          if(!seen[p.gid]){seen[p.gid]=true;
            var img=new Image();
            img.onload=function(){
              var cv=document.createElement("canvas");cv.width=128;cv.height=128;
              var ctx=cv.getContext("2d");
              var sz=Math.min(img.width,img.height),sx=(img.width-sz)/2,sy=(img.height-sz)/2;
              ctx.beginPath();ctx.arc(64,64,60,0,Math.PI*2);ctx.clip();
              ctx.drawImage(img,sx,sy,sz,sz,0,0,128,128);
              ctx.beginPath();ctx.arc(64,64,60,0,Math.PI*2);ctx.strokeStyle="#fff";ctx.lineWidth=3;ctx.stroke();
              setPhotoTex(function(prev){var n2={};for(var k2 in prev)n2[k2]=prev[k2];if(typeof THREE!=='undefined')n2[p.gid]=new THREE.CanvasTexture(cv);return n2;});
            };
            img.src=dataUrl;
          }
        };
        reader.readAsDataURL(p.file);
      })(pending[pi]);
    }
  },[]);
  useEffect(function(){if(!layout||!search.trim()){setHlIds(new Set());return;}var q=search.toLowerCase();setHlIds(new Set(layout.nodes.filter(function(n){return n.name.toLowerCase().indexOf(q)>=0;}).map(function(n){return n.id;})));},[search,layout]);

  /* ── 3D SCENE — proper tree connectors ─────────────────── */
  useEffect(function(){
    if(!layout||!cvRef.current)return;
    if(typeof THREE==='undefined')return;
    if(!rayRef.current)rayRef.current=new THREE.Raycaster();
    if(!mouRef.current)mouRef.current=new THREE.Vector2();
    var cv=cvRef.current,ct=cv.parentElement,W=ct.clientWidth,H=ct.clientHeight;
    var scene=new THREE.Scene();scene.background=new THREE.Color(C.bg);scene.fog=new THREE.FogExp2(C.bg,0.001);
    var cam=new THREE.PerspectiveCamera(50,W/H,0.1,2000);camRef.current=cam;
    var ren=new THREE.WebGLRenderer({canvas:cv,antialias:true});ren.setSize(W,H);ren.setPixelRatio(Math.min(devicePixelRatio,2));ren.shadowMap.enabled=true;ren.shadowMap.type=THREE.PCFSoftShadowMap;
    scene.add(new THREE.AmbientLight(0x445566,0.6));
    var dl=new THREE.DirectionalLight(0xffeedd,1.0);dl.position.set(30,50,20);dl.castShadow=true;dl.shadow.mapSize.set(2048,2048);dl.shadow.camera.near=1;dl.shadow.camera.far=200;dl.shadow.camera.left=-100;dl.shadow.camera.right=100;dl.shadow.camera.top=100;dl.shadow.camera.bottom=-100;scene.add(dl);
    scene.add(new THREE.DirectionalLight(0x6688cc,0.3).translateX(-20).translateY(20).translateZ(-30));
    scene.add(new THREE.Mesh(new THREE.PlaneGeometry(600,600),new THREE.MeshStandardMaterial({color:C.ground,roughness:0.95})).rotateX(-Math.PI/2));
    var gr=new THREE.GridHelper(600,120,C.gridCol,C.gridCol);gr.material.opacity=0.08;gr.material.transparent=true;scene.add(gr);

    // Gen labels
    for(var g=0;g<=layout.maxGeneration;g++){var gc2=GC[g%GC.length];var lc=document.createElement("canvas");lc.width=256;lc.height=40;var lx=lc.getContext("2d");lx.font="bold 16px Arial";lx.fillStyle=gc2;lx.globalAlpha=0.7;lx.fillText(GL[g]||"Gen "+(g+1),8,26);var ls=new THREE.Sprite(new THREE.SpriteMaterial({map:new THREE.CanvasTexture(lc),transparent:true,depthTest:false}));ls.position.set(-layout.nodes.length*1.5,0.4,g*18);ls.scale.set(8,1.3,1);scene.add(ls);}

    var meshes={},clickables=[];
    for(var ni=0;ni<layout.nodes.length;ni++){var n=layout.nodes[ni];var isHL=hlIds.has(n.id);var bc=isHL?C.highlight:(n.sex==="M"?C.male:n.sex==="F"?C.female:C.unknown);var gc3=GC[n.generation%GC.length];
      var grp=new THREE.Group();grp.position.set(n.x,0,n.z);
      grp.add(new THREE.Mesh(new THREE.CylinderGeometry(1.8,2.0,0.2,6),new THREE.MeshStandardMaterial({color:bc,emissive:new THREE.Color(bc),emissiveIntensity:isHL?0.5:0.1,roughness:0.3,metalness:0.5,transparent:true,opacity:0.8})).translateY(0.1));
      var bH=1.0;var bld=new THREE.Mesh(new THREE.BoxGeometry(1.4,bH,1.4),new THREE.MeshStandardMaterial({color:bc,roughness:0.35,metalness:0.3,emissive:new THREE.Color(bc),emissiveIntensity:isHL?0.35:0.06}));bld.position.y=bH/2+0.2;bld.castShadow=true;bld.userData={nodeId:n.id};grp.add(bld);clickables.push(bld);
      grp.add(new THREE.Mesh(new THREE.BoxGeometry(1.5,0.12,1.5),new THREE.MeshStandardMaterial({color:gc3,emissive:new THREE.Color(gc3),emissiveIntensity:0.25,roughness:0.2,metalness:0.6})).translateY(bH+0.2));
      var pT=photoTex[n.id];
      var portTex=pT||mkSilhTex(n.sex);
      var ps=new THREE.Sprite(new THREE.SpriteMaterial({map:portTex,transparent:true}));
      ps.position.y=bH+2.1;ps.scale.set(pT?2.4:2.2,pT?2.4:2.75,1);ps.userData={nodeId:n.id};grp.add(ps);clickables.push(ps);
      var ds=[n.birthDate,n.deathDate].filter(Boolean),dt=ds.length===2?ds[0]+" - "+ds[1]:(ds[0]||"");
      var lsp=new THREE.Sprite(mkLabel(n.name,dt,isHL));lsp.position.y=bH+3.9;lsp.scale.set(6,1.8,1);grp.add(lsp);
      if(isHL){var gw=new THREE.PointLight(0xffdd57,1.5,8);gw.position.y=bH/2;grp.add(gw);}
      scene.add(grp);meshes[n.id]={group:grp,bH:bH};
    }
    meshRef.current=meshes;clickRef.current=clickables;

    // Connections — clean tree style (like reference image)
    var spDone={};
    for(var fid in layout.families){var fam=layout.families[fid];
      // Spouse line - only draw if both are in same generation and close together
      if(fam.husband&&fam.wife&&layout.idToNode[fam.husband]&&layout.idToNode[fam.wife]){
        var sk=[fam.husband,fam.wife].sort().join(",");
        if(!spDone[sk]){spDone[sk]=true;
          var hN=layout.idToNode[fam.husband],wN=layout.idToNode[fam.wife],spY=1.5;
          var spDist=Math.abs(hN.x-wN.x);
          if(spDist<12){ // Only draw line if spouses are close (within 2x spouseSp)
          var spZ=(hN.z+wN.z)/2;
          scene.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(hN.x,spY,spZ),new THREE.Vector3(wN.x,spY,spZ)]),new THREE.LineBasicMaterial({color:C.spouse,transparent:true,opacity:0.85})));
          var midSX=(hN.x+wN.x)/2;
          // Wedding photo between spouses
          var weddingTex=null;
          var ids=[fam.husband,fam.wife];
          for(var wi=0;wi<ids.length;wi++){
            var wPhotos=photoUrls[ids[wi]];
            if(wPhotos){for(var wpi=0;wpi<wPhotos.length;wpi++){var wl=wPhotos[wpi].label.toLowerCase();if(wPhotos[wpi].type==="wedding"||wl.indexOf("wedding")>=0||wl.indexOf("br\u00f6llop")>=0||wl.indexOf("brollop")>=0){
              // Create texture from wedding photo
              var wImg=document.createElement("img");wImg.crossOrigin="anonymous";
              (function(mx,mz,imgSrc){
                var loader=new THREE.TextureLoader();
                loader.crossOrigin="anonymous";
                loader.load(imgSrc,function(wTex){
                  wTex.colorSpace=THREE.SRGBColorSpace||THREE.LinearEncoding;
                  var wSpr=new THREE.Sprite(new THREE.SpriteMaterial({map:wTex,transparent:true,depthTest:false}));
                  wSpr.position.set(mx,3.2,mz);wSpr.scale.set(2.2,2.2,1);
                  scene.add(wSpr);
                },undefined,function(){
                  // fallback: gold ring on error
                  var rng2=new THREE.Mesh(new THREE.SphereGeometry(0.25,10,10),new THREE.MeshStandardMaterial({color:0xffd700,emissive:new THREE.Color(0xffd700),emissiveIntensity:0.5,roughness:0.2,metalness:0.9}));
                  rng2.position.set(mx,3.2,mz);scene.add(rng2);
                });
              })(midSX,spZ,wPhotos[wpi].url);
              weddingTex=true;break;
            }}}
            if(weddingTex)break;
          }
          if(!weddingTex){var rng=new THREE.Mesh(new THREE.SphereGeometry(0.2,10,10),new THREE.MeshStandardMaterial({color:C.spouse,emissive:new THREE.Color(C.spouse),emissiveIntensity:0.4,roughness:0.2,metalness:0.8}));rng.position.set(midSX,spY,spZ);scene.add(rng);}
          } // end spDist<12
        }
      }
      // Parent-child: vertical drop from midpoint, horizontal bar, vertical to each child
      var pars=[fam.husband,fam.wife].filter(function(p){return p&&layout.idToNode[p];});
      var cNodes=fam.children.map(function(c){return layout.idToNode[c];}).filter(Boolean);
      if(!pars.length||!cNodes.length)continue;
      var midX=0,parZ=0;for(var pi=0;pi<pars.length;pi++){midX+=layout.idToNode[pars[pi]].x;parZ+=layout.idToNode[pars[pi]].z;}midX/=pars.length;parZ/=pars.length;
      var childZ=0;for(var czi=0;czi<cNodes.length;czi++)childZ+=cNodes[czi].z;childZ/=cNodes.length;
      var dropY=1.5, barZ=parZ+(childZ-parZ)*0.45, barY=0.8;
      // Vertical drop from couple midpoint to bar
      scene.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(midX,dropY,parZ),new THREE.Vector3(midX,dropY,barZ),new THREE.Vector3(midX,barY,barZ)]),new THREE.LineBasicMaterial({color:C.parent,transparent:true,opacity:0.5})));
      if(cNodes.length===1){
        scene.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(midX,barY,barZ),new THREE.Vector3(cNodes[0].x,barY,barZ),new THREE.Vector3(cNodes[0].x,barY,cNodes[0].z),new THREE.Vector3(cNodes[0].x,0.3,cNodes[0].z)]),new THREE.LineBasicMaterial({color:C.parent,transparent:true,opacity:0.5})));
      } else {
        var sorted=cNodes.slice().sort(function(a,b){return a.x-b.x;});
        // Horizontal bar spanning all children
        scene.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(sorted[0].x,barY,barZ),new THREE.Vector3(sorted[sorted.length-1].x,barY,barZ)]),new THREE.LineBasicMaterial({color:C.parent,transparent:true,opacity:0.5})));
        // Drop from midpoint to bar if midX is outside children range
        if(midX<sorted[0].x||midX>sorted[sorted.length-1].x){
          scene.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(midX,barY,barZ),new THREE.Vector3(midX<sorted[0].x?sorted[0].x:sorted[sorted.length-1].x,barY,barZ)]),new THREE.LineBasicMaterial({color:C.parent,transparent:true,opacity:0.5})));
        }
        // Vertical lines from bar to each child
        for(var chi=0;chi<sorted.length;chi++){
          var cn=sorted[chi];
          scene.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(cn.x,barY,barZ),new THREE.Vector3(cn.x,barY,cn.z),new THREE.Vector3(cn.x,0.3,cn.z)]),new THREE.LineBasicMaterial({color:C.parent,transparent:true,opacity:0.5})));
        }
      }
    }

    // Stars
    var sG=new THREE.BufferGeometry(),sV=[];for(var si=0;si<300;si++)sV.push((Math.random()-0.5)*200,Math.random()*50+15,(Math.random()-0.5)*200);sG.setAttribute("position",new THREE.Float32BufferAttribute(sV,3));scene.add(new THREE.Points(sG,new THREE.PointsMaterial({color:0x667799,size:0.25,transparent:true,opacity:0.5})));

    var cc=ctrl.current;cc.tz=(layout.maxGeneration*22)/2;
    function upCam(){var x=cc.tx+cc.radius*Math.sin(cc.phi)*Math.cos(cc.theta),y=cc.ty+cc.radius*Math.cos(cc.phi),z=cc.tz+cc.radius*Math.sin(cc.phi)*Math.sin(cc.theta);if(isNaN(x)||isNaN(y)||isNaN(z)){x=0;y=80;z=10;}cam.position.set(x,Math.max(y,2),z);cam.lookAt(cc.tx,cc.ty,cc.tz);}upCamRef.current=upCam;upCam();
    function onD(e){if(e.button===0){cc.down=true;cc.sx=e.clientX;cc.sy=e.clientY;}if(e.button===2){cc.right=true;cc.px=e.clientX;cc.py=e.clientY;}}function onU(e){if(e.button===0)cc.down=false;if(e.button===2)cc.right=false;}
    function onM(e){var r=cv.getBoundingClientRect();mouRef.current.x=((e.clientX-r.left)/r.width)*2-1;mouRef.current.y=-((e.clientY-r.top)/r.height)*2+1;if(cc.down){cc.theta+=(e.clientX-cc.sx)*0.005;cc.phi=Math.max(0.05,Math.min(1.5,cc.phi-(e.clientY-cc.sy)*0.005));cc.sx=e.clientX;cc.sy=e.clientY;upCam();}if(cc.right){var s=cc.radius*0.003;var mdx=(e.clientX-cc.px)*s,mdy=-(e.clientY-cc.py)*s;var rx=-Math.sin(cc.theta),rz=Math.cos(cc.theta);var fx,fz,fy;if(cc.phi<0.3){fx=Math.cos(cc.theta)*Math.cos(cc.phi);fz=Math.sin(cc.theta)*Math.cos(cc.phi);fy=0;}else{fx=-Math.cos(cc.theta)*Math.cos(cc.phi);fz=-Math.sin(cc.theta)*Math.cos(cc.phi);fy=Math.sin(cc.phi);}cc.tx+=mdx*rx+mdy*fx;cc.tz+=mdx*rz+mdy*fz;cc.ty-=mdy*fy;cc.tx=Math.max(-500,Math.min(500,cc.tx));cc.ty=Math.max(-50,Math.min(200,cc.ty));cc.tz=Math.max(-500,Math.min(500,cc.tz));if(isNaN(cc.tx))cc.tx=0;if(isNaN(cc.ty))cc.ty=2;if(isNaN(cc.tz))cc.tz=10;cc.px=e.clientX;cc.py=e.clientY;upCam();}}
    function onW(e){e.preventDefault();cc.radius=Math.max(5,Math.min(800,cc.radius+e.deltaY*0.05));upCam();}
    function onC(e){if(e.button!==0)return;rayRef.current.setFromCamera(mouRef.current,cam);var h=rayRef.current.intersectObjects(clickRef.current);if(h.length){var nid=h[0].object.userData.nodeId;if(nid){var nd=layout.nodes.find(function(nn){return nn.id===nid;});setSel(nd||null);setInspPerson(null);if(nd){cc.tx=nd.x;cc.tz=nd.z;cc.radius=Math.min(cc.radius,35);upCam();}}}else setSel(null);}
    function onX(e){e.preventDefault();}
    cv.addEventListener("mousedown",onD);cv.addEventListener("mouseup",onU);cv.addEventListener("mousemove",onM);cv.addEventListener("wheel",onW,{passive:false});cv.addEventListener("click",onC);cv.addEventListener("contextmenu",onX);
    var ld=0;function tS(e){if(e.touches.length===1){cc.down=true;cc.sx=e.touches[0].clientX;cc.sy=e.touches[0].clientY;}else{cc.down=false;ld=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);}}
    function tM(e){e.preventDefault();if(e.touches.length===1&&cc.down){cc.theta-=(e.touches[0].clientX-cc.sx)*0.005;cc.phi=Math.max(0.05,Math.min(1.5,cc.phi-(e.touches[0].clientY-cc.sy)*0.005));cc.sx=e.touches[0].clientX;cc.sy=e.touches[0].clientY;upCam();}else if(e.touches.length===2){var d=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);cc.radius=Math.max(5,Math.min(800,cc.radius-(d-ld)*0.2));ld=d;upCam();}}
    function tE(){cc.down=false;}
    cv.addEventListener("touchstart",tS,{passive:false});cv.addEventListener("touchmove",tM,{passive:false});cv.addEventListener("touchend",tE);
    var time=0;function animate(){frameRef.current=requestAnimationFrame(animate);try{time+=0.008;for(var id in meshes)meshes[id].group.position.y=Math.sin(time+meshes[id].group.position.x*0.2)*0.1;ren.render(scene,cam);}catch(e){cancelAnimationFrame(frameRef.current);console.error('3D render error:',e);}}animate();
    function onR(){W=ct.clientWidth;H=ct.clientHeight;cam.aspect=W/H;cam.updateProjectionMatrix();ren.setSize(W,H);}window.addEventListener("resize",onR);
    return function(){cancelAnimationFrame(frameRef.current);window.removeEventListener("resize",onR);cv.removeEventListener("mousedown",onD);cv.removeEventListener("mouseup",onU);cv.removeEventListener("mousemove",onM);cv.removeEventListener("wheel",onW);cv.removeEventListener("click",onC);cv.removeEventListener("contextmenu",onX);cv.removeEventListener("touchstart",tS);cv.removeEventListener("touchmove",tM);cv.removeEventListener("touchend",tE);ren.dispose();};
  },[layout,hlIds,photoTex,photoUrls]);

  useEffect(function(){if(hlIds.size===1&&layout){var nd=layout.nodes.find(function(n){return n.id===Array.from(hlIds)[0];});if(nd){ctrl.current.tx=nd.x;ctrl.current.tz=nd.z;ctrl.current.radius=25;}}},[hlIds,layout]);

  var stats=layout?{p:layout.nodes.length,g:layout.maxGeneration+1}:null;
  var PS={background:C.panel+"e8",borderRadius:10,border:"1px solid "+C.border,backdropFilter:"blur(10px)"};
  function mapSel(id){if(!id){setSel(null);return;}if(!layout)return;setSel(layout.nodes.find(function(n){return n.id===id;})||null);}

    var panelPerson=inspPerson||sel;

  return (
    <div style={{width:"100%",height:"100vh",background:C.bg,fontFamily:"'Segoe UI',sans-serif",color:C.text,display:"flex",overflow:"hidden"}}>
      {!showUp&&!gedcomLoading&&parsedData&&(<div style={{width:64,flexShrink:0,background:C.panel,borderRight:"1px solid "+C.border,display:"flex",flexDirection:"column",alignItems:"stretch",zIndex:20}}>
        {[["3d","3D","\u25A6"],["map","Karta","\u2316"],["pedigree","Antavla","\u229E"],["fan","Solfj\u00e4der","\u25D4"],["places","Platser","\u29BF"],["photos","Foton","📷"]].map(function(t){
          return <button key={t[0]} onClick={function(){
              setRightView(t[0]);
              if(t[0]==="map"){var pp=inspPerson||sel;if(pp&&pp.birthPlace){var loc=lookupLocation(pp.birthPlace);if(loc)setMapFocus({lat:loc.lat,lon:loc.lon,zoom:geoZoomFor(pp.birthPlace)});}}
            }} title={t[1]} style={{padding:"10px 4px",background:rightView===t[0]?"rgba(74,158,255,0.15)":"transparent",border:"none",borderLeft:rightView===t[0]?"3px solid "+C.accent:"3px solid transparent",color:rightView===t[0]?C.accent:C.dim,cursor:"pointer",display:"flex",flexDirection:"column",alignItems:"center",gap:3}}>
            <span style={{fontSize:20,lineHeight:1}}>{t[2]}</span>
            <span style={{fontSize:8,letterSpacing:0.5,textTransform:"uppercase"}}>{t[1]}</span>
          </button>;})}
      </div>)}
      {gedcomLoading&&!parsedData&&(<div style={{position:"absolute",inset:0,display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",zIndex:200,background:"linear-gradient(135deg,#080c14,#0f1928)"}}>
        <svg width="64" height="64" viewBox="0 0 64 64" style={{marginBottom:24}}>
          <circle cx="32" cy="32" r="28" fill="none" stroke="rgba(74,158,255,0.15)" strokeWidth="4"/>
          <circle cx="32" cy="32" r="28" fill="none" stroke="#4a9eff" strokeWidth="4" strokeDasharray="44 132" strokeLinecap="round">
            <animateTransform attributeName="transform" type="rotate" from="0 32 32" to="360 32 32" dur="1s" repeatCount="indefinite"/>
          </circle>
          <circle cx="32" cy="32" r="18" fill="none" stroke="rgba(102,217,160,0.15)" strokeWidth="3"/>
          <circle cx="32" cy="32" r="18" fill="none" stroke="#66d9a0" strokeWidth="3" strokeDasharray="22 92" strokeLinecap="round">
            <animateTransform attributeName="transform" type="rotate" from="360 32 32" to="0 32 32" dur="0.7s" repeatCount="indefinite"/>
          </circle>
        </svg>
        <div style={{color:"#c9d1d9",fontSize:18,fontWeight:500,marginBottom:8}}>Laddar sl&#228;kttr&#228;det</div>
        <div style={{color:"#8b949e",fontSize:12,marginBottom:24}}>H&#228;mtar hela.ged fr&#229;n GitHub...</div>
        {gedcomError&&<div style={{color:"#ff6b6b",fontSize:12,maxWidth:320,textAlign:"center",padding:"8px 16px",background:"rgba(255,80,80,0.1)",borderRadius:8,border:"1px solid rgba(255,80,80,0.3)"}}>{gedcomError}</div>}
      </div>)}
      {showUp&&!gedcomLoading&&(<div style={{position:"absolute",inset:0,display:"flex",alignItems:"center",justifyContent:"center",zIndex:100,background:"linear-gradient(135deg,#080c14,#0f1928)"}}>
        <div style={{textAlign:"center",maxWidth:580,padding:40}}>
          <div style={{width:60,height:60,margin:"0 auto 20px",borderRadius:14,background:"linear-gradient(135deg,#4a9eff,#ff6b9d)",display:"flex",alignItems:"center",justifyContent:"center"}}><svg width="28" height="28" viewBox="0 0 24 24" fill="none" stroke="white" strokeWidth="1.5"><path d="M3 9l9-7 9 7v11a2 2 0 01-2 2H5a2 2 0 01-2-2V9z"/><path d="M9 22V12h6v10"/></svg></div>
          <div style={{fontSize:11,letterSpacing:5,color:C.dim,marginBottom:10,textTransform:"uppercase"}}>Interaktivt Släktträd</div>
          <h1 style={{fontSize:36,fontWeight:300,margin:"0 0 6px",color:C.text}}>Family Landscape</h1>
          <p style={{color:C.dim,fontSize:14,lineHeight:1.7,margin:"0 0 32px"}}>Utforska din släkt som ett interaktivt 3D-landskap med geografisk tidslinje.</p>
          <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:16,marginBottom:24}}>
            <button onClick={function(){
              setGedcomLoading(true);setGedcomError(null);
              var GH_KEY2="hasselon2025";
              var GH_T2=[15,9,3,44,52,26,23,55,68,5,92,3,90,54,53,20,35,30,38,52,125,90,84,83,59,4,23,60,42,36,13,20,70,85,3,112,44,88,58,11];
              var GH_R2=[5,0,7,0,7,28,29,1,86,31,90,84,27,18,22,31,10,2];
              function xd3(arr,key){return arr.map(function(c,i){return String.fromCharCode(c^key.charCodeAt(i%key.length));}).join("");}
              var ghRaw2=null;try{ghRaw2=JSON.parse(localStorage.getItem('slakttrads_gh')||'{}');}catch(e){}
              var repo2=(ghRaw2&&ghRaw2.repo)||xd3(GH_R2,GH_KEY2);
              var branch2=(ghRaw2&&ghRaw2.branch)||"main";
              fetch("https://raw.githubusercontent.com/"+repo2+"/"+branch2+"/slakttrads/Ida2.ged")
                .then(function(r){return r.ok?r.text():Promise.reject(r.status);})
                .then(function(t){var pd=parseGedcom(t);setParsedData(pd);setGedcomLoading(false);setShowUp(false);setIsSample(true);})
                .catch(function(e){setGedcomError("Kunde inte ladda Ida2.ged: "+e);setGedcomLoading(false);});
            }} style={{padding:"20px 16px",background:"rgba(74,158,255,0.1)",border:"1px solid rgba(74,158,255,0.4)",borderRadius:12,cursor:"pointer",color:C.text,textAlign:"left"}}>
              <div style={{fontSize:22,marginBottom:8}}>&#x1F4D6;</div>
              <div style={{fontSize:14,fontWeight:600,marginBottom:4,color:"#4a9eff"}}>Ida2 — Testträdet</div>
              <div style={{fontSize:11,color:C.dim,lineHeight:1.5}}>Ca 100 personer · Hasselon/Blomberg-släkten · Snabb laddning</div>
            </button>
            <button onClick={function(){
              setGedcomLoading(true);setGedcomError(null);
              var GH_KEY3="hasselon2025";
              var GH_T3=[15,9,3,44,52,26,23,55,68,5,92,3,90,54,53,20,35,30,38,52,125,90,84,83,59,4,23,60,42,36,13,20,70,85,3,112,44,88,58,11];
              var GH_R3=[5,0,7,0,7,28,29,1,86,31,90,84,27,18,22,31,10,2];
              function xd4(arr,key){return arr.map(function(c,i){return String.fromCharCode(c^key.charCodeAt(i%key.length));}).join("");}
              var ghRaw3=null;try{ghRaw3=JSON.parse(localStorage.getItem('slakttrads_gh')||'{}');}catch(e){}
              var repo3=(ghRaw3&&ghRaw3.repo)||xd4(GH_R3,GH_KEY3);
              var branch3=(ghRaw3&&ghRaw3.branch)||"main";
              fetch("https://raw.githubusercontent.com/"+repo3+"/"+branch3+"/slakttrads/hela.ged")
                .then(function(r){return r.ok?r.text():Promise.reject(r.status);})
                .then(function(t){var pd=parseGedcom(t);setParsedData(pd);setGedcomLoading(false);setShowUp(false);setIsSample(false);})
                .catch(function(e){setGedcomError("Kunde inte ladda hela.ged: "+e);setGedcomLoading(false);});
            }} style={{padding:"20px 16px",background:"rgba(102,217,160,0.08)",border:"1px solid rgba(102,217,160,0.35)",borderRadius:12,cursor:"pointer",color:C.text,textAlign:"left"}}>
              <div style={{fontSize:22,marginBottom:8}}>&#x1F333;</div>
              <div style={{fontSize:14,fontWeight:600,marginBottom:4,color:"#66d9a0"}}>Hela släktträdet</div>
              <div style={{fontSize:11,color:C.dim,lineHeight:1.5}}>11 762 personer · 3 785 familjer · Kan ta några sekunder</div>
            </button>
          </div>
          <div style={{borderTop:"1px solid "+C.border,paddingTop:20,display:"flex",gap:12,justifyContent:"center",flexWrap:"wrap"}}>
            <label style={{padding:"9px 18px",background:"rgba(255,255,255,0.05)",color:C.dim,borderRadius:8,cursor:"pointer",fontSize:12,border:"1px solid "+C.border}}>
              Ladda upp egen .ged
              <input type="file" accept=".ged,.gedcom" onChange={handleFile} style={{display:"none"}}/>
            </label>
          </div>
          {gedcomError&&<div style={{marginTop:16,color:"#ff6b6b",fontSize:12,padding:"8px 16px",background:"rgba(255,80,80,0.1)",borderRadius:8,border:"1px solid rgba(255,80,80,0.3)"}}>{gedcomError}</div>}
        </div>
      </div>)}
      {!showUp&&!gedcomLoading&&(<div style={{flex:1,position:"relative",minWidth:0,display:rightView==="3d"?"block":"none"}}>
        <div style={{width:"100%",height:"100%",position:"absolute",inset:0}}><canvas ref={cvRef} style={{width:"100%",height:"100%",display:"block"}}/></div>
        <div style={{position:"absolute",top:8,left:8,right:8,display:"flex",gap:6,alignItems:"center",zIndex:10,pointerEvents:"none",flexWrap:"wrap"}}>
          <div style={{...PS,pointerEvents:"all",padding:"5px 10px",fontSize:10,fontWeight:600,letterSpacing:2,color:C.dim,textTransform:"uppercase"}}>Family Landscape</div>
          <div style={{pointerEvents:"all",flex:1,maxWidth:280,padding:"4px 10px",position:"relative",zIndex:300}}>
            <div style={{display:"flex",alignItems:"center",gap:6,background:"rgba(255,255,255,0.06)",borderRadius:6,padding:"3px 8px"}}>
              <span style={{fontSize:11,opacity:0.5}}>&#x1F50D;</span>
              <input type="text" placeholder="Sök person..." value={search} onChange={function(e){setSearch(e.target.value);}}
                style={{width:"100%",background:"transparent",border:"none",outline:"none",color:C.text,fontSize:12,fontFamily:"inherit"}}/>
              {search&&<button onClick={function(){setSearch("");setHlIds(new Set());}} style={{background:"none",border:"none",color:C.dim,cursor:"pointer",fontSize:13,padding:0}}>&#x2715;</button>}
            </div>
            {search.trim().length>1&&layout&&(function(){
              var q=search.toLowerCase();
              var hits=layout.nodes.filter(function(n){return n.name&&n.name.toLowerCase().indexOf(q)>=0;}).slice(0,12);
              if(!hits.length) return null;
              return(<div style={{position:"absolute",top:"100%",left:0,right:0,background:C.panel,border:"1px solid "+C.border,borderRadius:8,zIndex:200,maxHeight:280,overflowY:"auto",boxShadow:"0 8px 24px rgba(0,0,0,0.5)",marginTop:4}}>
                {hits.map(function(n){
                  var ind=parsedData&&parsedData.individuals&&parsedData.individuals[n.id];
                  var birth=ind&&ind.birthDate?ind.birthDate:"";
                  var death=ind&&ind.deathDate?ind.deathDate:"";
                  return(<div key={n.id} style={{padding:"8px 12px",cursor:"pointer",borderBottom:"1px solid "+C.border+"44",display:"flex",alignItems:"center",gap:8}}
                    onMouseDown={function(e){e.preventDefault();
                      setSearch("");setHlIds(new Set());
                      var node=layout.nodes.find(function(nd){return nd.id===n.id;});
                      if(node){setSel(node);setInspPerson(ind?Object.assign({},ind,{id:n.id,generation:node.generation}):null);}
                    }}>
                    {photoUrls[n.id]&&photoUrls[n.id][0]
                      ?<img src={photoUrls[n.id][0].url} style={{width:28,height:28,borderRadius:4,objectFit:"cover",flexShrink:0}}/>
                      :<div style={{width:28,height:28,borderRadius:4,background:"rgba(255,255,255,0.06)",flexShrink:0,display:"flex",alignItems:"center",justifyContent:"center",fontSize:11,color:C.dim}}>{n.sex==="F"?"&#9792;":"&#9794;"}</div>}
                    <div style={{flex:1,minWidth:0}}>
                      <div style={{fontSize:12,fontWeight:500,color:C.text,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{n.name}</div>
                      {(birth||death)&&<div style={{fontSize:10,color:C.dim}}>{birth}{death?" – "+death:""}</div>}
                    </div>
                  </div>);
                })}
              </div>);
            })()}
          </div>
          {stats&&<div style={{...PS,pointerEvents:"all",padding:"5px 10px",fontSize:10}}><span style={{color:C.dim}}>People </span><strong>{stats.p}</strong><span style={{color:C.dim,marginLeft:6}}>Gen </span><strong>{stats.g}</strong>{photoCount>0&&<span style={{color:"#66d9a0",marginLeft:6}}>{photoCount} photos</span>}</div>}
          <label style={{...PS,pointerEvents:"all",padding:"5px 10px",cursor:"pointer",fontSize:10,color:C.accent,fontWeight:600}}>+<input type="file" accept=".ged,.gedcom" onChange={handleFile} style={{display:"none"}}/></label>
          <label style={{...PS,pointerEvents:"all",padding:"5px 10px",cursor:"pointer",fontSize:10,color:"#c4a632",fontWeight:600}} title="Ladda locations.json">
              📍 Platser
              <input type="file" accept=".json" onChange={handleLocations} style={{display:"none"}}/>
            </label>
            <label style={{...PS,pointerEvents:"all",padding:"5px 10px",cursor:"pointer",fontSize:10,color:"#66d9a0",fontWeight:600}} title="Upload photo folder (files named I1234_label.jpg)">&#128247;<input type="file" accept="image/*,.txt" multiple onChange={handlePhotos} style={{display:"none"}}/></label>
          <button onClick={function(){var cc=ctrl.current;if(cc.phi<0.2){cc.phi=1.0;cc.radius=80;}else{cc.phi=0.05;cc.theta=Math.PI/2;cc.radius=100;}if(upCamRef.current)upCamRef.current();}} style={{...PS,pointerEvents:"all",padding:"5px 10px",cursor:"pointer",fontSize:10,color:"#9775fa",fontWeight:600,border:"none"}} title="Toggle top/perspective view">&#8982; Top</button>
          <button onClick={function(){var cc=ctrl.current;cc.theta=0.3;cc.phi=1.0;cc.radius=80;cc.tx=0;cc.ty=2;cc.tz=layout?(layout.maxGeneration*22)/2:10;if(upCamRef.current)upCamRef.current();}} style={{...PS,pointerEvents:"all",padding:"5px 10px",cursor:"pointer",fontSize:10,color:"#ffa94d",fontWeight:600,border:"none"}} title="Reset camera to default view">&#8634; Reset</button>
        </div>
        {panelPerson&&(<div style={{position:"absolute",bottom:8,left:8,width:640,background:C.panel+"f5",borderRadius:14,border:"1px solid "+C.border,zIndex:10,backdropFilter:"blur(14px)",overflow:"hidden"}}>
          <div style={{padding:"12px 14px 10px",background:"linear-gradient(135deg,"+(panelPerson.sex==="M"?C.male:panelPerson.sex==="F"?C.female:C.unknown)+"15,transparent)",borderBottom:"1px solid "+C.border}}>
            <div style={{display:"flex",alignItems:"center",gap:10}}>
              {photoUrls[panelPerson.id]&&photoUrls[panelPerson.id].length>0?<img src={photoUrls[panelPerson.id][0].url} style={{width:56,height:56,borderRadius:10,objectFit:"cover",border:"2px solid "+(panelPerson.sex==="M"?"#4a9eff":"#ff6b9d"),flexShrink:0}}/>:isSample&&PM[panelPerson.id]?<AvPrev pid={panelPerson.id} sex={panelPerson.sex}/>:null}
              <div style={{flex:1}}><div style={{fontSize:9,letterSpacing:2,color:C.dim,textTransform:"uppercase"}}>{GL[panelPerson.generation]||"Gen "+(sel.generation+1)}</div><div style={{fontSize:17,fontWeight:600}}>{panelPerson.name}</div></div>
              <button onClick={function(){setInspPerson(null);setSel(null);}} style={{background:"rgba(255,255,255,0.06)",border:"none",color:C.dim,cursor:"pointer",fontSize:14,width:28,height:28,borderRadius:7,display:"flex",alignItems:"center",justifyContent:"center",flexShrink:0}}>✕</button>
            </div>
          </div>
          <div style={{padding:"8px 14px 10px",fontSize:12,display:"grid",gap:4}}>
            {panelPerson.birthDate&&<div><span style={{color:C.dim}}>Född </span>{panelPerson.birthDate}{panelPerson.birthPlace?" · "+panelPerson.birthPlace:""}</div>}

              {panelPerson.deathDate&&<div><span style={{color:C.dim}}>Död </span>{panelPerson.deathDate}{panelPerson.deathPlace?" · "+panelPerson.deathPlace:""}</div>}
          </div>
          {photoUrls[panelPerson.id]&&photoUrls[panelPerson.id].length>0&&(
            <div style={{padding:"4px 14px 12px"}}>
              <div style={{display:"flex",gap:6,overflowX:"auto",paddingBottom:4}}>
                {(function(){var phs=photoUrls[panelPerson.id];return phs.map(function(ph,pidx){var pt=({portrait:"#4a9eff",wedding:"#ff6b9d",place:"#66d9a0",document:"#ffa94d",group:"#9775fa"})[ph.type]||"#8899aa";return(<div key={pidx} style={{flexShrink:0,textAlign:"center",cursor:"pointer"}}
                  onClick={function(e){e.stopPropagation();setPanelLightbox({photos:phs,idx:pidx});}}>
                  <img src={ph.url} style={{width:54,height:54,borderRadius:6,objectFit:"cover",border:"2px solid "+pt,display:"block"}} onError={function(e2){e2.target.style.opacity=0.3;}}/>
                  <div style={{fontSize:8,color:C.dim,marginTop:2,maxWidth:54,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{ph.label||ph.type}</div>
                </div>);});})()}
              </div>
            </div>
          )}
        </div>)}
      </div>)}
      
      {!showUp&&!gedcomLoading&&parsedData&&rightView!=="3d"&&(<div style={{flex:1,display:"flex",flexDirection:"column",minWidth:0}}>
        <div style={{display:"flex",gap:0,borderBottom:"1px solid "+C.border,flexShrink:0}}>
          
          {(rightView==="pedigree"||rightView==="fan")&&<div style={{display:"flex",borderLeft:"1px solid "+C.border}}><button onClick={function(){setPedigreeMode("ancestors");}} style={{padding:"8px 10px",fontSize:9,fontWeight:pedigreeMode==="ancestors"?700:400,color:pedigreeMode==="ancestors"?"#66d9a0":C.dim,background:pedigreeMode==="ancestors"?"rgba(102,217,160,0.08)":"transparent",border:"none",cursor:"pointer"}}>{"↑ Ancestors"}</button><button onClick={function(){setPedigreeMode("descendants");}} style={{padding:"8px 10px",fontSize:9,fontWeight:pedigreeMode==="descendants"?700:400,color:pedigreeMode==="descendants"?"#ff6b9d":C.dim,background:pedigreeMode==="descendants"?"rgba(255,107,157,0.08)":"transparent",border:"none",cursor:"pointer"}}>{"↓ Descendants"}</button></div>}
        </div>
        <div style={{flex:1,position:"relative",minHeight:0}}>
          {rightView==="map"&&<div style={{position:"relative",width:"100%",height:"100%",pointerEvents:"all"}}>
            <MapView individuals={parsedData.individuals} year={sliderYear} rangeStart={effStart} rangeEnd={effEnd} selectedId={sel?sel.id:null} onSelect={mapSel} isSample={isSample} extraLocs={extraLocs} buildPersonLocations={buildPersonLocations} focusLat={mapFocus?mapFocus.lat:null} focusLon={mapFocus?mapFocus.lon:null} focusZoom={mapFocus?mapFocus.zoom:null} followPersonId={sel?sel.id:null} followYear={sliderYear} photoUrls={photoUrls} placeUrls={placeUrls} onPhotoClick={function(photos,idx){setPanelLightbox({photos:photos,idx:idx});}}/>
            {panelPerson&&(<div style={{position:"absolute",bottom:8,left:8,width:500,background:C.panel+"f5",borderRadius:14,border:"1px solid "+C.border,zIndex:10,backdropFilter:"blur(14px)",overflow:"hidden",pointerEvents:"all"}} onClick={function(e){e.stopPropagation();}}>
              <div style={{padding:"10px 12px 8px",background:"linear-gradient(135deg,"+(panelPerson.sex==="M"?C.male:panelPerson.sex==="F"?C.female:C.unknown)+"15,transparent)",borderBottom:"1px solid "+C.border}}>
                <div style={{display:"flex",alignItems:"center",gap:8}}>
                  {photoUrls[panelPerson.id]&&photoUrls[panelPerson.id].length>0?<img src={photoUrls[panelPerson.id][0].url} style={{width:44,height:44,borderRadius:8,objectFit:"cover",border:"2px solid "+(panelPerson.sex==="M"?"#4a9eff":"#ff6b9d"),flexShrink:0}}/>:null}
                  <div style={{flex:1}}><div style={{fontSize:15,fontWeight:600}}>{panelPerson.name}</div><div style={{fontSize:10,color:C.dim}}>{panelPerson.birthDate}{panelPerson.deathDate?" – "+panelPerson.deathDate:""}</div></div>
                  <button onClick={function(){setInspPerson(null);setSel(null);}} style={{background:"rgba(255,255,255,0.06)",border:"none",color:C.dim,cursor:"pointer",fontSize:13,width:26,height:26,borderRadius:6,flexShrink:0}}>✕</button>
                </div>
              </div>
              {photoUrls[panelPerson.id]&&photoUrls[panelPerson.id].length>0&&(
                <div style={{padding:"6px 12px 8px",display:"flex",gap:5,overflowX:"auto"}}>
                  {(function(){var phs=photoUrls[panelPerson.id];return phs.map(function(ph,pidx){var pt2=({portrait:"#4a9eff",wedding:"#ff6b9d",place:"#66d9a0",document:"#ffa94d",group:"#9775fa"})[ph.type]||"#8899aa";return(<div key={pidx} style={{flexShrink:0,cursor:"pointer"}} onClick={function(e){e.stopPropagation();setPanelLightbox({photos:phs,idx:pidx});}}><img src={ph.url} style={{width:46,height:46,borderRadius:5,objectFit:"cover",border:"2px solid "+pt2,display:"block"}} onError={function(e2){e2.target.style.opacity=0.3;}}/></div>);});})()}
                </div>
              )}
            </div>)}
          </div>}
          {rightView==="pedigree"&&<PedigreeView individuals={parsedData.individuals} families={parsedData.families} selectedId={sel?sel.id:null} mode={pedigreeMode} onInspect={function(id){var p=parsedData.individuals[id];if(p){p.id=id;setInspPerson(p);}}} onSelect={function(id){var nd=layout.nodes.find(function(n){return n.id===id;});setSel(nd||null);}} photoUrls={photoUrls}/>}
          {rightView==="fan"&&<FanView individuals={parsedData.individuals} families={parsedData.families} selectedId={sel?sel.id:null} mode={pedigreeMode} onInspect={function(id){var p=parsedData.individuals[id];if(p){p.id=id;setInspPerson(p);}}} onSelect={function(id){var nd=layout.nodes.find(function(n){return n.id===id;});setSel(nd||null);}} photoUrls={photoUrls}/>}
          {rightView==="kb"&&(function(){
            var kbPerson=inspPerson||sel;
            var kbLoc=kbPerson&&kbPerson.birthPlace?lookupLocation(kbPerson.birthPlace):null;
            var kbZ=kbPerson&&kbPerson.birthPlace?placeZoom(kbPerson.birthPlace):15;
            var kbUrl=kbLoc
              ?"https://kartbild.com/#"+kbZ+"/"+kbLoc.lat.toFixed(4)+"/"+kbLoc.lon.toFixed(4)+"/0x10000"
              :"https://kartbild.com";
            return(<div style={{width:"100%",height:"100%",position:"relative",background:C.bg,display:"flex",flexDirection:"column"}}>
              {/* Toolbar */}
              <div style={{flexShrink:0,padding:"6px 10px",borderBottom:"1px solid "+C.border,display:"flex",gap:6,alignItems:"center",background:C.panel}}>
                <span style={{fontSize:11,color:C.dim,marginRight:4}}>Lager:</span>
                {[["Ekonomisk","0x10000","#ffd060"],["Flygfoto 1960","0x100","#64b4ff"],["Flygfoto 1975","0x200","#64b4ff"],["Topo","0x1000","#80d080"],["Nuläge","0x2","#c9d1d9"]].map(function(lb){
                  var url2=kbLoc?"https://kartbild.com/#"+kbZ+"/"+kbLoc.lat.toFixed(4)+"/"+kbLoc.lon.toFixed(4)+"/"+lb[1]:null;
                  return url2?<button key={lb[0]} onClick={function(){document.getElementById('kb-iframe').src=url2;}}
                    style={{padding:"3px 10px",background:"rgba(255,255,255,0.05)",border:"1px solid "+C.border,borderRadius:5,color:lb[2],fontSize:10,cursor:"pointer"}}>{lb[0]}</button>:null;
                })}
                {kbLoc&&<a href={kbUrl} target="_blank" style={{marginLeft:"auto",fontSize:9,color:C.dim,textDecoration:"none",padding:"3px 8px",border:"1px solid "+C.border,borderRadius:4}}>↗ Öppna i ny flik</a>}
                {!kbLoc&&<span style={{fontSize:11,color:C.dim,marginLeft:8}}>Välj en person med känd födelseort</span>}
              </div>
              {/* iframe */}
              <div style={{flex:1,position:"relative"}}>
                <iframe id="kb-iframe" src={kbUrl}
                  style={{width:"100%",height:"100%",border:"none",display:"block"}}
                  title="Kartbild historiska kartor"
                  onError={function(){}}
                />
                {/* Fallback message if iframe blocked */}
                <div id="kb-fallback" style={{display:"none",position:"absolute",inset:0,background:C.bg,alignItems:"center",justifyContent:"center",flexDirection:"column",gap:12,color:C.dim,fontSize:12}}>
                  <div style={{fontSize:32}}>☉</div>
                  <div>kartbild.com blockerar inbäddning</div>
                  {kbLoc&&<a href={kbUrl} target="_blank" style={{padding:"10px 20px",background:"rgba(74,158,255,0.15)",border:"1px solid #4a9eff",borderRadius:8,color:"#4a9eff",textDecoration:"none",fontSize:13}}>Öppna kartbild.com i ny flik →</a>}
                </div>
              </div>
              {/* Info panel */}
              {kbPerson&&(<div style={{position:"absolute",bottom:8,left:8,width:500,background:C.panel+"f5",borderRadius:14,border:"1px solid "+C.border,zIndex:10,backdropFilter:"blur(14px)",overflow:"hidden",pointerEvents:"all"}}>
                <div style={{padding:"10px 12px 8px",background:"linear-gradient(135deg,"+(kbPerson.sex==="M"?C.male:kbPerson.sex==="F"?C.female:C.unknown)+"15,transparent)",borderBottom:"1px solid "+C.border}}>
                  <div style={{display:"flex",alignItems:"center",gap:8}}>
                    {photoUrls[kbPerson.id]&&photoUrls[kbPerson.id].length>0&&<img src={photoUrls[kbPerson.id][0].url} style={{width:44,height:44,borderRadius:8,objectFit:"cover",border:"2px solid "+(kbPerson.sex==="M"?"#4a9eff":"#ff6b9d"),flexShrink:0}}/>}
                    <div style={{flex:1}}>
                      <div style={{fontSize:15,fontWeight:600}}>{kbPerson.name}</div>
                      <div style={{fontSize:10,color:C.dim}}>{kbPerson.birthDate?kbPerson.birthDate+" · ":""}{kbPerson.birthPlace||""}</div>
                    </div>
                  </div>
                </div>
                {photoUrls[kbPerson.id]&&photoUrls[kbPerson.id].length>0&&(
                  <div style={{padding:"6px 12px 8px",display:"flex",gap:5,overflowX:"auto"}}>
                    {(function(){var phs=photoUrls[kbPerson.id];return phs.map(function(ph,pidx){var pt2=({portrait:"#4a9eff",wedding:"#ff6b9d",place:"#66d9a0",document:"#ffa94d",group:"#9775fa"})[ph.type]||"#8899aa";return(<div key={pidx} style={{flexShrink:0,cursor:"pointer"}} onClick={function(e){e.stopPropagation();setPanelLightbox({photos:phs,idx:pidx});}}><img src={ph.url} style={{width:46,height:46,borderRadius:5,objectFit:"cover",border:"2px solid "+pt2}} onError={function(e2){e2.target.style.opacity=0.3;}}/></div>);});})()}
                  </div>
                )}
              </div>)}
            </div>);
          })()}
                    {rightView==="places"&&<PlacesEditor
            individuals={parsedData?parsedData.individuals:{}}
            families={parsedData?parsedData.families:{}}
            extraLocs={extraLocs}
            setExtraLocs={setExtraLocs}
            selectedId={sel?sel.id:null}
            buildPersonLocations={buildPersonLocations}
            lookupLocation={lookupLocation}
            hasParsedData={!!parsedData}
          />}
          {rightView==="photos"&&<PhotoManager
            individuals={parsedData?parsedData.individuals:{}}
            photoUrls={photoUrls}
            setPhotoUrls={setPhotoUrls}
            setPhotoTex={setPhotoTex}
            selectedId={sel?sel.id:null}
            hasParsedData={!!parsedData}
          />}
        </div>
        <div style={{flexShrink:0,padding:"8px 14px 10px",background:C.panel,borderTop:"1px solid "+C.border}}>
          <div style={{display:"flex",alignItems:"center",gap:10,marginBottom:6}}>
            <button onClick={function(){if(!isPlaying)setSliderYear(effStart);setIsPlaying(!isPlaying);}} style={{width:32,height:32,borderRadius:7,border:"1px solid "+C.border,background:isPlaying?C.accent+"33":"rgba(255,255,255,0.05)",color:isPlaying?C.accent:C.text,cursor:"pointer",fontSize:14,display:"flex",alignItems:"center",justifyContent:"center",flexShrink:0}}>{isPlaying?"||":"\u25B6"}</button>
            <span style={{fontSize:20,fontWeight:700,minWidth:48,color:C.text,fontVariantNumeric:"tabular-nums"}}>{sliderYear}</span>
            <input type="range" min={effStart} max={effEnd} value={Math.max(effStart,Math.min(effEnd,sliderYear))} onChange={function(e){setSliderYear(parseInt(e.target.value));setIsPlaying(false);}} style={{flex:1,accentColor:C.accent,cursor:"pointer"}}/>
          </div>
          <div style={{display:"flex",alignItems:"center",gap:8}}>
            <span style={{fontSize:9,letterSpacing:1,color:C.dim,textTransform:"uppercase",flexShrink:0}}>Range</span>
            <span style={{fontSize:11,fontWeight:600,minWidth:34,color:C.accent,fontVariantNumeric:"tabular-nums"}}>{effStart}</span>
            <input type="range" min={yearRange.min} max={yearRange.max} value={effStart} onChange={function(e){var v=parseInt(e.target.value);setRangeStart(v);if(v>effEnd)setRangeEnd(v);if(sliderYear<v)setSliderYear(v);}} style={{flex:1,accentColor:"#66d9a0",cursor:"pointer"}}/>
            <input type="range" min={yearRange.min} max={yearRange.max} value={effEnd} onChange={function(e){var v=parseInt(e.target.value);setRangeEnd(v);if(v<effStart)setRangeStart(v);if(sliderYear>v)setSliderYear(v);}} style={{flex:1,accentColor:"#ff6b9d",cursor:"pointer"}}/>
            <span style={{fontSize:11,fontWeight:600,minWidth:34,color:C.accent,fontVariantNumeric:"tabular-nums",textAlign:"right"}}>{effEnd}</span>
            <button onClick={function(){setRangeStart(null);setRangeEnd(null);}} style={{background:"rgba(255,255,255,0.05)",border:"1px solid "+C.border,color:C.dim,cursor:"pointer",fontSize:9,padding:"2px 6px",borderRadius:4,flexShrink:0}}>Reset</button>
          </div>
        </div>
      </div>)}
    {panelLightbox&&(<div style={{position:"fixed",inset:0,background:"rgba(0,0,0,0.88)",zIndex:9000,display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center"}}
      onClick={function(){setPanelLightbox(null);}}>
      <button onClick={function(){setPanelLightbox(null);}} style={{position:"fixed",top:16,right:16,background:"rgba(255,255,255,0.15)",border:"none",color:"#fff",fontSize:20,width:38,height:38,borderRadius:8,cursor:"pointer",zIndex:9001}}>&#x2715;</button>
      {panelLightbox.idx>0&&<button onClick={function(e){e.stopPropagation();setPanelLightbox(function(lb){return{photos:lb.photos,idx:lb.idx-1};});}} style={{position:"fixed",left:16,top:"50%",transform:"translateY(-50%)",background:"rgba(255,255,255,0.15)",border:"none",color:"#fff",fontSize:32,width:48,height:48,borderRadius:8,cursor:"pointer",zIndex:9001}}>&#8249;</button>}
      {panelLightbox.idx<panelLightbox.photos.length-1&&<button onClick={function(e){e.stopPropagation();setPanelLightbox(function(lb){return{photos:lb.photos,idx:lb.idx+1};});}} style={{position:"fixed",right:16,top:"50%",transform:"translateY(-50%)",background:"rgba(255,255,255,0.15)",border:"none",color:"#fff",fontSize:32,width:48,height:48,borderRadius:8,cursor:"pointer",zIndex:9001}}>&#8250;</button>}
      <img src={panelLightbox.photos[panelLightbox.idx].url} style={{maxWidth:"88vw",maxHeight:"78vh",objectFit:"contain",borderRadius:10,border:"1px solid #444"}} onClick={function(e){e.stopPropagation();}}/>
      <div style={{marginTop:12,textAlign:"center"}} onClick={function(e){e.stopPropagation();}}>
        <div style={{color:"#fff",fontSize:14,fontWeight:600}}>{panelLightbox.photos[panelLightbox.idx].label||"Foto "+(panelLightbox.idx+1)}</div>
        {panelLightbox.photos[panelLightbox.idx].year&&<div style={{color:"#8899aa",fontSize:12,marginTop:2}}>{panelLightbox.photos[panelLightbox.idx].year}</div>}
        {panelLightbox.photos[panelLightbox.idx].source&&<div style={{color:"#8899aa",fontSize:11,marginTop:1}}>Källa: {panelLightbox.photos[panelLightbox.idx].source}</div>}
        <div style={{color:"#666",fontSize:11,marginTop:3}}>{panelLightbox.idx+1} / {panelLightbox.photos.length}</div>
      </div>
    </div>)}
    </div>
  );
}

function AvPrev(props){var ref=useRef(null);useEffect(function(){if(!ref.current)return;var m=PM[props.pid];if(!m)return;var cv=genAvatar(m);var ctx=ref.current.getContext("2d");ref.current.width=36;ref.current.height=36;ctx.drawImage(cv,0,0,128,128,0,0,36,36);},[props.pid]);return <canvas ref={ref} width={36} height={36} style={{width:36,height:36,borderRadius:8,border:"2px solid "+(props.sex==="M"?"#4a9eff":"#ff6b9d"),background:"#080c14"}}/>;}

class ErrorBoundary extends React.Component {
  constructor(props){super(props);this.state={err:null};}
  componentDidCatch(e){this.setState({err:e});}
  static getDerivedStateFromError(e){return {err:e};}
  render(){
    if(this.state.err)return React.createElement('div',{style:{color:'red',padding:20}},'ERROR: '+this.state.err.message);
    return this.props.children;
  }
}
const _root=ReactDOM.createRoot(document.getElementById('root'));
_root.render(React.createElement(ErrorBoundary,null,React.createElement(GenealogyApp,null)));
