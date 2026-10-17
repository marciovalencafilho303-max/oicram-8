const W=550,H=400,N=120,Z=1.35,$=s=>document.querySelector(s);
const cv=$('#stage'),cx=cv.getContext('2d'),hc=document.createElement('canvas').getContext('2d'),sw=$('#sw');
cv.width=W*2;cv.height=H*2;
const fresh=()=>({layers:[{name:'Layer 1',vis:1,lock:0,keys:{0:[]}}],len:24,fps:12,bg:'#ffffff',lib:[]});
let S;try{S=JSON.parse(localStorage.oicram8)}catch(e){}
if(!S||!S.layers)S=fresh();
let cur=0,cl=0,tool='brush',zoom=1,onion=false,sel=null,play=null,drag=null,hover=null,scrub=false;
let hist=[JSON.stringify(S)],hi=0;
const val=id=>$(id).value;
const SIZES=[2,4,8,14,24,40];let SZ=14;
const size=()=>SZ,pw=()=>Math.max(1,Math.round(SZ/4));

/* ---------- estado ---------- */
const save=()=>{try{localStorage.oicram8=JSON.stringify(S)}catch(e){}};
function commit(){hist.length=hi+1;hist.push(JSON.stringify(S));hi++;if(hist.length>60){hist.shift();hi--}save();ui()}
function restore(i){if(i<0||i>=hist.length)return;hi=i;S=JSON.parse(hist[i]);$('#bgc').value=S.bg;$('#fps').value=S.fps;sel=null;cur=Math.min(cur,S.len-1);cl=Math.min(cl,S.layers.length-1);save();ui()}
const kf=(l,f)=>{for(let i=f;i>=0;i--)if(l.keys[i])return i;return -1};
const objs=(l,f)=>{const k=kf(l,f);return k<0?null:l.keys[k]};
function curObjs(){const l=S.layers[cl],k=kf(l,cur);if(k<0){l.keys[cur]=[];return l.keys[cur]}return l.keys[k]}
const clone=o=>JSON.parse(JSON.stringify(o));

/* ---------- imagens (preenchimentos do balde) ---------- */
const IMG={};
function img(o){let m=IMG[o.src];if(!m){m=IMG[o.src]=new Image;m.onload=render;m.src=o.src}return m}
const pc=document.createElement('canvas');pc.width=W*2;pc.height=H*2;const pcx=pc.getContext('2d',{willReadFrequently:true});
function inImg(o,pt){const m=img(o);if(!m.complete)return false;pcx.clearRect(0,0,pc.width,pc.height);pcx.drawImage(m,0,0);return pcx.getImageData(pt[0]*2|0,pt[1]*2|0,1,1).data[3]>10}
function preload(){const ims=[];S.layers.forEach(l=>Object.values(l.keys).forEach(a=>a.forEach(o=>{if(o.t=='i')ims.push(img(o))})));
  return Promise.all(ims.map(m=>m.complete?0:new Promise(r=>{m.addEventListener('load',r);m.addEventListener('error',r)})))}
function dil(a,w,h,r){const t=new Uint8Array(a.length),o=new Uint8Array(a.length);
  for(let y=0;y<h;y++){let c=0;const b=y*w;for(let x=-r;x<w;x++){if(x+r<w)c+=a[b+x+r];if(x-r-1>=0)c-=a[b+x-r-1];if(x>=0)t[b+x]=c>0?1:0}}
  for(let x=0;x<w;x++){let c=0;for(let y=-r;y<h;y++){if(y+r<h)c+=t[(y+r)*w+x];if(y-r-1>=0)c-=t[(y-r-1)*w+x];if(y>=0)o[y*w+x]=c>0?1:0}}
  return o}
/* balde: acerta objetos preenchidos/traços; em áreas vazias fecha a região (com tolerância de lacunas) */
function bucket(p,fc){
  const hh=hit(p,1);
  if(hh){const o=hh.o;if(o.t=='p'||o.t=='l')o.c=fc;else o.f=fc;commit();return}
  const w=W*2,h=H*2,n=w*h,c=document.createElement('canvas');c.width=w;c.height=h;
  const x=c.getContext('2d',{willReadFrequently:true});x.scale(2,2);
  curObjs().forEach(o=>{if(o.t!='i')drawObj(x,o)});
  const d=x.getImageData(0,0,w,h).data;let bar=new Uint8Array(n);
  for(let i=0;i<n;i++)bar[i]=d[i*4+3]>=64?1:0;
  const g=+val('#gap');if(g)bar=dil(bar,w,h,g);
  const s=(p[1]*2|0)*w+(p[0]*2|0);if(bar[s])return;
  let m=new Uint8Array(n);const st=[s];m[s]=1;
  while(st.length){const i=st.pop(),xx=i%w;
    for(const j of[xx>0?i-1:-1,xx<w-1?i+1:-1,i>=w?i-w:-1,i<n-w?i+w:-1])if(j>=0&&!m[j]&&!bar[j]){m[j]=1;st.push(j)}}
  if(m.reduce((q,v)=>q+v,0)>n*.5){S.bg=fc;$('#bgc').value=fc;$('#ebg').value=fc;commit();return}
  m=dil(m,w,h,Math.max(g,1));
  const[r,gr,b]=[1,3,5].map(k=>parseInt(fc.substr(k,2),16)),out=x.createImageData(w,h);
  for(let i=0;i<n;i++)if(m[i]){out.data[i*4]=r;out.data[i*4+1]=gr;out.data[i*4+2]=b;out.data[i*4+3]=255}
  x.putImageData(out,0,0);
  const a=curObjs();let k=0;while(a[k]&&a[k].t=='i')k++;
  a.splice(k,0,{t:'i',src:c.toDataURL()});commit()}
/* suavização do lápis ao soltar o mouse */
function dist(p,a,b){const dx=b[0]-a[0],dy=b[1]-a[1],l=dx*dx+dy*dy;
  if(!l)return Math.hypot(p[0]-a[0],p[1]-a[1]);
  return Math.abs(dy*p[0]-dx*p[1]+b[0]*a[1]-b[1]*a[0])/Math.sqrt(l)}
function rdp(q,e){if(q.length<3)return q;let m=0,k=0;
  for(let i=1;i<q.length-1;i++){const d=dist(q[i],q[0],q[q.length-1]);if(d>m){m=d;k=i}}
  if(m<=e)return[q[0],q[q.length-1]];
  return rdp(q.slice(0,k+1),e).slice(0,-1).concat(rdp(q.slice(k),e))}
function chaikin(q,n){while(n--){const r=[q[0]];
  for(let i=0;i<q.length-1;i++){const a=q[i],b=q[i+1];r.push([a[0]*.75+b[0]*.25,a[1]*.75+b[1]*.25],[a[0]*.25+b[0]*.75,a[1]*.25+b[1]*.75])}
  r.push(q[q.length-1]);q=r}return q}
const smooth=q=>q.length<3?q:chaikin(rdp(q,4),3);

/* ---------- desenho ---------- */
function pathOf(o){const p=new Path2D;if(o.t=='i')return p;
  if(o.t=='p'){const q=o.pts;p.moveTo(...q[0]);
    if(q.length<3)q.forEach(a=>p.lineTo(...a));
    else{for(let i=1;i<q.length-1;i++)p.quadraticCurveTo(...q[i],(q[i][0]+q[i+1][0])/2,(q[i][1]+q[i+1][1])/2);p.lineTo(...q[q.length-1])}}
  else if(o.t=='l'){p.moveTo(o.x,o.y);p.lineTo(o.x2,o.y2)}
  else if(o.t=='r')p.rect(o.x,o.y,o.w,o.h);
  else p.ellipse(o.x+o.w/2,o.y+o.h/2,Math.abs(o.w/2),Math.abs(o.h/2),0,0,7);
  return p}
function drawObj(c,o){if(o.t=='i'){const m=img(o);if(m.complete&&m.naturalWidth)c.drawImage(m,0,0,W,H);return}const p=pathOf(o);c.lineCap=c.lineJoin='round';
  if(o.f){c.fillStyle=o.f;c.fill(p)}
  if(o.s){c.strokeStyle=o.c;c.lineWidth=o.s;c.stroke(p)}}
function drawFrame(c,f,a){c.globalAlpha=a;S.layers.forEach(l=>{if(!l.vis)return;const o=objs(l,f);if(o)o.forEach(x=>drawObj(c,x))});c.globalAlpha=1}
function render(){
  cx.setTransform(2,0,0,2,0,0);cx.clearRect(0,0,W,H);cx.fillStyle=S.bg;cx.fillRect(0,0,W,H);
  if(onion&&cur>0)drawFrame(cx,cur-1,.25);
  drawFrame(cx,cur,1);
  if(sel){cx.save();cx.setLineDash([6,4]);cx.lineCap=cx.lineJoin='round';cx.strokeStyle='#4da3ff';cx.lineWidth=(sel.s||1)+4;cx.stroke(pathOf(sel));cx.restore()}
  if(hover&&!play&&(tool=='brush'||tool=='eraser')){cx.beginPath();cx.arc(hover[0],hover[1],size()/2,0,7);cx.fillStyle=tool=='brush'?'#000a':'#f003';cx.fill()}}
function hit(pt,tol=6){const a=curObjs();
  for(let i=a.length-1;i>=0;i--){const o=a[i];if(o.t=='i')continue;const p=pathOf(o);hc.lineWidth=(o.s||0)+tol;
    if(hc.isPointInStroke(p,...pt)||(o.f&&hc.isPointInPath(p,...pt)))return{o,a,i}}
  return null}
function eraseAt(pt){const a=curObjs();let n=0;
  for(let i=a.length-1;i>=0;i--){const o=a[i];if(o.t=='i'){if(inImg(o,pt)){a.splice(i,1);n++}continue}const p=pathOf(o);hc.lineWidth=(o.s||0)+size();
    if(hc.isPointInStroke(p,...pt)||(o.f&&hc.isPointInPath(p,...pt))){if(sel===o)sel=null;a.splice(i,1);n++}}
  return n}
function mv(o,dx,dy){if(o.pts)o.pts.forEach(q=>{q[0]+=dx;q[1]+=dy});else{o.x+=dx;o.y+=dy;if(o.t=='l'){o.x2+=dx;o.y2+=dy}}}
const pos=e=>{const r=cv.getBoundingClientRect();return[(e.clientX-r.left)/r.width*W,(e.clientY-r.top)/r.height*H]};

cv.onpointerdown=e=>{
  if(play)return;
  const p=pos(e),L=S.layers[cl];cv.setPointerCapture(e.pointerId);
  if(tool=='hand'){drag={hand:1,x:e.clientX,y:e.clientY,sx:sw.scrollLeft,sy:sw.scrollTop};return}
  if(tool=='zoom'){setZoom(zoom*(e.shiftKey||e.altKey?.5:2));return}
  if(tool=='eye'){render();const d=cx.getImageData(p[0]*2|0,p[1]*2|0,1,1).data;
    const h='#'+[...d].slice(0,3).map(v=>v.toString(16).padStart(2,'0')).join('');
    if(e.shiftKey)$('#fc').value=h;else $('#sc').value=h;return}
  if(L.lock||!L.vis)return;
  const a=curObjs(),sc=val('#sc'),fc=val('#fc');
  if(tool=='brush'||tool=='pencil'){const o={t:'p',pts:[p],c:tool=='brush'?fc:sc,s:tool=='brush'?size():pw()};a.push(o);sel=null;drag={o,pencil:tool=='pencil'}}
  else if(tool=='line'){const o={t:'l',x:p[0],y:p[1],x2:p[0],y2:p[1],c:sc,s:pw()};a.push(o);drag={o}}
  else if(tool=='rect'||tool=='oval'){const o={t:tool=='rect'?'r':'o',x:p[0],y:p[1],w:0,h:0,c:sc,s:pw(),f:fc};a.push(o);drag={o,sp:p}}
  else if(tool=='eraser'){drag={er:1,n:eraseAt(p)}}
  else if(tool=='select'){const h=hit(p);sel=h?h.o:null;if(h)drag={mv:h.o,last:p,moved:0}}
  else if(tool=='bucket')bucket(p,fc);
  render()};
cv.onpointermove=e=>{
  const p=pos(e);hover=p;const d=drag;
  if(d){
    if(d.hand){sw.scrollLeft=d.sx-(e.clientX-d.x);sw.scrollTop=d.sy-(e.clientY-d.y)}
    else if(d.mv){mv(d.mv,p[0]-d.last[0],p[1]-d.last[1]);d.last=p;d.moved=1}
    else if(d.er)d.n+=eraseAt(p);
    else if(d.o){const o=d.o;
      if(o.t=='p'){const q=o.pts[o.pts.length-1];if(Math.hypot(p[0]-q[0],p[1]-q[1])>1.5)o.pts.push(p)}
      else if(o.t=='l'){o.x2=p[0];o.y2=p[1]}
      else{o.w=p[0]-d.sp[0];o.h=p[1]-d.sp[1]}}}
  render()};
cv.onpointerup=()=>{const d=drag;drag=null;if(!d)return;
  if(d.pencil){const q=d.o.pts;if(q.length>8&&Math.hypot(q[0][0]-q[q.length-1][0],q[0][1]-q[q.length-1][1])<12)q[q.length-1]=[...q[0]];d.o.pts=smooth(q)}
  if(d.o||d.er&&d.n||d.mv&&d.moved)commit();else render()};
cv.onpointerleave=()=>{hover=null;render()};

/* ---------- zoom e ferramentas ---------- */
function setZoom(z){zoom=Math.min(4,Math.max(.25,z));cv.style.width=W*Z*zoom+'px';cv.style.height=H*Z*zoom+'px';
  const s=$('#zs');s.querySelectorAll('[data-c]').forEach(o=>o.remove());if(![...s.options].some(o=>+o.value==zoom)){const o=new Option(Math.round(zoom*100)+'%',zoom);o.dataset.c=1;s.add(o)}s.value=zoom}
$('#zs').onchange=e=>setZoom(+e.target.value);
$('#zi').onclick=()=>setZoom(zoom*1.25);$('#zo').onclick=()=>setZoom(zoom/1.25);
const T=[['select','selection','Seleção (V)','v'],['pencil','pencil','Lápis (Y)','y'],['brush','paintbrush','Pincel (B)','b'],['line','line','Linha (N)','n'],['rect','rectangle','Retângulo (R)','r'],['oval','oval','Oval (O)','o'],['bucket','paintBucket','Balde de tinta (K)','k'],['eye','eyedropper','Conta-gotas (I)','i'],['eraser','eraser','Borracha (E)','e'],['hand','hand','Mão (H)','h'],['zoom','magnifier','Zoom (Z)','z']];
const cursors={select:'default',hand:'grab',zoom:'zoom-in',eraser:'none',brush:'none'};
function setTool(t){tool=t;sel=t=='select'?sel:null;cv.style.cursor=cursors[t]||'crosshair';document.querySelectorAll('#tgrid button').forEach(b=>b.classList.toggle('on',b.dataset.t==t));render()}
T.forEach(([id,ic,tt])=>{const b=document.createElement('button');b.innerHTML=`<img src="icons/${ic}.gif" alt="">`;b.title=tt;b.dataset.t=id;b.onclick=()=>setTool(id);$('#tgrid').append(b)});
const sb=$('#sizes');
SIZES.forEach(s=>{const b=document.createElement('button'),d=Math.max(3,s*Z);b.dataset.s=s;b.title='Espessura '+s;b.innerHTML=`<span style="width:${d}px;height:${d}px"></span>`;b.onclick=()=>{SZ=s;markSize();render()};sb.append(b)});
function markSize(){sb.querySelectorAll('button').forEach(b=>b.classList.toggle('on',+b.dataset.s==SZ))}
$('#bgc').oninput=e=>{S.bg=e.target.value;$('#ebg').value=S.bg;save();render()};
$('#bgc').onchange=()=>commit();
$('#swap').onclick=()=>{const a=$('#sc'),b=$('#fc'),t=a.value;a.value=b.value;b.value=t};

/* ---------- quadros e camadas ---------- */
function shift(fn){S.layers.forEach(l=>{const n={};for(const k in l.keys){const j=fn(+k);if(j!==null)n[j]=l.keys[k]}if(!n[0])n[0]=[];l.keys=n})}
const ops={
  kf(){const l=S.layers[cl],k=kf(l,cur);if(!l.keys[cur])l.keys[cur]=k<0?[]:clone(l.keys[k]);S.len=Math.min(N,Math.max(S.len,cur+1))},
  bk(){S.layers[cl].keys[cur]=[];S.len=Math.min(N,Math.max(S.len,cur+1))},
  ins(){if(S.len>=N)return;shift(k=>k>cur?k+1:k);S.len++},
  del(){if(S.len<=1)return;S.layers.forEach(l=>{if(l.keys[cur]&&cur>0)delete l.keys[cur]});shift(k=>k>cur?k-1:k);S.len--;cur=Math.min(cur,S.len-1)},
  clr(){curObjs().length=0;sel=null},
  nofill(){const a=curObjs();for(let i=a.length-1;i>=0;i--)if(a[i].t=='i')a.splice(i,1)}};
const run=n=>{ops[n]();commit()};
document.querySelectorAll('[data-op]').forEach(b=>b.onclick=()=>run(b.dataset.op));
function addLayer(){S.layers.push({name:'Layer '+(S.layers.length+1),vis:1,lock:0,keys:{0:[]}});cl=S.layers.length-1;commit()}
function delLayer(){if(S.layers.length<2)return;S.layers.splice(cl,1);cl=Math.max(0,cl-1);sel=null;commit()}
$('#addL').onclick=addLayer;$('#delL').onclick=delLayer;
$('#onion').onclick=()=>{onion=!onion;ui()};
$('#home').onclick=()=>{cur=0;ui()};
function toggle(){if(play){clearInterval(play);play=null}else{play=setInterval(()=>{cur=(cur+1)%S.len;ui()},1000/S.fps)}$('#play').textContent=play?'⏸':'▶'}
$('#play').onclick=toggle;
$('#fps').onchange=e=>{S.fps=Math.min(60,Math.max(1,+e.target.value||12));if(play){toggle();toggle()}commit()};

function tl(){
  let h='<div class="row hd"><div class="ln"></div><div class="cs">';
  for(let f=0;f<N;f++)h+=`<i data-f="${f}" class="${f==cur?'ph':''}">${f==0||(f+1)%5==0?f+1:''}</i>`;
  h+='</div></div>';
  for(let li=S.layers.length-1;li>=0;li--){const l=S.layers[li];
    h+=`<div class="row ${li==cl?'sel':''}"><div class="ln" data-l="${li}"><span data-eye="${li}" class="${l.vis?'':'off'}">👁</span><span data-lock="${li}" class="${l.lock?'':'off'}">🔒</span><span>${l.name}</span><b></b></div><div class="cs">`;
    for(let f=0;f<N;f++){const k=kf(l,f),isK=!!l.keys[f];
      const c=[f==cur?'ph':'',isK?'k':k>=0&&f<S.len?'h':f>=S.len?'x':''].join(' ');
      h+=`<i data-f="${f}" data-l="${li}" class="${c}">${isK?(l.keys[f].length?'●':'○'):''}</i>`}
    h+='</div></div>'}
  const b=$('#tlb'),st=b.scrollLeft,sy=b.scrollTop;b.innerHTML=h;b.scrollLeft=st;b.scrollTop=sy}
function pick(e){const t=document.elementFromPoint(e.clientX,e.clientY);if(!t)return;const c=t.closest('[data-f]');if(!c)return;
  cur=Math.min(+c.dataset.f,N-1);if(c.dataset.l!==undefined)cl=+c.dataset.l;ui()}
$('#tlb').onpointerdown=e=>{
  const eye=e.target.closest('[data-eye]'),lk=e.target.closest('[data-lock]'),ln=e.target.closest('.ln[data-l]');
  if(eye){const l=S.layers[+eye.dataset.eye];l.vis=l.vis?0:1;commit();return}
  if(lk){const l=S.layers[+lk.dataset.lock];l.lock=l.lock?0:1;commit();return}
  if(ln){cl=+ln.dataset.l;ui();return}
  scrub=true;pick(e)};
document.addEventListener('pointermove',e=>{if(scrub)pick(e)});
document.addEventListener('pointerup',()=>scrub=false);

/* ---------- biblioteca ---------- */
function toSym(){if(!sel){alert('Selecione um objeto com a ferramenta de seleção para convertê-lo em símbolo.');return}
  S.lib.push({name:'Symbol '+(S.lib.length+1),o:clone(sel)});commit()}
function libUI(){$('#lib').innerHTML=S.lib.length?S.lib.map((s,i)=>`<div data-i="${i}" title="Clique para inserir no quadro"><span>${s.name}</span><span>Graphic</span></div>`).join(''):'<p>Empty library</p>'}
$('#lib').onclick=e=>{const r=e.target.closest('[data-i]');if(!r)return;
  const o=clone(S.lib[+r.dataset.i].o);mv(o,24,24);curObjs().push(o);sel=o;setTool('select');commit()};
function delSel(){if(!sel)return;const a=curObjs(),i=a.indexOf(sel);if(i>=0)a.splice(i,1);sel=null;commit()}

/* ---------- arquivo ---------- */
function down(b,n){const a=document.createElement('a');a.href=URL.createObjectURL(b);a.download=n;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),5000)}
const saveJSON=()=>down(new Blob([JSON.stringify(S)],{type:'application/json'}),'oicram8-projeto.json');
function load(s){S=s;hist=[JSON.stringify(S)];hi=0;cur=0;cl=0;sel=null;$('#bgc').value=S.bg;$('#fps').value=S.fps;save();ui()}
function newDoc(){if(confirm('Descartar o projeto atual e começar um novo?'))load(fresh())}
$('#open').onchange=e=>{const f=e.target.files[0];if(!f)return;
  f.text().then(t=>{const j=JSON.parse(t);if(!j.layers)throw 0;load(j)}).catch(()=>alert('Arquivo de projeto inválido.'));e.target.value=''};

/* ---------- exportação ---------- */
const crcT=(()=>{const t=[];for(let n=0;n<256;n++){let c=n;for(let k=0;k<8;k++)c=c&1?0xEDB88320^(c>>>1):c>>>1;t[n]=c>>>0}return t})();
const crc=u=>{let c=-1;for(const b of u)c=crcT[(c^b)&255]^(c>>>8);return(~c)>>>0};
function zip(files){const parts=[],cd=[],enc=new TextEncoder();let off=0,cs=0;
  for(const[n,d]of files){const nm=enc.encode(n),c=crc(d);
    const h=new DataView(new ArrayBuffer(30));h.setUint32(0,0x04034b50,true);h.setUint16(4,20,true);h.setUint32(14,c,true);h.setUint32(18,d.length,true);h.setUint32(22,d.length,true);h.setUint16(26,nm.length,true);
    const e=new DataView(new ArrayBuffer(46));e.setUint32(0,0x02014b50,true);e.setUint16(4,20,true);e.setUint16(6,20,true);e.setUint32(16,c,true);e.setUint32(20,d.length,true);e.setUint32(24,d.length,true);e.setUint16(28,nm.length,true);e.setUint32(42,off,true);
    parts.push(h,nm,d);cd.push(e,nm);off+=30+nm.length+d.length;cs+=46+nm.length}
  const end=new DataView(new ArrayBuffer(22));end.setUint32(0,0x06054b50,true);end.setUint16(8,files.length,true);end.setUint16(10,files.length,true);end.setUint32(12,cs,true);end.setUint32(16,off,true);
  return new Blob([...parts,...cd,end],{type:'application/zip'})}
function frameCv(f,tr,bg){const c=document.createElement('canvas');c.width=W*2;c.height=H*2;const x=c.getContext('2d');
  if(!tr){x.fillStyle=bg;x.fillRect(0,0,c.width,c.height)}x.scale(2,2);drawFrame(x,f,1);return c}
const blob=c=>new Promise(r=>c.toBlob(r,'image/png'));
async function doExport(){
  const f=val('#fmt'),tr=$('#tr').checked,bg=val('#ebg'),btn=$('#go');btn.disabled=true;btn.textContent='Exportando…';
  try{
    await preload();if(f=='png')down(await blob(frameCv(cur,tr,bg)),`quadro-${cur+1}.png`);
    else if(f=='zip'){const fl=[];for(let i=0;i<S.len;i++)fl.push([`quadro_${String(i+1).padStart(3,'0')}.png`,new Uint8Array(await(await blob(frameCv(i,tr,bg))).arrayBuffer())]);down(zip(fl),'oicram8-quadros.zip')}
    else if(f=='json')saveJSON();
    else{
      const c=document.createElement('canvas');c.width=W*2;c.height=H*2;const x=c.getContext('2d');
      const mt=['video/webm;codecs=vp9','video/webm'].find(t=>MediaRecorder.isTypeSupported(t));
      const mr=new MediaRecorder(c.captureStream(S.fps),{mimeType:mt}),ch=[];
      mr.ondataavailable=e=>ch.push(e.data);const done=new Promise(r=>mr.onstop=r);mr.start();
      for(let i=0;i<S.len;i++){x.setTransform(1,0,0,1,0,0);x.clearRect(0,0,c.width,c.height);
        if(!tr){x.fillStyle=bg;x.fillRect(0,0,c.width,c.height)}x.scale(2,2);drawFrame(x,i,1);
        await new Promise(r=>setTimeout(r,1000/S.fps))}
      mr.stop();await done;down(new Blob(ch,{type:'video/webm'}),'oicram8.webm')}
    $('#dlg').close();
  }catch(err){alert('Não foi possível exportar neste navegador: '+err.message)}
  btn.disabled=false;btn.textContent='Exportar'}
$('#go').onclick=doExport;$('#cancel').onclick=()=>$('#dlg').close();

/* ---------- menus ---------- */
const M={
  File:[['Novo','',newDoc],['Abrir projeto...','',()=>$('#open').click()],['Salvar projeto','save',saveJSON],['Exportar...','export',()=>$('#dlg').showModal()]],
  Edit:[['Desfazer','undo',()=>restore(hi-1)],['Refazer','redo',()=>restore(hi+1)],['Excluir seleção','delsel',delSel],['Configurações...','',openSettings]],
  View:[['Aumentar zoom','zin',()=>ACT.zin()],['Diminuir zoom','zout',()=>ACT.zout()],['100%','',()=>setZoom(1)],['Onion skin','',()=>{onion=!onion;ui()}]],
  Insert:[['Converter em símbolo','sym',toSym],['Quadro','ins',()=>run('ins')],['Quadro-chave','kf',()=>run('kf')],['Quadro-chave vazio','bk',()=>run('bk')],['Remover quadro','del',()=>run('del')],['Nova camada','',addLayer]],
  Modify:[['Limpar quadro','',()=>run('clr')],['Remover preenchimentos do quadro','',()=>run('nofill')],['Excluir camada','',delLayer]],
  Control:[['Reproduzir / Parar','play',toggle],['Voltar ao início','',()=>{cur=0;ui()}]],
  Window:[['Mostrar / ocultar painéis','',()=>$('#side').classList.toggle('hide')]],
  Help:[['Sobre o Oicram 8','',()=>alert('Oicram 8 — editor de animação quadro a quadro.\nAtalhos e zoom do mouse: Edit > Configurações.')]]};
const mb=$('#menubar'),closeMenu=()=>{const d=$('#dd');if(d)d.remove()};
Object.keys(M).forEach(k=>{const b=document.createElement('div');b.className='mi';b.textContent=k;
  b.onclick=e=>{e.stopPropagation();closeMenu();const d=document.createElement('div');d.id='dd';d.style.left=b.offsetLeft+'px';
    M[k].forEach(([n,s,fn])=>{const r=document.createElement('div');r.innerHTML=`<span>${n}</span><em>${KEYS[s]||''}</em>`;r.onclick=()=>{closeMenu();fn()};d.append(r)});mb.append(d)};
  mb.append(b)});
document.addEventListener('click',closeMenu);

/* ---------- configurações e atalhos ---------- */
const DEF={select:'v',pencil:'y',brush:'b',line:'n',rect:'r',oval:'o',bucket:'k',eye:'i',eraser:'e',hand:'h',zoom:'z',play:'Enter',kf:'F6',bk:'F7',ins:'F5',del:'Shift+F5',sym:'F8',delsel:'Delete',undo:'Ctrl+z',redo:'Ctrl+y',save:'Ctrl+s',export:'Ctrl+Shift+s',prev:'ArrowLeft',next:'ArrowRight',zin:'=',zout:'-'};
const LBL={select:'Ferramenta Seleção',pencil:'Lápis',brush:'Pincel',line:'Linha',rect:'Retângulo',oval:'Oval',bucket:'Balde',eye:'Conta-gotas',eraser:'Borracha',hand:'Mão',zoom:'Zoom (ferramenta)',play:'Reproduzir / parar',kf:'Quadro-chave',bk:'Quadro-chave vazio',ins:'Inserir quadro',del:'Remover quadro',sym:'Converter em símbolo',delsel:'Excluir seleção',undo:'Desfazer',redo:'Refazer',save:'Salvar projeto',export:'Exportar',prev:'Quadro anterior',next:'Próximo quadro',zin:'Aumentar zoom',zout:'Diminuir zoom'};
const ldj=(k,d)=>{try{return{...d,...JSON.parse(localStorage[k])}}catch(e){return{...d}}};
let KEYS=ldj('oicram8keys',DEF),CFG=ldj('oicram8cfg',{zoom:'ctrl'}),capture=null;
const saveCfg=()=>{try{localStorage.oicram8keys=JSON.stringify(KEYS);localStorage.oicram8cfg=JSON.stringify(CFG)}catch(e){}};
const ACT={...Object.fromEntries(T.map(t=>[t[0],()=>setTool(t[0])])),play:toggle,kf:()=>run('kf'),bk:()=>run('bk'),ins:()=>run('ins'),del:()=>run('del'),sym:toSym,delsel:delSel,undo:()=>restore(hi-1),redo:()=>restore(hi+1),save:saveJSON,export:()=>$('#dlg').showModal(),prev:()=>{cur=Math.max(0,cur-1);ui()},next:()=>{cur=Math.min(N-1,cur+1);ui()},zin:()=>setZoom(zoom*1.25),zout:()=>setZoom(zoom/1.25)};
const combo=e=>[e.ctrlKey||e.metaKey?'Ctrl':'',e.altKey?'Alt':'',e.shiftKey?'Shift':'',e.key==' '?'Space':e.key.length==1?e.key.toLowerCase():e.key].filter(Boolean).join('+');
function refreshTitles(){document.querySelectorAll('#tgrid button').forEach(b=>b.title=LBL[b.dataset.t]+(KEYS[b.dataset.t]?' ('+KEYS[b.dataset.t]+')':''))}
function keysUI(){$('#keys').innerHTML=Object.keys(DEF).map(k=>`<div><span>${LBL[k]}</span><button data-k="${k}" class="${capture==k?'on':''}">${capture==k?'Pressione a tecla…':KEYS[k]||'(nenhuma)'}</button></div>`).join('');refreshTitles()}
function openSettings(){capture=null;keysUI();$('#zmode').value=CFG.zoom;$('#sdlg').showModal()}
$('#keys').onclick=e=>{const b=e.target.closest('[data-k]');if(b){capture=b.dataset.k;keysUI()}};
$('#kreset').onclick=()=>{KEYS={...DEF};saveCfg();keysUI()};
$('#zmode').onchange=e=>{CFG.zoom=e.target.value;saveCfg()};
$('#sclose').onclick=()=>$('#sdlg').close();
$('#pexp').onclick=()=>$('#dlg').showModal();$('#pset').onclick=openSettings;
$('#fps2').onchange=e=>{$('#fps').value=e.target.value;$('#fps').dispatchEvent(new Event('change'))};
$('#sdlg').addEventListener('close',()=>{capture=null});
sw.addEventListener('wheel',e=>{const m=CFG.zoom;if(m=='scroll'||(m=='ctrl'&&e.ctrlKey)){e.preventDefault();setZoom(zoom*(e.deltaY<0?1.1:1/1.1))}},{passive:false});
document.addEventListener('change',e=>{if(e.target.matches('select,input[type=color]'))e.target.blur()});
document.addEventListener('keydown',e=>{
  if(['Control','Shift','Alt','Meta'].includes(e.key))return;
  if(capture){e.preventDefault();const a=capture;capture=null;
    if(e.key!='Escape'){const c=combo(e);for(const k in KEYS)if(k!=a&&KEYS[k]==c)KEYS[k]='';KEYS[a]=e.key=='Backspace'&&!e.ctrlKey?'':c;saveCfg()}
    keysUI();return}
  if(e.target.matches('textarea,input:not([type=color]):not([type=checkbox])')||$('#dlg').open||$('#sdlg').open)return;
  const c=combo(e);let a=Object.keys(KEYS).find(k=>KEYS[k]&&KEYS[k]==c);
  if(!a&&c=='Ctrl+Shift+z')a='redo';
  if(a){e.preventDefault();ACT[a]()}});

/* ---------- interface ---------- */
function ui(){
  tl();libUI();render();
  $('#fps').value=$('#fps2').value=S.fps;
  $('#fno').textContent=cur+1;$('#time').textContent=(cur/S.fps).toFixed(1)+'s';
  $('#onion').classList.toggle('on',onion);
  $('#tab').textContent='Untitled-1'+(hi?'*':'')}
$('#bgc').value=S.bg;$('#fps').value=S.fps;$('#ebg').value=S.bg;
setZoom(1);setTool('brush');markSize();refreshTitles();ui();
