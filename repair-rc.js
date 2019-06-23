/*****************************************
	Re-Pair 2018.5.15
******************************************
Re-Pair is the name of the algorithm and the software which implements the
recursive pairing algorithm. Its corresponding decompressor is Des-Pair.
this version implemented CBT coding by binary Range coder.
Header has a rank table.

 usage:
	RePair(A)
	@A	:à≥èkå≥îzóÒ	{n|0..255}
	ï‘íl	:à≥èkîzóÒ	{n|0..255}

	DePair(A)
	@A	:à≥èkîzóÒ	{n|0..255}
	ï‘íl	:ïúçÜîzóÒ	{n|0..255}
******************************************/
var primes=[11,19,37,67,131,283,521,1033,2053,4099,8219,16427,32771,65581,131101,262147,524309,1048583,2097169,4194319,8388617,16777259,33554467,67108879,134217757,268435459,536870923,1073741909,0];

function locatePair(Hash,left,right){
 for(var p=Hash[(1+left)*(1+right)%primes[Hash.hN]];p;p=p.link)
	if(p.left===left&&p.right===right)return p}

function buildHash(Hash,Q){
 var h,i=0,p,n=primes[++Hash.hN];Hash.length=0;
 do{
	if(++i===Q.max)i=0;
	for(p=Q[i];p;p=p.next)
	 p.link=Hash[h=(1+p.left)*(1+p.right)%n],
	 Hash[h]=p}
 while(i)}

function insertPairPQ(Q,P,n,t){
 t=Q[n<Q.max?n:n=0];Q[n]=P;P.prev=0;
 if(P.next=t)t.prev=P}

function removePairPQ(Q,P,n){
 if(P.prev){
	if(P.prev.next=P.next)P.next.prev=P.prev;return}
 if(Q[n<Q.max?n:0]=P.next)P.next.prev=0}

function destructPair(Hash,Q,P){
 var h=(1+P.left)*(1+P.right)%primes[Hash.hN],p=Hash[h],q;
 for(removePairPQ(Q,P,P.freq);p&&(p.left-P.left||p.right-P.right);p=p.link)q=p;
 q?q.link=p.link:Hash[h]=p.link;
 Q.pairs--}

function incrementPair(Q,P){
 if(P.freq>=Q.max)return++P.freq;
 removePairPQ(Q,P,P.freq);
 insertPairPQ(Q,P,++P.freq)}

function decrementPair(Hash,Q,P){
 if(P.freq>Q.max)return--P.freq;
 if(P.freq<2)return destructPair(Hash,Q,P);
 removePairPQ(Q,P,P.freq);
 insertPairPQ(Q,P,--P.freq)}

function createPair(Hash,Q,l,r,p){
 var pair={left:l,right:r,freq:1,top:p,pos:p};
 ++Q.pairs<primes[Hash.hN]||buildHash(Hash,Q);
 pair.link=Hash[p=++l*++r%primes[Hash.hN]];
 insertPairPQ(Q,Hash[p]=pair,1);
 return pair}

function resetPQ(Hash,Q,n,p){
 for(p=Q[n],Q[n]=0;p;p=n)
	n=p.next,destructPair(Hash,Q,p)}

function initRDS(Hash,Q,Code,Prev,Next){
 for(var i=0,l=Code.length-1,a,b,pair;i<l;i++)
	if(pair=locatePair(Hash,a=Code[i],b=Code[i+1]))
	 Next[Prev[i]=pair.pos]=pair.pos=i,
	 incrementPair(Q,pair);
	else createPair(Hash,Q,a,b,i);
 resetPQ(Hash,Q,1)}

function getMaxPair(Q){
 var p=Q[0],mp,m=0;
 if(p){do if(m<p.freq)m=p.freq,mp=p;while(p=p.next)}
 else{
	for(p=Q.i||Q.max-1;p>1;p--)if(mp=Q[p])break;Q.i=p}
 return mp}

function removeLinkSQ(Prev,Next,pos){
 var p=Prev[pos],n=Next[pos],u=Infinity;
 p<u&&n<u?Prev[Next[p]=n]=p:n<u?Prev[n]=u:p<u&&(Next[p]=u)}

function updateBlockSQ(Hash,Q,Code,Prev,Next,n,pos,skip){
 var l=Code.length,p=pos,lc=p,u=1/0,np=Next[p],
	lp=lc?Code[--lc]>-1?lc:Next[lc]:u,
	rp=++p<l?Code[p]>-1?p:Prev[p]:u,
	rp2=++rp<l?Code[rp]>-1?rp:Prev[rp]:u,
	r=Code[--rp];
 if(np===rp)np=Next[np];
 if(!skip&&lp<u){
	removeLinkSQ(Prev,Next,lp);
	if(p=locatePair(Hash,lc=Code[lp],Code[pos])){
	 if(p.top===lp)p.top=Next[lp];
	 decrementPair(Hash,Q,p)}
	if(p=locatePair(Hash,lc,n))
	 Next[lp]=u,
	 Next[Prev[lp]=p.pos]=p.pos=lp,
	 incrementPair(Q,p);
	else Prev[lp]=Next[lp]=u,
	 createPair(Hash,Q,lc,n,lp)}
 removeLinkSQ(Prev,Next,pos);
 removeLinkSQ(Prev,Next,rp);
 if(skip)return;
 Code[pos]=n,Code[rp]=-1;
 if(rp2<u){
	if(p=locatePair(Hash,r,r=Code[rp2])){
	 if(p.top===rp)p.top=Next[rp];
	 decrementPair(Hash,Q,p)}
	if(pos^rp2-2)
	 Prev[pos+1]=rp2,
	 Next[pos+1]=Prev[rp2-1]=u,
	 Next[rp2-1]=pos;
	else Prev[pos+1]=rp2,Next[pos+1]=pos;
	if(np>rp2)
	 if(p=locatePair(Hash,n,r))
		Next[Next[Prev[pos]=p.pos]=p.pos=pos]=u,
		incrementPair(Q,p);
	 else Prev[pos]=Next[pos]=u,
		createPair(Hash,Q,n,r,pos);
	else Next[pos]=Prev[pos]=u}
 else if(++pos<l)
	Next[pos]=pos-1,
	Prev[pos]=Prev[rp]=Next[rp]=u}

function replace(Hash,Q,Code,Prev,Next,m,n){
 for(var i=m.top,j,l=Code.length,p,r=0,u=1/0;i<u;i=j){
	j=Next[p=i];
	if(j===(++p<l?Code[p]>-1?p:Prev[p]:u))j=Next[j];
	updateBlockSQ(Hash,Q,Code,Prev,Next,n,i,!r++&&j===u)}
 m.freq^1&&destructPair(Hash,Q,m);
 resetPQ(Hash,Q,1);return r>1?r:0}

function RePair(A){
 function eb(i,b,P){
	var p=(P[i]||(P[i]=0x80000000))>>>9,r=(x>>>12)*(p>>11||1);
	b?x=r:(x-=r,y+=r);
	for(P[i]+=(((b<<23)-p)*Y[r=P[i]&127]&0xffffff80)+(r<127);x<16777216;x*=256){
		if((y^0xff000000)>>>0>0xffffff){
		 O[o++]=B+(r=y/0x100000000)&255;
		 for(r+=255;N;N--)O[o++]=r&255;
		 B=y>>>24}
		else++N;
		y=y<<8>>>0}}
 function eb2(i,s,P){
	for(var b,c=1;i;c+=c+b)eb(c,b=s>>--i&1,P)
 }
 function eB(i,s,r){
	for(;i;){r=x>>>=1;
	 if(s>>>--i&1)y+=r;
	 for(;x<16777216;x*=256){
		if((y^0xff000000)>>>0>0xffffff){
		 O[o++]=B+(r=y/0x100000000)&255;
		 for(r+=255;N;N--)O[o++]=r&255;
		 B=y>>>24}
		else++N;
		y=y<<8>>>0}
	}
 }
 for(var x=-1>>>0,y=128,B=0,N=0,b=0,l=0,m,n=1/0,nc=0,nl=A.length,o=nl,Hash=[],Code=Array(o),Prev=Array(o),Next=Array(o),Left=[],Right=[],O=[],Q=[],T=[],E=[],F=[],Y=[];y;)Y[--y]=4096/(y+128)|0;
 for(Q.max=Math.ceil(Math.sqrt(o)),Q.i=Q.max-1;o--;Next[o]=Prev[o]=n)T[A[o]]=1;
 for(eB(1,T[Q.pairs=0]);n=l<256;eB(m*2-1,n)){
	for(m=T[l];m&&(T[l]=nc++),m==T[++l]&&l<256;n++);
	if(n<256)for(m=0;n>>++m;);else m=5,n=0}

 for(n=0;n<nl;)Code[n]=T[A[n++]];
 for(m=n=T.length=nc;Left[--m]=T[m]=m;);
 Hash.hN=15;initRDS(Hash,Q,Code,Prev,Next);
 for(;m=getMaxPair(Q);replace(Hash,Q,Code,Prev,Next,m,n)&&n++)
	Left[n]=m.left,Right[n]=m.right;
 for(m=n=l=0;n<nl;)Code[n]>-1?Code[m++]=Code[n++]:n=Prev[n];
 for(;m>>++l;);
 eB(5,l);eB(--l,m^1<<l);l=nc-1;
 T.e=function(L,R,c,m,n){
	if(this[c]>-1){
	 for(eb(b,b=1,F);nc>>nl;)nl++;
	 if(c>l)c=this[c];
	 if(c<(n=(1<<nl)-nc))eb2(nl-1,c,E);
	 else c+=n,eb2(nl-1,c>>1,E),eB(1,c&1)}
	else
	 this.e(L,R,L[c]),
	 this.e(L,R,R[c]),
	 eb(b,b=0,F),this[c]=nc++};
 for(nl=n=0;n<m;b=2)T.e(Left,Right,Code[n++]),eb(b,0,F);
 for(n=5;n--;y=y<<8>>>0)
	if((y^0xff000000)>>>0>0xffffff){
	 O[o++]=B+(m=y/0x100000000)&255;
	 for(m+=255;N;N--)O[o++]=m&255;
	 B=y>>>24}
	else++N;
 return O}

function DePair(A){
 function dB(i,c,b){
	for(c=0;i--;c+=c-b){
		x>>>=1;b=y-x>>>31;
		for(y-=x&--b;x<16777216;x*=256)y=(y<<8|A[a++])>>>0}
	return c}

 function db(P,c){
	var p=(P[c]||(P[c]=0x80000000))>>>9,r=(x>>>12)*(p>>11||1),b=1;
	y<r?x=r:(x-=r,y-=r,b=0);
	for(P[c]+=(((b<<23)-p)*Y[r=P[c]&127]&0xffffff80)+(r<127);x<16777216;x*=256)y=(y<<8|A[a++])>>>0;
	return b}

 function db2(P,i,c,d){
	for(c=1,d=i;i--;)c+=c+db(P,c);return c^1<<d}

 for(var a=0,b=0,c,d,e=0,l,m,n=0,o,r,s,x=-1>>>0,y=128,O=[],L=[],R=[],S=[],T=[],Y=[],E=[],F=[];y;)Y[--y]=4096/(y+128)|0;
 for(;a<4;)y=(y<<8|A[a++])>>>0;
 for(l=dB(1);e<256;l^=1){
	for(o=0;o<9&&!dB(1);)o++;
	for(o=o<9?1<<o|dB(o):256;o--;e++)if(l)T[L[n]=n++]=e}

 O.e=function(L,R,s){
	if(s<m)return this[++o]=T[s];
	this.e(L,R,L[s]);
	this.e(L,R,R[s])};

 if(r=dB(5),!r)return O;
 for(r=dB(--r)|1<<r,m=n;r--;)
	for(e=s=0;;)
	 if(db(F,b)){b=1;
		for(e++;n>>l;)l++;
		if((c=db2(E,l-1))>=(d=(1<<l)-n))c+=c+dB(1)-d;
		O.e(L,R,S[s++]=c)}
	 else{if(!--e){b=2;break}b=0;
		R[n]=S[--s];L[n]=S[--s];S[s++]=n++}
 delete O.e;delete A.d;return O}