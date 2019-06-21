/* 
re-pair --  A dictionary-based compression based on the recursive paring.
Copyright(c)2011 Shirou Maruyama, 2015-2018 xezz

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

1. Redistributions of source code must retain the above Copyright
   notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above Copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

3. Neither the name of the authors nor the names of its contributors
   may be used to endorse or promote products derived from this
   software without specific prior written permission.
*/
#ifdef __GNUC__

#define _FILE_OFFSET_BITS 64
#define _fseeki64 fseeko64
#define _ftelli64 ftello64

#endif // __GNUC__

#define _CRT_SECURE_CPP_OVERLOAD_STANDARD_NAMES 1
#define _CRT_SECURE_NO_WARNINGS
#define _CRT_DISABLE_PERFCRIT_LOCKS

#include<assert.h>
#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<math.h>
#include<limits.h>
#include<time.h>

#define CHAR_SIZE 256
#define NIL (CODE)-1
#define INIT_DICTIONARY_SIZE 32768
#define DICTIONARY_SCALING_FACTOR (1.25)
#define INIT_HASH_NUM 15
#define NaN UINT_MAX

typedef unsigned int CODE;
typedef unsigned char U8;
typedef unsigned int U32;
typedef unsigned long long U64;

const char noMem[]="not enough memory";
const U32 primes[]={11,19,37,67,131,283,521,1033,2053,4099,8219,16427,32771,65581,131101,262147,524309,1048583,2097169,4194319,8388617,16777259,33554467,67108879,134217757,268435459,536870923,1073741909,0};
/////////////////////////////////////////////////////////////////////
typedef struct Sequence{
	CODE code;
	U32 next, prev;
}SEQ;

typedef struct Pair{
	CODE left, right;
	U32 freq, f_pos, b_pos;
	struct Pair *link, *next, *prev;
}PAIR;

typedef struct RePair_data_structures{
	U32 txt_len, pairs, h_num, p_max, mp;
	SEQ *seq;
	PAIR **h_first, **p_que;
}RDS;

typedef struct Rule{
	CODE left, right;
}RULE;

typedef struct Dictionary{
	U32 rules, length;
	RULE *rule;
	CODE *tcode;
}DICT;

#define toHash(P, A, B) (((A+1)*(B+1))%primes[P])

static inline PAIR *locatePair(RDS *rds, CODE left, CODE right){
	PAIR *p = rds->h_first[toHash(rds->h_num, left, right)];

	for(;p&&(p->left != left || p->right != right);p = p->link);
	return p;
}

static inline void reconstructHash(RDS *rds){
	PAIR *p, *q;
	U32 i = primes[++rds->h_num], h;
	rds->h_first = (PAIR**)realloc(rds->h_first, sizeof(PAIR*)*primes[rds->h_num]);
	for(;i;)rds->h_first[--i] = NULL;
	do{
		if(++i == rds->p_max) i = 0;
		for(p = rds->p_que[i];p;p = p->next)
			p->link = NULL,
			q = rds->h_first[h = toHash(rds->h_num, p->left, p->right)],
			rds->h_first[h] = p,
			p->link = q;
	}while(i);
}

static inline void insertPair_PQ(RDS *rds, PAIR *p, U32 n){
	if(n >= rds->p_max)n = 0;
	PAIR *q = rds->p_que[n];
	rds->p_que[n] = p;
	p->prev = NULL;
	if(p->next = q)q->prev = p;
}

static inline void removePair_PQ(RDS *rds, PAIR *p, U32 n){
	if(p->prev){
		if(p->prev->next = p->next)
			p->next->prev = p->prev;
		return;
	}
	if(n >= rds->p_max)n = 0;
	if(rds->p_que[n] = p->next)p->next->prev = NULL;
}

static inline void destructPair(RDS *rds, PAIR *o){
	U32 h = toHash(rds->h_num,o->left,o->right);
	PAIR *p = rds->h_first[h], *q = NULL;

	removePair_PQ(rds,o,o->freq);
	for(;p&&(p->left != o->left || p->right != o->right);p = p->link)q = p;

	assert(p != NULL);
	q == NULL? (rds->h_first[h] = p->link): (q->link = p->link);
	free(o);
	rds->pairs--;
}

static inline void incrementPair(RDS *rds, PAIR *p){
	if(p->freq >= rds->p_max){
		++p->freq;
		return;
	}
	removePair_PQ(rds,p,p->freq);
	insertPair_PQ(rds,p,++p->freq);
}

static inline void decrementPair(RDS *rds, PAIR *p){
	if(p->freq > rds->p_max){
		--p->freq;
		return;
	}
	if(p->freq == 1)return destructPair(rds,p);
	removePair_PQ(rds,p,p->freq);
	insertPair_PQ(rds,p,--p->freq);
}

static inline PAIR *createPair(RDS *rds, CODE l, CODE r, U32 i){
	PAIR *p = (PAIR*)malloc(sizeof(PAIR));

	p->left = l;p->right = r;p->freq = 1;
	p->f_pos = p->b_pos = i;
	p->prev = p->next = NULL;

	if(++rds->pairs >= primes[rds->h_num])reconstructHash(rds);

	p->link = rds->h_first[i = toHash(rds->h_num,l,r)];
	insertPair_PQ(rds, rds->h_first[i] = p,1);
	return p;
}

static inline void resetPQ(RDS *rds, U32 n){
	PAIR **p_que = rds->p_que, *pair, *q = p_que[n];
	for(p_que[n] = NULL;pair = q;destructPair(rds, pair))q = q->next;
}

void initRDS(RDS *rds, int opt){
	U32 i=0, j=-1, size = rds->txt_len-1;
	SEQ *seq = rds->seq;
	CODE l, r, s=-1;
	PAIR *pair;

	for(;i<size;i++,s=l)
		if(pair = locatePair(rds, l=seq[i].code, r=seq[i+1].code)){
			if(opt==1 && l==r && l==s && i==j+1)continue;	// avoid "aaa"
			pair->b_pos = seq[seq[i].prev = pair->b_pos].next = j=i,
			incrementPair(rds, pair);
			if(opt==2)i+=l==r&&l==s;
		}else createPair(rds, l, r, j=i);
	resetPQ(rds, 1);
}

U32 createRDS(RDS *rds, SEQ *seq, int *U, FILE *ip, U32 bs, U64 *size, int opt){
	U32 c, cs=0, i=CHAR_SIZE, h_num = INIT_HASH_NUM, p_max;

	for(;i--;)U[i]=0;
	for(;++i<bs&&(c = getc(ip)) != EOF;U[seq[i].code = c]=1)seq[i].next = seq[i].prev = NaN;
	for(c=-1;++c<CHAR_SIZE;)U[c]=U[c]? cs++: -1;
	printf("input: %d, alphabet size:%d\n", i,cs);
	for(*size-=rds->txt_len=i;i--;)seq[i].code=U[seq[i].code];

	PAIR **h_first = (PAIR**)calloc(sizeof(PAIR*), primes[h_num]), **p_que = (PAIR**)calloc(sizeof(PAIR*), p_max = 1+(U32)ceil(sqrt((double)bs)));

	rds->pairs = rds->mp=0;
	rds->h_num = h_num;
	rds->h_first = h_first;
	rds->p_max = p_max;
	rds->p_que = p_que;
	initRDS(rds,opt);
	return cs;
}

static inline PAIR *getMaxPair(RDS *rds){
	PAIR **p_que=rds->p_que, *p=*p_que, *best=NULL;

	if(p){
		U32 max=0;
		do if(max < p->freq)max = p->freq, best = p;while(p = p->next);
	}else{U32 i = rds->mp;
		if(i == 0)i = rds->p_max-1;
		for(;i>1;i--)if(best = p_que[i])break;
		rds->mp=i;
	}
	return best;
}

static inline U32 leftPos_SQ(SEQ *seq, U32 p){
	assert(p != NaN);
	if(p == 0)return NaN;
	if(seq[--p].code == NIL)return seq[p].next;
	return p;
}

static inline U32 rightPos_SQ(SEQ *seq, U32 p, U32 end){
	assert(p != NaN);
	if(++p == end)return NaN;
	if(seq[p].code == NIL)return seq[p].prev;
	return p;
}

static inline void removeLink_SQ(SEQ *seq, U32 i){
	assert(seq[i].code != NIL);
	U32 p=seq[i].prev, n=seq[i].next;
	p != NaN && n != NaN?(seq[seq[p].next = n].prev = p):
	n != NaN?(seq[n].prev = NaN):p != NaN&&(seq[p].next = NaN);
}

static inline void updateBlock_SQ(RDS *rds, CODE nc, U32 p, int skip){
	SEQ *seq=rds->seq;
	U32 len=rds->txt_len, lp=leftPos_SQ(seq,p), rp=rightPos_SQ(seq,p,len), rrp=rightPos_SQ(seq,rp,len), np=seq[p].next;
	CODE c=seq[p].code, rc=seq[rp].code, lc, rrc;
	PAIR *Lp, *Cp, *Rp;

	assert(c != NIL&&rc != NIL);

	if(np == rp)np = seq[np].next;
	if(lp != NaN){
		lc = seq[lp].code;
		assert(lc != NIL);
		removeLink_SQ(seq,lp);
		if(skip)goto next;
		if(Lp = locatePair(rds,lc,c)){
			if(Lp->f_pos == lp)Lp->f_pos = seq[lp].next;
			decrementPair(rds,Lp);
		}
		if(Lp = locatePair(rds,lc,nc))
			seq[lp].next = NaN,
			Lp->b_pos = seq[seq[lp].prev = Lp->b_pos].next = lp,
			incrementPair(rds,Lp);
		else
			seq[lp].prev = seq[lp].next = NaN,
			createPair(rds,lc,nc,lp);
	}
next:
	removeLink_SQ(seq,p);
	removeLink_SQ(seq,rp);
	if(skip)return;
	seq[p].code = nc,seq[rp].code = NIL;
	if(rrp != NaN){
		rrc = seq[rrp].code;
		assert(rrc != NIL);
		if(Rp = locatePair(rds,rc,rrc)){
			if(Rp->f_pos == rp) Rp->f_pos = seq[rp].next;
			decrementPair(rds,Rp);
		}
		if(p == rrp-2)
			seq[p+1].prev = rrp,
			seq[p+1].next = p;
		else seq[p+1].prev = rrp,
			seq[p+1].next = seq[rrp-1].prev = NaN,
			seq[rrp-1].next = p;
		if(np > rrp){
			if(Cp = locatePair(rds,nc,rrc))
				seq[p].next = NaN,
				Cp->b_pos =seq[seq[p].prev = Cp->b_pos].next = p,
				incrementPair(rds,Cp);
			else seq[p].prev = seq[p].next = NaN,
				createPair(rds,nc,rrc,p);
		}
		else seq[p].next = seq[p].prev = NaN;
	}
	else if(++p < len){
		assert(seq[p].code == NIL);
		seq[p].next = p-1;
		seq[p].prev = seq[rp].prev = seq[rp].next = NaN;
	}
}

static inline U32 replace(RDS *rds, PAIR *best, CODE c){
	U32 i=best->f_pos, j, len=rds->txt_len, rep=0;
	SEQ *seq = rds->seq;

	for(;i!=NaN;i=j){
		j = seq[i].next;
		if(j == rightPos_SQ(seq,i,len))j = seq[j].next;
		updateBlock_SQ(rds,c,i,++rep<2&&j==NaN);
	}
	if(best->freq != 1)destructPair(rds,best);
	resetPQ(rds,1);
	return rep-=rep==1;
}

static inline CODE addNewPair(DICT *d, PAIR *p){
	RULE *R = d->rule;
	CODE c = d->rules++;

	R[c].left = p->left;
	R[c].right = p->right;

	if(d->rules >= d->length){
		d->length *= DICTIONARY_SCALING_FACTOR;
		d->rule = (RULE*)realloc(R,sizeof(RULE)*d->length);
		if(d->rule == NULL) free(R), puts(noMem), exit(1);
	}
	return c;
}

/////////////////////////////////////////////////////////////////////
void *RePair(FILE *ip, FILE *op, U64 size, U32 bs, int opt){
	if(bs<65536)bs=65536;
	if(bs>size)bs=size;
	printf("	[block size:%u]\n", bs);

	PAIR *best;
	DICT *dict = (DICT*)malloc(sizeof(DICT));
	RDS *rds = (RDS*)malloc(sizeof(RDS));
	SEQ *seq = rds->seq =(SEQ*)malloc(sizeof(SEQ)*bs);
	U32 rep, slen, c, bn, cb, cs, nc, n=0, tlen=256, i=dict->length=INIT_DICTIONARY_SIZE;
	int U[CHAR_SIZE];
	// range coder
	U8 B=0;
	U32 R=-1, N=0;
	U64 L=0;
	// models
	U8 D[128], f=128, g;
	U32 C[CHAR_SIZE+1], *E, F[6];	// symbol & flag

	inline void eb(int b, U32 *P){
		U32 p=*P>>9, r=p>>11;
		r=(R>>12)*(r+!r);
		b?R=r:(R-=r,L+=r);r=*P&127;
		for(*P+=(((b<<23)-p)*D[r]&0xffffff80)+(r<127);R<16777216;R<<=8){
			if((L^0xff000000)>0xffffff){
				putc(B+(r=L>>32),op);
				for(r+=255;N;N--)putc(r,op);
				B=(U32)L>>24;
			}else++N;
			L=(U32)L<<8;
		}
	}
	inline void eb2(int i, int s, U32 *P){
		int b, c=1;
		for(;i;c+=c+b)eb(b=s>>--i&1,P+c);
	}

	inline void eB(int i, int s){
		for(;i;){
			U32 r=R>>=1;
			if(s>>--i&1)L+=r;
			for(;R<16777216;R<<=8){
				if((L^0xff000000)>0xffffff){
					putc(B+(r=L>>32),op);
					for(r+=255;N;N--)putc(r,op);
					B=(U32)L>>24;
				}else++N;
				L=(U32)L<<8;
			}
		}
	}
	void enc(U32 c){
		if(dict->tcode[c] == NIL){	// unknown rule
			enc(dict->rule[c].left);
			enc(dict->rule[c].right);
			dict->tcode[c] = cs+nc++;
			eb(0,F+f);f=0;return;
		}
		eb(1,F+f);f=1;
		if(c<cs)
			eb(0,F+g), g=3, eb2(cb,c,C);
		else{
			eb(1,F+g), g=4;	// non terminal
			for(c=dict->tcode[c]-cs;nc>>bn;)++bn;
			U32 n=(1<<bn)-nc;
			if(c<n)eb2(bn-1,c,E);
			else c+=n, eb2(bn-1,c>>1,E), eB(1,c&1);
		}
	}

	for(;f;)D[--f]=4096/(f+128);
	dict->rule = (RULE*)malloc(sizeof(RULE)*i);
	dict->tcode = (CODE*)malloc(sizeof(CODE)*tlen);

loop:
	printf("Generating CFG(%d)... ",++n);
	dict->rules=cs=createRDS(rds,seq,U,ip,bs,&size,opt);
	for(rep=0;best = getMaxPair(rds);c||--dict->rules)
		nc = addNewPair(dict, best),
		rep +=c=replace(rds, best, nc);
	free(rds->h_first);free(rds->p_que);
	slen = rds->txt_len-rep;
	i=c=dict->rules;
	if(i>=tlen)dict->tcode = (CODE*)realloc(dict->tcode, sizeof(CODE)*(tlen=i));
	for(;i>cs;)dict->tcode[--i] = NIL;
	for(;dict->tcode[--i]=i;);
	printf("Done! replaced count:%u, seqLen:%u\nEncoding CFG...",rep,slen);
	{
		U32 l=rds->txt_len, u=0;

		E=(U32*)malloc(sizeof(*E)*c);
		for(i=c;i;)E[--i]=1<<31;
		for(i=CHAR_SIZE;i;)C[--i]=1<<31;
		for(f=sizeof(F)/sizeof(F[0]);f;)F[--f]=1<<31;
		for(g=3;c>>++u;);
		eB(5,u--);eB(u,c^1<<u);
		for(cb=u=0;slen>>++u;);
		eB(5,u--);eB(u,slen^1<<u);
		for(;cs-1>>++cb;);

		for(eB(1,U[i=0]>-1);c=i<CHAR_SIZE;eB(u*2-1,c)){
			for(u=U[i]>-1;u==(U[++i]>-1)&&i<256;c++);
			if(c<256)for(u=0;c>>++u;);
			else u=5, c=0;
		}
		for(nc=bn=0;c<l;){
			if(seq[c].code == NIL){
				c = seq[c].prev;
				continue;
			}enc(seq[c++].code);
			eb(0,F+f);f=2;
		}free(E);
		printf("Done! last code: %d\n",nc);
	}
	if(size)goto loop;

	for(eB(i=5,0);i--;L=(U32)L<<8)
		if((L^0xff000000)>>0>0xffffff){
			putc(B+(c=L>>32),op);
			for(c+=255;N;N--)putc(c,op);
			B=(U32)L>>24;
		}else++N;
	free(dict->rule);free(dict->tcode);
	free(dict);free(seq);free(rds);
}

/////////////////////////////////////////////////////////////////////
void DesPair(FILE *ip, FILE *op, int vbs){
	U8 toChar[CHAR_SIZE], cb;
	RULE *rule=0;
	U32 rules, seqs, cs, nc, bn, smax=256, rmax=0;
	U32 i=128, c, n, exc, *stack=(U32*)malloc(sizeof(U32)*smax);
	// range coder
	U32 R=5, L=0;
	// models
	U8 D[128], f, g;
	U32 C[CHAR_SIZE], *E=0, F[6];	// symbol & flag

	if(!stack)puts(noMem), exit(1);
	for(;i;)D[--i]=4096/(i+128);
	for(;R--;)L=L<<8|getc(ip);

	void dec(RULE *rule, U32 c){
		if(c<cs){putc(toChar[c],op);return;}
		dec(rule,rule[c].left);
		dec(rule,rule[c].right);
	}
	inline U32 dB(int i){
		U32 b, c=0;
		for(;i--;c+=c-b){
			R>>=1;b=L-R>>31;
			for(L-=R&--b;R<16777216;R<<=8)L=L<<8|getc(ip);
		}return c;
	}
	inline U32 db(U32 *P){
		U32 p=*P>>9, r=p>>11, b;
		r=(R>>12)*(r+!r), b=L<r;
		b?R=r:(R-=r,L-=r);r=*P&127;
		for(*P+=(((b<<23)-p)*D[r]&0xffffff80)+(r<127);R<16777216;R<<=8)L=L<<8|getc(ip);
		return b;
	}

	inline U32 db2(U32 *P, int i){
		U32 c=1, d=1<<i;
		for(;i--;)c+=c+db(P+c);return c^d;
	}
loop:
	n=dB(5);
	if(!n--)goto end;
	rules=1<<n|dB(n);
	n=dB(5)-1;
	seqs=1<<n|dB(n);
	if(rmax<rules){
		n=sizeof(RULE)*rules;
		rule=(RULE*)(rule?realloc(rule,n):malloc(n));
		n=sizeof(U32)*rules;
		E=(U32*)(E?realloc(E,n):malloc(n));
		if(!rule||!E){puts(noMem);goto end;}
		for(i=rmax=rules;i;)E[--i]=1<<31;
	}else for(i=rules;i;)E[--i]=1<<31;

	// read char table
	i=g=bn=cb=cs=nc=0;
	for(n=dB(1);i<CHAR_SIZE;n^=1){
		for(c=0;c<9&&!dB(1);++c);;
		for(c=c<9?1<<c|dB(c):256;c--;i++)if(n)toChar[cs++]=i;
	}
	for(;cs-1>>++cb;);
	vbs||printf("rules = %u, seq len = %u, alphabet = %d\n",rules,seqs,cs);

	for(f=sizeof(F)/sizeof(F[0]);f;)F[--f]=1<<31;
	for(i=CHAR_SIZE;i;)C[--i]=1<<31;
	for(;++c<cs;)rule[rule[c].left = c].right = cs;
	for(;++c<rules;)rule[c].left = rule[c].right = cs;
	while(seqs--)
		for(exc=i=0;;)
			if(db(F+f)){
				if(i>=smax){
					if((smax=i*1.25)>rmax)smax=rmax;
					stack=(U32*)realloc(stack,sizeof(U32)*smax);
					if(!stack){puts(noMem);goto end;}
				}exc++;
				if(g=db(F+g+3)){
					for(;nc>>bn;)++bn;
					c=db2(E,bn-1);
					if(c>=(n=(1<<bn)-nc))c+=c+dB(1)-n;
					c+=cs;
				}else c=db2(C,cb);
				dec(rule,stack[i++]=c);f=1;
			}else{
				if(!--exc){f=2;break;}
				rule[cs+nc].right = stack[--i];
				rule[cs+nc].left = stack[--i];
				stack[i++] = cs+nc++;f=0;
			}
	goto loop;
end:
	if(rule)free(rule);if(stack)free(stack);if(E)free(E);
	puts("Done!");
}

/////////////////////////////////////////////////////////////////////
U32 getNum(char**c,U32 limit){U32 n=0;
 for(;*++(*c)<58&&*(*c)>47;)if(n<limit)n=n*10+(*(*c)-48);return n;}

int main(int i, char**v){
	if (i<3)usage:printf(
"RePair compressor v2.2\n"
"(c)2011 Shirou Maruyama, (c)2014-2018 xezz\n"
"To compress: %s c[#1,#2] infile [outfile]\n"
" outfile  default name is infile.rp\n"
" #1       block size(65536 - 2147483648). default 16MB\n"
"          add 'k' means *KB, add 'm' means *MB\n"
"          above case, separator of #2 is not needed\n"
" #2       optimization for first scan.\n"
"          0: nothing\n"
"          1: skip 3run length\n"
"          2: almost the same as above\n\n"
" Example:\n"
" %s c in out\n"
" %s c1m in out\n"
" %s c,1 in out\n"
" %s c1m1 in out\n\n"
"To decompress: %s d infile [outfile]\n"
" outfile  default name is infile.dp\n"
, *v,*v,*v,*v,*v,*v), exit(1);
	char *c=v[1], d=*c, *name=v[2], *name2=i<4?(char*)malloc(strlen(name)+4): v[3];
	if(!name2)puts(noMem),exit(1);

	FILE *ip, *op;
	U32 b=1<<24;
	clock_t t=clock();
	if(i<4)
		strcpy(name2, name),
		strcat(name2, d=='c'?".rp":".dp");
	if(ip = fopen(name2,"rb"))printf("Warning: overwrite [%s]\n",name2), fclose(ip);
	else printf("output = %s\n", name2);

	ip = fopen(name,"rb");
	op = fopen(name2,"wb");
	if(i<4)free(name2);
	if(!ip || !op)
		puts("File open error at the beginning."),
		exit(1);
	fseek(ip,0,SEEK_END);
	U64 l = _ftelli64(ip), n;
	rewind(ip);
	if(!l)puts("0byte"), exit(1);
	if(d=='c'){
		U32 A[]={1<<24,0}, a=i=n=0, s=sizeof(A)/sizeof(A[0]);
		for(;*++c&&i<s;)
			if(*c<58&&*c>47){
				if(a<10)n=n*10+*c-48,a++;
			}else{
				if(a)A[i]=*c=='k'?n<<10:*c=='m'?n<<20:n;i++;
				a=n=0;
			}
		if(a&&i<s)A[i]=n;
		RePair(ip,op,l,A[0],A[1]);
	}else if(d=='d'||d=='D')DesPair(ip,op,d=='d');
	else goto usage;
	n=_ftelli64(op);
	printf("size:%I64d -> %I64d (%2.2f%%, %2.2f bpb)\ntime:%2.3f s\n",l,n,100.0*n/l,8.0*n/l,(double)(clock()-t)/CLOCKS_PER_SEC);
	fclose(ip);fclose(op);
}