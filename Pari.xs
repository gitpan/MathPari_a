#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include <genpari.h>

/* 	$Id: Pari.xs,v 1.7 1995/01/23 18:50:58 ilya Exp ilya $	 */
/* dFUNCTION should be the last declaration! */
#ifdef __cplusplus
  #define VARARG ...
#else
  #define VARARG
#endif

#define dFUNCTION(retv)  retv (*FUNCTION)(VARARG) = \
            (retv (*)(VARARG)) CvXSUBANY( SvTYPE(ST(items)) == SVt_PVCV ? \
					    ST(items): \
					    (SvTYPE(ST(items)) == SVt_PVGV ? \
					       (SV*)GvCV(ST(items)): \
					       wrongT(ST(items), \
						      __FILE__, __LINE__)) \
					 ).any_dptr

#define CASE_INTERFACE(inter) case inter: \
                   subaddr = CAT2(XS_Math__Pari_interface, inter); break

typedef entree * PariVar;

SV* PariStack;

SV*
wrongT(SV *sv, char *file, int line)
{
  if (SvTYPE(sv) != SVt_PVCV || SvTYPE(sv) != SVt_PVGV) {
    croak("Got the type 0x%x instead of CV=0x%x or GV=0x%x in %s, %i", 
	  SvTYPE(sv), SVt_PVCV, SVt_PVGV, file, line);      
  } else {
    croak("Something very wrong  in %s, %i", file, line);
  }
  return NULL;				/* To pacify compiler. */
}

PariVar
findVariable(char *s)
{
  char *olds = s, *u, *v;
  long n;
  GEN p1;
  entree *ep;
  
  for (n = 0; isalnum(*s); s++) n = n << 1 ^ *s;
  if (*s) goto junk;
  if (n < 0) n = -n; n %= TBLSZ;
  for(ep = hashtable[n]; ep; ep = ep->next)
  {
    for(u = ep->name, v = olds; (*u) && *u == *v; u++, v++);
    if (!*u && !*v) {
      if (ep->valence != 200)
	croak("Got a function name instead of a variable");
      return ep;
    }
  }
  ep = (entree *)malloc(sizeof(entree) + 7*BYTES_IN_LONG 
			+ s - olds + 1);
  ep->name = (char *)ep + sizeof(entree) + 7*BYTES_IN_LONG;
  for (u = ep->name, v = olds; v < s;) *u++ = *v++; *u = 0;
  ep->value = (void *)((char *)ep + sizeof(entree));
  ep->next = hashtable[n];
  hashtable[n] = ep;
  p1 = (GEN)ep->value;
  if (nvar == MAXVAR) err(trucer1);
  ep->valence = 200;
  p1[0] = evaltyp(10)+evalpere(1)+evallg(4);
  p1[1] = evalsigne(1)+evallgef(4)+evalvarn(nvar);
  p1[2] = zero; p1[3] = un;
  polx[nvar] = p1;
  polvar[nvar+1] = (long)p1;
  p1 += 4;
  p1[0] = evaltyp(10)+evalpere(1)+evallg(3);
  p1[1] = evalsigne(1)+evallgef(3)+evalvarn(nvar); p1[2] = un;
  polun[nvar] = p1;
  varentries[nvar++] = ep;
  setlg(polvar, nvar+1);
  return ep;
 junk:
  croak("Junk when expecting variable name");
  return NULL;
}



static int
not_here(s)
char *s;
{
    croak("%s not implemented on this architecture", s);
    return -1;
}

static double
constant(name, arg)
char *name;
int arg;
{
    errno = 0;
    switch (*name) {
    }
    errno = EINVAL;
    return 0;

not_there:
    errno = ENOENT;
    return 0;
}

SV* worksv;

void
svputc(char c)
{
  sv_catpvn(worksv,&c,1);
}


void
svputs(char* p)
{
  sv_catpv(worksv,p);
}


PariOUT perlOut={svputc, svputs};

GEN
sv2pari(SV* sv)
{
  if (SvROK(sv)) {
    if (sv_isa(sv, "Math::Pari")) {
      IV tmp = SvIV((SV*)SvRV(sv));
      return (GEN) tmp;
    } else {
      SV* tmp=SvRV(sv);
      int type=SvTYPE(tmp);
      if (type==SVt_PVAV) {
	AV* av=(AV*) tmp;
	I32 len=av_len(av);	/* Length-1 */
	GEN ret=cgetg(len+2,17);
	int i;
	for (i=0;i<=len;i++) {
	  SV** svp=av_fetch(av,i,0);
	  if (!svp) croak("Internal error in perl2pari!");
	  ret[i+1]=(long)sv2pari(*svp);
	}
	return ret;
      } else {
	return lisexpr(SvPV(sv,na));
      }
    }
  }
  else if (SvIOKp(sv)) return stoi(SvIV(sv));
  else if (SvNOKp(sv)) return dbltor(SvNV(sv));
  else if (SvPOK(sv)) return lisexpr(SvPV(sv,na));
  else if (!SvOK(sv)) return stoi(0);
  else
    croak("Variable in perl2pari is not of known type");  
}

GEN
sv2parimat(SV* sv)
{
  GEN in=sv2pari(sv);
  if (typ(in)==17) {
    long len=lg(in)-1;
    long t;
    long l=lg(in[1]);
    for (;len;len--) {
      if ((t=typ(in[len])) == 17) {
	settyp(in[len],18);
      } else if (t!=18) {
	croak("Not a vector where column of a matrix expected");
      }
      if (lg(in[len])!=l) {
	croak("Columns of input matrix are of different height");
      }
    }
    settyp(in,19);
    return in;
  } else if (typ(in)==19) {
    return in;
  } else {
    croak("Not a matrix where matrix expected");
  }
}


SV*
pari2iv(GEN in)
{
  return newSViv((IV)gtolong(in));
}

SV*
pari2nv(GEN in)
{
  return newSVnv(gtodouble(in));
}

SV*
pari2pv(GEN in)
{
  PariOUT *old=pariOut;
  pariOut=&perlOut;
  worksv=newSVpv("",0);
  bruteall(in,'g',-1,0);
  pariOut=old;
  return worksv;
}

long
moveoffstackafter(SV* sv)
{
  SV* sv1;
  SV* nextsv;
  long ret=0;
  
  for (sv1=PariStack;sv1 != sv;sv1=nextsv) {
    ret++;
    nextsv = (SV *) SvPVX(sv1);
    SvPVX(sv1)=NULL;	/* Mark as moved off stack */
    SvIVX(sv1) = (IV) gclone((GEN)SvIV(sv1));
  }
  return ret;
}


MODULE = Math::Pari PACKAGE = Math::Pari

GEN
sv2pari(sv)
long	oldavma=avma;
     SV *	sv

GEN
sv2parimat(sv)
long	oldavma=avma;
     SV *	sv


SV *
pari2iv(in)
long	oldavma=avma;
     GEN	in


SV *
pari2nv(in)
long	oldavma=avma;
     GEN	in


SV *
pari2num(in)
long	oldavma=avma;
     GEN	in
   CODE:
     if (typ(in)==1) {
       RETVAL=pari2iv(in);
     } else {
       RETVAL=pari2nv(in);
     }
   OUTPUT:
     RETVAL

SV *
pari2pv(in,...)
long	oldavma=avma;
     GEN	in
   CODE:
     RETVAL=pari2pv(in);
   OUTPUT:
     RETVAL

GEN
PARI(...)
long	oldavma=avma;
   CODE:
     if (items==1) {
       RETVAL=sv2pari(ST(0));
     } else {
	int i;

	RETVAL=cgetg(items+1,17);
	for (i=0;i<items;i++) {
	  RETVAL[i+1]=(long)sv2pari(ST(i));
	}
     }
   OUTPUT:
     RETVAL

GEN
PARIcol(...)
long	oldavma=avma;
   CODE:
     if (items==1) {
       RETVAL=sv2pari(ST(0));
     } else {
	int i;

	RETVAL=cgetg(items+1,17);
	for (i=0;i<items;i++) {
	  RETVAL[i+1]=(long)sv2pari(ST(i));
	}
     }
     settyp(RETVAL,18);
   OUTPUT:
     RETVAL

GEN
PARImat(...)
long	oldavma=avma;
   CODE:
     if (items==1) {
       RETVAL=sv2parimat(ST(0));
     } else {
	int i;

	RETVAL=cgetg(items+1,17);
	for (i=0;i<items;i++) {
	  RETVAL[i+1]=(long)sv2pari(ST(i));
	  settyp(RETVAL[i+1],18);
	}
     }
     settyp(RETVAL,19);
   OUTPUT:
     RETVAL

double
constant(name,arg)
	char *		name
	int		arg


double
fake(name,in)
     char *	name
     char *	in

# In what follows if a function returns long, we do not need anything
# on the stack, thus we add a cleanup section.

GEN
interface0()
long	oldavma=avma;
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(prec);
  }
 OUTPUT:
   RETVAL

GEN
interface1(arg1)
long	oldavma=avma;
GEN	arg1
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,prec);
  }
 OUTPUT:
   RETVAL

# with fake arguments for overloading

GEN
interface199(arg1,arg2,inv)
long	oldavma=avma;
GEN	arg1
GEN	arg2 = NO_INIT
long	inv = NO_INIT
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,prec);
  }
 OUTPUT:
   RETVAL


long
interface10(arg1)
long	oldavma=avma;
GEN	arg1
 CODE:
  {
    dFUNCTION(long);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1);
  }
 OUTPUT:
   RETVAL
 CLEANUP:
   avma=oldavma;

# With fake arguments for overloading

long
interface109(arg1,arg2,inv)
long	oldavma=avma;
GEN	arg1
GEN	arg2 = NO_INIT
long	inv = NO_INIT
 CODE:
  {
    dFUNCTION(long);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1);
  }
 OUTPUT:
   RETVAL
 CLEANUP:
   avma=oldavma;

GEN
interface11(arg1)
long	oldavma=avma;
long	arg1
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,prec);
  }
 OUTPUT:
   RETVAL

long
interface15(arg1)
long	oldavma=avma;
long	arg1
 CODE:
  {
    dFUNCTION(long);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1);
  }
 OUTPUT:
   RETVAL
 CLEANUP:
   avma=oldavma;

GEN
interface2(arg1,arg2)
long	oldavma=avma;
GEN	arg1
GEN	arg2
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,prec);
  }
 OUTPUT:
   RETVAL

# With fake arguments for overloading

GEN
interface299(arg1,arg2,inv)
long	oldavma=avma;
GEN	arg1
GEN	arg2
bool	inv
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL = inv? FUNCTION(arg2,arg1): FUNCTION(arg1,arg2);
  }
 OUTPUT:
   RETVAL

long
interface20(arg1,arg2)
long	oldavma=avma;
GEN	arg1
GEN	arg2
 CODE:
  {
    dFUNCTION(long);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2);
  }
 OUTPUT:
   RETVAL
 CLEANUP:
   avma=oldavma;

# With fake arguments for overloading and comparison to gun for speed

long
interface2099(arg1,arg2,inv)
long	oldavma=avma;
GEN	arg1
GEN	arg2
bool	inv
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL = (inv? FUNCTION(arg2,arg1): FUNCTION(arg1,arg2)) == gun;
  }
 OUTPUT:
   RETVAL
 CLEANUP:
   avma=oldavma;

# With fake arguments for overloading

long
interface209(arg1,arg2,inv)
long	oldavma=avma;
GEN	arg1
GEN	arg2
bool	inv
 CODE:
  {
    dFUNCTION(long);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL = inv? FUNCTION(arg2,arg1): FUNCTION(arg1,arg2);
  }
 OUTPUT:
   RETVAL
 CLEANUP:
   avma=oldavma;

GEN
interface3(arg1,arg2,arg3)
long	oldavma=avma;
GEN	arg1
GEN	arg2
GEN	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,arg3,prec);
  }
 OUTPUT:
   RETVAL

long
interface30(arg1,arg2,arg3)
long	oldavma=avma;
GEN	arg1
GEN	arg2
GEN	arg3
 CODE:
  {
    dFUNCTION(long);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,arg3);
  }
 OUTPUT:
   RETVAL
 CLEANUP:
   avma=oldavma;

GEN
interface4(arg1,arg2,arg3,arg4)
long	oldavma=avma;
GEN	arg1
GEN	arg2
GEN	arg3
GEN	arg4
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,arg3,arg4,prec);
  }
 OUTPUT:
   RETVAL

GEN
interface5(arg1,arg2,arg3,arg4,arg5)
long	oldavma=avma;
GEN	arg1
GEN	arg2
GEN	arg3
GEN	arg4
GEN	arg5
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,arg3,arg4,prec);
  }
 OUTPUT:
   RETVAL

GEN
interface12(arg1,arg2)
long	oldavma=avma;
GEN	arg1
GEN	arg2
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,numvar(arg2), precdl);
  }
 OUTPUT:
   RETVAL


GEN
interface13(arg1)
long	oldavma=avma;
GEN	arg1
 CODE:
  {
    long junk;
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, &junk);
  }
 OUTPUT:
   RETVAL


GEN
interface14(arg1,arg2)
long	oldavma=avma;
GEN	arg1
GEN	arg2
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,numvar(arg2));
  }
 OUTPUT:
   RETVAL


GEN
interface21(arg1,arg2)
long	oldavma=avma;
GEN	arg1
long	arg2
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2);
  }
 OUTPUT:
   RETVAL


GEN
interface22(arg1,arg2,arg3)
long	oldavma=avma;
GEN	arg1
PariVar	arg2
char *	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg2, arg1, arg3);
  }
 OUTPUT:
   RETVAL

GEN
interface23(arg1,arg2)
long	oldavma=avma;
GEN	arg1
long	arg2
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,prec);
  }
 OUTPUT:
   RETVAL

GEN
interface24(arg1,arg2)
long	oldavma=avma;
long	arg1
GEN	arg2
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,prec);
  }
 OUTPUT:
   RETVAL

GEN
interface25(arg1,arg2)
long	oldavma=avma;
GEN	arg1
GEN	arg2
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2);
  }
 OUTPUT:
   RETVAL

GEN
interface26(arg1,arg2,arg3)
long	oldavma=avma;
GEN	arg1
GEN	arg2
GEN	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, numvar(arg2), arg3);
  }
 OUTPUT:
   RETVAL

GEN
interface27(arg1,arg2,arg3)
long	oldavma=avma;
PariVar	arg1
GEN	arg2
char *	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg2, arg3, prec);
  }
 OUTPUT:
   RETVAL

GEN
interface28(arg1,arg2)
long	oldavma=avma;
GEN	arg1
GEN	arg2
 CODE:
  {
    long junk;
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg2, &junk);
  }
 OUTPUT:
   RETVAL

long
interface29(arg1,arg2)
long	oldavma=avma;
GEN	arg1
long	arg2
 CODE:
  {
    dFUNCTION(long);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2);
  }
 OUTPUT:
   RETVAL
 CLEANUP:
   avma=oldavma;

GEN
interface31(arg1,arg2,arg3)
long	oldavma=avma;
GEN	arg1
GEN	arg2
GEN	arg3
 CODE:
  {
    GEN junk;
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg2, arg3, &junk);
    cgiv(junk);
  }
 OUTPUT:
   RETVAL

GEN
interface32(arg1,arg2,arg3)
long	oldavma=avma;
GEN	arg1
GEN	arg2
long	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,arg3);
  }
 OUTPUT:
   RETVAL

GEN
interface33(arg1,arg2,arg3)
long	oldavma=avma;
GEN	arg1
long	arg2
long	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,arg3);
  }
 OUTPUT:
   RETVAL

GEN
interface34(arg1,arg2,arg3)
long	oldavma=avma;
long	arg1
long	arg2
long	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg2, arg3);
  }
 OUTPUT:
   RETVAL

GEN
interface35(arg1,arg2,arg3)
long	oldavma=avma;
long	arg1
GEN	arg2
GEN	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1,arg2,arg3);
  }
 OUTPUT:
   RETVAL

GEN
interface37(arg1,arg2,arg3,arg4)
long	oldavma=avma;
PariVar	arg1
GEN	arg2
GEN	arg3
char *	arg4
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg2, arg3, arg4, prec);
  }
 OUTPUT:
   RETVAL

GEN
interface48(arg0,arg1,arg2,arg3,arg4)
long	oldavma=avma;
GEN	arg0
PariVar	arg1
GEN	arg2
GEN	arg3
char *	arg4
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg0, arg2, arg3, arg4, prec);
  }
 OUTPUT:
   RETVAL

GEN
interface49(arg0,arg00,arg1,arg2,arg3)
long	oldavma=avma;
GEN	arg0
GEN	arg00
PariVar	arg1
PariVar	arg2
char *	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg2, arg0, arg00, arg3);
  }
 OUTPUT:
   RETVAL

GEN
interface83(arg1,arg2,arg3,arg4)
long	oldavma=avma;
PariVar	arg1
GEN	arg2
GEN	arg3
char *	arg4
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg2, arg3, arg4);
  }
 OUTPUT:
   RETVAL

GEN
interface84(arg1,arg2,arg3,arg4)
long	oldavma=avma;
PariVar	arg1
GEN	arg2
char *	arg3
 CODE:
  {
    dFUNCTION(GEN);

    if (!FUNCTION) {
      croak("XSUB call through interface did not provide *function");
    }

    RETVAL=FUNCTION(arg1, arg2, arg3);
  }
 OUTPUT:
   RETVAL

bool
_2bool(arg1,arg2,inv)
long	oldavma=avma;
     GEN	arg1
     GEN	arg2 = NO_INIT
     long	inv = NO_INIT
   CODE:
     RETVAL=!gcmp0(arg1);
   OUTPUT:
     RETVAL

bool
pari2bool(arg1)
long	oldavma=avma;
     GEN	arg1
   CODE:
     RETVAL=!gcmp0(arg1);
   OUTPUT:
     RETVAL

CV *
loadPari(name)
     char *	name
   CODE:
     {
       char *olds = name;
       entree *ep=NULL;
       long n, valence;
       void (*func)(void*)=NULL;
       void (*unsupported)(void*) = (void (*)(void*)) not_here;

       if (*name=='g') {
	 if (strEQ(name,"gneg")) {
	   valence=1;
	   func=(void (*)(void*)) gneg;
	 } else if (strEQ(name,"gadd")) {
	   valence=2;
	   func=(void (*)(void*)) gadd;
	 } else if (strEQ(name,"gsub")) {
	   valence=2;
	   func=(void (*)(void*)) gsub;
	 } else if (strEQ(name,"gmul")) {
	   valence=2;
	   func=(void (*)(void*)) gmul;
	 } else if (strEQ(name,"gdiv")) {
	   valence=2;
	   func=(void (*)(void*)) gdiv;
	 } else if (strEQ(name,"gdivent")) {
	   valence=299;
	   func=(void (*)(void*)) gdivent;
	 } else if (strEQ(name,"gmod")) {
	   valence=2;
	   func=(void (*)(void*)) gmod;
	 } else if (strEQ(name,"gpui")) {
	   valence=2;
	   func=(void (*)(void*)) gpui;
	 } else if (strEQ(name,"gle")) {
	   valence=2;
	   func=(void (*)(void*)) gle;
	 } else if (strEQ(name,"gne")) {
	   valence=2;
	   func=(void (*)(void*)) gne;
	 } else if (strEQ(name,"glt")) {
	   valence=2;
	   func=(void (*)(void*)) glt;
	 } else if (strEQ(name,"gge")) {
	   valence=2;
	   func=(void (*)(void*)) gge;
	 } else if (strEQ(name,"ggt")) {
	   valence=2;
	   func=(void (*)(void*)) ggt;
	 } else if (strEQ(name,"geq")) {
	   valence=2;
	   func=(void (*)(void*)) geq;
	 } else if (strEQ(name,"gor")) {
	   valence=2;
	   func=(void (*)(void*)) gor;
	 } else if (strEQ(name,"gand")) {
	   valence=2;
	   func=(void (*)(void*)) gand;
	 } else if (strEQ(name,"gcmp")) {
	   valence=20;
	   func=(void (*)(void*)) gcmp;
	 } else if (strEQ(name,"gegal")) {
	   valence=20;
	   func=(void (*)(void*)) gegal;
	 } else if (strEQ(name,"gcmp0")) {
	   valence=10;
	   func=(void (*)(void*)) gcmp0;
	 } else if (strEQ(name,"gcmp1")) {
	   valence=10;
	   func=(void (*)(void*)) gcmp1;
	 } else if (strEQ(name,"gcmp_1")) {
	   valence=10;
	   func=(void (*)(void*)) gcmp_1;
	 }
       } else if (*name=='_') {
	 if (strEQ(name,"_gneg")) {
	   valence=199;
	   func=(void (*)(void*)) gneg;
	 } else if (strEQ(name,"_gadd")) {
	   valence=299;
	   func=(void (*)(void*)) gadd;
	 } else if (strEQ(name,"_gsub")) {
	   valence=299;
	   func=(void (*)(void*)) gsub;
	 } else if (strEQ(name,"_gmul")) {
	   valence=299;
	   func=(void (*)(void*)) gmul;
	 } else if (strEQ(name,"_gdiv")) {
	   valence=299;
	   func=(void (*)(void*)) gdiv;
	 } else if (strEQ(name,"_gmod")) {
	   valence=299;
	   func=(void (*)(void*)) gmod;
	 } else if (strEQ(name,"_gpui")) {
	   valence=299;
	   func=(void (*)(void*)) gpui;
	 } else if (strEQ(name,"_gle")) {
	   valence=2099;
	   func=(void (*)(void*)) gle;
	 } else if (strEQ(name,"_gne")) {
	   valence=2099;
	   func=(void (*)(void*)) gne;
	 } else if (strEQ(name,"_glt")) {
	   valence=2099;
	   func=(void (*)(void*)) glt;
	 } else if (strEQ(name,"_gge")) {
	   valence=2099;
	   func=(void (*)(void*)) gge;
	 } else if (strEQ(name,"_ggt")) {
	   valence=2099;
	   func=(void (*)(void*)) ggt;
	 } else if (strEQ(name,"_geq")) {
	   valence=2099;
	   func=(void (*)(void*)) geq;
	 } else if (strEQ(name,"_gor")) {
	   valence=2099;
	   func=(void (*)(void*)) gor;
	 } else if (strEQ(name,"_gand")) {
	   valence=2099;
	   func=(void (*)(void*)) gand;
	 } else if (strEQ(name,"_gcmp")) {
	   valence=209;
	   func=(void (*)(void*)) gcmp;
	 } else if (strEQ(name,"_lex")) {
	   valence=209;
	   func=(void (*)(void*)) lexcmp;
	 } else if (strEQ(name,"_gcmp0")) {
	   valence=109;
	   func=(void (*)(void*)) gcmp0;
	 } else if (strEQ(name,"_abs")) {
	   valence=199;
	   func=(void (*)(void*)) gabs;
	 } else if (strEQ(name,"_sin")) {
	   valence=199;
	   func=(void (*)(void*)) gsin;
	 } else if (strEQ(name,"_cos")) {
	   valence=199;
	   func=(void (*)(void*)) gcos;
	 } else if (strEQ(name,"_exp")) {
	   valence=199;
	   func=(void (*)(void*)) gexp;
	 } else if (strEQ(name,"_log")) {
	   valence=199;
	   func=(void (*)(void*)) glog;
	 } else if (strEQ(name,"_sqrt")) {
	   valence=199;
	   func=(void (*)(void*)) gsqrt;
	 }
       }
       if (!func) {
	 for (n = 0; *name; name++) n = n << 1 ^ *name;
	 if (n < 0) n = -n; n %= TBLSZ;
	 for(ep = hashtable[n]; ep; ep = ep->next) {
	   if (strEQ(olds,ep->name)) { /* Name in the symbol table */
	     break;
	   }
	 }
	 if (!ep) {
	   croak("`%s' is not a Pari function name",olds);
	 }
	 if (ep && (ep->valence<100 && ep>=fonctions
		    && ep<fonctions+NUMFUNC)) { /* Builtin */
	   valence=ep->valence;
	   func=(void (*)(void*)) ep->value;
	   if (!func) {
	     func = unsupported;
	   }
	 } 
       }
       if (func == unsupported) {
	 croak("Do not know how to work with Pari control structure `%s'",
	       olds);
       } else if (func) {
	 void (*subaddr)(CV*);
	 char* file = __FILE__;
	 char subname[276]="Math::Pari::";
	 
	 strcpy(subname+12,olds);
	 switch (valence) {
	   CASE_INTERFACE(0);
	   CASE_INTERFACE(1);
	   CASE_INTERFACE(10);
	   CASE_INTERFACE(199);
	   CASE_INTERFACE(109);
	   CASE_INTERFACE(11);
	   CASE_INTERFACE(15);
	   CASE_INTERFACE(2);
	   CASE_INTERFACE(20);
	   CASE_INTERFACE(299);
	   CASE_INTERFACE(209);
	   CASE_INTERFACE(2099);
	   CASE_INTERFACE(3);
	   CASE_INTERFACE(30);
	   CASE_INTERFACE(4);
	   CASE_INTERFACE(5);
	   CASE_INTERFACE(21);
	   CASE_INTERFACE(23);
	   CASE_INTERFACE(24);
	   CASE_INTERFACE(25);
	   CASE_INTERFACE(29);
	   CASE_INTERFACE(32);
	   CASE_INTERFACE(33);
	   CASE_INTERFACE(35);
	   CASE_INTERFACE(12);
	   CASE_INTERFACE(13);
	   CASE_INTERFACE(14);
	   CASE_INTERFACE(26);
	   CASE_INTERFACE(28);
	   CASE_INTERFACE(31);
	   CASE_INTERFACE(34);
	   CASE_INTERFACE(22);
	   CASE_INTERFACE(27);
	   CASE_INTERFACE(37);
	   CASE_INTERFACE(48);
	   CASE_INTERFACE(49);
	   CASE_INTERFACE(83);
	   CASE_INTERFACE(84);
	 default: croak("Unsupported interface %d for a Pari function %s",
			valence, olds);
	 }
	 RETVAL = newXS(subname,subaddr,file);
	 CvXSUBANY(RETVAL).any_dptr = func;
       } else {
	 croak("Cannot load a Pari macro `%s'",olds);
       }
     }
   OUTPUT:
     RETVAL

BOOT:
   init(4000000,500000); /* take four million bytes of memory for the
	 		  * stack, calculate primes up to 500000 */
   PariStack=(SV *)&PariStack;


MODULE = Math::Pari PACKAGE = Math::Pari PREFIX = Math_Pari_

void
Math_Pari_DESTROY(rv)
     SV *	rv
   CODE:
     {
       SV* sv = SvRV(rv);
       SV* prev = (SV*)SvPVX(sv);
       long oldavma=SvCUR(sv)+bot;
       long howmany;
       
       SvPVX(sv)=NULL;		/* To avoid extra free() */
       if (prev && prev != (SV*)&PariStack) { /* It is on stack, &PariStack
					       * is just an atom here. */
	 if (sv != PariStack) { /* There is another value on stack */
	   howmany=moveoffstackafter(sv);
	   DEBUG_u( deb("%li items moved off stack\n", howmany) );
	 }
	 avma=oldavma;		/* Mark the space on stack as free */
	 PariStack=prev;
       } else if (!prev) {			/* Is malloc()ed */ 
	 killbloc((void*)SvIV(sv));
       }
     }
