/*
 Tensor product of two arrays, using strides to avoid 
 duplication.  Jonathan Rougier <J.C.Rougier@durham.ac.uk>
 
 v1.0 09.09.00

 10.09.00 Minor correction in default case of main switch
 11.09.00 Cleaner case switching with modeAB
 12.09.00 Tidy up the case switching in CPLXSXP
 15.09.00 Cleaner still with modeA and modeB
 05.10.00 Changes in generic vector syntax for R v1.2

 */

#include <R.h>
#include <Rdefines.h>

#define IS_ARRAY(x) isArray(x) /* omitted from Rdefines.h, R.1.0.1 */

/* check for duplicates in x */

static int isDup(int *x, const int n)
{
  int i, j;

  for (i = 0; i < n; i++)
    for (j = i+1; j < n; j++)
      if (x[i] == x[j])
	return 1;
  return 0;
}

/* little integer perm */

static void littlePerm(int *x, const int n, const int *pp, int *scratch)
{
  int i;

  for (i = 0; i < n; i++)
    scratch[i] = x[i];
  for (i = 0; i < n; i++)
    x[i] = scratch[pp[i]];
}

/* move the indices given in ss to the end of x */

static void permToEnd(int *x, const int n, const int *ss, const int nss, int *scratch)
{
  int i, j, k;

  for (i = 0; i < n; i++)
    scratch[i] = x[i];

  for (i = 0, j = 0; j < n - nss; i++) {
    for (k = 0; k < nss; k++)
      if (i == ss[k])
	break;
    if (k == nss)
      x[j++] = scratch[i];
  }
  for (k = 0; k < nss; x[j++] = scratch[ss[k++]]);
}

/* rotate an index set by 1: nb very inportant that this  
   passes back to zero, as this avoids a deliberate reset */

static void incdd(int *dd, const int *dim, const int n)
{
  int j;

  for (j = 0; j<n; j++)
    if (dd[j] < dim[j]-1) {
      dd[j] += 1;
      break;
    } else
      dd[j] = 0;
}

SEXP tensor(SEXP A, SEXP B, SEXP alongA, SEXP alongB)
{
  int *dimA, ndimA, *dimB, ndimB, nalong;
  int *strideA, *strideB, *sdimA, *sdimB, *permA, *permB, *scratch;
  int i, j, k, r, ipa, ipb;
  int ilen, jlen, klen, xlen, baseA, posA, baseB, posB;
  int *ppI, nppI, *ppJ, nppJ, *ppK, nppK;

  int Isum, ItermA, ItermB;
  double Dsum, DtermA, DtermB;
  Rcomplex Csum, CtermA, CtermB;

  SEXP X;
  SEXPTYPE modeX, modeA, modeB;

  if (GET_LENGTH(A) == 0 || GET_LENGTH(B) == 0)
    error("Require objects of non-zero length");

  /* coercion is wasteful of memory: we'll switch instead */

  if (IS_INTEGER(A))
    modeA = INTSXP;
  else if (IS_NUMERIC(A))
    modeA = REALSXP;
  else if (IS_COMPLEX(A))
    modeA = CPLXSXP;
  else error("Inadmissable type for \"A\"");

  if (IS_INTEGER(B))
    modeB = INTSXP;
  else if (IS_NUMERIC(B))
    modeB = REALSXP;
  else if (IS_COMPLEX(B))
    modeB = CPLXSXP;
  else error("Inadmissable type for \"B\"");

  if (modeA==INTSXP && modeB==INTSXP)
    modeX = INTSXP;
  else if (modeA!=CPLXSXP && modeB!=CPLXSXP)
    modeX = REALSXP;
  else modeX = CPLXSXP;

  /* handle vector A or B without coercion */

  if (!IS_ARRAY(A)) {
    ndimA = 1;
    dimA = (int *) R_alloc(1, sizeof(int));
    dimA[0] = GET_LENGTH(A);
  } else {
    ndimA = GET_LENGTH(GET_DIM(A));
    dimA = (int *) R_alloc(ndimA, sizeof(int));
    for (r = 0; r < ndimA; r++)
      dimA[r] = INTEGER_POINTER(GET_DIM(A))[r];
  }

  if (!IS_ARRAY(B)) {
    ndimB = 1;
    dimB = (int *) R_alloc(1, sizeof(int));
    dimB[0] = GET_LENGTH(B);
  } else {
    ndimB = GET_LENGTH(GET_DIM(B));
    dimB = (int *) R_alloc(ndimB, sizeof(int));
    for (r = 0; r < ndimB; r++)
      dimB[r] = INTEGER_POINTER(GET_DIM(B))[r];
  }

  /* but coerce the along vectors (which could have length 0) */

  PROTECT(alongA = AS_INTEGER(alongA));
  PROTECT(alongB = AS_INTEGER(alongB));
  nalong = GET_LENGTH(alongA);

  if (nalong != GET_LENGTH(alongB)) {
    UNPROTECT(2); /* alongA, alongB */
    error("Require \"along\" vectors to be equal length");
  }

  if (nalong>0 && (isDup(INTEGER_POINTER(alongA), nalong) ||
      isDup(INTEGER_POINTER(alongB), nalong))) {
    UNPROTECT(2);
    error("Cannot have duplicates in \"along\" vectors");
  }

  for (r = 0; r < nalong; r++) {

    INTEGER_POINTER(alongA)[r] -= 1; /* 1-offset in R */
    INTEGER_POINTER(alongB)[r] -= 1;

    ipa = INTEGER_POINTER(alongA)[r];
    ipb = INTEGER_POINTER(alongB)[r];

    if (ipa<0 || ipa>=ndimA || ipb<0 || ipb>=ndimB) {
      UNPROTECT(2);
      error("Unavailable extents in \"along\" vectors");
    }

    if (dimA[ipa] != dimB[ipb]) {
      UNPROTECT(2);
      error("Unmatched extents in \"along\" vectors");
    }
  }

  /* set up the two strides */

  strideA = (int *) R_alloc(ndimA, sizeof(int));
  for (strideA[0] = 1, r = 1; r < ndimA; r++)
    strideA[r] = strideA[r-1] * dimA[r-1];

  strideB = (int *) R_alloc(ndimB, sizeof(int));
  for (strideB[0] = 1, r = 1; r < ndimB; r++)
    strideB[r] = strideB[r-1] * dimB[r-1];
  
  /* make up two permutation vectors for A and B, and perm
     the along extents to the end of the strides, also make
     sdims to match */

  scratch = Calloc(ndimA > ndimB ? ndimA : ndimB, int);

  permA = (int *) R_alloc(ndimA, sizeof(int));
  sdimA = (int *) R_alloc(ndimA, sizeof(int));
  for (r = 0; r < ndimA; r++) {
    permA[r] = r;
    sdimA[r] = dimA[r];
  }
  permToEnd(permA, ndimA, INTEGER_POINTER(alongA), nalong, scratch);

  littlePerm(strideA, ndimA, permA, scratch);
  littlePerm(sdimA, ndimA, permA, scratch);

  permB = (int *) R_alloc(ndimB, sizeof(int));
  sdimB = (int *) R_alloc(ndimB, sizeof(int));
  for (r = 0; r < ndimB; r++) {
    permB[r] = r;
    sdimB[r] = dimB[r];
  }
  permToEnd(permB, ndimB, INTEGER_POINTER(alongB), nalong, scratch);

  littlePerm(strideB, ndimB, permB, scratch);
  littlePerm(sdimB, ndimB, permB, scratch);

  Free(scratch);

  /* three index-sets to run through rectangular objects */

  nppI = ndimA - nalong;
  if (nppI > 0)
    ppI = (int *) R_alloc(nppI, sizeof(int)); /* rows of A */

  nppJ = nalong;
  if (nppJ > 0)
    ppJ = (int *) R_alloc(nppJ, sizeof(int)); /* cols of A / B */

  nppK = ndimB - nalong;
  if (nppK > 0)
    ppK = (int *) R_alloc(nppK, sizeof(int)); /* rows of B */

  for (ilen = 1, i = 0; i < nppI; ilen *= sdimA[i++]);
  for (jlen = 1; i < ndimA; jlen *= sdimA[i++]);
  for (klen = 1, i = 0; i < nppK; klen *= sdimB[i++]);
  
  /* zero all index sets: these rotate so will stay in synch 
     through the looping, except for NA jumps, eg IEEE_754 */

  for (r = 0; r < nppI; ppI[r++] = 0);
  for (r = 0; r < nppJ; ppJ[r++] = 0);
  for (r = 0; r < nppK; ppK[r++] = 0);

  /* Define the returning object, setting the SEXPTYPE.
     Note that where the two objects are completely reduced the
     return is a scalar and NOT a 1D array.  See the help file
     for my reasons for this. */

  xlen = ilen * klen;
  PROTECT(X = allocVector(modeX, xlen));

  if (nppI>0 || nppK>0) {

    SEXP dimX;

    PROTECT(dimX = NEW_INTEGER(nppI + nppK));
    for (r = 0; r < nppI; r++)
      INTEGER_POINTER(dimX)[r] = sdimA[r];
    for (r = 0; r < nppK; r++)
      INTEGER_POINTER(dimX)[nppI + r] = sdimB[r];
    SET_DIM(X, dimX);
    UNPROTECT(1);
  }

  /* sort out the dimnames as well (argh!!!) */

  if (nppI > 0 || nppK > 0) {

    SEXP dnA, dnB;

    if (IS_ARRAY(A))
      PROTECT(dnA = GET_DIMNAMES(A));
    else if (GET_NAMES(A) != NULL_USER_OBJECT) {
      PROTECT(dnA = NEW_LIST(1));
#if R_VERSION >= R_Version(1, 2, 0)
      SET_VECTOR_ELT(dnA, 0, GET_NAMES(A));
#else
      LIST_POINTER(dnA)[0] = GET_NAMES(A);
#endif
    } else PROTECT(dnA = NULL_USER_OBJECT);

    if (IS_ARRAY(B))
      PROTECT(dnB = GET_DIMNAMES(B));
    else if (GET_NAMES(B) != NULL_USER_OBJECT) {
      PROTECT(dnB = NEW_LIST(1));
#if R_VERSION >= R_Version(1, 2, 0)
      SET_VECTOR_ELT(dnB, 0, GET_NAMES(B));
#else
      LIST_POINTER(dnB)[0] = GET_NAMES(B);
#endif
    } else PROTECT(dnB = NULL_USER_OBJECT);

    if ((nppI > 0 && dnA != NULL_USER_OBJECT)
	|| (nppK > 0 && dnB != NULL_USER_OBJECT)) {

      SEXP dimnames, dimnamesnames, dn;

      PROTECT(dimnames = NEW_LIST(nppI + nppK));
      PROTECT(dimnamesnames = NEW_CHARACTER(nppI + nppK));

      if (dnA != NULL_USER_OBJECT) {
	PROTECT(dn = GET_NAMES(dnA));
	for (r = 0; r < nppI; r++) {
#if R_VERSION >= R_Version(1, 2, 0)
          SET_VECTOR_ELT(dimnames, r, VECTOR_ELT(dnA, permA[r]));
	  if (dn != NULL_USER_OBJECT)
	    SET_STRING_ELT(dimnamesnames, r, STRING_ELT(dn, permA[r]));
#else
	  LIST_POINTER(dimnames)[r] = LIST_POINTER(dnA)[permA[r]];
	  if (dn != NULL_USER_OBJECT)
	    CHARACTER_POINTER(dimnamesnames)[r] = CHARACTER_POINTER(dn)[permA[r]];
#endif
	}
	UNPROTECT(1);
      }

      if (dnB != NULL_USER_OBJECT) {
	PROTECT(dn = GET_NAMES(dnB));
	for (r = 0; r < nppK; r++) {
#if R_VERSION >= R_Version(1, 2, 0)
	  SET_VECTOR_ELT(dimnames, nppI + r, VECTOR_ELT(dnB, permB[r]));
	  if (dn != NULL_USER_OBJECT)
	    SET_STRING_ELT(dimnamesnames, nppI + r, STRING_ELT(dn, permB[r]));
#else
	  LIST_POINTER(dimnames)[nppI + r] = LIST_POINTER(dnB)[permB[r]];
	  if (dn != NULL_USER_OBJECT)
	    CHARACTER_POINTER(dimnamesnames)[nppI + r] = CHARACTER_POINTER(dn)[permB[r]];
#endif
	}
	UNPROTECT(1);
      }

      SET_NAMES(dimnames, dimnamesnames);
      SET_DIMNAMES(X, dimnames);
      UNPROTECT(2); /* dimnames, dimnamesnames */
    }

    UNPROTECT(2); /* dnA and dnB */
  }

  /* huge switch here to handle each mode differently:
     not the most elegant, but certainly the fastest solution! 
     Also makes the structure of the calculation clear. */

  switch(modeX) {

  case INTSXP:

    /* integer NA requires special handling (see below) */

    if (modeX==INTSXP)
      for (r = 0; r < xlen; r++)
	INTEGER_POINTER(X)[r] = NA_INTEGER;

    for (i = 0; i < ilen; i++) {

      for (baseA = 0, r = 0; r < nppI; r++)
	baseA += strideA[r] * ppI[r];

      for (k = 0; k < klen; k++) {

	for (baseB = 0, r = 0; r < nppK; r++)
	  baseB += strideB[r] * ppK[r];

	Isum = 0;
    
	for (j = 0; j < jlen; j++) {

	  for (posA = baseA, posB = baseB, r = 0; r < nppJ; r++) {
	    posA += strideA[nppI + r] * ppJ[r];
	    posB += strideB[nppK + r] * ppJ[r];
	  }

	  ItermA = INTEGER_POINTER(A)[posA];
	  ItermB = INTEGER_POINTER(B)[posB];
	
	  /* this bit is peculiar to integers */

	  if (ItermA==NA_INTEGER || ItermB==NA_INTEGER) {
	    for (r = 0; r < nppJ; ppJ[r++] = 0);
	    goto InextLoop;
	  }

	  Isum += ItermA * ItermB;

	  if (nppJ > 0)
	    incdd(ppJ, sdimA + nppI, nppJ);
	}

	INTEGER_POINTER(X)[i + ilen * k] = Isum;

      InextLoop:

	if (nppK > 0)
	  incdd(ppK, sdimB, nppK);
      }

      if (nppI > 0)
	incdd(ppI, sdimA, nppI);
    }

    break;

  case REALSXP:

#ifndef IEEE_754
    for (r = 0; r < xlen; r++)
      NUMERIC_POINTER(X)[r] = NA_REAL;
#endif

    for (i = 0; i < ilen; i++) {

      for (baseA = 0, r = 0; r < nppI; r++)
	baseA += strideA[r] * ppI[r];

      for (k = 0; k < klen; k++) {

	for (baseB = 0, r = 0; r < nppK; r++)
	  baseB += strideB[r] * ppK[r];

	Dsum = 0.0;

	for (j = 0; j < jlen; j++) {

	  for (posA = baseA, posB = baseB, r = 0; r < nppJ; r++) {
	    posA += strideA[nppI + r] * ppJ[r];
	    posB += strideB[nppK + r] * ppJ[r];
	  }

	  if (modeA == INTSXP) {
	    DtermA = (double) INTEGER_POINTER(A)[posA];
	    DtermB = NUMERIC_POINTER(B)[posB];
	  } else if (modeB == INTSXP) {
	    DtermA = NUMERIC_POINTER(A)[posA];
	    DtermB = (double) INTEGER_POINTER(B)[posB];
	  } else {
	    DtermA = NUMERIC_POINTER(A)[posA];
	    DtermB = NUMERIC_POINTER(B)[posB];
	  }

#ifndef IEEE_754
	  if (ISNAN(DtermA) || ISNAN(DtermB)) {
	    for (r = 0; r < nppJ; ppJ[r++] = 0);
	    goto DnextLoop;
	  }
#endif

	  Dsum += DtermA * DtermB;

	  if (nppJ > 0)
	    incdd(ppJ, sdimA + nppI, nppJ);
	}

	NUMERIC_POINTER(X)[i + ilen * k] = Dsum;

#ifndef IEEE_754
      DnextLoop:
#endif

	if (nppK > 0)
	  incdd(ppK, sdimB, nppK);
      }

      if (nppI > 0)
	incdd(ppI, sdimA, nppI);
    }

    break;

  case CPLXSXP:

#ifndef IEEE_754
    for (r = 0; r < xlen; r++) {
      COMPLEX_POINTER(X)[r].r = NA_REAL;
      COMPLEX_POINTER(X)[r].i = NA_REAL;
    }
#endif

    for (i = 0; i < ilen; i++) {

      for (baseA = 0, r = 0; r < nppI; r++)
	baseA += strideA[r] * ppI[r];

      for (k = 0; k < klen; k++) {

	for (baseB = 0, r = 0; r < nppK; r++)
	  baseB += strideB[r] * ppK[r];

	Csum.r = 0.0;
	Csum.i = 0.0;

	for (j = 0; j < jlen; j++) {

	  for (posA = baseA, posB = baseB, r = 0; r < nppJ; r++) {
	    posA += strideA[nppI + r] * ppJ[r];
	    posB += strideB[nppK + r] * ppJ[r];
	  }

	  if (modeA != CPLXSXP) {
	    if (modeA == INTSXP)
	      CtermA.r = (double) INTEGER_POINTER(A)[posA];
	    else
	      CtermA.r = NUMERIC_POINTER(A)[posA];
	    CtermA.i = 0.0;
	    CtermB.r = COMPLEX_POINTER(B)[posB].r;
	    CtermB.i = COMPLEX_POINTER(B)[posB].i;
	  } else if (modeB != CPLXSXP) {
	    if (modeB == INTSXP)
	      CtermB.r = (double) INTEGER_POINTER(B)[posB];
	    else
	      CtermB.r = NUMERIC_POINTER(B)[posB];
	    CtermB.i = 0.0;
	    CtermA.r = COMPLEX_POINTER(A)[posA].r;
	    CtermA.i = COMPLEX_POINTER(A)[posA].i;
	  } else {
	    CtermA.r = COMPLEX_POINTER(A)[posA].r;
	    CtermA.i = COMPLEX_POINTER(A)[posA].i;
	    CtermB.r = COMPLEX_POINTER(B)[posB].r;
	    CtermB.i = COMPLEX_POINTER(B)[posB].i;
	  }

#ifndef IEEE_754
	  if (ISNAN(CtermA.r) || ISNAN(CtermA.i)
	      || ISNAN(CtermB.r) || ISNAN(CtermB.i)) {
	    for (r = 0; r < nppJ; ppJ[r++] = 0);
	    goto CnextLoop;
	  }
#endif

	  Csum.r += CtermA.r * CtermB.r - CtermA.i * CtermB.i;
	  Csum.i += CtermA.i * CtermB.r + CtermA.r * CtermB.i;

	  if (nppJ > 0)
	    incdd(ppJ, sdimA + nppI, nppJ);
	}

	COMPLEX_POINTER(X)[i + ilen * k].r = Csum.r;
	COMPLEX_POINTER(X)[i + ilen * k].i = Csum.i;

#ifndef IEEE_754
      CnextLoop:
#endif

	if (nppK > 0)
	  incdd(ppK, sdimB, nppK);
      }

      if (nppI > 0)
	incdd(ppI, sdimA, nppI);
    }

    break;

  default:
    UNPROTECT(3);
    error("Never get here");
    break;

  } /* end huge switch statement */

  UNPROTECT(3); /* alongA, alongB, X */
  return X;
}
