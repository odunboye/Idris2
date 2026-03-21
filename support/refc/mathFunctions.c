#include "mathFunctions.h"
#include "memoryManagement.h"
#include "refc_util.h"
#include "runtime.h"
#include <inttypes.h>
#include <stdint.h>

/* Helper macros for the GMP fast path.
 * xi_of / yi_of: extract the int64_t value of a small Integer operand,
 * or mpz_get_si for a GMP operand.
 * BOTH_SMALL: true when both operands use the fast path. */
#ifndef IDRIS2_NO_GMP
#define _INT_VAL(v)                                                            \
  (IDRIS2_INT_IS_SMALL((Value_Integer *)(v))                                   \
       ? IDRIS2_INT_FAST((Value_Integer *)(v))                                 \
       : mpz_get_si(IDRIS2_INT_MPZ((Value_Integer *)(v))))
#define _BOTH_SMALL(x, y)                                                      \
  (IDRIS2_INT_IS_SMALL((Value_Integer *)(x)) &&                                \
   IDRIS2_INT_IS_SMALL((Value_Integer *)(y)))
#endif

/* cmp (function to avoid macro-expansion conflicts with GMP's mpz_cmp) */
#ifndef IDRIS2_NO_GMP
int idris2_cmp_Integer(Value *l, Value *r) {
  Value_Integer *li = (Value_Integer *)l;
  Value_Integer *ri = (Value_Integer *)r;
  if (IDRIS2_INT_IS_SMALL(li) && IDRIS2_INT_IS_SMALL(ri)) {
    int64_t lv = IDRIS2_INT_FAST(li), rv = IDRIS2_INT_FAST(ri);
    return (lv > rv) - (lv < rv);
  }
  if (IDRIS2_INT_IS_SMALL(li))
    return -mpz_cmp_si(IDRIS2_INT_MPZ(ri), (long)IDRIS2_INT_FAST(li));
  if (IDRIS2_INT_IS_SMALL(ri))
    return mpz_cmp_si(IDRIS2_INT_MPZ(li), (long)IDRIS2_INT_FAST(ri));
  return mpz_cmp(IDRIS2_INT_MPZ(li), IDRIS2_INT_MPZ(ri));
}
#endif

/* add */
Value *idris2_add_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  if (_BOTH_SMALL(x, y)) {
    int64_t result;
    if (!__builtin_add_overflow(IDRIS2_INT_FAST((Value_Integer *)x),
                                IDRIS2_INT_FAST((Value_Integer *)y), &result))
      return idris2_mkIntegerFast(result);
  }
  Value_Integer *retVal = idris2_mkInteger();
  if (IDRIS2_INT_IS_SMALL((Value_Integer *)x)) {
    mpz_set_si(IDRIS2_INT_MPZ(retVal),
               (long)IDRIS2_INT_FAST((Value_Integer *)x));
    mpz_add_ui(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ(retVal),
               0); /* no-op, normalises */
    mpz_add(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ(retVal),
            IDRIS2_INT_MPZ((Value_Integer *)y));
  } else if (IDRIS2_INT_IS_SMALL((Value_Integer *)y)) {
    long yv = (long)IDRIS2_INT_FAST((Value_Integer *)y);
    if (yv >= 0)
      mpz_add_ui(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x),
                 (unsigned long)yv);
    else
      mpz_sub_ui(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x),
                 (unsigned long)(-yv));
  } else {
    mpz_add(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x),
            IDRIS2_INT_MPZ((Value_Integer *)y));
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t result;
#if defined(__GNUC__) || defined(__clang__)
  IDRIS2_REFC_VERIFY(!__builtin_add_overflow(xi, yi, &result),
                     "Integer addition overflow (IDRIS2_NO_GMP): "
                     "%" PRId64 " + %" PRId64,
                     xi, yi);
#else
  result = xi + yi;
  IDRIS2_REFC_VERIFY(!((xi ^ result) & (yi ^ result) & INT64_MIN),
                     "Integer addition overflow (IDRIS2_NO_GMP)");
#endif
  retVal->i = result;
  return (Value *)retVal;
#endif
}

/* sub */
Value *idris2_sub_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  if (_BOTH_SMALL(x, y)) {
    int64_t result;
    if (!__builtin_sub_overflow(IDRIS2_INT_FAST((Value_Integer *)x),
                                IDRIS2_INT_FAST((Value_Integer *)y), &result))
      return idris2_mkIntegerFast(result);
  }
  Value_Integer *retVal = idris2_mkInteger();
  if (IDRIS2_INT_IS_SMALL((Value_Integer *)y)) {
    long yv = (long)IDRIS2_INT_FAST((Value_Integer *)y);
    if (!IDRIS2_INT_IS_SMALL((Value_Integer *)x)) {
      if (yv >= 0)
        mpz_sub_ui(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x),
                   (unsigned long)yv);
      else
        mpz_add_ui(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x),
                   (unsigned long)(-yv));
    } else {
      mpz_set_si(IDRIS2_INT_MPZ(retVal),
                 (long)IDRIS2_INT_FAST((Value_Integer *)x));
      if (yv >= 0)
        mpz_sub_ui(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ(retVal),
                   (unsigned long)yv);
      else
        mpz_add_ui(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ(retVal),
                   (unsigned long)(-yv));
    }
  } else if (IDRIS2_INT_IS_SMALL((Value_Integer *)x)) {
    mpz_set_si(IDRIS2_INT_MPZ(retVal),
               (long)IDRIS2_INT_FAST((Value_Integer *)x));
    mpz_sub(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ(retVal),
            IDRIS2_INT_MPZ((Value_Integer *)y));
  } else {
    mpz_sub(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x),
            IDRIS2_INT_MPZ((Value_Integer *)y));
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t result;
#if defined(__GNUC__) || defined(__clang__)
  IDRIS2_REFC_VERIFY(!__builtin_sub_overflow(xi, yi, &result),
                     "Integer subtraction overflow (IDRIS2_NO_GMP): "
                     "%" PRId64 " - %" PRId64,
                     xi, yi);
#else
  result = xi - yi;
  IDRIS2_REFC_VERIFY(!((xi ^ yi) & (xi ^ result) & INT64_MIN),
                     "Integer subtraction overflow (IDRIS2_NO_GMP)");
#endif
  retVal->i = result;
  return (Value *)retVal;
#endif
}

/* negate */
Value *idris2_negate_Integer(Value *x) {
#ifndef IDRIS2_NO_GMP
  if (IDRIS2_INT_IS_SMALL((Value_Integer *)x)) {
    int64_t xi = IDRIS2_INT_FAST((Value_Integer *)x);
    int64_t result;
    if (!__builtin_sub_overflow((int64_t)0, xi, &result))
      return idris2_mkIntegerFast(result);
  }
  Value_Integer *retVal = idris2_mkInteger();
  if (IDRIS2_INT_IS_SMALL((Value_Integer *)x)) {
    /* Only reachable if xi == INT64_MIN; promote to GMP. */
    mpz_set_si(IDRIS2_INT_MPZ(retVal),
               (long)IDRIS2_INT_FAST((Value_Integer *)x));
    mpz_neg(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ(retVal));
  } else {
    mpz_neg(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x));
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  int64_t xi = ((Value_Integer *)x)->i;
  IDRIS2_REFC_VERIFY(xi != INT64_MIN,
                     "Integer negation overflow (IDRIS2_NO_GMP): INT64_MIN");
  retVal->i = -xi;
  return (Value *)retVal;
#endif
}

/* mul */
Value *idris2_mul_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  if (_BOTH_SMALL(x, y)) {
    int64_t result;
    if (!__builtin_mul_overflow(IDRIS2_INT_FAST((Value_Integer *)x),
                                IDRIS2_INT_FAST((Value_Integer *)y), &result))
      return idris2_mkIntegerFast(result);
  }
  Value_Integer *retVal = idris2_mkInteger();
  /* Promote any small operand to GMP for the fallback path. */
  if (IDRIS2_INT_IS_SMALL((Value_Integer *)x)) {
    mpz_t tmp;
    mpz_init_set_si(tmp, (long)IDRIS2_INT_FAST((Value_Integer *)x));
    mpz_mul(IDRIS2_INT_MPZ(retVal), tmp, IDRIS2_INT_MPZ((Value_Integer *)y));
    mpz_clear(tmp);
  } else if (IDRIS2_INT_IS_SMALL((Value_Integer *)y)) {
    mpz_mul_si(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x),
               (long)IDRIS2_INT_FAST((Value_Integer *)y));
  } else {
    mpz_mul(IDRIS2_INT_MPZ(retVal), IDRIS2_INT_MPZ((Value_Integer *)x),
            IDRIS2_INT_MPZ((Value_Integer *)y));
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t result;
#if defined(__GNUC__) || defined(__clang__)
  IDRIS2_REFC_VERIFY(!__builtin_mul_overflow(xi, yi, &result),
                     "Integer multiplication overflow (IDRIS2_NO_GMP): "
                     "%" PRId64 " * %" PRId64,
                     xi, yi);
#else
  result = xi * yi;
  IDRIS2_REFC_VERIFY(xi == 0 || result / xi == yi,
                     "Integer multiplication overflow (IDRIS2_NO_GMP)");
#endif
  retVal->i = result;
  return (Value *)retVal;
#endif
}

/* div */
Value *idris2_div_Int8(Value *x, Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int8_t num = idris2_vp_to_Int8(x);
  int8_t denom = idris2_vp_to_Int8(y);
  int8_t rem = num % denom;
  return idris2_mkInt8(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Value *idris2_div_Int16(Value *x, Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int16_t num = idris2_vp_to_Int16(x);
  int16_t denom = idris2_vp_to_Int16(y);
  int16_t rem = num % denom;
  return idris2_mkInt16(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Value *idris2_div_Int32(Value *x, Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int32_t num = idris2_vp_to_Int32(x);
  int32_t denom = idris2_vp_to_Int32(y);
  int32_t rem = num % denom;
  return idris2_mkInt32(num / denom + ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}
Value *idris2_div_Int64(Value *x, Value *y) {
  // Correction term added to convert from truncated division (C default) to
  // Euclidean division For proof of correctness, see Division and Modulus for
  // Computer Scientists (Daan Leijen)
  // https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/

  int64_t num = idris2_vp_to_Int64(x);
  int64_t denom = idris2_vp_to_Int64(y);
  int64_t rem = num % denom;
  return (Value *)idris2_mkInt64(num / denom +
                                 ((rem < 0) ? (denom < 0) ? 1 : -1 : 0));
}

Value *idris2_div_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  if (_BOTH_SMALL(x, y)) {
    int64_t xi = IDRIS2_INT_FAST((Value_Integer *)x);
    int64_t yi = IDRIS2_INT_FAST((Value_Integer *)y);
    int64_t rem = xi % yi;
    if (rem < 0)
      rem += (yi < 0) ? -yi : yi;
    return idris2_mkIntegerFast((xi - rem) / yi);
  }
  Value_Integer *retVal = idris2_mkInteger();
  {
    int sx = IDRIS2_INT_IS_SMALL((Value_Integer *)x);
    int sy = IDRIS2_INT_IS_SMALL((Value_Integer *)y);
    mpz_t tmpx, tmpy, rem, yq;
    if (sx)
      mpz_init_set_si(tmpx, (long)IDRIS2_INT_FAST((Value_Integer *)x));
    if (sy)
      mpz_init_set_si(tmpy, (long)IDRIS2_INT_FAST((Value_Integer *)y));
    mpz_ptr xmpz = sx ? tmpx : IDRIS2_INT_MPZ((Value_Integer *)x);
    mpz_ptr ympz = sy ? tmpy : IDRIS2_INT_MPZ((Value_Integer *)y);
    mpz_inits(rem, yq, NULL);
    mpz_mod(rem, xmpz, ympz);
    mpz_sub(yq, xmpz, rem);
    mpz_divexact(IDRIS2_INT_MPZ(retVal), yq, ympz);
    mpz_clears(rem, yq, NULL);
    if (sx)
      mpz_clear(tmpx);
    if (sy)
      mpz_clear(tmpy);
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t rem = xi % yi;
  if (rem < 0)
    rem += (yi < 0) ? -yi : yi;
  retVal->i = (xi - rem) / yi;
  return (Value *)retVal;
#endif
}

/* mod */
Value *idris2_mod_Int8(Value *x, Value *y) {
  int8_t num = idris2_vp_to_Int8(x);
  int8_t denom = idris2_vp_to_Int8(y);
  denom = (denom < 0) ? -denom : denom;
  return (Value *)idris2_mkInt8(num % denom + (num < 0 ? denom : 0));
}

Value *idris2_mod_Int16(Value *x, Value *y) {
  int16_t num = idris2_vp_to_Int16(x);
  int16_t denom = idris2_vp_to_Int16(y);
  denom = (denom < 0) ? -denom : denom;
  return (Value *)idris2_mkInt16(num % denom + (num < 0 ? denom : 0));
}
Value *idris2_mod_Int32(Value *x, Value *y) {
  int32_t num = idris2_vp_to_Int32(x);
  int32_t denom = idris2_vp_to_Int32(y);
  denom = (denom < 0) ? -denom : denom;
  return (Value *)idris2_mkInt32(num % denom + (num < 0 ? denom : 0));
}
Value *idris2_mod_Int64(Value *x, Value *y) {
  int64_t num = idris2_vp_to_Int64(x);
  int64_t denom = idris2_vp_to_Int64(y);
  denom = (denom < 0) ? -denom : denom;
  return (Value *)idris2_mkInt64(num % denom + (num < 0 ? denom : 0));
}
Value *idris2_mod_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  if (_BOTH_SMALL(x, y)) {
    int64_t xi = IDRIS2_INT_FAST((Value_Integer *)x);
    int64_t yi = IDRIS2_INT_FAST((Value_Integer *)y);
    int64_t rem = xi % yi;
    if (rem < 0)
      rem += (yi < 0) ? -yi : yi;
    return idris2_mkIntegerFast(rem);
  }
  Value_Integer *retVal = idris2_mkInteger();
  {
    int sx = IDRIS2_INT_IS_SMALL((Value_Integer *)x);
    int sy = IDRIS2_INT_IS_SMALL((Value_Integer *)y);
    mpz_t tmpx, tmpy;
    if (sx)
      mpz_init_set_si(tmpx, (long)IDRIS2_INT_FAST((Value_Integer *)x));
    if (sy)
      mpz_init_set_si(tmpy, (long)IDRIS2_INT_FAST((Value_Integer *)y));
    mpz_ptr xmpz = sx ? tmpx : IDRIS2_INT_MPZ((Value_Integer *)x);
    mpz_ptr ympz = sy ? tmpy : IDRIS2_INT_MPZ((Value_Integer *)y);
    mpz_mod(IDRIS2_INT_MPZ(retVal), xmpz, ympz);
    if (sx)
      mpz_clear(tmpx);
    if (sy)
      mpz_clear(tmpy);
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  int64_t xi = ((Value_Integer *)x)->i;
  int64_t yi = ((Value_Integer *)y)->i;
  int64_t rem = xi % yi;
  if (rem < 0)
    rem += (yi < 0) ? -yi : yi;
  retVal->i = rem;
  return (Value *)retVal;
#endif
}

/* shiftl */
Value *idris2_shiftl_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  Value_Integer *retVal = idris2_mkInteger();
  {
    mp_bitcnt_t cnt =
        IDRIS2_INT_IS_SMALL((Value_Integer *)y)
            ? (mp_bitcnt_t)IDRIS2_INT_FAST((Value_Integer *)y)
            : (mp_bitcnt_t)mpz_get_ui(IDRIS2_INT_MPZ((Value_Integer *)y));
    int sx = IDRIS2_INT_IS_SMALL((Value_Integer *)x);
    mpz_t tmpx;
    if (sx)
      mpz_init_set_si(tmpx, (long)IDRIS2_INT_FAST((Value_Integer *)x));
    mpz_ptr xmpz = sx ? tmpx : IDRIS2_INT_MPZ((Value_Integer *)x);
    mpz_mul_2exp(IDRIS2_INT_MPZ(retVal), xmpz, cnt);
    if (sx)
      mpz_clear(tmpx);
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  int64_t cnt = ((Value_Integer *)y)->i;
  retVal->i = (cnt <= 0 || cnt >= 63) ? 0 : ((Value_Integer *)x)->i << cnt;
  return (Value *)retVal;
#endif
}

/* shiftr */
Value *idris2_shiftr_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  Value_Integer *retVal = idris2_mkInteger();
  {
    mp_bitcnt_t cnt =
        IDRIS2_INT_IS_SMALL((Value_Integer *)y)
            ? (mp_bitcnt_t)IDRIS2_INT_FAST((Value_Integer *)y)
            : (mp_bitcnt_t)mpz_get_ui(IDRIS2_INT_MPZ((Value_Integer *)y));
    int sx = IDRIS2_INT_IS_SMALL((Value_Integer *)x);
    mpz_t tmpx;
    if (sx)
      mpz_init_set_si(tmpx, (long)IDRIS2_INT_FAST((Value_Integer *)x));
    mpz_ptr xmpz = sx ? tmpx : IDRIS2_INT_MPZ((Value_Integer *)x);
    mpz_fdiv_q_2exp(IDRIS2_INT_MPZ(retVal), xmpz, cnt);
    if (sx)
      mpz_clear(tmpx);
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  int64_t cnt = ((Value_Integer *)y)->i;
  int64_t xi = ((Value_Integer *)x)->i;
  retVal->i = (cnt <= 0) ? xi : (cnt >= 63) ? (xi < 0 ? -1 : 0) : xi >> cnt;
  return (Value *)retVal;
#endif
}

/* and */
Value *idris2_and_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  if (_BOTH_SMALL(x, y))
    return idris2_mkIntegerFast(IDRIS2_INT_FAST((Value_Integer *)x) &
                                IDRIS2_INT_FAST((Value_Integer *)y));
  Value_Integer *retVal = idris2_mkInteger();
  {
    int sx = IDRIS2_INT_IS_SMALL((Value_Integer *)x);
    int sy = IDRIS2_INT_IS_SMALL((Value_Integer *)y);
    mpz_t tmpx, tmpy;
    if (sx)
      mpz_init_set_si(tmpx, (long)IDRIS2_INT_FAST((Value_Integer *)x));
    if (sy)
      mpz_init_set_si(tmpy, (long)IDRIS2_INT_FAST((Value_Integer *)y));
    mpz_ptr xmpz = sx ? tmpx : IDRIS2_INT_MPZ((Value_Integer *)x);
    mpz_ptr ympz = sy ? tmpy : IDRIS2_INT_MPZ((Value_Integer *)y);
    mpz_and(IDRIS2_INT_MPZ(retVal), xmpz, ympz);
    if (sx)
      mpz_clear(tmpx);
    if (sy)
      mpz_clear(tmpy);
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  retVal->i = ((Value_Integer *)x)->i & ((Value_Integer *)y)->i;
  return (Value *)retVal;
#endif
}

/* or */
Value *idris2_or_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  if (_BOTH_SMALL(x, y))
    return idris2_mkIntegerFast(IDRIS2_INT_FAST((Value_Integer *)x) |
                                IDRIS2_INT_FAST((Value_Integer *)y));
  Value_Integer *retVal = idris2_mkInteger();
  {
    int sx = IDRIS2_INT_IS_SMALL((Value_Integer *)x);
    int sy = IDRIS2_INT_IS_SMALL((Value_Integer *)y);
    mpz_t tmpx, tmpy;
    if (sx)
      mpz_init_set_si(tmpx, (long)IDRIS2_INT_FAST((Value_Integer *)x));
    if (sy)
      mpz_init_set_si(tmpy, (long)IDRIS2_INT_FAST((Value_Integer *)y));
    mpz_ptr xmpz = sx ? tmpx : IDRIS2_INT_MPZ((Value_Integer *)x);
    mpz_ptr ympz = sy ? tmpy : IDRIS2_INT_MPZ((Value_Integer *)y);
    mpz_ior(IDRIS2_INT_MPZ(retVal), xmpz, ympz);
    if (sx)
      mpz_clear(tmpx);
    if (sy)
      mpz_clear(tmpy);
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  retVal->i = ((Value_Integer *)x)->i | ((Value_Integer *)y)->i;
  return (Value *)retVal;
#endif
}

/* xor */
Value *idris2_xor_Integer(Value *x, Value *y) {
#ifndef IDRIS2_NO_GMP
  if (_BOTH_SMALL(x, y))
    return idris2_mkIntegerFast(IDRIS2_INT_FAST((Value_Integer *)x) ^
                                IDRIS2_INT_FAST((Value_Integer *)y));
  Value_Integer *retVal = idris2_mkInteger();
  {
    int sx = IDRIS2_INT_IS_SMALL((Value_Integer *)x);
    int sy = IDRIS2_INT_IS_SMALL((Value_Integer *)y);
    mpz_t tmpx, tmpy;
    if (sx)
      mpz_init_set_si(tmpx, (long)IDRIS2_INT_FAST((Value_Integer *)x));
    if (sy)
      mpz_init_set_si(tmpy, (long)IDRIS2_INT_FAST((Value_Integer *)y));
    mpz_ptr xmpz = sx ? tmpx : IDRIS2_INT_MPZ((Value_Integer *)x);
    mpz_ptr ympz = sy ? tmpy : IDRIS2_INT_MPZ((Value_Integer *)y);
    mpz_xor(IDRIS2_INT_MPZ(retVal), xmpz, ympz);
    if (sx)
      mpz_clear(tmpx);
    if (sy)
      mpz_clear(tmpy);
  }
  return (Value *)retVal;
#else
  Value_Integer *retVal = idris2_mkInteger();
  retVal->i = ((Value_Integer *)x)->i ^ ((Value_Integer *)y)->i;
  return (Value *)retVal;
#endif
}
