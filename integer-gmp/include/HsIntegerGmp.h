#ifndef _HS_INTEGER_GMP_H_
#define _HS_INTEGER_GMP_H_

/* Whether GMP is embedded into integer-gmp */
#define GHC_GMP_INTREE     0

/* The following values denote the GMP version used during GHC build-time */
#define GHC_GMP_VERSION_MJ 6
#define GHC_GMP_VERSION_MI 1
#define GHC_GMP_VERSION_PL 2
#define GHC_GMP_VERSION \
    (6 * 10000 + 1 * 100 + 2)

#endif /* _HS_INTEGER_GMP_H_ */
