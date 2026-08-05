/* Enumerate canonical candidate antichains for the n=6,7 computation.
 *
 * Compile with -DNV=6 or -DNV=7.  A printed family F satisfies
 *   4 <= |F| <= NV; every type has size 2,...,NV-1;
 *   F is an antichain, covers every voter, has empty intersection,
 *   and every voter has degree at least 2;
 *   for some 2 <= k <= |F|-2, the largest allowed utility vector is
 *   not dominated by an integral k-committee.
 *
 * Each S_NV orbit is printed once, as its lexicographically least member.
 * Optional arguments OUT WORKER JOBS split the root branches between jobs.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifndef NV
#define NV 7
#endif

#define ALLV ((1 << NV) - 1)
#define MAXF NV
#define MAXM (1 << NV)

static int masks[MAXM], nm;
static uint64_t comparable[MAXM][2], packed[MAXM];
static uint8_t *perm_image;
static int nperm;

static int chosen[MAXF], degree[NV], chosen_n;
static long long visited, filtered, interesting, emitted;
static int worker, jobs = 1;
static FILE *out;

static int popcount(int x) { return __builtin_popcount((unsigned)x); }

static void make_permutations(void)
{
    int p[NV], count = 1, row = 0;
    for (int i = 0; i < NV; i++) p[i] = i;
    for (int i = 2; i <= NV; i++) count *= i;
    nperm = count;
    perm_image = malloc((size_t)nperm * MAXM);
    if (!perm_image) { perror("malloc"); exit(1); }

    for (;;) {
        uint8_t *image = perm_image + (size_t)row * MAXM;
        for (int m = 0; m < MAXM; m++) {
            int result = 0;
            for (int i = 0; i < NV; i++)
                if ((m >> i) & 1) result |= 1 << p[i];
            image[m] = (uint8_t)result;
        }
        row++;

        int i = NV - 2;
        while (i >= 0 && p[i] >= p[i + 1]) i--;
        if (i < 0) break;
        int j = NV - 1;
        while (p[j] <= p[i]) j--;
        int t = p[i]; p[i] = p[j]; p[j] = t;
        for (int a = i + 1, b = NV - 1; a < b; a++, b--) {
            t = p[a]; p[a] = p[b]; p[b] = t;
        }
    }
    if (row != nperm) { fprintf(stderr, "permutation error\n"); exit(1); }
}

static int is_canonical(void)
{
    uint64_t own = 0;
    for (int j = 0; j < chosen_n; j++)
        own = (own << 8) | (uint8_t)chosen[j];

    for (int pi = 1; pi < nperm; pi++) {
        uint8_t *image = perm_image + (size_t)pi * MAXM;
        uint8_t values[MAXF];
        for (int j = 0; j < chosen_n; j++) values[j] = image[chosen[j]];
        for (int j = 1; j < chosen_n; j++) {
            uint8_t value = values[j];
            int q = j - 1;
            while (q >= 0 && values[q] > value) {
                values[q + 1] = values[q]; q--;
            }
            values[q + 1] = value;
        }
        uint64_t key = 0;
        for (int j = 0; j < chosen_n; j++)
            key = (key << 8) | values[j];
        if (key < own) return 0;
    }
    return 1;
}

/* Cheap integral prefilter.  Utilities are packed into independent 8-bit
 * lanes, so adding the incidence words adds all voter utilities at once.
 * Setting each lane's high bit lets the subtraction test all coordinatewise
 * inequalities without borrowing between lanes. */
static int has_interesting_k(void)
{
    const uint64_t HIGH_BITS = 0x8080808080808080ULL;
    uint64_t incidence[MAXF];
    for (int j = 0; j < chosen_n; j++) incidence[j] = packed[chosen[j]];

    for (int k = 2; k <= chosen_n - 2; k++) {
        uint64_t upper = 0;
        for (int i = 0; i < NV; i++) {
            int d = degree[i] < k ? degree[i] : k;
            upper |= (uint64_t)(d - 1) << (8 * i);
        }
        int dominated = 0;
        for (int subset = 0; subset < (1 << chosen_n) && !dominated; subset++) {
            if (popcount(subset) != k) continue;
            uint64_t utility = 0;
            for (int bits = subset; bits; bits &= bits - 1)
                utility += incidence[__builtin_ctz((unsigned)bits)];
            dominated = ((((utility | HIGH_BITS) - upper) & HIGH_BITS) == HIGH_BITS);
        }
        if (!dominated) return 1;
    }
    return 0;
}

static void examine(void)
{
    visited++;
    int union_mask = 0, intersection = ALLV;
    for (int j = 0; j < chosen_n; j++) {
        union_mask |= chosen[j];
        intersection &= chosen[j];
    }
    if (union_mask != ALLV || intersection != 0) return;
    for (int i = 0; i < NV; i++) if (degree[i] < 2) return;
    filtered++;
    if (!has_interesting_k()) return;
    interesting++;
    if (!is_canonical()) return;

    emitted++;
    for (int j = 0; j < chosen_n; j++)
        fprintf(out, "%d%c", chosen[j], j + 1 == chosen_n ? '\n' : ' ');
}

/* available0/1 are the at most 128 still-eligible types.  On choosing type j
 * we delete every comparable type, which makes every leaf an antichain.  The
 * loop consumes candidates in increasing order, so every labelled antichain
 * is reached along exactly one branch. */
static void dfs(uint64_t available0, uint64_t available1)
{
    if (chosen_n >= 4) examine();
    if (chosen_n == MAXF) return;
    int remaining = MAXF - chosen_n;
    for (int i = 0; i < NV; i++)
        if (2 - degree[i] > remaining) return;

    uint64_t a0 = available0, a1 = available1;
    int root_index = 0;
    while (a0 || a1) {
        int j;
        if (a0) { j = __builtin_ctzll(a0); a0 &= a0 - 1; }
        else { j = 64 + __builtin_ctzll(a1); a1 &= a1 - 1; }
        if (chosen_n == 0 && root_index++ % jobs != worker) continue;

        int type = masks[j];
        chosen[chosen_n++] = type;
        for (int i = 0; i < NV; i++) degree[i] += (type >> i) & 1;
        dfs(a0 & ~comparable[j][0], a1 & ~comparable[j][1]);
        for (int i = 0; i < NV; i++) degree[i] -= (type >> i) & 1;
        chosen_n--;
    }
}

int main(int argc, char **argv)
{
    const char *filename = argc > 1 ? argv[1] : "candidates.txt";
    if (argc > 3) { worker = atoi(argv[2]); jobs = atoi(argv[3]); }
    if (worker < 0 || jobs < 1 || worker >= jobs) {
        fprintf(stderr, "invalid worker split\n"); return 2;
    }

    for (int m = 1; m < MAXM; m++) {
        int size = popcount(m);
        if (2 <= size && size <= NV - 1) masks[nm++] = m;
    }
    for (int i = 0; i < nm; i++) {
        for (int j = 0; j < nm; j++) {
            int a = masks[i], b = masks[j];
            if (i != j && ((a | b) == a || (a | b) == b))
                comparable[i][j >> 6] |= 1ULL << (j & 63);
        }
    }
    for (int m = 0; m < MAXM; m++)
        for (int i = 0; i < NV; i++)
            if ((m >> i) & 1) packed[m] += 1ULL << (8 * i);
    make_permutations();

    out = fopen(filename, "w");
    if (!out) { perror("fopen"); return 1; }
    uint64_t a0 = nm >= 64 ? ~0ULL : (1ULL << nm) - 1;
    uint64_t a1 = nm <= 64 ? 0 : (1ULL << (nm - 64)) - 1;
    dfs(a0, a1);
    fclose(out);

    printf("n=%d worker=%d/%d visited=%lld filtered=%lld interesting=%lld emitted=%lld\n",
           NV, worker, jobs, visited, filtered, interesting, emitted);
    free(perm_image);
    return 0;
}
