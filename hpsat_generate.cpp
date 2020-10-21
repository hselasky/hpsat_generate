/*-
 * Copyright (c) 2020 Hans Petter Selasky. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <err.h>
#include <sysexits.h>
#include <stdlib.h>
#include <unistd.h>

#include <assert.h>

#define	MAXVAR 64

typedef struct var {
	int	z[MAXVAR];
} var_t;

static int varnum;
static int nexpr;
static int maxvar;
static int zerovar;
static int onevar;
static int runs;
static int function;
static int closed;
static unsigned long long cvalue;
static int pmsb = -1;
static int greater;
static int rounded;

#define	printf(...) do { if (runs) printf(__VA_ARGS__); } while (0)

static bool
sub_if_gte_64(uint64_t *pa, uint64_t *ps, uint64_t value)
{
	uint64_t x;
	uint64_t y;

	x = *pa ^ *ps ^ value;
	y = 2 * ((~*pa & *ps) | (~(*pa & ~*ps) & value));

	if (x >= y) {
		*pa = x;
		*ps = y;
		return (1);
	}
	return (0);
}

static uint32_t
sqrt_64(uint64_t z)
{
	uint64_t y = 0;
	uint64_t zc = 0;
	int8_t k;

	for (k = 62; k != -2; k -= 2) {
		if (sub_if_gte_64(&z, &zc, (y | 1) << k))
			y |= 2;
		y *= 2;
	}
	return (y / 4);
}

static void
print_triplet(int a, int b, int c)
{
	int array[3];
	int t;

	assert(a && b && c);

	array[0] = a;
	array[1] = b;
	array[2] = c;

	for (a = 0; a != 3; a++) {
		for (b = a + 1; b != 3; b++) {
			if (array[a] > array[b]) {
				t = array[b];
				array[b] = array[a];
				array[a] = t;
			}
		}
	}

	for (t = a = 0; a != 3; a++) {
		if (array[a] != t) {
			t = array[a];
			printf("%d ", t);
		}
	}
	printf("0\n");
	nexpr++;
}

static void
out_equal(int a, int value)
{
	assert(a);

	printf("%d 0\n", value ? a : -a);
	nexpr += 1;
}

static void
out_var_equal(int a, int b)
{
	assert(a && b);

	printf("%d %d 0\n", -a, b);
	printf("%d %d 0\n", a, -b);
	nexpr += 2;
}

static int
make_one_var(void)
{
	int x = varnum;

	varnum++;
	return (x);
}

/* a = b & c */
static void
out_and(int *pa, int b, int c)
{
	if ((b == zerovar || b == onevar) &&
	    (c == zerovar || c == onevar)) {
		int bb = (b == onevar);
		int cc = (c == onevar);

		*pa = ((bb & cc) ? onevar : zerovar);
		return;
	}

	*pa = make_one_var();

	if (b == c) {
		out_var_equal(*pa, b);
	} else if (b == -c) {
		out_equal(*pa, 0);
	} else {
		print_triplet(*pa, -b, -c);
		print_triplet(-*pa, b, c);
		print_triplet(-*pa, b, -c);
		print_triplet(-*pa, -b, c);
	}
}

/* a = b ^ c */
static void
out_xor(int *pa, int b, int c)
{
	if ((b == zerovar || b == onevar) &&
	    (c == zerovar || c == onevar)) {
		int bb = (b == onevar);
		int cc = (c == onevar);

		*pa = ((bb ^ cc) ? onevar : zerovar);
		return;
	}

	*pa = make_one_var();

	if (b == c) {
		out_equal(*pa, 0);
	} else if (b == -c) {
		out_equal(*pa, 1);
	} else {
		print_triplet(*pa, b, -c);
		print_triplet(*pa, -b, c);
		print_triplet(-*pa, b, c);
		print_triplet(-*pa, -b, -c);
	}
}

/* a = b | c */
static void
out_or(int *pa, int b, int c)
{
	if ((b == zerovar || b == onevar) &&
	    (c == zerovar || c == onevar)) {
		int bb = (b == onevar);
		int cc = (c == onevar);

		*pa = ((bb | cc) ? onevar : zerovar);
		return;
	}

	*pa = make_one_var();

	if (b == c) {
		out_var_equal(*pa, b);
	} else if (b == -c) {
		out_equal(*pa, 1);
	} else {
		print_triplet(*pa, b, -c);
		print_triplet(*pa, -b, c);
		print_triplet(*pa, -b, -c);
		print_triplet(-*pa, b, c);
	}
}

static var_t
make_var(void)
{
	var_t temp = {};
	int x;

	for (x = 0; x != maxvar; x++)
		temp.z[x] = make_one_var();
	return (temp);
}

static var_t
const_var(uint32_t var)
{
	var_t temp = {};
	int x;

	for (x = 0; x != maxvar; x++) {
		if (x >= 32)
			temp.z[x] = zerovar;
		else
			temp.z[x] = ((var >> x) & 1) ? onevar : zerovar;
	}
	return (temp);
}

static var_t
make_half_var(void)
{
	var_t temp = {};
	int x;

	for (x = 0; x != maxvar / 2; x++)
		temp.z[x] = make_one_var();
	return (temp);
}

static var_t
do_xor(const var_t &a, const var_t &b)
{
	var_t c;
	int x;

	for (x = 0; x != maxvar; x++)
		out_xor(&c.z[x], a.z[x], b.z[x]);

	return (c);
}

static var_t
do_add(const var_t &_a, const var_t &_b, size_t max)
{
	var_t a = _a;
	var_t b = _b;
	var_t r = {};
	int t[5] = {};
	int x;

	t[0] = zerovar;
	for (x = 0; x != max; x++) {
		out_xor(&t[1], a.z[x], b.z[x]);
		out_xor(&t[1], t[1], t[0]);
		out_and(&t[2], a.z[x], b.z[x]);
		out_and(&t[3], a.z[x], t[0]);
		out_and(&t[4], b.z[x], t[0]);
		out_or(&t[0], t[2], t[3]);
		out_or(&t[0], t[0], t[4]);

		r.z[x] = t[1];
	}
	return (r);
}

static void
do_greater(int *pc, const var_t &a, int32_t sa, const var_t &b, int32_t sb, bool equal)
{
	int y;
	int t;
	int n = onevar;

	*pc = zerovar;

	while (sa >= 0 || sb >= 0) {
		int va = (sa >= 0 && sa < maxvar) ? a.z[sa] : zerovar;
		int vb = (sb >= 0 && sb < maxvar) ? b.z[sb] : zerovar;

		if (va == 0)
			va = zerovar;
		if (vb == 0)
			vb = zerovar;

		out_xor(&y, va, vb);
		out_and(&t, y, va);	/* check if "a" is greater */
		out_and(&t, t, n);	/* check if update shall be applied */
		out_or(pc, *pc, t);	/* OR in update */
		out_and(&n, n, -y);	/* update logic */

		sa--;
		sb--;
	}

	if (equal)
		out_or(pc, *pc, n);	/* OR in update */
}

static int
do_sub_if_gte(var_t &a, var_t &b, const var_t &value)
{
	var_t x = {};
	var_t y = {};
	int t[3];
	int n;
	int g;

	for (int i = 0; i != maxvar; i++) {
		out_and(&t[0], -a.z[i], b.z[i]);
		out_and(&t[1], a.z[i], -b.z[i]);
		out_and(&t[2], -t[1], value.z[i]);
		out_or(&y.z[i], t[0], t[2]);

		out_or(&t[0], t[0], t[1]);
		out_xor(&x.z[i], t[0], value.z[i]);
	}

	/* compute "x" >= "y" */

	g = y.z[maxvar - 1];
	n = -y.z[maxvar - 1];

	for (int i = maxvar; i-- != 1;) {
		out_xor(&t[0], x.z[i], y.z[i - 1]);
		out_and(&t[1], t[0], y.z[i - 1]);	/* check if "y" is
							 * greater */
		out_and(&t[1], t[1], n);	/* check if update shall be
						 * applied */
		out_or(&g, g, t[1]);	/* OR in update */
		out_and(&n, n, -t[0]);	/* update logic */
	}

	for (int i = 0; i != maxvar; i++) {
		out_and(&t[0], x.z[i], -g);
		out_and(&t[1], a.z[i], g);
		out_or(&a.z[i], t[0], t[1]);

		if (i == 0)
			t[0] = zerovar;
		else
			out_and(&t[0], y.z[i - 1], -g);
		out_and(&t[1], b.z[i], g);
		out_or(&b.z[i], t[0], t[1]);
	}
	return (-g);
}

static void
do_zero_mod_linear(var_t &rem, const var_t &hdiv)
{
	var_t sub = const_var(0);
	var_t tmp;
	int max = (pmsb > -1) ? (pmsb + 1) : (maxvar / 2);

	for (int x = maxvar - max + 1; x--;) {
		for (int y = 0; y != x; y++)
			tmp.z[y] = zerovar;
		for (int y = x; y != (x + max); y++)
			tmp.z[y] = hdiv.z[y - x];
		for (int y = (x + max); y != maxvar; y++)
			tmp.z[y] = zerovar;

		do_sub_if_gte(rem, sub, tmp);
	}
	/* result must be zero */
	for (int x = 0; x != maxvar; x++)
		out_var_equal(rem.z[x], sub.z[x]);
}

static var_t
do_mul_2adic(const var_t &a, const var_t &b)
{
	var_t c;
	int x;
	int y;
	int z[maxvar][maxvar];
	int t;

	memset(&c, 0, sizeof(c));

	for (x = 0; x != maxvar; x++) {
		for (y = 0; y != maxvar; y++) {
			out_and(&z[x][y], a.z[x], b.z[y]);
		}
	}

	for (x = 0; x != maxvar; x++) {
		for (y = 0; y != maxvar; y++) {
			t = (x + y) % maxvar;
			if (c.z[t] == 0) {
				c.z[t] = z[x][y];
			} else {
				out_xor(&c.z[t], c.z[t], z[x][y]);
			}
		}
	}
	return (c);
}

static var_t
do_mul_linear(const var_t &a, const var_t &b)
{
	var_t c;
	var_t d;
	int x;
	int y;
	int z[maxvar / 2][maxvar / 2];

	for (x = 0; x != maxvar / 2; x++) {
		for (y = 0; y != maxvar / 2; y++) {
			out_and(&z[x][y], a.z[x], b.z[y]);
		}
	}

	for (x = 0; x != maxvar; x++)
		c.z[x] = zerovar;

	for (x = 0; x != maxvar / 2; x++) {
		for (y = 0; y != maxvar; y++)
			d.z[y] = zerovar;
		for (y = 0; y != maxvar / 2; y++)
			d.z[x + y] = z[x][y];
		if (x == 0)
			c = d;
		else
			c = do_add(c, d, maxvar);
	}
	return (c);
}

static void
generate_adder_cnf(void)
{
top:	;
	int old_varnum = varnum;
	int old_nexpr = nexpr;
	int z;

	varnum = 1;
	nexpr = 0;

	if (closed) {
		printf("c The following CNF computes all\n"
		    "c sums of 0x%08llx\n", cvalue);
	} else {
		printf("c The following CNF computes and open adder\n"
		    "c having %d bits for each variable\n", maxvar);
	}

	var_t a = make_var();
	var_t b = make_var();
	var_t f = make_var();
	var_t e;

	zerovar = make_one_var();
	onevar = -zerovar;

	for (z = 0; z != maxvar; z++)
		printf("c Solution in %d + %d = %d\n", a.z[z], b.z[z], f.z[z]);

	printf("p cnf %d %d %d\n", old_varnum - 1, old_nexpr, varnum - 1);

	out_equal(zerovar, 0);

	e = do_add(a, b, maxvar);

	for (z = 0; z != maxvar; z++)
		out_var_equal(e.z[z], f.z[z]);

	if (closed) {
		for (z = 0; z != maxvar; z++)
			out_equal(f.z[z], (cvalue >> z) & 1);
	}

	if (greater) {
		int gt;

		do_greater(&gt, a, maxvar, e, maxvar, false);
		out_equal(gt, 0);
		do_greater(&gt, b, maxvar, e, maxvar, false);
		out_equal(gt, 0);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_2adic_cnf(void)
{
top:	;
	int old_varnum = varnum;
	int old_nexpr = nexpr;
	int z;

	varnum = 1;
	nexpr = 0;

	if (closed) {
		printf("c The following CNF computes and closed 2-adic multiplier\n"
		    "c having %d bits for each variable and result(0x%08llx)\n", maxvar, cvalue);
	} else {
		printf("c The following CNF computes and open 2-adic multiplier\n"
		    "c having %d bits for each variable\n", maxvar);
	}

	var_t a = make_var();
	var_t b = make_var();
	var_t f = make_var();
	var_t e;

	zerovar = make_one_var();
	onevar = -zerovar;

	for (z = 0; z != maxvar; z++)
		printf("c Solution in %d = %d x %d\n", f.z[z], a.z[z], b.z[z]);

	printf("p cnf %d %d %d\n", old_varnum - 1, old_nexpr, varnum - 1);

	out_equal(zerovar, 0);

	if (greater) {
		do_greater(&z, a, maxvar, b, maxvar, false);
		out_equal(z, 0);
	}

	e = do_mul_2adic(a, b);

	for (z = 0; z != maxvar; z++)
		out_var_equal(e.z[z], f.z[z]);

	if (closed) {
		for (z = 0; z != maxvar; z++)
			out_equal(f.z[z], (cvalue >> z) & 1);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_cnf(void)
{
top:	;
	int old_varnum = varnum;
	int old_nexpr = nexpr;
	int z;

	varnum = 1;
	nexpr = 0;

	if (closed) {
		printf("c The following CNF computes and closed multiplier\n"
		    "c having %d bits for each variable and \n"
		    "c %d bits for the result (0x%08llx)\n", maxvar / 2, maxvar, cvalue);
	} else {
		printf("c The following CNF computes and open multiplier\n"
		    "c having %d bits for each variable and \n"
		    "c %d bits for the result\n", maxvar / 2, maxvar);
	}

	var_t a = make_half_var();
	var_t b = make_half_var();
	var_t f = make_var();
	var_t e;

	zerovar = make_one_var();
	onevar = -zerovar;

	for (z = 0; z != maxvar / 2; z++)
		printf("c Solution in %d + %d = %d, %d\n", a.z[z], b.z[z], f.z[z], f.z[z + maxvar / 2]);

	printf("p cnf %d %d %d\n", old_varnum - 1, old_nexpr, varnum - 1);

	out_equal(zerovar, 0);

	if (greater) {
		do_greater(&z, a, maxvar / 2, b, maxvar / 2, false);
		out_equal(z, 0);
	}

	e = do_mul_linear(a, b);

	for (z = 0; z != maxvar; z++)
		out_var_equal(e.z[z], f.z[z]);

	if (closed) {
		for (z = 0; z != maxvar; z++)
			out_equal(f.z[z], (cvalue >> z) & 1);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_limit_cnf(void)
{
top:	;
	int old_varnum = varnum;
	int old_nexpr = nexpr;
	int z;
	unsigned long long cvalue_sqrt = sqrt_64(cvalue);

	varnum = 1;
	nexpr = 0;

	printf(
	    "c The following CNF computes and closed multiplier\n"
	    "c having %d bits for each variable and \n"
	    "c %d bits for the result (0x%08llx)\n", maxvar / 2, maxvar, cvalue);

	var_t a = make_half_var();
	var_t b = make_half_var();
	var_t f = make_var();
	var_t e;
	var_t g = {};
	var_t h = {};

	zerovar = make_one_var();
	onevar = -zerovar;

	for (z = 0; z != maxvar / 2; z++) {
		printf("c Solution in %d + %d = %d, %d\n", a.z[z], b.z[z], f.z[z], f.z[z + maxvar / 2]);

		g.z[z] = ((cvalue_sqrt >> z) & 1) ? onevar : zerovar;
		h.z[z] = (z == 0) ? onevar : zerovar;
	}

	printf("p cnf %d %d %d\n", old_varnum - 1, old_nexpr, varnum - 1);

	out_equal(zerovar, 0);

	do_greater(&z, a, maxvar / 2, g, maxvar / 2, false);
	out_equal(z, 0);

	do_greater(&z, b, maxvar / 2, g, maxvar / 2, true);
	out_equal(z, 1);

	do_greater(&z, a, maxvar / 2, h, maxvar / 2, false);
	out_equal(z, 1);

	e = do_mul_linear(a, b);

	for (z = 0; z != maxvar; z++)
		out_var_equal(e.z[z], f.z[z]);

	for (z = 0; z != maxvar; z++)
		out_equal(f.z[z], (cvalue >> z) & 1);

	if (runs++ == 0)
		goto top;
}

static void
generate_sqr_linear_cnf(void)
{
top:	;
	int old_varnum = varnum;
	int old_nexpr = nexpr;
	int z;

	varnum = 1;
	nexpr = 0;

	if (closed) {
		printf("c The following CNF computes and closed multiplier\n"
		    "c having %d bits for each variable and \n"
		    "c %d bits for the result (0x%08llx)\n", maxvar / 2, maxvar, cvalue);
	} else {
		printf("c The following CNF computes and open multiplier\n"
		    "c having %d bits for each variable and \n"
		    "c %d bits for the result\n", maxvar / 2, maxvar);
	}

	var_t a = make_half_var();
	var_t f = make_var();
	var_t e;

	zerovar = make_one_var();
	onevar = -zerovar;

	for (z = 0; z != maxvar / 2; z++)
		printf("c Solution in %d = %d, %d\n", a.z[z], f.z[z], f.z[z + maxvar / 2]);

	printf("p cnf %d %d %d\n", old_varnum - 1, old_nexpr, varnum - 1);

	out_equal(zerovar, 0);

	e = do_mul_linear(a, a);

	if (rounded) {
		var_t b = make_var();

		e = do_add(e, b, maxvar);
		do_greater(&z, b, 1 + maxvar, a, maxvar, false);
		out_equal(z, 0);
	}

	for (z = 0; z != maxvar; z++)
		out_var_equal(e.z[z], f.z[z]);

	if (closed) {
		for (z = 0; z != maxvar; z++)
			out_equal(f.z[z], (cvalue >> z) & 1);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mod_linear_cnf(void)
{
top:	;
	int old_varnum = varnum;
	int old_nexpr = nexpr;
	int z;

	varnum = 1;
	nexpr = 0;

	if (closed) {
		printf("c The following CNF computes and closed linear modulus\n"
		    "c having %d bits for each variable and \n"
		    "c %d bits for the result (0x%08llx)\n", maxvar / 2, maxvar, cvalue);
	} else {
		printf("c The following CNF computes and open linear modulus\n"
		    "c having %d bits for each variable and \n"
		    "c %d bits for the result\n", maxvar / 2, maxvar);
	}

	var_t a = make_half_var();
	var_t f = make_var();

	zerovar = make_one_var();
	onevar = -zerovar;

	for (z = 0; z != maxvar / 2; z++)
		printf("c Solution in %d = %d, %d\n", a.z[z], f.z[z], f.z[z + maxvar / 2]);

	printf("p cnf %d %d %d\n", old_varnum - 1, old_nexpr, varnum - 1);

	out_equal(zerovar, 0);

	if (closed) {
		if (cvalue & 1)
			out_equal(a.z[0], 1);
		if (pmsb > -1 && pmsb < (maxvar / 2)) {
			out_equal(a.z[pmsb], 1);
			for (z = pmsb + 1; z != (maxvar / 2); z++)
				out_equal(a.z[z], 0);
		}
		for (z = 0; z != maxvar; z++)
			out_equal(f.z[z], (cvalue >> z) & 1);
	}

	do_zero_mod_linear(f, a);

	if (runs++ == 0)
		goto top;
}

static void
usage(void)
{
	fprintf(stderr, "Usage: hpsat_generate [-h] -f <n> -b <bits 0..%d> [-g] [-r] [-v <value> ] [ -P <value> ]\n", MAXVAR);
	fprintf(stderr, "	-g     # b >= a\n");
	fprintf(stderr, "	-r     # rounded\n");
	fprintf(stderr, "	-P <n> # predict this bit is true\n");
	fprintf(stderr, "	-f 1   # Generate linear adder\n");
	fprintf(stderr, "	-f 2   # Generate 2-adic multiplier\n");
	fprintf(stderr, "	-f 3   # Generate linear multiplier\n");
	fprintf(stderr, "	-f 4   # Generate linear square\n");
	fprintf(stderr, "	-f 5   # Generate linear zero mod\n");
	fprintf(stderr, "	-f 6 -v <X> # Generate linear multiplier with variable limit\n");
	exit(EX_USAGE);
}

int
main(int argc, char **argv)
{
	const char *const optstring = "ghf:cb:rv:P:";
	int ch;

	while ((ch = getopt(argc, argv, optstring)) != -1) {
		switch (ch) {
		case 'f':
			function = atoi(optarg);
			break;
		case 'b':
			maxvar = atoi(optarg);
			if (maxvar > MAXVAR)
				maxvar = MAXVAR;
			else if (maxvar < 1)
				maxvar = 1;
			break;
		case 'v':
			cvalue = strtoull(optarg, NULL, 0);
			closed = 1;
			break;
		case 'g':
			greater = 1;
			break;
		case 'r':
			rounded = 1;
			break;
		case 'P':
			pmsb = atoi(optarg);
			if (pmsb > MAXVAR)
				pmsb = MAXVAR;
			else if (pmsb < 0)
				pmsb = 0;
			break;
		default:
			usage();
			break;
		}
	}

	if (maxvar == 0 || function == 0)
		usage();

	switch (function) {
	case 1:
		generate_adder_cnf();
		break;
	case 2:
		generate_mul_2adic_cnf();
		break;
	case 3:
		generate_mul_linear_cnf();
		break;
	case 4:
		generate_sqr_linear_cnf();
		break;
	case 5:
		generate_mod_linear_cnf();
		break;
	case 6:
		if (!closed)
			usage();
		generate_mul_linear_limit_cnf();
		break;
	default:
		usage();
		break;
	}
	return (0);
}
