/*-
 * Copyright (c) 2020-2021 Hans Petter Selasky. All rights reserved.
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

static int varnum;
static int nexpr;
static int old_varnum;
static int old_nexpr;
static size_t maxvar;
static int zerovar;
static int runs;
static int function;
static unsigned long long cmask;
static unsigned long long cvalue;
static int greater;
static int rounded;
static int maxsat;

#define	printf(...) do { \
    if (runs) \
	printf(__VA_ARGS__); \
} while (0)

static int
new_variable(void)
{
	return (varnum++);
}

class variable_t {
public:
	int v;
	variable_t(void) {
		v = zerovar;
		assert(v != 0);
	};
	variable_t(int other) {
		v = other;
		assert(v != 0);
	};
	variable_t operator =(int other) {
		v = other;
		assert(v != 0);
		return (*this);
	};
	variable_t operator =(const variable_t &other) {
		if (&other != this) {
			v = other.v;
			assert(v != 0);
		}
		return (*this);
	};
	void equal_to(bool) const;
	void equal_to(const variable_t &other) const;

	variable_t operator ~(void) const {
		variable_t ret = -v;
		assert(v != 0);
		return (ret);
	};
	variable_t operator &(const variable_t &) const;
	variable_t &operator &=(const variable_t &);
	variable_t operator ^(const variable_t &) const;
	variable_t &operator ^=(const variable_t &);
	variable_t operator |(const variable_t &) const;
	variable_t &operator |=(const variable_t &);
};

static void
do_cnf_reset(void)
{
	old_varnum = varnum;
	old_nexpr = nexpr;
	varnum = 1;
	nexpr = 0;
	zerovar = new_variable();
}

static void
do_cnf_header(void)
{
	if (maxsat)
		printf("c Solution is given by maximum variables set to one\n");

	printf("p cnf %d %d %d\n", old_varnum - 1, old_nexpr, varnum - 1);

	(variable_t(zerovar)).equal_to(false);
}

class var_t {
public:
	variable_t *z;

	var_t(void) {
		z = new variable_t [maxvar];
	};

	var_t(const var_t &other) {
		z = new variable_t [maxvar];

		for (size_t x = 0; x != maxvar; x++)
			z[x] = other.z[x];
	};

	~var_t(void) {
		delete [] z;
	};

	var_t operator =(const var_t &other) {
		if (&other != this) {
			for (size_t x = 0; x != maxvar; x++)
				z[x] = other.z[x];
		}
		return (*this);
	};

	void alloc(size_t max = maxvar) {
		for (size_t x = 0; x != max; x++)
			z[x].v = new_variable();
	};

	void from_const(uint64_t var) {
		for (size_t x = 0; x != maxvar; x++) {
			if (x >= 64)
				z[x] = zerovar;
			else
				z[x] = ((var >> x) & 1) ? -zerovar : zerovar;
		}
	};

	void equal_to(bool other) const {
		for (size_t x = 0; x != maxvar; x++)
			z[x].equal_to(other);
	};

	void equal_to(const var_t &other) const {
		for (size_t x = 0; x != maxvar; x++)
			z[x].equal_to(other.z[x]);
	};

	var_t operator ~(void) const {
		var_t r = *this;
		for (size_t x = 0; x != maxvar; x++)
			r.z[x] = ~r.z[x];
		return (r);
	};

	var_t operator ^(const var_t &other) const {
		var_t c;
		for (size_t x = 0; x != maxvar; x++)
			c.z[x] = z[x] ^ other.z[x];
		return (c);
	};

	var_t operator ^(const variable_t &other) const {
		var_t c;
		for (size_t x = 0; x != maxvar; x++)
			c.z[x] = z[x] ^ other;
		return (c);
	};

	var_t operator &(const var_t &other) const {
		var_t c;
		for (size_t x = 0; x != maxvar; x++)
			c.z[x] = z[x] & other.z[x];
		return (c);
	};

	var_t operator &(const variable_t &other) const {
		var_t c;
		for (size_t x = 0; x != maxvar; x++)
			c.z[x] = z[x] & other;
		return (c);
	};

	var_t operator |(const var_t &other) const {
		var_t c;
		for (size_t x = 0; x != maxvar; x++)
			c.z[x] = z[x] | other.z[x];
		return (c);
	};

	var_t operator |(const variable_t &other) const {
		var_t c;
		for (size_t x = 0; x != maxvar; x++)
			c.z[x] = z[x] | other;
		return (c);
	};

	var_t operator <<(size_t shift) const {
		var_t c;
		if (shift < maxvar) {
			for (size_t x = 0; x != maxvar - shift; x++)
				c.z[x + shift] = z[x];
		}
		return (c);
	};

	var_t operator +(const var_t &other) const {
		variable_t carry = zerovar;
		var_t r;

		for (size_t x = 0; x != maxvar; x++) {
			r.z[x] = z[x] ^ other.z[x] ^ carry;
			carry = (z[x] & carry) ^ (other.z[x] & carry) ^ (z[x] & other.z[x]);
		}
		return (r);
	};

	var_t &operator +=(const var_t &other) {
		*this = *this + other;
		return (*this);
	};

	variable_t operator >(const var_t &other) {
		variable_t y;
		variable_t t;
		variable_t n = -zerovar;
		variable_t r = zerovar;
		size_t s = maxvar;

		while (s--) {
			const variable_t &va = z[s];
			const variable_t &vb = other.z[s];

			y = va ^ vb;
			t = y & va & n;
			r = r | t;
			n = n & ~y;
		}
		return (r);
	};

	variable_t operator >=(const var_t &other) {
		variable_t y;
		variable_t t;
		variable_t n = -zerovar;
		variable_t r = zerovar;
		size_t s = maxvar;

		while (s--) {
			const variable_t &va = z[s];
			const variable_t &vb = other.z[s];

			y = va ^ vb;
			t = y & va & n;
			r = r | t;
			n = n & ~y;
		}
		r = r | n;
		return (r);
	};

	variable_t operator <(const var_t &other) {
		variable_t y;
		variable_t t;
		variable_t n = -zerovar;
		variable_t r = zerovar;
		size_t s = maxvar;

		while (s--) {
			const variable_t &va = z[s];
			const variable_t &vb = other.z[s];

			y = va ^ vb;
			t = y & va & n;
			r = r | t;
			n = n & ~y;
		}
		r = r | n;
		return (~r);
	};
};

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
out_triplet(int a, int b, int c)
{
	int array[3];
	int t;

	assert(a != 0);
	assert(b != 0);
	assert(c != 0);

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
out_dual(int a, int b)
{
	int array[2];
	int t;

	assert(a != 0);
	assert(b != 0);

	array[0] = a;
	array[1] = b;

	for (a = 0; a != 2; a++) {
		for (b = a + 1; b != 2; b++) {
			if (array[a] > array[b]) {
				t = array[b];
				array[b] = array[a];
				array[a] = t;
			}
		}
	}

	for (t = a = 0; a != 2; a++) {
		if (array[a] != t) {
			t = array[a];
			printf("%d ", t);
		}
	}
	printf("0\n");
	nexpr++;
}

void
variable_t :: equal_to(bool value) const
{
	assert(v != 0);

	printf("%d 0\n", value ? v : -v);
	nexpr++;
}

void
variable_t :: equal_to(const variable_t &other) const
{
	assert(v != 0 && other.v != 0);

	printf("%d %d 0\n", -v, other.v);
	printf("%d %d 0\n", v, -other.v);
	nexpr += 2;
}

variable_t
variable_t :: operator &(const variable_t &other) const
{
	if (v == other.v) {
		/* same variable */
		return (v);
	} else if (v == -other.v) {
		/* inverted same variable */
		return (zerovar);
	} else if (maxsat) {
		/*
		 * Truth table for (a ^ v&o)
		 * a v   (a & !v)
		 * 0 0      0
		 * 0 1      0
		 * 1 0      1
		 * 1 1      0
		 *
		 * a o   (a & !o)
		 * 0 0      0
		 * 0 1      0
		 * 1 0      1
		 * 1 1      0
		 */
		const int a = new_variable();

		out_dual(-a, v);
		out_dual(-a, other.v);

		return (a);
	} else {
		/*
		 * Truth table:
		 *
		 * a v o  (a ^ v&o)
		 * 0 0 0     0
		 * 0 0 1     0
		 * 0 1 0     0
		 * 0 1 1     1
		 * 1 0 0     1
		 * 1 0 1     1
		 * 1 1 0     1
		 * 1 1 1     0
		 */
		const int a = new_variable();

		out_triplet(a, -v, -other.v);
		out_triplet(-a, v, other.v);
		out_triplet(-a, v, -other.v);
		out_triplet(-a, -v, other.v);

		return (a);
	}
}

variable_t &
variable_t :: operator &=(const variable_t &other)
{
	*this = *this & other;
	return (*this);
}

variable_t
variable_t :: operator ^(const variable_t &other) const
{
	if (v == other.v) {
		/* same variable */
		return (zerovar);
	} else if (v == -other.v) {
		/* inverted same variable */
		return (-zerovar);
	} else {
		const int a = new_variable();

		out_triplet(a, v, -other.v);
		out_triplet(a, -v, other.v);
		out_triplet(-a, v, other.v);
		out_triplet(-a, -v, -other.v);

		return (a);
	}
}

variable_t &
variable_t :: operator ^=(const variable_t &other)
{
	*this = *this ^ other;
	return (*this);

}

variable_t
variable_t :: operator |(const variable_t &other) const
{
	if (v == other.v) {
		/* same variable */
		return (v);
	} else if (v == -other.v) {
		/* inverted same variable */
		return (-zerovar);
	} else if (maxsat) {
		return (*this ^ other ^ (*this & other));
	} else {
		const int a = new_variable();

		out_triplet(a, v, -other.v);
		out_triplet(a, -v, other.v);
		out_triplet(a, -v, -other.v);
		out_triplet(-a, v, other.v);

		return (a);
	}
}

variable_t &
variable_t :: operator |=(const variable_t &other)
{
	*this = *this | other;
	return (*this);
}

static var_t
do_add_full_v2(const var_t &a, const var_t &b, const var_t &z)
{
	variable_t carry = zerovar;
	var_t r;

	for (size_t x = 0; x != maxvar; x++) {
		carry = carry ^ z.z[x];

		if (x != 0)
			carry = carry ^ z.z[x - 1];

		r.z[x] = a.z[x] ^ b.z[x] ^ carry;
		carry = (a.z[x] & b.z[x]) ^ (a.z[x] & carry) ^ (b.z[x] & carry);
	}
	return (r);
}

static void
do_add_half_v1(const var_t &a, var_t &r, var_t &c, const var_t &z)
{
	variable_t t[2];

	for (size_t x = 0; x != maxvar; x++) {
		t[0] = a.z[x] ^ r.z[x] ^ c.z[x];
		t[1] = (a.z[x] & r.z[x]) ^ (a.z[x] & c.z[x]) ^ (r.z[x] & c.z[x]);

		r.z[x] = t[0];
		c.z[x] = t[1];
	}

	/* shift up carry and XOR in zero */
	for (size_t x = maxvar; x--; ) {
		variable_t y;

		if (x == 0)
			y = zerovar;
		else
			y = c.z[x - 1];

		y = y ^ z.z[x];
		if (x != 0)
			y = y ^ z.z[x - 1];

		c.z[x] = y;
	}
}

static variable_t
do_sub_if_gte(var_t &a, var_t &b, const var_t &value)
{
	var_t x;
	var_t y;

	x = a ^ b ^ value;
	y = ((~a & b) | (~(a & ~b) & value)) << 1;

	variable_t gte = (x >= y);

	a = (x & gte) | (a & ~gte);
	b = (y & gte) | (b & ~gte);

	return (gte);
}

static void
do_zero_mod_linear(var_t &rem, const var_t &hdiv)
{
	var_t sub;
	var_t tmp;
	size_t max = (maxvar / 2);

	for (size_t x = maxvar - max + 1; x--;) {
		for (size_t y = 0; y != x; y++)
			tmp.z[y] = zerovar;
		for (size_t y = x; y != (x + max); y++)
			tmp.z[y] = hdiv.z[y - x];
		for (size_t y = (x + max); y != maxvar; y++)
			tmp.z[y] = zerovar;

		do_sub_if_gte(rem, sub, tmp);
	}

	/* result must be zero */
	rem.equal_to(sub);
}

static var_t
do_mul_2adic(const var_t &a, const var_t &b)
{
	variable_t z[maxvar / 2][maxvar / 2];
	var_t c;

	for (size_t x = 0; x != maxvar / 2; x++) {
		for (size_t y = 0; y != maxvar / 2; y++) {
			z[x][y] = a.z[x] & b.z[y];
		}
	}

	for (size_t x = 0; x != maxvar / 2; x++) {
		for (size_t y = 0; y != maxvar / 2; y++) {
			const size_t t = x + y;

			c.z[t] = c.z[t] ^ z[x][y];
		}
	}
	return (c);
}

static var_t
do_mul_linear_v1(const var_t &a, const var_t &b)
{
	variable_t z[maxvar / 2][maxvar / 2];
	var_t c;
	var_t d;

	for (size_t x = 0; x != maxvar / 2; x++) {
		for (size_t y = 0; y != maxvar / 2; y++) {
			z[x][y] = a.z[x] & b.z[y];
		}
	}

	for (size_t x = 0; x != maxvar / 2; x++) {
		for (size_t y = 0; y != maxvar; y++)
			d.z[y] = zerovar;
		for (size_t y = 0; y != maxvar / 2; y++)
			d.z[x + y] = z[x][y];
		if (x == 0)
			c = d;
		else
			c = c + d;
	}
	return (c);
}

static var_t
do_mul_linear_v2(const var_t &a, const var_t &b, const var_t &zero)
{
	variable_t t[maxvar / 2][maxvar / 2];
	var_t c;
	var_t d;
	var_t r;

	for (size_t x = 0; x != maxvar / 2; x++) {
		for (size_t y = 0; y != maxvar / 2; y++) {
			t[x][y] = a.z[x] & b.z[y];
		}
	}

	/* set carry to zero */
	c = zero;

	/* set remainder to zero */
	r = zero;

	/* do multiply */
	for (size_t x = 0; x != maxvar / 2; x++) {
		/* set "d" to zero */
		d = zero;

		/* XOR in multiplier */
		for (size_t y = 0; y != maxvar / 2; y++)
			d.z[x + y] = d.z[x + y] ^ t[x][y];

		/* do half adder */
		do_add_half_v1(d, r, c, zero);
	}

	c.equal_to(zero);
	r.equal_to(false);

	/* add up everything */
	c = do_add_full_v2(r, c, zero);

	/* final XOR */
	c = c ^ zero;

	return (c);
}

static void
generate_adder_cnf(void)
{
top:
	printf("c The following CNF computes the addition of two %zd bit\n"
	       "c variables into a %zd bit sum: ((a + b) & 0x%08llx) = 0x%08llx\n",
	       maxvar, maxvar, cmask, cvalue);

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc();
	b.alloc();
	f.alloc();

	for (size_t z = 0; z != maxvar; z++)
		printf("c Solution in %d + %d = %d\n", a.z[z].v, b.z[z].v, f.z[z].v);

	do_cnf_header();

	e = a + b;

	e.equal_to(f);

	for (size_t z = 0; z != maxvar; z++) {
		if ((cmask >> z) & 1)
			f.z[z].equal_to((cvalue >> z) & 1);
	}

	if (greater) {
		(a > e).equal_to(false);
		(b > e).equal_to(false);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_2adic_cnf(void)
{
top:
	printf("c The following CNF computes a 2-adic multiplier\n"
	       "c having %zd bits for each variable and (result & 0x%08llx) = 0x%08llx\n",
	       maxvar, cmask, cvalue);

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	for (size_t z = 0; z != maxvar; z++)
		printf("c Solution in %d = %d x %d\n", f.z[z].v, a.z[z].v, b.z[z].v);

	do_cnf_header();

	if (greater)
		(a > b).equal_to(false);

	e = do_mul_2adic(a, b);

	e.equal_to(f);

	for (size_t z = 0; z != maxvar; z++) {
		if ((cmask >> z) & 1)
			f.z[z].equal_to((cvalue >> z) & 1);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_v1_cnf(void)
{
top:
	printf("c The following CNF computes a multiplier\n"
	       "c having %zd bits for each variable and\n"
	       "c having %zd bits for (result & 0x%08llx) = 0x%08llx\n",
	       maxvar / 2, maxvar, cmask, cvalue);

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	for (size_t z = 0; z != maxvar / 2; z++)
		printf("c Solution in %d + %d = %d, %d\n", a.z[z].v, b.z[z].v, f.z[z].v, f.z[z + maxvar / 2].v);

	do_cnf_header();

	if (greater)
		(a > b).equal_to(false);

	e = do_mul_linear_v1(a, b);

	e.equal_to(f);

	for (size_t z = 0; z != maxvar; z++) {
		if ((cmask >> z) & 1)
			f.z[z].equal_to((cvalue >> z) & 1);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_v2_cnf(void)
{
top:
	printf("c The following CNF computes a multiplier\n"
	       "c having %zd bits for each variable and\n"
	       "c having %zd bits for (result & 0x%08llx) = 0x%08llx\n",
	       maxvar / 2, maxvar, cmask, cvalue);

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	for (size_t z = 0; z != maxvar / 2; z++)
		printf("c Solution in %d + %d = %d, %d\n", a.z[z].v, b.z[z].v, f.z[z].v, f.z[z + maxvar / 2].v);

	do_cnf_header();

	if (greater)
		(a > b).equal_to(false);

	e = do_mul_linear_v2(a, b, f);

	e.equal_to(f);

	for (size_t z = 0; z != maxvar; z++) {
		if ((cmask >> z) & 1)
			f.z[z].equal_to((cvalue >> z) & 1);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_limit_cnf(void)
{
	unsigned long long cvalue_sqrt = sqrt_64(cvalue);
top:
	printf(
	    "c The following CNF computes a multiplier\n"
	    "c having %zd bits for each variable and\n"
	    "c having %zd bits for (result & 0x%08llx) = 0x%08llx\n",
	    maxvar / 2, maxvar, cmask, cvalue);

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;
	var_t g;
	var_t h;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	for (size_t z = 0; z != maxvar / 2; z++) {
		printf("c Solution in %d + %d = %d, %d\n", a.z[z].v, b.z[z].v, f.z[z].v, f.z[z + maxvar / 2].v);

		g.z[z] = ((cvalue_sqrt >> z) & 1) ? -zerovar : zerovar;
		h.z[z] = (z == 0) ? -zerovar : zerovar;
	}

	do_cnf_header();

	(a > g).equal_to(false);
	(b >= g).equal_to(true);
	(a > h).equal_to(true);

	e = do_mul_linear_v1(a, b);

	e.equal_to(f);

	for (size_t z = 0; z != maxvar; z++)
		f.z[z].equal_to((cvalue >> z) & 1);

	if (runs++ == 0)
		goto top;
}

static void
generate_sqr_linear_cnf(void)
{
top:
	printf("c The following CNF computes a linear square\n"
	       "c having %zd bits for each variable and\n"
	       "c %zd bits for the result, (result & 0x%08llx) = 0x%08llx\n",
	       maxvar / 2, maxvar, cmask, cvalue);

	do_cnf_reset();

	var_t a;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	f.alloc();

	for (size_t z = 0; z != maxvar / 2; z++)
		printf("c Solution in %d = %d, %d\n", a.z[z].v, f.z[z].v, f.z[z + maxvar / 2].v);

	do_cnf_header();

	e = do_mul_linear_v1(a, a);

	if (rounded) {
		var_t b;

		b.alloc();

		e = e + b;

		/* limit range of "b" variable */
		(b > (a << 1)).equal_to(false);
	}

	e.equal_to(f);

	for (size_t z = 0; z != maxvar; z++) {
		if ((cmask >> z) & 1)
			f.z[z].equal_to((cvalue >> z) & 1);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mod_linear_cnf(void)
{
top:
	printf("c The following CNF computes a linear modulus\n"
	       "c having %zd bits for each variable and\n"
	       "c %zd bits for the result, (result & 0x%08llx) = 0x%08llx\n",
	       maxvar / 2, maxvar, cmask, cvalue);

	do_cnf_reset();

	var_t a;
	var_t f;

	a.alloc(maxvar / 2);
	f.alloc();

	for (size_t z = 0; z != maxvar / 2; z++)
		printf("c Solution in %d = %d, %d\n", a.z[z].v, f.z[z].v, f.z[z + maxvar / 2].v);

	do_cnf_header();

	if (cmask & cvalue & 1)
		a.z[0].equal_to(true);

	for (size_t z = 0; z != maxvar; z++) {
		if ((cmask >> z) & 1)
			f.z[z].equal_to((cvalue >> z) & 1);
	}

	do_zero_mod_linear(f, a);

	if (runs++ == 0)
		goto top;
}

static void
usage(void)
{
	fprintf(stderr, "Usage: hpsat_generate [-h] -f <n> -b <bits 0..%d> [-g] [-r] [-v <value> ] [ -m <value> ]\n", MAXVAR);
	fprintf(stderr, "	-M     # output solution as a max sat\n");
	fprintf(stderr, "	-g     # b >= a\n");
	fprintf(stderr, "	-v <X> # specify resulting value\n");
	fprintf(stderr, "	-m <X> # specify resulting value mask (default is -1)\n");
	fprintf(stderr, "	-r     # rounded\n");
	fprintf(stderr, "	-f 1   # Generate linear adder\n");
	fprintf(stderr, "	-f 2   # Generate 2-adic multiplier\n");
	fprintf(stderr, "	-f 3   # Generate linear multiplier (v1)\n");
	fprintf(stderr, "	-f 4   # Generate linear square\n");
	fprintf(stderr, "	-f 5   # Generate linear zero mod\n");
	fprintf(stderr, "	-f 6 -v <X> # Generate linear multiplier with variable limit\n");
	fprintf(stderr, "	-f 7   # Generate linear multiplier (v2)\n");
	exit(EX_USAGE);
}

int
main(int argc, char **argv)
{
	const char *const optstring = "ghf:cb:rv:m:M";
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
			cmask = -1;
			break;
		case 'M':
			maxsat = 1;
			break;
		case 'm':
			cmask = strtoull(optarg, NULL, 0);
			break;
		case 'g':
			greater = 1;
			break;
		case 'r':
			rounded = 1;
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
		generate_mul_linear_v1_cnf();
		break;
	case 4:
		generate_sqr_linear_cnf();
		break;
	case 5:
		generate_mod_linear_cnf();
		break;
	case 6:
		if (!cmask)
			usage();
		generate_mul_linear_limit_cnf();
		break;
	case 7:
		generate_mul_linear_v2_cnf();
		break;
	default:
		usage();
		break;
	}
	return (0);
}
