/*-
 * Copyright (c) 2020-2022 Hans Petter Selasky.
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

#include <iostream>

#include <gmpxx.h>

#define	MAXVAR 65536

static int varnum;
static int nexpr;
static int old_varnum;
static int old_nexpr;
static size_t maxvar;
static int zerovar;
static int runs;
static int function;
static mpz_class a_value;
static mpz_class b_value;
static mpz_class r_value;
static int greater;
static int rounded;
static int varlimit;
static const char *inputexpr;
static int do_parse;
static int has_a_value;
static int has_b_value;
static int has_r_value;
static int output_format;
static const char *comment = "c";

#define	outcnf(...) do { \
    if (runs) \
	std::cout << __VA_ARGS__; \
} while (0)

#define	outvar(v) do { \
    if ((v) < 0) \
	outcnf("(1 - v" << -v << ")"); \
    else \
        outcnf("v" << v); \
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
	variable_t &operator =(int other) {
		v = other;
		assert(v != 0);
		return (*this);
	};
	void toggleInverted(void);
	bool isInverted(void);
	void equal_to_const(bool) const;
	void equal_to_var(const variable_t &other) const;

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
	if (output_format != 0) {
		outcnf(comment << " " << (old_varnum - 1) << " variables and " << old_nexpr << " expressions\n");
		outcnf("v0\n");
		outcnf("v1\n");
	} else {
		if (varlimit)
			outcnf("p cnf " << old_varnum - 1 << " " << old_nexpr << " " << varnum - 1 << "\n");
		else
			outcnf("p cnf " << old_varnum - 1 << " " << old_nexpr << "\n");

		(variable_t(zerovar)).equal_to_const(false);
	}
}

class var_t {
public:
	variable_t *z;

	var_t(void) {
		z = new variable_t [maxvar];
	};

	var_t(const variable_t &other) {
		z = new variable_t [maxvar];
		z[0] = other;
	};

	var_t(const var_t &other) {
		z = new variable_t [maxvar];

		for (size_t x = 0; x != maxvar; x++)
			z[x] = other.z[x];
	};

	~var_t(void) {
		delete [] z;
	};

	var_t &operator =(const var_t &other) {
		if (&other != this) {
			for (size_t x = 0; x != maxvar; x++)
				z[x] = other.z[x];
		}
		return (*this);
	};

	void alloc(size_t max = maxvar, bool is_signed = false) {
		for (size_t x = 0; x != max; x++)
			z[x].v = new_variable();
		for (size_t x = max; x != maxvar; x++)
			z[x].v = is_signed ? z[max - 1].v : zerovar;
	};

	void from_const(uint64_t var) {
		for (size_t x = 0; x != maxvar; x++) {
			if (x >= 64)
				z[x] = zerovar;
			else
				z[x] = ((var >> x) & 1) ? -zerovar : zerovar;
		}
	};

	void equal_to_const(bool other) const {
		for (size_t x = 0; x != maxvar; x++)
			z[x].equal_to_const(other);
	};

	void equal_to_var(const var_t &other) const {
		for (size_t x = 0; x != maxvar; x++)
			z[x].equal_to_var(other.z[x]);
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

	var_t &operator ^=(const var_t &other) {
		*this = *this ^ other;
		return (*this);
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

	var_t &operator &=(const var_t &other) {
		*this = *this & other;
		return (*this);
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

	var_t &operator |=(const var_t &other) {
		*this = *this | other;
		return (*this);
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

	var_t operator >>(size_t shift) const {
		var_t c;
		if (shift < maxvar) {
			for (size_t x = shift; x != maxvar; x++)
				c.z[x - shift] = z[x];
		}
		return (c);
	};

	var_t operator +(const var_t &other) const {
		const var_t &a = *this;
		const var_t &b = other;
		var_t c;

		c.alloc();

		/*
		 * Build equation for addition after HP Selasky 2021:
		 * a + b = c
		 */
		var_t t = (a ^ b);
		var_t u = (a | b);

		(t ^ c ^ (u << 1) ^ ((t & c) << 1)).equal_to_const(false);

		return (c);
	};

	var_t &operator +=(const var_t &other) {
		*this = *this + other;
		return (*this);
	};

	var_t operator -(const var_t &other) const {
		var_t a;
		const var_t &b = other;
		const var_t &c = *this;

		a.alloc();

		/*
		 * Build equation for addition after HP Selasky 2021:
		 * a = c - b
		 */
		var_t t = (a ^ b);
		var_t u = (a | b);

		(t ^ c ^ (u << 1) ^ ((t & c) << 1)).equal_to_const(false);

		return (a);
	};

	var_t &operator -=(const var_t &other) {
		*this = *this - other;
		return (*this);
	};

	var_t polar_add(const var_t &other) const {
		var_t r;
		r.alloc();

		const var_t c = (*this & other) ^ (*this & r) ^ (other & r);

		(*this ^ other ^ r ^ (c << 1)).equal_to_const(false);

		return (r);
	};

	var_t polar_mul(const var_t &other) const {
		var_t r;
		var_t c;

		for (size_t x = 0; x != maxvar; x++) {
			const var_t a = (*this & other.z[x]) << x;

			var_t var;
			var.alloc();

			const var_t cn = (r & a) ^ (r & var) ^ (a & var);

			(r ^ a ^ var ^ c).equal_to_const(false);

			r = var;
			c = cn << 1;
		}
		return (r);
	};

	var_t log() const {
		var_t r;
		var_t t = *this;

		z[0].equal_to_const(true);

		for (size_t x = 1; x != maxvar; x++) {
			r.z[x] = t.z[x];
			t = t + ((t & t.z[x]) << x);
		}
		return (r);
	};

	var_t exp() const {
		var_t r;

		z[0].equal_to_const(false);

		r.z[0] = -zerovar;

		for (size_t x = 1; x != maxvar; x++)
			r += (r & z[x]) << x;
		return (r);
	};

	var_t log_xor() const {
		var_t r;
		var_t t = *this;

		z[0].equal_to_const(true);

		for (size_t x = 1; x != maxvar; x++) {
			r.z[x] = t.z[x];
			t = t ^ ((t & t.z[x]) << x);
		}
		return (r);
	};

	var_t exp_xor() const {
		var_t r;

		z[0].equal_to_const(false);

		r.z[0] = -zerovar;

		for (size_t x = 1; x != maxvar; x++)
			r ^= (r & z[x]) << x;
		return (r);
	};

	var_t mul_xor(const var_t &other) const {
		var_t r;
		for (size_t x = 0; x != maxvar; x++) {
			const var_t rol = (*this << x) ^ (*this >> (maxvar - x));
			r = r ^ (rol & other.z[x]);
		}
		return (r);
	};

	var_t exp_xor(const var_t &other) const {
		var_t base = *this;
		var_t r;

		r.from_const(1);

		for (size_t x = 0; x != maxvar; x++) {
			r = (r.mul_xor(base) & other.z[x]) ^ (r & ~other.z[x]);
			base = base.mul_xor(base);
		}
		return (r);
	};

	var_t operator *(const var_t &other) const {
		var_t r;
		for (size_t x = 0; x != maxvar; x++)
			r = r + ((*this & other.z[x]) << x);
		return (r);
	};

	var_t &operator *=(const var_t &other) {
		*this = *this * other;
		return (*this);
	};

	var_t operator %(const var_t &other) const {
		var_t r = *this;
		for (size_t max = maxvar; max--; ) {
			if (other.z[max].v != zerovar) {
				for (size_t x = (maxvar - max); x--; ) {
					var_t temp = (other << x);
					r -= (temp & (temp >= r));
				}
				break;
			}
		}
		return (r);
	};

	var_t &operator %=(const var_t &other) {
		*this = *this % other;
		return (*this);
	};

	variable_t operator >(const var_t &other) {
		return (other - *this).z[maxvar - 1];
	};

	variable_t operator >=(const var_t &other) {
		return ~(*this - other).z[maxvar - 1];
	};

	variable_t operator <(const var_t &other) {
		return (*this - other).z[maxvar - 1];
	};

	variable_t operator <=(const var_t &other) {
		return ~(other - *this).z[maxvar - 1];
	};
};

static void
set_value(const var_t &f, mpz_class value)
{
	for (size_t z = 0; z != maxvar; z++)
		f.z[z].equal_to_const(((value >> z) & 1) != 0);
}

static void
set_values(const var_t &a, const var_t &b, const var_t &r)
{
	if (has_a_value)
		set_value(a, a_value);
	if (has_b_value)
		set_value(b, b_value);
	if (has_r_value)
		set_value(r, r_value);
}

static ssize_t
input_read_value(std::string &line, size_t &offset)
{
	bool sign = 0;
	ssize_t value = 0;

	while (line[offset] != 0) {
		if (isdigit(line[offset])) {
			value *= 10;
			value += line[offset] - '0';
			offset++;
		} else if (line[offset] == '-') {
			sign = 1;
			offset++;
		} else {
			break;
		}
	}
	return (sign ? -value : value);
}

static void
input_skip_space(std::string &line, size_t &offset)
{
	while (line[offset] == ' ' || line[offset] == '\t')
		offset++;
}

static int
compare_variable(const void *a, const void *b)
{
	ssize_t va = *(ssize_t *)a;
	ssize_t vb = *(ssize_t *)b;

	if (va > vb)
		return (1);
	else if (va < vb)
		return (-1);
	else
		return (0);
}

static int
input_variables(mpz_class &v0, const var_t &x0,
		mpz_class &v1, const var_t &x1,
		mpz_class &v2, const var_t &x2)
{
	std::string line;
	ssize_t v;
	size_t offset;
	mpz_class one = 1;
	ssize_t map[3 * maxvar];
	uint8_t value[3 * maxvar];
	size_t nvar;
	ssize_t *ptr;

	for (size_t x = 0; x != maxvar; x++) {
		map[x] = x0.z[x].v;
		map[x + maxvar] = x1.z[x].v;
		map[x + 2 * maxvar] = x2.z[x].v;
	}

	mergesort(map, 3 * maxvar, sizeof(map[0]), &compare_variable);

	for (size_t x = nvar = 0; x != 3 * maxvar; ) {
		size_t y;
		for (y = x + 1; y != 3 * maxvar; y++) {
			if (compare_variable(map + x, map + y))
				break;
		}
		map[nvar++] = map[x];
		x = y;
	}

	memset(value, 0, nvar * sizeof(value[0]));

	while (getline(std::cin, line)) {
		if (line[0] != 'v')
			continue;

		offset = 1;
		while (line[offset] != 0) {
			input_skip_space(line, offset);
			v = input_read_value(line, offset);
			input_skip_space(line, offset);
			if (v == 0) {
				v0 = v1 = v2 = 0;

				for (size_t x = 0; x != maxvar; x++) {
					v = x0.z[x].v;
					ptr = (ssize_t *)bsearch(&v, map, nvar, sizeof(map[0]), &compare_variable);
					if (value[ptr - map])
						v0 |= one << x;
					v = x1.z[x].v;
					ptr = (ssize_t *)bsearch(&v, map, nvar, sizeof(map[0]), &compare_variable);
					if (value[ptr - map])
						v1 |= one << x;
					v = x2.z[x].v;
					ptr = (ssize_t *)bsearch(&v, map, nvar, sizeof(map[0]), &compare_variable);
					if (value[ptr - map])
						v2 |= one << x;
				}
				return (0);
			}
			ptr = (ssize_t *)bsearch(&v, map, nvar, sizeof(map[0]), &compare_variable);
			if (ptr != 0)
				value[ptr - map] = 1;
		}
	}
	return (-1);
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
			outcnf(t << " ");
		}
	}
	outcnf("0\n");
	nexpr++;
}

void
variable_t :: equal_to_const(bool value) const
{
	assert(v != 0);

	if (output_format != 0) {
		outvar(v); outcnf(" - " << value << "\n");
		nexpr++;
	} else {
		outcnf((value ? v : -v) << " 0\n");
		nexpr++;
	}
}

void
variable_t :: equal_to_var(const variable_t &other) const
{
	assert(v != 0 && other.v != 0);

	if (output_format != 0) {
		outvar(v); outcnf(" - "); outvar(other.v); outcnf("\n");
		nexpr++;
	} else {
		outcnf(-v << " " << other.v << " 0\n");
		outcnf(v << " " << -other.v << " 0\n");
		nexpr += 2;
	}
}

void
variable_t :: toggleInverted(void)
{
	assert(v != 0);

	v = -v;
}

bool
variable_t :: isInverted(void)
{
	assert(v != 0);

	return (v < 0);
}

variable_t
variable_t :: operator &(const variable_t &other) const
{
	assert(v != 0 && other.v != 0);

	if (v == other.v) {
		/* same variable */
		return (v);
	} else if (v == -other.v) {
		/* inverted same variable */
		return (zerovar);
	} else if (output_format != 0) {
		/*
		 * Truth table:
		 * a + b - 2 * c - d = 0
		 */
		const int c = new_variable();
		const int d = new_variable();

		outvar(v); outcnf(" + "); outvar(other.v); outcnf(" - 2 * "); outvar(c); outcnf(" - "); outvar(d); outcnf("\n");
		nexpr++;

		return (c);
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
	assert(v != 0 && other.v != 0);

	if (v == other.v) {
		/* same variable */
		return (zerovar);
	} else if (v == -other.v) {
		/* inverted same variable */
		return (-zerovar);
	} else if (output_format != 0) {
		/*
		 * Truth table:
		 * a + b - 2 * c - d = 0
		 */
		const int c = new_variable();
		const int d = new_variable();

		outvar(v); outcnf(" + "); outvar(other.v); outcnf(" + "); outvar(c); outcnf(" - 2 * "); outvar(d); outcnf("\n");
		nexpr++;

		return (c);
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
	assert(v != 0 && other.v != 0);

	if (v == other.v) {
		/* same variable */
		return (v);
	} else if (v == -other.v) {
		/* inverted same variable */
		return (-zerovar);
	} else if (output_format != 0) {
		/*
		 * Truth table:
		 * a | b = a ^ b ^ (a & b)
		 */
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

/*
 * Geometric layout of half multiplier in 2-D:
 *
 *     +---------+
 *     | 0,1 1,1 |
 *     |         |
 *     | 0,0 1,0 |
 *     +---------+-------+
 *     | MSB     |  LSB  |
 */
static void
do_mul_half_v1(const variable_t &v0_0,
	       const variable_t &v0_1,
	       const variable_t &v1_0,
	       const variable_t &v1_1)
{
	/* half multiplier after HP Selasky 2021 */
	(v0_0 ^ v0_1 ^ (~v1_0 & v1_1)).equal_to_const(false);
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
	rem.equal_to_var(sub);
}

static variable_t
do_cond_half_sub(var_t &a, var_t &b, const var_t &value, const variable_t &gte)
{
	var_t x;
	var_t y;

	x = a ^ b ^ value;
	y = ((~a & b) | (~(a & ~b) & value)) << 1;

	a = (x & gte) | (a & ~gte);
	b = (y & gte) | (b & ~gte);

	return (gte);
}

static void
do_zero_mul_linear(var_t &rem, const var_t &hdiv, const var_t &vmul)
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

		do_cond_half_sub(rem, sub, tmp, vmul.z[x]);
	}

	/* result must be zero */
	rem.equal_to_var(sub);
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

	c.equal_to_var(zero);
	r.equal_to_const(false);

	/* add up everything */
	c = do_add_full_v2(r, c, zero);

	/* final XOR */
	c = c ^ zero;

	return (c);
}

static void
do_full_add_linear(const variable_t *pa, const variable_t *pb,
    const variable_t *pr, size_t a_size, size_t b_size)
{
	variable_t t[a_size + 1][b_size + 1];

	/* allocate variables */
	for (size_t x = 1; x != a_size + 1; x++) {
		for (size_t y = 1; y != b_size; y++) {
			t[x][y] = new_variable();
		}
	}

	/* setup variables */
	for (size_t x = 1; x != a_size + 1; x++) {
		t[x][0] = pa[x - 1];
		t[x][b_size] = pr[x - 1];
	}
	for (size_t x = 1; x != b_size + 1; x++)
		t[0][x] = ~pb[x - 1];

	/* set carry in to zero */
	t[0][0] = zerovar;

	/* build logic */
	for (size_t x = 0; x != a_size; x++) {
		for (size_t y = 0; y != b_size; y++) {
			do_mul_half_v1(t[x+1][y+1],
				       t[x+1][y],
				       t[x][y+1],
				       t[x][y]);
		}
	}
}

static var_t
do_sqr_linear_v2(const var_t &a)
{
	size_t sz = ((maxvar / 2) * (maxvar / 2) - (maxvar / 2)) / 2;
	variable_t ta[sz];
	var_t tn;
	var_t t;

	for (size_t x = 0, z = 0; x != maxvar / 2; x++) {
		for (size_t y = x + 1; y != maxvar / 2; y++, z++) {
			ta[z] = a.z[x] & a.z[y];
		}
	}

	for (size_t p = 0, n; p != maxvar; p++) {
		n = (~p & 1);

		for (size_t x = 0; x != maxvar / 2; x++) {
			for (size_t y = x + 1; y != maxvar / 2; y++) {
				if (x + y + 1 == p)
					n++;
			}
		}

		variable_t bv[2 * n];

		n = 0;
		if (~p & 1)
			bv[1 + 2 * n++] = a.z[p / 2];

		for (size_t x = 0, z = 0; x != maxvar / 2; x++) {
			for (size_t y = x + 1; y != maxvar / 2; y++, z++) {
				if (x + y + 1 == p)
					bv[1 + 2 * n++] = ta[z];
			}
		}

		size_t as = 0;

		for (size_t log2 = 0;; log2++) {
			if ((1UL << log2) >= (n + (n + 1) / 2)) {
				as = log2 + 1;
				break;
			}
		}

		if (as == 0 || n == 0)
			continue;

		if (p + as > maxvar)
			as = maxvar - p;

		tn = t;

		for (size_t x = 0; x != as; x++)
			tn.z[p + x] = new_variable();

		do_full_add_linear(t.z + p, bv, tn.z + p, as, 2 * n);

		t = tn;
	}
	return (t);
}

static var_t
do_mul_linear_v4(const var_t &a, const var_t &b)
{
	size_t sz = (maxvar / 2) * (maxvar / 2);
	variable_t ta[sz];
	var_t tn;
	var_t t;

	for (size_t x = 0, z = 0; x != maxvar / 2; x++) {
		for (size_t y = 0; y != maxvar / 2; y++, z++) {
			ta[z] = a.z[x] & b.z[y];
		}
	}

	for (size_t p = 0, n; p != maxvar; p++) {
		n = 0;

		for (size_t x = 0; x != maxvar / 2; x++) {
			for (size_t y = 0; y != maxvar / 2; y++) {
				if (x + y == p)
					n++;
			}
		}

		variable_t bv[2 * n];

		n = 0;

		for (size_t x = 0, z = 0; x != maxvar / 2; x++) {
			for (size_t y = 0; y != maxvar / 2; y++, z++) {
				if (x + y == p)
					bv[1 + 2 * n++] = ta[z];
			}
		}

		size_t as = 0;

		for (size_t log2 = 0;; log2++) {
			if ((1UL << log2) >= (n + (n + 1) / 2)) {
				as = log2 + 1;
				break;
			}
		}

		if (as == 0 || n == 0)
			continue;

		if (p + as > maxvar)
			as = maxvar - p;

		tn = t;

		for (size_t x = 0; x != as; x++)
			tn.z[p + x] = new_variable();

		do_full_add_linear(t.z + p, bv, tn.z + p, as, 2 * n);

		t = tn;
	}
	return (t);
}

static void
generate_adder_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the addition of two " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit sum: (a + b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc();
	b.alloc();
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " + " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " + " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	(a + b).equal_to_var(f);

	set_values(a,b,f);

	if (greater) {
		(a > f).equal_to_const(false);
		(b > f).equal_to_const(false);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_2adic_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the 2-adic multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " x " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " x " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	e = do_mul_2adic(a, b);

	e.equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_v1_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the linear multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	(a * b).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_v2_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the linear multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	e = do_mul_linear_v2(a, b, f);

	e.equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_v3_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the linear multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	(a * b).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_v4_cnf(void)
{
	mpz_class r_value_sqrt = sqrt(r_value);
top:
	outcnf(comment << " The following CNF computes the linear multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t g;
	var_t h;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " * 2 = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++) {
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");
		g.z[z].v = (((r_value_sqrt >> z) & 1) != 0) ? -zerovar : zerovar;
	}

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	(a <= g).equal_to_const(true);

	var_t r;

	for (size_t x = 0; x != maxvar; x++)
		r = r + ((a ^ b.z[x]) << x);

	(h - r - a - b).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_v5_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the linear multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t h;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++) {
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");
	}

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	do_mul_linear_v4(a,b).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_full_add_linear_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the full adition of two " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit sum: f(a, b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc();
	b.alloc();
	f.alloc();

	if (do_parse == true) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " + " << vb.get_str(2) << " = " << vf <<
			    " D=" << vf - va << "\n";
		}
		return;
	}

	do_cnf_header();

	do_full_add_linear(a.z, b.z, f.z, maxvar, maxvar);

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_limit_cnf(void)
{
	mpz_class r_value_sqrt = sqrt(r_value);
top:
	outcnf(comment << " The following CNF computes the linear multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;
	var_t g;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");

	for (size_t z = 0; z != maxvar; z++)
		g.z[z] = (((r_value_sqrt >> z) & 1) != 0) ? -zerovar : zerovar;

	do_cnf_header();

	(a <= g).equal_to_const(true);
	(b >= g).equal_to_const(true);
	(b <= (f >> 1)).equal_to_const(true);

	(a * b).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_linear_by_squaring_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the linear multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * a) - (b * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << "**2 - " << vb << "**2 = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	(a > b).equal_to_const(true);

	if (greater) {
		((a + b) <= f).equal_to_const(true);
		((a - b) <= f).equal_to_const(true);
	}

	(a * a - b * b).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_sqr_linear_cnf_v1(void)
{
top:
	outcnf(comment << " The following CNF computes the linear square root of a " << maxvar << " bit\n" <<
	       comment << " variables into a " << (maxvar / 2) << " bit result: sqrt(a) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, var_t(),
				       vf, f) == 0) {
			std::cout << "sqrt(" << vf << ") = " << va << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in sqrt(" << f.z[z].v << ") = " << a.z[z].v << "\n");

	do_cnf_header();

	e = (a * a);

	if (rounded) {
		var_t b;

		b.alloc();

		e = e + b;

		/* limit range of "b" variable */
		(b > (a << 1)).equal_to_const(false);
	}

	e.equal_to_var(f);

	set_values(a,var_t(),f);

	if (runs++ == 0)
		goto top;
}

static void
generate_sqr_linear_cnf_v2(void)
{
top:
	outcnf(comment << " The following CNF computes the linear square root of a " << maxvar << " bit\n" <<
	       comment << " variables into a " << (maxvar / 2) << " bit result: sqrt(a) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, var_t(),
				       vf, f) == 0) {
			std::cout << "sqrt(" << vf << ") = " << va << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in sqrt(" << f.z[z].v << ") = " << a.z[z].v << "\n");

	do_cnf_header();

	do_sqr_linear_v2(a).equal_to_var(f);

	set_values(a,var_t(),f);

	if (runs++ == 0)
		goto top;
}

static void
generate_zero_mod_linear_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the linear modulus of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a % b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t f;

	a.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, var_t(),
				       vf, f) == 0) {
			std::cout << vf << " mod " << va << " = 0\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << f.z[z].v << " % " << a.z[z].v << " = 0\n");

	do_cnf_header();

	set_values(a,var_t(),f);

	do_zero_mod_linear(f, a);

	if (runs++ == 0)
		goto top;
}

static void
generate_zero_mul_linear_cnf(bool isSquare)
{
top:
	outcnf(comment << " The following CNF computes the linear multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc(maxvar / 2);
	if (isSquare)
		b = a;
	else
		b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << vf << " = " << va << " * " << vb << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << f.z[z].v << " = " << a.z[z].v << " * " << b.z[z].v << "\n");

	do_cnf_header();

	set_values(a,b,f);

	do_zero_mul_linear(f, a, b);

	if (runs++ == 0)
		goto top;
}

static void
generate_and_cnf(void)
{
top:
	outcnf(comment << " The following CNF implements an AND circuit\n" <<
	       comment << " having two inputs and one output\n");

	do_cnf_reset();

	variable_t a = new_variable();
	variable_t b = new_variable();
	variable_t c;

	if (do_parse) {
		mpz_class va,vb,vc;

		while (input_variables(va, var_t(a),
				       vb, var_t(b),
				       vc, var_t()) == 0) {
			std::cout << va << " & " << vb << " = 0\n";
		}
		return;
	}

	outcnf(comment << " Solution in " << a.v << " & " << b.v << " = " << c.v << "\n");

	do_cnf_header();

	c = (a & b);

	if (has_r_value)
		c.equal_to_const((r_value & 1) != 0);

	if (runs++ == 0)
		goto top;
}

static void
generate_or_cnf(void)
{
top:
	outcnf(comment << " The following CNF implements an OR circuit\n" <<
	       comment << " having two inputs and one output\n");

	do_cnf_reset();

	variable_t a = new_variable();
	variable_t b = new_variable();
	variable_t c;

	if (do_parse) {
		mpz_class va,vb,vc;

		while (input_variables(va, var_t(a),
				       vb, var_t(b),
				       vc, var_t()) == 0) {
			std::cout << va << " | " << vb << " = 0\n";
		}
		return;
	}

	outcnf(comment << " Solution in " << a.v << " | " << b.v << " = " << c.v << "\n");

	do_cnf_header();

	c = (a | b);

	if (has_r_value)
		c.equal_to_const((r_value & 1) != 0);

	if (runs++ == 0)
		goto top;
}

static void
generate_xor_cnf(void)
{
top:
	outcnf(comment << " The following CNF implements an XOR circuit\n" <<
	       comment << " having two inputs and one output\n");

	do_cnf_reset();

	variable_t a = new_variable();
	variable_t b = new_variable();
	variable_t c;

	if (do_parse) {
		mpz_class va,vb,vc;

		while (input_variables(va, var_t(a),
				       vb, var_t(b),
				       vc, var_t()) == 0) {
			std::cout << va << " ^ " << vb << " = 0\n";
		}
		return;
	}

	outcnf(comment << " Solution in " << a.v << " ^ " << b.v << " = " << c.v << "\n");

	do_cnf_header();

	c = (a ^ b);

	if (has_r_value)
		c.equal_to_const((r_value & 1) != 0);

	if (runs++ == 0)
		goto top;
}

static size_t
generate_input_maxvar(const char *ptr, uint64_t *pmask)
{
	size_t retval = 0;

	while (*ptr) {
		if (*ptr >= 'a' && *ptr <= 'z') {
			const size_t z = *ptr - 'a' + 1;
			if (z > retval)
				retval = z;
			*pmask |= (1ULL << (z - 1));
		} else if (*ptr >= 'A' && *ptr <= 'Z') {
			const size_t z = *ptr - 'A' + 1;
			if (z > retval)
				retval = z;
			*pmask |= (1ULL << (z - 1));
		}
		ptr++;
	}
	return (retval);
}

static variable_t
generate_input_parse(const var_t &var, const char *ptr)
{
	variable_t ret;
	variable_t opvar;
	char last = 0;
	int level = 0;

	while (*ptr) {
		if (*ptr == '1') {
			opvar = -zerovar;
			goto do_var;
		} else if (*ptr == '0') {
			opvar = zerovar;
			goto do_var;
		} else if (*ptr >= 'a' && *ptr <= 'z') {
			const size_t n = *ptr - 'a';
			if (n < maxvar) {
				opvar = var.z[n];
				goto do_var;
			} else {
				fprintf(stderr, "Invalid variable '%c'\n", *ptr);
			}
		} else if (*ptr >= 'A' && *ptr <= 'Z') {
			const size_t n = *ptr - 'A';
			if (n < maxvar) {
				opvar = ~var.z[n];
				goto do_var;
			} else {
				fprintf(stderr, "Invalid variable '%c'\n", *ptr);
			}
		} else if (*ptr == '(') {
			opvar = generate_input_parse(var, ptr + 1);
		do_var:
			switch (last) {
			case 0:
				ret = opvar;
				break;
			case '^':
				ret ^= opvar;
				break;
			case '&':
				ret &= opvar;
				break;
			case '|':
				ret |= opvar;
				break;
			default:
				fprintf(stderr, "Invalid operator '%c'\n", last);
				break;
			}
			last = 0;

			if (*ptr == '(') {
				while (*ptr) {
					if (*ptr == '(')
						level++;
					else if (*ptr == ')')
						level--;
					if (level == 0)
						break;
					ptr++;
				}
				if (level != 0)
					fprintf(stderr, "Unbalanced expression\n");
			}
		} else if (*ptr == '^' || *ptr == '&' || *ptr == '|') {
			if (last)
				fprintf(stderr, "Duplicate operator '%c'\n", last);
			last = *ptr;
		} else if (*ptr == ')') {
			break;
		} else if (*ptr == ' ' || *ptr == '\t' || *ptr == '\r' || *ptr == '\n') {

		} else {
			fprintf(stderr, "Invalid character '%c'\n", *ptr);
		}
		if (*ptr == 0)
			break;
		ptr++;
	}
	if (last != 0)
		fprintf(stderr, "Missing variable after '%c'\n", last);
	return (ret);
}

static void
generate_input_cnf(void)
{
	uint64_t mask = 0;
	maxvar = generate_input_maxvar(inputexpr, &mask);

top:
	outcnf(comment << " This CNF-file implements the following expression\n"
	       "c\n" <<
	       comment << "   '" << inputexpr << "'\n"
	       "c\n");

	do_cnf_reset();

	var_t var;
	var.alloc();

	if (do_parse) {
		mpz_class va,vb,vc;

		while (input_variables(va, var,
				       vb, var_t(),
				       vc, var_t()) == 0) {
			for (size_t x = 0; x != maxvar; x++) {
				if (~(mask >> x) & 1)
					continue;
				std::cout << (char)('a' + x) << "=" << (((va >> x) & 1) != 0) << " ";
			}
			std::cout << "\n";
		}
		return;
	}

	outcnf(comment << " Variable mapping used:\n"
	       "c\n");
	for (size_t x = 0; x != maxvar; x++) {
		if (~(mask >> x) & 1)
			continue;
		outcnf(comment << "   '" << (char)('a' + x) << "' = " << var.z[x].v << "\n");
	}
	outcnf("c\n"
	       "c\n");

	do_cnf_header();

	generate_input_parse(var, inputexpr).equal_to_const(false);

	/* ground unused variables */
	for (size_t x = 0; x != maxvar; x++) {
		if ((mask >> x) & 1)
			continue;
		var.z[x].equal_to_const(false);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_div_linear_v1_cnf(bool isSquare)
{
	mpz_class r_value_sqrt = sqrt(r_value);
top:
	outcnf(comment << " The following CNF computes a divisor\n" <<
	       comment << " having " << (maxvar / 2) << " bits for each variable and\n" <<
	       comment << " having " << maxvar << " bits for the result.\n" <<
	       comment << " The starting point for the division is " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t e;
	var_t f;
	var_t g;

	f.alloc(maxvar / 2);
	if (isSquare)
		b = f;
	else
		b.alloc(maxvar / 2);
	a.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " / " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " / " << b.z[z].v << " = " << f.z[z].v << "\n");

	for (size_t z = 0; z != maxvar; z++)
		g.z[z].v = (((r_value_sqrt >> z) & 1) != 0) ? -zerovar : zerovar;

	do_cnf_header();

	b.z[0].equal_to_const(1);

	if (greater) {
		(b <= g).equal_to_const(true);
		(f > a).equal_to_const(false);
	}

	set_values(f,b,a);

	for (size_t z = 0; z != (maxvar / 2); z++) {
		variable_t bit = a.z[z];
		f.z[z].equal_to_var(bit);
		a -= (b << z) & bit;
	}

	for (size_t z = 0; z != maxvar; z++)
		a.z[z].equal_to_const(false);

	if (runs++ == 0)
		goto top;
}

static void
generate_inv_multiplier_v1_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes an inverse multiplier\n" <<
	       comment << " having " << maxvar << " bits for each variable and\n" <<
	       comment << " having " << maxvar << " bits for the result.\n" <<
	       comment << " The starting point for the division is " << r_value << "\n");

	do_cnf_reset();

	variable_t bit;
	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in (" << a.z[z].v << " * " << b.z[z].v << ") = " << f.z[z].v << "\n");

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	a.z[0].equal_to_const(true);
	b.z[0].equal_to_const(true);
	f.z[0].equal_to_const(true);
	e.z[0].toggleInverted();

	set_values(a,b,f);

	for (size_t z = 1; z != maxvar; z++) {
		bit = a.z[z];
		a += (a << z) & bit;
		e += (e << z) & bit;
		bit = b.z[z];
		b += (b << z) & bit;
		e += (e << z) & bit;
	}

	var_t g;

	g.z[0].toggleInverted();

	for (size_t z = 1; z != maxvar; z++) {
		bit = e.z[z];
		e += (e << z) & bit;
		g += (g << z) & bit;
	}

	for (size_t z = 0; z != maxvar; z++)
		f.z[z].equal_to_var(g.z[z]);

	if (runs++ == 0)
		goto top;
}

static void
generate_inv_2adic_multiplier_v1_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes an inverse multiplier\n" <<
	       comment << " having " << maxvar << " bits for each variable and\n" <<
	       comment << " having " << maxvar << " bits for the result.\n" <<
	       comment << " The starting point for the division is " << r_value << "\n");

	do_cnf_reset();

	variable_t bit;
	var_t a;
	var_t b;
	var_t f;
	var_t e;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in (" << a.z[z].v << " x " << b.z[z].v << ") = " << f.z[z].v << "\n");

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	a.z[0].equal_to_const(true);
	b.z[0].equal_to_const(true);
	f.z[0].equal_to_const(true);
	e.z[0].toggleInverted();

	set_values(a,b,f);

	for (size_t z = 1; z != maxvar; z++) {
		bit = a.z[z];
		a ^= (a << z) & bit;
		e ^= (e << z) & bit;
		bit = b.z[z];
		b ^= (b << z) & bit;
		e ^= (e << z) & bit;
	}

	var_t g;

	g.z[0].toggleInverted();

	for (size_t z = 1; z != maxvar; z++) {
		bit = e.z[z];
		e ^= (e << z) & bit;
		g ^= (g << z) & bit;
	}

	for (size_t z = 0; z != maxvar; z++)
		f.z[z].equal_to_var(g.z[z]);

	if (runs++ == 0)
		goto top;
}

static void
generate_mul_2adic_rol_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the 2-adic rotating multiplication of two " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc(maxvar);
	b.alloc(maxvar);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " x " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " x " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	a.mul_xor(b).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_exp_2adic_rol_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the 2-adic rotating exponent of two " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit product: (a ** b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc(maxvar);
	b.alloc(maxvar);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " ** " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " x " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	if (greater)
		(a > b).equal_to_const(false);

	a.exp_xor(b).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_polar_add_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the polar addition of two " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit sum: (a + b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc();
	b.alloc();
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " + " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " + " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	a.polar_add(b).equal_to_var(f);

	set_values(a,b,f);

	if (greater) {
		(a > f).equal_to_const(false);
		(b > f).equal_to_const(false);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_polar_mul_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the polar multiplication of two " << (maxvar / 2) << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit sum: (a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t f;

	a.alloc(maxvar / 2);
	b.alloc(maxvar / 2);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << va << " * " << vb << " = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in " << a.z[z].v << " * " << b.z[z].v << " = " << f.z[z].v << "\n");

	do_cnf_header();

	a.polar_mul(b).equal_to_var(f);

	set_values(a,b,f);

	if (greater) {
		(a > f).equal_to_const(false);
		(b > f).equal_to_const(false);
	}

	if (runs++ == 0)
		goto top;
}

static void
generate_log_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the logarithm of odd value \"a\" " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit result: log(a) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t f;
	var_t e;

	a.alloc(maxvar);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, var_t(),
				       vf, f) == 0) {
			std::cout << "log(" << va << ") = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in log(" << a.z[z].v << ") = " << f.z[z].v << "\n");

	do_cnf_header();

	a.log().equal_to_var(f);

	set_values(a,var_t(),f);

	if (runs++ == 0)
		goto top;
}

static void
generate_dual_log_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the logarithm of odd value \"a\" and \"b\" " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit result: log(a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t c;
	var_t d;
	var_t f;
	var_t e;

	a.alloc();
	b.alloc();
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << "log(" << va << " * " << vb << ") = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in log(" << a.z[z].v << " * " << b.z[z].v << ") = " << f.z[z].v << "\n");

	do_cnf_header();

	c = a.log();
	d = b.log();

	(c & d).equal_to_const(false);
	(c ^ d).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_exp_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the exponent of even value \"a\" " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit result: exp(a) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t f;
	var_t e;

	a.alloc(maxvar);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, var_t(),
				       vf, f) == 0) {
			std::cout << "exp(" << va << ") = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in exp(" << a.z[z].v << ") = " << f.z[z].v << "\n");

	do_cnf_header();

	a.exp().equal_to_var(f);

	set_values(a,var_t(),f);

	if (runs++ == 0)
		goto top;
}

static void
generate_log_xor_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the XOR logarithm of odd value \"a\" " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit result: log_xor(a) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t f;
	var_t e;

	a.alloc(maxvar);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, var_t(),
				       vf, f) == 0) {
			std::cout << "log_xor(" << va << ") = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in log_xor(" << a.z[z].v << ") = " << f.z[z].v << "\n");

	do_cnf_header();

	a.log_xor().equal_to_var(f);

	set_values(a,var_t(),f);

	if (runs++ == 0)
		goto top;
}

static void
generate_dual_log_xor_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the XOR logarithm of odd value \"a\" and \"b\" " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit result: log_xor(a * b) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t b;
	var_t c;
	var_t d;
	var_t f;
	var_t e;

	a.alloc();
	b.alloc();
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, b,
				       vf, f) == 0) {
			std::cout << "log_xor(" << va << " * " << vb << ") = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in log_xor(" << a.z[z].v << " * " << b.z[z].v << ") = " << f.z[z].v << "\n");

	do_cnf_header();

	c = a.log_xor();
	d = b.log_xor();

	(c & d).equal_to_const(false);
	(c ^ d).equal_to_var(f);

	set_values(a,b,f);

	if (runs++ == 0)
		goto top;
}

static void
generate_exp_xor_cnf(void)
{
top:
	outcnf(comment << " The following CNF computes the XOR exponent of even value \"a\" " << maxvar << " bit\n" <<
	       comment << " variables into a " << maxvar << " bit result: exp_xor(a) = " << r_value << "\n");

	do_cnf_reset();

	var_t a;
	var_t f;
	var_t e;

	a.alloc(maxvar);
	f.alloc();

	if (do_parse) {
		mpz_class va,vb,vf;

		while (input_variables(va, a,
				       vb, var_t(),
				       vf, f) == 0) {
			std::cout << "exp_xor(" << va << ") = " << vf << "\n";
		}
		return;
	}

	for (size_t z = 0; z != maxvar; z++)
		outcnf(comment << " Solution in exp_xor(" << a.z[z].v << ") = " << f.z[z].v << "\n");

	do_cnf_header();

	a.exp_xor().equal_to_var(f);

	set_values(a,var_t(),f);

	if (runs++ == 0)
		goto top;
}

static void
usage(void)
{
	fprintf(stderr, "Usage: hpsat_generate [-h] -f <n> -b <bits 1..%d> [-g] [-r] [-v <value> ]\n", MAXVAR);
	fprintf(stderr, "	-V     # output variable limit in CNF header\n");
	fprintf(stderr, "	-p     # pretty print result from solver via standard input\n");
	fprintf(stderr, "	-g     # b >= a\n");
	fprintf(stderr, "	-R     # use output format suitable for hpRsat\n");
	fprintf(stderr, "	-A <X> # specify \"A\" value\n");
	fprintf(stderr, "	-B <X> # specify \"B\" value\n");
	fprintf(stderr, "	-v <X> # specify resulting value\n");
	fprintf(stderr, "	-r     # rounded\n");
	fprintf(stderr, "	-i <X> # Input binary expression, which must be equal to zero\n");
	fprintf(stderr, "	-i <(a ^ b) & (c | d)> # Binary expression example\n");
	fprintf(stderr, "	-f 1   # Generate linear adder\n");
	fprintf(stderr, "	-f 2   # Generate 2-adic multiplier\n");
	fprintf(stderr, "	-f 3   # Generate linear multiplier (v1)\n");
	fprintf(stderr, "	-f 4   # Generate linear square (v1)\n");
	fprintf(stderr, "	-f 5   # Generate linear zero mod\n");
	fprintf(stderr, "	-f 6 -v <X> # Generate linear multiplier with variable limit\n");
	fprintf(stderr, "	-f 7   # Generate linear multiplier (v2)\n");
	fprintf(stderr, "	-f 8   # Generate AND circuit\n");
	fprintf(stderr, "	-f 9   # Generate OR circuit\n");
	fprintf(stderr, "	-f 10  # Generate XOR circuit\n");
	fprintf(stderr, "	-f 11  # Generate linear divisor\n");
	fprintf(stderr, "	-f 12  # Generate inverse linear multiplier\n");
	fprintf(stderr, "	-f 13  # Generate inverse 2-adic multiplier\n");
	fprintf(stderr, "	-f 14  # Generate linear multiplier (v3)\n");
	fprintf(stderr, "	-f 15  # Generate linear multiplier by squaring\n");
	fprintf(stderr, "	-f 16  # Generate linear multiplier (v4)\n");
	fprintf(stderr, "	-f 17  # Generate 2-adic rotating multiplier\n");
	fprintf(stderr, "	-f 18  # Generate 2-adic rotating exponent\n");
	fprintf(stderr, "	-f 19  # Generate polar addition\n");
	fprintf(stderr, "	-f 20  # Generate polar multiplication\n");
	fprintf(stderr, "	-f 21  # Generate linear square divisor\n");
	fprintf(stderr, "	-f 22  # Generate linear multiplier (v5)\n");
	fprintf(stderr, "	-f 23  # Generate linear squarer (v2)\n");
	fprintf(stderr, "	-f 24  # Generate full adder\n");
	fprintf(stderr, "	-f 25  # Generate linear square (v2)\n");
	fprintf(stderr, "	-f 26  # Generate linear multiplier (v6)\n");
	fprintf(stderr, "	-f 27  # Generate non-linear log()\n");
	fprintf(stderr, "	-f 28  # Generate non-linear exp()\n");
	fprintf(stderr, "	-f 29  # Generate dual non-linear log()\n");
	fprintf(stderr, "	-f 30  # Generate non-linear log_xor()\n");
	fprintf(stderr, "	-f 31  # Generate non-linear exp_xor()\n");
	fprintf(stderr, "	-f 32  # Generate dual non-linear log_xor()\n");
	exit(EX_USAGE);
}

int
main(int argc, char **argv)
{
	const char *const optstring = "ghf:cb:rv:Vi:pA:B:R";
	int ch;

	while ((ch = getopt(argc, argv, optstring)) != -1) {
		switch (ch) {
		case 'R':
			output_format = 1;
			comment = "#";
			break;
		case 'p':
			do_parse = 1;
			break;
		case 'i':
			inputexpr = optarg;
			break;
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
		case 'A':
			has_a_value = 1;
			a_value = 0;
			for (const char *ptr = optarg; *ptr != 0; ptr++) {
				if (*ptr >= '0' && *ptr <= '9') {
					a_value *= 10;
					a_value += *ptr - '0';
				} else if (*ptr == '-' && ptr == optarg) {
					continue;
				} else {
					usage();
				}
			}
			if (optarg[0] == '-')
				a_value = -a_value;
			break;
		case 'B':
			has_b_value = 1;
			b_value = 0;
			for (const char *ptr = optarg; *ptr != 0; ptr++) {
				if (*ptr >= '0' && *ptr <= '9') {
					b_value *= 10;
					b_value += *ptr - '0';
				} else if (*ptr == '-' && ptr == optarg) {
					continue;
				} else {
					usage();
				}
			}
			if (optarg[0] == '-')
				b_value = -b_value;
			break;
		case 'v':
			has_r_value = 1;
			r_value = 0;
			for (const char *ptr = optarg; *ptr != 0; ptr++) {
				if (*ptr >= '0' && *ptr <= '9') {
					r_value *= 10;
					r_value += *ptr - '0';
				} else if (*ptr == '-' && ptr == optarg) {
					continue;
				} else {
					usage();
				}
			}
			if (optarg[0] == '-')
				r_value = -r_value;
			break;
		case 'g':
			greater = 1;
			break;
		case 'r':
			rounded = 1;
			break;
		case 'V':
			varlimit = 1;
			break;
		default:
			usage();
			break;
		}
	}

	if (inputexpr != NULL) {
		generate_input_cnf();
		return (0);
	} else if (maxvar == 0 || function == 0)
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
		generate_sqr_linear_cnf_v1();
		break;
	case 5:
		generate_zero_mod_linear_cnf();
		break;
	case 6:
		if (has_r_value == 0)
			usage();
		generate_mul_linear_limit_cnf();
		break;
	case 7:
		generate_mul_linear_v2_cnf();
		break;
	case 8:
		generate_and_cnf();
		break;
	case 9:
		generate_or_cnf();
		break;
	case 10:
		generate_xor_cnf();
		break;
	case 11:
		generate_div_linear_v1_cnf(false);
		break;
	case 12:
		generate_inv_multiplier_v1_cnf();
		break;
	case 13:
		generate_inv_2adic_multiplier_v1_cnf();
		break;
	case 14:
		generate_mul_linear_v3_cnf();
		break;
	case 15:
		generate_mul_linear_by_squaring_cnf();
		break;
	case 16:
		generate_mul_linear_v4_cnf();
		break;
	case 17:
		generate_mul_2adic_rol_cnf();
		break;
	case 18:
		generate_exp_2adic_rol_cnf();
		break;
	case 19:
		generate_polar_add_cnf();
		break;
	case 20:
		generate_polar_mul_cnf();
		break;
	case 21:
		generate_div_linear_v1_cnf(true);
		break;
	case 22:
		generate_zero_mul_linear_cnf(false);
		break;
	case 23:
		generate_zero_mul_linear_cnf(true);
		break;
	case 24:
		generate_full_add_linear_cnf();
		break;
	case 25:
		generate_sqr_linear_cnf_v2();
		break;
	case 26:
		generate_mul_linear_v5_cnf();
		break;
	case 27:
		generate_log_cnf();
		break;
	case 28:
		generate_exp_cnf();
		break;
	case 29:
		generate_dual_log_cnf();
		break;
	case 30:
		generate_log_xor_cnf();
		break;
	case 31:
		generate_exp_xor_cnf();
		break;
	case 32:
		generate_dual_log_xor_cnf();
		break;
	default:
		usage();
		break;
	}
	return (0);
}
