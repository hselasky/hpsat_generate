PROG_CXX=hpsat_generate
PREFIX?=/usr/local
MAN=
SRCS=	hpsat_generate.cpp
BINDIR?=${PREFIX}/bin

.if defined(HAVE_DEBUG)
CFLAGS+= -g -O0
.endif

CFLAGS+= -I${PREFIX}/include
LDFLAGS+= -L${PREFIX}/lib -lgmp -lgmpxx

.include <bsd.prog.mk>
