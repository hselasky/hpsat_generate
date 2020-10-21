PROG_CXX=hpsat_generate
MAN=
SRCS=	hpsat_generate.cpp
BINDIR?=/usr/local/bin

.if defined(HAVE_DEBUG)
CFLAGS+= -g -O0
.endif

.include <bsd.prog.mk>
