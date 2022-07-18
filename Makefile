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

.include <bsd.own.mk>
.if ${TARGET_OSNAME} == "Linux"
CXXFLAGS+=  -DLIBBSD_OVERLAY -I/usr/include/bsd
LDFLAGS+= -lbsd
_CCLINK = ${CXX}
.endif
# XXX following line is needed on Linux and NetBSD
PROG:=    ${PROG_CXX}

.include <bsd.prog.mk>
