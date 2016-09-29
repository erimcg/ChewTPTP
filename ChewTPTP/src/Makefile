CFLAGS := -Wall 

all: chewtptp

chewtptp: lex.yy.o y.tab.c struct.o unification.o encode_util.o yices_encoding.o yices_nonhorn_cyclic_tableaux_encoding.o yices_cycle_check.o main.o
	g++  ${CFLAGS}  lex.yy.o y.tab.c struct.o unification.o encode_util.o yices_encoding.o yices_nonhorn_cyclic_tableaux_encoding.o yices_cycle_check.o main.o -o ../bin/chewtptp -L ../gmp-4.2.2/.libs -L ../yices-1.0.13/lib -lyices -lgmp

main.o:
	g++ ${CFLAGS} -c -I ../yices-1.0.13/include main.cpp

yices_cycle_check.o:
	g++ ${CFLAGS} -c -I ../yices-1.0.13/include yices_cycle_check.cpp

yices_nonhorn_cyclic_tableaux_encoding.o:
	g++ ${CFLAGS} -c -I ../yices-1.0.13/include yices_nonhorn_cyclic_tableaux_encoding.cpp

yices_encoding.o:
	g++ ${CFLAGS} -c -I ../yices-1.0.13/include yices_encoding.cpp

encode_util.o:
	g++ ${CFLAGS} -c encode_util.cpp

unification.o:
	g++ ${CFLAGS} -c unification.cpp	

struct.o:
	g++ ${CFLAGS} -c struct.cpp 

lex.yy.o: lex.yy.c y.tab.c
	gcc ${CFLAGS} -c lex.yy.c -o lex.yy.o

y.tab.o: y.tab.c
	gcc ${CFLAGS}  -c y.tab.c -o y.tab.o

y.tab.c:
	yacc -d parser.y

lex.yy.c:
	lex lexer.l 

clean:
	rm -rf *.o lex.yy.c y.tab.*


 
