STANDARD := -std=c++20

CADICAL_INC := cadical/src/
CADICAL_LIB_DIR := cadical/build/
CADICAL_LIB := -lcadical
MUS_INC := include

mus: src/main.cpp
	g++ ${STANDARD} -o $@ src/main.cpp src/cardinality.cpp src/util.cpp -O3 -I${MUS_INC} -I${CADICAL_INC} -L${CADICAL_LIB_DIR} ${CADICAL_LIB}

rez-mež: src/full.cpp src/cardinality.cpp src/util.cpp
	g++ ${STANDARD} -o $@ $^ -O3 -I${MUS_INC} -I${CADICAL_INC} -L${CADICAL_LIB_DIR} ${CADICAL_LIB}

mss: src/mss.cpp
	g++ ${STANDARD} -o $@ src/mss.cpp src/cardinality.cpp src/util.cpp -O3 -I${MUS_INC} -I${CADICAL_INC} -L${CADICAL_LIB_DIR} ${CADICAL_LIB}

res_cm: src/res_cm.cpp src/util.cpp
	g++ ${STANDARD} -o $@ $^ -O3 -I${MUS_INC} -I${CADICAL_INC} -L${CADICAL_LIB_DIR} ${CADICAL_LIB}

from_d-dnnf: src/from_dDnnf.cpp src/cardinality.cpp src/util.cpp 
	g++ ${STANDARD} -o $@ $^ -O3 -I${MUS_INC} -I${CADICAL_INC} -L${CADICAL_LIB_DIR} ${CADICAL_LIB}

to_dnf: src/to_dnf.cpp src/cardinality.cpp src/util.cpp
	g++ ${STANDARD} -o $@ $^ -O3 -I${MUS_INC} -I${CADICAL_INC} -L${CADICAL_LIB_DIR} ${CADICAL_LIB}

gen_tar: src/*.cpp include/*.hpp Makefile
	mkdir mus && mkdir mus/src && cp src/*.cpp mus/src && mkdir mus/include && cp include/*.hpp mus/include && cp Makefile mus && tar -cvf mus.tar mus && rm -rf mus
