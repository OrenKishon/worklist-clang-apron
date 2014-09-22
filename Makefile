LLVM_PATH=$(HOME)/llvm
APRON_PATH=$(HOME)/apron-0.9.9

include $(APRON_PATH)/Makefile.config

ICFLAGS = \
-I$(GMP_PREFIX)/include \
-I$(MPFR_PREFIX)/include \
-I$(APRON_PREFIX)/include \
-Wall -Wstrict-prototypes -Wimplicit-function-declaration \
    --std=c++0x -Wno-unused-parameter -Wno-undef -Wno-cast-align

# -std=c99
# -Winline -Wconversion

LCFLAGS = \
-L$(GMP_PREFIX)/lib \
-L$(MPFR_PREFIX)/lib \
-L$(APRON_PREFIX)/lib \
-L$(PPL_PREFIX)/lib \
-L$(CAMLIDL_PREFIX)/lib/ocaml

OCAMLINC = \
-I $(MLGMPIDL_PREFIX)/lib \
-I $(APRON_PREFIX)/lib

OCAMLLDFLAGS = \
-noautolink -ccopt "$(LCFLAGS)" \
bigarray.cma gmp.cma apron.cma \
box.cma oct.cma polka.cma ppl.cma \
-cclib "-lpolkaGrid_caml -lap_pkgrid_debug -lap_ppl_caml -lap_ppl_debug -lppl -lpolka_caml -lpolka_debug -loct_caml -loctMPQ -lbox_caml -lbox_debug -litv_debug -lapron_caml_debug -lapron_debug -lgmp_caml -lmpfr -lgmpxx -lgmp -lbigarray -lcamlidl"

OCAMLOPTLDFLAGS = \
-noautolink -verbose -ccopt "$(LCFLAGS)" \
bigarray.cmxa gmp.cmxa apron.cmxa box.cmxa polka.cmxa ppl.cmxa \
-cclib "-lpolkaGrid_caml -lap_pkgrid_debug -lap_ppl_caml -lap_ppl_debug -lppl -lpolka_caml -lpolka_debug -loct_caml -loctMPQ -lbox_caml -lbox_debug -litv_debug -lapron_caml_debug -lapron_debug -lgmp_caml -lmpfr -lgmpxx -lgmp -lbigarray -lcamlidl"

WORKLISTIFLAGS = \
    -I$(LLVM_PATH)/build/include \
    -I$(LLVM_PATH)/llvm/include \
    -I$(LLVM_PATH)/build/tools/clang/include \
    -I$(LLVM_PATH)/llvm/tools/clang/include/ $(ICFLAGS)

WORKLISTLFLAGS = -L$(LLVM_PATH)/build/Debug+Asserts/lib $(LCFLAGS) 

LIB = -fno-rtti \
      -lclangTooling -lclangDriver \
      -lclangFrontendTool \
      -lclangFrontend -lclangSerialization \
      -lclangCodeGen -lclangParse -lclangSema \
      -lclangStaticAnalyzerFrontend -lclangStaticAnalyzerCheckers \
      -lclangStaticAnalyzerCore -lclangAnalysis \
      -lclangARCMigrate -lclangRewriteFrontend \
      -lclangRewrite -lclangEdit \
      -lclangLex -lclangBasic \
      -lclangAST \
      -lclangASTMatchers \
      -lLLVMSupport -I~/opt/include/

all: C ml

# C examples

C: example1g

ss: selectionsortg

loop: loop_example_aprong

%g: %g.o
	$(CXX) $(CXXFLAGS) $(ICFLAGS) $(LCFLAGS) -o $@  $< -lpolka -loctMPQ -lboxMPQ_debug -lapron_debug -litvMPQ_debug -lmpfr -lgmp

%g.o: %.cpp
	$(CXX) $(CXXFLAGS_DEBUG) $(ICFLAGS) -c -o $@ $<

worklist: worklist.o
	$(CXX) -Wcast-align $(CXXFLAGS) $(WORKLISTIFLAGS) $(WORKLISTLFLAGS) -o $@ $< -lpolka -loctMPQ -lboxMPQ_debug -lapron_debug -litvMPQ_debug -lmpfr -lgmp $(LIB) `$(LLVM_PATH)/build/Debug+Asserts/bin/llvm-config --cxxflags --ldflags --libs all --system-libs`
    

worklist.o: worklist.cpp
	$(CXX) $(CXXFLAGS_DEBUG) $(WORKLISTIFLAGS) -c -o $@ $< `$(LLVM_PATH)/build/Debug+Asserts/bin/llvm-config --cxxflags --ldflags --libs all --system-libs`

# OCaml examples

ml: mlexample1.opt

mlexample%.opt: mlexample%.cmx
	$(OCAMLOPT) -cc "g++" $(OCAMLOPTFLAGS) $(OCAMLINC) $(OCAMLOPTLDFLAGS) -o $@ $<
test.opt: test.cmx
	$(OCAMLOPT) -cc "g++" $(OCAMLOPTFLAGS) $(OCAMLINC) $(OCAMLOPTLDFLAGS) -o $@ $<

%: %.cmo $(APRON_PREFIX)/bin/apronrun
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) $(OCAMLLDFLAGS) -g -use-runtime $(APRON_PREFIX)/bin/apronrun -o $@ $<

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) $(OCAMLINC) -c -o $@ $<

%.cmx: %.m -o $@ $<

#

clean:
	rm -f worklist loop_example_aprong example1g *.cm[ioxa] *.o mlexample1 mlexample2 mlexample3 mlexample4 mlexample5 *.opt selectionsortg loop

distclean: clean

dist: example1.c mlexample1.ml mlexample2.ml mlexample3.ml Makefile README
	(cd ..; tar zcvf examples.tgz $(^:%=examples/%))
