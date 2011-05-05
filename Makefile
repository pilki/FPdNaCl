DIRS=TCB NTCB ASM

INCLUDES=$(patsubst %,-I %, $(DIRS))
include Makefile.conf

COQLIBS=-I $(CASES_TAC)/src -R $(CASES_TAC)/theories Case_Tactics

COQC=coqc -q $(INCLUDES) $(COQLIBS)
COQDEP=coqdep $(INCLUDES) $(COQLIBS)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) $(COQLIBS) -batch -load-vernac-source


OCAMLBUILD=ocamlbuild
OCB_INCLUDES=-I extraction $(INCLUDES)
OCB_QUICK_INCLUDES=-I quick_extraction $(INCLUDES)
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links


ifneq (,$(findstring CYGWIN,$(shell uname -s)))
SLN=cp
else
SLN=ln -s
endif


VPATH=$(DIRS)
GPATH=$(DIRS)

NTCB=NSet.v Lib.v BinaryAux.v Validator.v DoOption.v ValidatorProof.v
TCB=BinaryDefs.v BinaryProps.v Semantics.v SemanticsProg.v LazyList.v ValidatorProp.v Memory.v Byte.v
ASM=ASM.v


FILES=$(NTCB) $(TCB) $(ASM)

proof: $(FILES:.v=.vo)


extraction: extraction/extraction.v
	rm -f extraction/*.ml extraction/*.mli extraction/*.vo
	$(COQEXEC) extraction/extraction.v

#.PHONY: extraction

.SUFFIXES: .v .vo

.v.vo:
#	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob /dev/null $*.v

depend: $(FILES)
	$(COQDEP) $^ \
        > .depend

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -rf _build
	rm -f doc/coq2html.ml doc/coq2html
	rm -f extraction/*.ml extraction/*.mli


validator: glue.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) $(OCB_INCLUDES) glue.native \
        && rm -f validator && $(SLN) _build/glue.native validator

quick_validator: glue.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) $(OCB_QUICK_INCLUDES) glue.native \
        && rm -f validator && $(SLN) _build/glue.native validator

all:
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) validator



.PHONY: proof extraction validator quick_validator


include .depend

FORCE:
