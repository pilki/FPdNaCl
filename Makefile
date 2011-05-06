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

all_quick:
	@$(MAKE) asm
	@$(MAKE) quick_validator

asm:
	@$(MAKE) -C assembly

test:
	@$(MAKE) -C test

# the validator built from the ml source on the git repo, not the extracted ones
quick_validator: glue.ml
	@echo "\nBuild the validator from the tracked sources, not the one extracted from the Coq files" \
	&& echo "To build from those source, please do \"make all\"\n"
	$(OCAMLBUILD) $(OCB_OPTIONS) $(OCB_QUICK_INCLUDES) glue.native \
        && rm -f validator && $(SLN) _build/glue.native validator
	@echo "\nTo run the tests: make test\n"


all:
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) validator
	$(MAKE) -C assembly

proof: $(FILES:.v=.vo)


extraction: extraction/extraction.v
	rm -f extraction/*.ml extraction/*.mli extraction/*.vo
	$(COQEXEC) extraction/extraction.v

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
	$(MAKE) -C assembly clean


validator: glue.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) $(OCB_INCLUDES) glue.native \
        && rm -f validator && $(SLN) _build/glue.native validator

.PHONY: proof extraction validator quick_validator all_quick asm test


-include .depend

FORCE:
