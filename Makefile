DIRS=TCB NTCB ASM

INCLUDES=$(patsubst %,-I %, $(DIRS))

COQLIBS:=-I ~/devel/cases/src -R ~/devel/cases/theories Case_Tactics

COQC=coqc -q $(INCLUDES) $(COQLIBS)
COQDEP=coqdep $(INCLUDES) $(COQLIBS)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) $(COQLIBS) -batch -load-vernac-source


OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  -I extraction $(INCLUDES)

VPATH=$(DIRS)
GPATH=$(DIRS)

NTCB=NSet.v Lib.v BinaryAux.v Validator.v DoOption.v ValidatorProof.v
TCB=BinaryDefs.v BinaryProps.v Semantics.v SemanticsProg.v LazyList.v ValidatorProp.v Memory.v
ASM=ASM.v

EXTRACTION=extraction.v

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

.PHONY: proof extraction


include .depend

FORCE:
