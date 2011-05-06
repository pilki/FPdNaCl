OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links


ifneq (,$(findstring CYGWIN,$(shell uname -s)))
SLN=cp
else
SLN=ln -s
endif

asm: asm.mll
	$(OCAMLBUILD) $(OCB_OPTIONS) asm.native \
        && rm -f asm && $(SLN) _build/asm.native asm

clean:
	rm -rf _build asm

.PHONY: asm clean
