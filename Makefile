# COQC='/home/vladimir/.opam/default/bin/coqc'
COQC=coqc

all: extract
	dune build
	mv pcc.exe petitc

check: clean
	$(COQC) -Q . PetitC Star.v
	$(COQC) -Q . PetitC Permutation.v
	$(COQC) -Q . PetitC Sublist.v
	$(COQC) -Q . PetitC Tactics.v
	$(COQC) -Q . PetitC Ids.v
	$(COQC) -Q . PetitC Monad.v
	$(COQC) -Q . PetitC Values.v
	$(COQC) -Q . PetitC ValuesLemmas.v
	$(COQC) -Q . PetitC Memory.v
	$(COQC) -Q . PetitC MemoryLemmas.v
	$(COQC) -Q . PetitC Output.v
	$(COQC) -Q . PetitC InbuiltFunc.v
	$(COQC) -Q . PetitC InbuiltFuncSemantics.v
	$(COQC) -Q . PetitC InbuiltFuncLemmas.v
	$(COQC) -Q . PetitC TypedTree.v
	$(COQC) -Q . PetitC Semantics.v
	$(COQC) -Q . PetitC SemanticsLemmas.v
	$(COQC) -Q . PetitC Asm.v
	$(COQC) -Q . PetitC AsmSemantics.v
	$(COQC) -Q . PetitC MemoryEquivalence.v
	$(COQC) -Q . PetitC Codegen.v
	$(COQC) -Q . PetitC CodegenLemmas.v

extract: check
	$(COQC) -Q . PetitC Extraction.v

clean:
	rm -f *.vo *.glob *.vos *.vok
	rm -f Codegen.ml Codegen.mli
