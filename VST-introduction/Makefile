COQMFFLAGS := -Q . VC \
			-Q /Users/linemeitongmaodejgaard/.opam/coq-8.17.1/lib/coq/user-contrib/iris iris 

ALLVFILES := hints.v Preface.v sum.v helper.v ASI_kalloc.v Spec_kalloc.v VSU_kalloc_kfree_definitions.v client1.v
build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
