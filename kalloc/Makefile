COQMFFLAGS := -Q . VC \
			-Q /Users/linemeitongmaodejgaard/.opam/coq-8.17.1/lib/coq/user-contrib/iris iris 

ALLVFILES := kalloc.v clientsfun.v tactics.v ASI_kalloc.v Spec_kalloc.v kallocfun.v Verif_kalloc_kfree.v Verif_clients.v
build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
