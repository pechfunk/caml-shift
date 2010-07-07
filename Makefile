# Building the library of delimited continuations and the corresponding ocaml
# top level.
# 	make all
#	     to build the libraries
#	make top
#	     to build the top level
#	make install
#	     to install the libraries
#	make testd0
#	     to build and run the tests
#	make tests0
#	     to build and run the continuation serialization test
#	make memory_leak1
#	     to build and run the memory leak test. It should run forever
#	     in constant memory
#	make memory_leak_plugged
#	     to build and run another memory leak test. See the comments
#	     in the source code.
#       make bench_exc
#	     to benchmark delimcc's abort, comparing with native exceptions
#
# This Makefile is based on the one included in the callcc distribution
# by Xavier Leroy
#
# $Id: Makefile,v 1.6 2006/02/07 00:33:52 oleg Exp $

# To compile the library, we need a few files that are not normally
# installed by the OCaml distribution.
# We only need .h files from the directory $OCAMLSOURCES/byterun/
# If you don't have the OCaml distribution handy, the present distribution
# contains the copy, in the directory ocaml-byterun
# That copy corresponds to the ia32 platform. For other platforms,
# you really need a configured OCaml distribution.

#OCAMLINCLUDES=../../byterun
#OCAMLINCLUDES=./ocaml-byterun-3.09
#OCAMLINCLUDES=./ocaml-byterun-3.10
OCAMLINCLUDES=./ocaml-byterun-3.11
# Directory of your OCAML executables...
#OCAMLBIN=../../bin
#OCAMLBIN=`dirname $$(which ocaml)`

#OCAMLC=$(OCAMLBIN)/ocamlc
#OCAMLTOP=$(OCAMLBIN)/ocaml
#OCAMLMKLIB=$(OCAMLBIN)/ocamlmklib
#OCAMLMKTOP=$(OCAMLBIN)/ocamlmktop

#If you have ocamlfind, use these
OCAMLFIND:=ocamlfind
OCAMLC:=$(OCAMLFIND) ocamlc
OCAMLMKLIB:=ocamlmklib
OCAMLMKTOP:=$(OCAMLFIND) ocamlmktop -package "caml-shift"
LIBDIR=`$(OCAMLFIND) printconf stdlib`

STDINCLUDES=$(LIBDIR)/caml
STUBLIBDIR=$(LIBDIR)/stublibs
CC=gcc
CFLAGS=-fPIC -Wall -I$(OCAMLINCLUDES) -I$(STDINCLUDES) -O
RANLIB=ranlib

.SUFFIXES: .ml .mli .cmo .cmi .tex .pdf

all: libdelimcc.a delimcc.cma

libdelimcc.a: stacks.o
	$(OCAMLMKLIB) -oc delimcc stacks.o -R .

delimcc.cma: delimcc.cmo
	$(OCAMLMKLIB) -o delimcc -oc delimcc delimcc.cmo -R .

install:
	if test -f dlldelimcc.so; then cp dlldelimcc.so $(STUBLIBDIR); fi
	cp libdelimcc.a $(LIBDIR)
	cd $(LIBDIR) && $(RANLIB) libdelimcc.a
	cp delimcc.cma delimcc.cmi $(LIBDIR)

findlib-install: delimcc.cma
	$(OCAMLFIND) install caml-shift META delimcc.cma delimcc.cmi dlldelimcc.so 	

.mli.cmi:
	$(OCAMLC) -c $*.mli
.ml.cmo:
	$(OCAMLC) -c $*.ml

top:	libdelimcc.a delimcc.cma
	$(OCAMLMKTOP) -o ocamltopcc delimcc.cma

.PRECIOUS: testd0
testd0: libdelimcc.a testd0.ml delimcc.cmi
	$(OCAMLC) -o $@ -dllpath . delimcc.cma  $@.ml
	./testd0

# serialization test
.PRECIOUS: tests0
tests0: libdelimcc.a tests0.ml delimcc.cmi
	$(OCAMLC) -o $@ -dllpath . delimcc.cma $@.ml
	./$@
	./$@ /tmp/k1

clean::
	rm -f testd0 tests0

delimcc.cmo: delimcc.cmi

clean::
	rm -f *.cm[io] *.[oa] *~


memory%: libdelimcc.a memory%.ml libdelimcc.a delimcc.cmi
	$(OCAMLC) -o $@ -dllpath . delimcc.cma $@.ml
	./$@ > /dev/null

%: libdelimcc.a %.ml libdelimcc.a delimcc.cmi
	$(OCAMLC) -o $@ -dllpath . delimcc.cma $@.ml
	./$@

export BIBTEX := bibtex -min-crossrefs=9999

.tex.pdf:
	texi2dvi -b --pdf $<

