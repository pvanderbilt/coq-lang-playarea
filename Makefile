MODULES := LDef LProps LEval Tests Tests2 LEProps3
VS      := $(MODULES:%=%.v)
PSF			:= ../../Coq/pierce_software_foundations_3.2

.PHONY: coq clean rsync
	
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	coq_makefile -I $(PSF) -I . $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

# A private rule to keep a copy of .v files in Dropbox.
rsync:
	rsync --itemize-changes --times --progress *.v ~/Dropbox/Research/coq