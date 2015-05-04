MODULES := LDef LProps LEval Tests Tests2 LEProps LEProps3 Utils
VS      := $(MODULES:%=%.v)
PSF			:= ../../Coq/pierce_software_foundations_3.2

.PHONY: coq clean html rsync
	
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	coq_makefile -I $(PSF) -I . $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

html:: Makefile.coq
	$(MAKE) -f Makefile.coq html

# A private rule to keep a copy of .v files in Dropbox.
rsync:
	rsync --itemize-changes --times --progress *.v Makefile README.md ~/Dropbox/Research/coq
