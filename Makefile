MODULES := Common Utils LDef LProps OLDef OLProps LEval LEProps LEProps3 Tests Tests2 TestsR
VS      := $(MODULES:%=%.v)
PSF			:= ../../Coq/pierce_software_foundations_3.2

.PHONY: coq clean html rsync

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	coq_makefile -I . -I $(PSF) $(VS) -o Makefile.coq

# clean:: Makefile.coq
# 	$(MAKE) -f Makefile.coq clean
# 	rm -f Makefile.coq
clean:
	rm -f Makefile.coq *.v.d *.vo *.glob

html:: Makefile.coq
	$(MAKE) -f Makefile.coq html

$(MODULES:%=%.vo): Init.v


# A private rule to keep a copy of .v files in Dropbox.
RSYNC_FILES := *.v Makefile README.md html
rsync:
	rsync --itemize-changes --times --recursive --progress $(RSYNC_FILES) ~/Dropbox/Research/coq
