# Unix Makefile stub for separate compilation with Moscow ML.  

MOSMLHOME=$(HOME)/mosml
MOSMLTOOLS=camlrunm $(MOSMLHOME)/tools
MOSMLC=mosmlc -c -liberal
MOSMLL=mosmlc
MOSMLLEX=mosmllex
MOSMLYACC=mosmlyac

UNITS= -structure EA_implementation_sml -toplevel makeTables parseElectionData parseBLTFile random_ballots EA_main

.SUFFIXES :
.SUFFIXES : .sig .sml .ui .uo
 
all: EA

EA: EA_implementation_sml.uo makeTables.uo parseElectionData.uo parseBLTFile.uo random_ballots.uo EA_main.uo
	$(MOSMLL) -o EA EA_implementation_sml.uo makeTables.uo parseElectionData.uo random_ballots.uo EA_main.uo

clean:
	rm -f *.ui
	rm -f *.uo
	rm -f Makefile.bak

# these rules are only needed if UNITS is undefined or empty
.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: 
	rm -f Makefile.bak
	mv Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep $(UNITS) >> Makefile

### DO NOT DELETE THIS LINE
EA_implementation_sml.uo: EA_implementation_sml.sml 
	$(MOSMLC) -structure \
    EA_implementation_sml.sml 
makeTables.uo: makeTables.sml EA_implementation_sml.uo 
	$(MOSMLC) -toplevel \
    EA_implementation_sml.ui makeTables.sml 
parseElectionData.uo: parseElectionData.sml makeTables.uo 
	$(MOSMLC) -toplevel makeTables.ui \
    EA_implementation_sml.ui parseElectionData.sml 
parseBLTFile.uo: parseBLTFile.sml parseElectionData.uo 
	$(MOSMLC) -toplevel parseElectionData.ui makeTables.ui \
    EA_implementation_sml.ui parseBLTFile.sml 
random_ballots.uo: random_ballots.sml parseElectionData.uo 
	$(MOSMLC) -toplevel parseElectionData.ui makeTables.ui \
    EA_implementation_sml.ui random_ballots.sml 
EA_main.uo: EA_main.sml random_ballots.uo 
	$(MOSMLC) -toplevel random_ballots.ui parseBLTFile.ui parseElectionData.ui makeTables.ui \
    EA_implementation_sml.ui EA_main.sml 
