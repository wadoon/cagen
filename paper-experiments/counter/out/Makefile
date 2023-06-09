CBMC_PARAM=--unwind 256 --external-sat-solver ~/work/kissat/build/kissat
CBMC=cbmc $(CBMC_PARAM)
LTLCHECK=/home/weigl/share/nuXmv-2.0.0-Linux/bin/nuXmv -source ltl.xmv
INVCHECK=/home/weigl/share/nuXmv-2.0.0-Linux/bin/nuXmv -source ic3.xmv
SEAHORN="./seahorn.sh"

PO_UpDown_refines_Interval:
	./time.sh "$(INVCHECK) PO_UpDown_refines_Interval.smv"

PO_Counter_fulfills_UpDown_simple_cbmc:
	./time.sh "$(CBMC) PO_Counter_fulfills_UpDown_simple.c"

PO_Counter_fulfills_UpDown_simple_seahorn:
	./time.sh "$(SEAHORN) PO_Counter_fulfills_UpDown_simple.c"

PO_CounterBroken_fulfills_UpDown_simple_cbmc:
	./time.sh "$(CBMC) PO_CounterBroken_fulfills_UpDown_simple.c"

PO_CounterBroken_fulfills_UpDown_simple_seahorn:
	./time.sh "$(SEAHORN) PO_CounterBroken_fulfills_UpDown_simple.c"

