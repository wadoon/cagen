CBMC_PARAM=--unwind 256 --external-sat-solver ~/work/kissat/build/kissat
CBMC=cbmc $(CBMC_PARAM)
LTLCHECK=/home/weigl/share/nuXmv-2.0.0-Linux/bin/nuXmv -source ltl.xmv
SEAHORN="./seahorn.sh"


format:
	clang-format -i *.c

PO_AEBLogic_fulfills_AEBLogic_Spec_simple_cbmc:
	./time.sh "$(CBMC) PO_AEBLogic_fulfills_AEBLogic_Spec_simple.c"

PO_AEBLogic_fulfills_AEBLogic_Spec_simple_seahorn:
	./time.sh "$(SEAHORN) PO_AEBLogic_fulfills_AEBLogic_Spec_simple.c"

PO_TTCCalculation_fulfills_TTC_Spec_simple_cbmc:
	./time.sh "$(CBMC) PO_TTCCalculation_fulfills_TTC_Spec_simple.c"

PO_TTCCalculation_fulfills_TTC_Spec_simple_seahorn:
	./time.sh "$(SEAHORN) PO_TTCCalculation_fulfills_TTC_Spec_simple.c"

PO_StoppingTimeCalculation_fulfills_STC_simple_cbmc:
	./time.sh "$(CBMC) PO_StoppingTimeCalculation_fulfills_STC_simple.c"

PO_StoppingTimeCalculation_fulfills_STC_simple_seahorn:
	./time.sh "$(SEAHORN) PO_StoppingTimeCalculation_fulfills_STC_simple.c"

PO_Gt_fulfills_Gt_Spec_simple_cbmc:
	./time.sh "$(CBMC) PO_Gt_fulfills_Gt_Spec_simple.c"

PO_Gt_fulfills_Gt_Spec_simple_seahorn:
	./time.sh "$(SEAHORN) PO_Gt_fulfills_Gt_Spec_simple.c"

PO_AEBTop_composition_refine:
	./time.sh "$(LTLCHECK) PO_AEBTop_composition_refine.smv"
