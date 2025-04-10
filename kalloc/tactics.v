(************************ Helper functions and tactics  *************************)

Require Import VST.floyd.proofauto.

Ltac auto_contradict := try discriminate; try contradiction.

Ltac if_tac_auto_contradict :=
  if_tac; auto_contradict.

Definition PGSIZE : Z := 4096.