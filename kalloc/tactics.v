(************************ Helper functions and tactics  *************************)

Require Import VST.floyd.proofauto.

Ltac auto_contradict := try discriminate; try contradiction.