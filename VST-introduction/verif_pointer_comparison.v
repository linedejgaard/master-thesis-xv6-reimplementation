Require VC.Preface.  (* Check for the right version of VST *)

(* ----------------------------------------------------------------- *)
(** *** Standard boilerplate *)
Require Import VST.floyd.proofauto.
Require Import VC.pointer_comparison.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition pointer_comparison (p q : val) (cmp : comparison) : val :=
   force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp cmp p q))).

Definition PGSIZE : Z := 4096. 
Definition pointer_comparison_1_spec :=
   DECLARE _pointer_comparison_1
      WITH b:block, p:ptrofs, q:val
      PRE  [ tptr tvoid, tptr tvoid]
            PROP ()
            PARAMS (Vptr b p; q)
            SEP(denote_tc_test_order ((Vptr b (Ptrofs.add p (Ptrofs.repr (PGSIZE))))) q) 
      POST [ tint ]
            PROP()
            RETURN (
                pointer_comparison (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q Cle)
            SEP (denote_tc_test_order ((Vptr b (Ptrofs.add p (Ptrofs.repr (PGSIZE))))) q). 


Definition pointer_cmp_bool (p q : val) (cmp : comparison) : bool :=
    eq_dec (pointer_comparison p q cmp) (Vint (Int.repr 1)).

Definition pointer_le_bool (p q : val) : bool :=
    pointer_cmp_bool p q Cle.

Definition pointer_comparison_2_spec :=
    DECLARE _pointer_comparison_2
        WITH b:block, p:ptrofs, q:val
        PRE  [ tptr tvoid, tptr tvoid]
                PROP () 
                PARAMS (Vptr b p; q)
                SEP(denote_tc_test_order ((Vptr b (Ptrofs.add p (Ptrofs.repr (PGSIZE))))) q) 
        POST [ tint ]
                PROP()
                RETURN (if (pointer_le_bool (Vptr b (Ptrofs.add p (Ptrofs.repr (PGSIZE)))) q) 
                        then Vint (Int.repr (42))
                        else Vint (Int.repr (13))
                        )
                SEP (denote_tc_test_order ((Vptr b (Ptrofs.add p (Ptrofs.repr (PGSIZE))))) q). 


(******************** loop ******************)


Definition while_1_spec : ident * funspec :=
    DECLARE _while_1
    WITH n:Z
    PRE [ tint ]
        PROP ( 0 <= n <= Int.max_signed )
        PARAMS (Vint (Int.repr n))
        SEP ()
    POST [ tint ]
    EX s,
        PROP (n = s)
        RETURN (Vint (Int.repr s))
        SEP ().

Definition while_1_1_spec : ident * funspec :=
    DECLARE _while_1
    WITH n:Z
    PRE [ tint ]
        PROP ( 0 <= n /\ Z.add n 1 <= Int.max_signed )
        PARAMS (Vint (Int.repr n))
        SEP ()
    POST [ tint ]
    EX s:Z,
        PROP (s = (Z.add n 1))
        RETURN (Vint (Int.repr s))
        SEP ().


Definition while_2_spec : ident * funspec :=
    DECLARE _while_2
    WITH b_s:block, p_s:ptrofs, b_e:block, p_e:ptrofs
    PRE [ tptr tvoid, tptr tvoid ]
        PROP ( ( (Ptrofs.unsigned p_s)<= (Ptrofs.unsigned p_e)) /\ 
                0 <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) <= Int.max_signed 
                )
        PARAMS (Vptr b_s p_s; Vptr b_e p_e)
        SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e))
    POST [ tptr tvoid ]
    EX p_s_final,
        PROP (Ptrofs.unsigned (Ptrofs.add p_s_final (Ptrofs.repr (PGSIZE))) > Ptrofs.unsigned p_e)
        RETURN (Vptr b_s p_s_final)
        SEP ().

Definition for_1_spec : ident * funspec :=
    DECLARE _for_1
    WITH n:Z
    PRE [ tint ]
        PROP ( 0 <= n <= Int.max_signed )
        PARAMS (Vint (Int.repr n))
        SEP ()
    POST [ tint ]
    EX sum,
        PROP (n = sum)
        RETURN (Vint (Int.repr sum))
        SEP ().


Definition for_1_1_spec : ident * funspec :=
    DECLARE _for_1_1
    WITH n:Z
    PRE [ tint ]
        PROP ( 0 <= n /\ Z.add n 1 <= Int.max_signed )
        PARAMS (Vint (Int.repr n))
        SEP ()
    POST [ tint ]
    EX s:Z,
        PROP (s = (Z.add n 1))
        RETURN (Vint (Int.repr s))
        SEP ().


Definition for_2_spec : ident * funspec :=
    DECLARE _for_2
    WITH  b_s:block, p_s:ptrofs, b_e:block, p_e:ptrofs
    PRE [ tptr tvoid, tptr tvoid ]
        PROP ( 0 <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) <= Int.max_signed )
        PARAMS (Vptr b_s p_s; Vptr b_e p_e)
        SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e))
    POST [ tint ]
    EX sum,
        PROP (0 <= sum <= Int.max_signed /\ 
            (PGSIZE * sum) <= Ptrofs.unsigned (Ptrofs.sub p_e p_s) 
        )
        RETURN (Vint (Int.repr sum))
        SEP ().
(*********************************************)

Definition Gprog : funspecs := [
pointer_comparison_1_spec; 
pointer_comparison_2_spec;
while_1_spec; while_1_1_spec;
for_1_spec; for_1_1_spec;
while_2_spec
].


Lemma cmp_le_is_either_0_or_1 : forall p q i,
   sem_cmp_pp Cle p q = Some (Vint i) ->
   (i = Int.zero) \/ (i = Int.one).
Proof.
intros.
destruct (eq_dec i Int.zero). left; auto.
destruct (eq_dec i Int.one). right; auto.
unfold sem_cmp_pp in H. inversion H.
unfold bool2val in H1. unfold Z.b2z in H1. unfold option_map in H1.
destruct (Val.cmplu_bool true2 Cle p q).
- destruct b; inversion H1; exfalso.
   + apply n0; auto.
   + apply n; auto.
- inversion H1.
Qed.

Lemma body_pointer_comparison_1: semax_body Vprog Gprog f_pointer_comparison_1 pointer_comparison_1_spec.
Proof. start_function. forward. Qed.

Lemma body_pointer_comparison_2: semax_body Vprog Gprog f_pointer_comparison_2 pointer_comparison_2_spec.
Proof. start_function. 
assert (sem_cmp_pp Cle
(Vptr b (Ptrofs.add p (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 4096))))) q =
sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) q) by auto. 
assert (sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q =
sem_cmp_pp Cle (Vptr b (Ptrofs.add p
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 4096))))) q
) by auto. 
forward_if.
- forward.
    entailer!. 
    destruct (pointer_le_bool (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q) eqn:e; auto.
    rewrite H in H1.
    destruct (sem_cmp_pp Cle
    (Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) q) eqn:e2; try discriminate; try contradiction.
    destruct v; try discriminate; try contradiction.
    apply typed_true_tint_Vint in H1.
    assert (i = Int.zero \/ i = Int.one). {
        apply cmp_le_is_either_0_or_1 with (p:= Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) (q:=q); auto.
    }
    destruct H2; try contradiction.
    unfold pointer_le_bool in e. unfold pointer_cmp_bool in e.
    unfold pointer_comparison in e.
    rewrite H0 in e. rewrite H in e. rewrite H2 in e.
    try discriminate.
- forward. entailer!.
    destruct (pointer_le_bool (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q) eqn:e; auto.
    rewrite H in H1.
    destruct (sem_cmp_pp Cle
    (Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) q) eqn:e2; try discriminate; try contradiction.
    destruct v; try discriminate; try contradiction.
    apply typed_false_tint_Vint in H1.
    assert (i = Int.zero \/ i = Int.one). {
        apply cmp_le_is_either_0_or_1 with (p:= Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) (q:=q); auto.
    }
    destruct H2; try contradiction.
    +unfold pointer_le_bool in e. unfold pointer_cmp_bool in e.
    unfold pointer_comparison in e.
    assert (sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q =
    sem_cmp_pp Cle (Vptr b (Ptrofs.add p
        (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 4096))))) q
    ) by auto. 
    rewrite H3 in e. rewrite H in e. rewrite H2 in e.
    try discriminate. 
    + rewrite H1 in H2. inversion H2.
Qed.


Lemma body_pointer_comparison_3: semax_body Vprog Gprog f_pointer_comparison_3 pointer_comparison_2_spec.
Proof. start_function. 
assert (sem_cmp_pp Cle
(Vptr b (Ptrofs.add p (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 4096))))) q =
sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) q) by auto. 
assert (sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q =
sem_cmp_pp Cle (Vptr b (Ptrofs.add p
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 4096))))) q
) by auto. 
forward_if.
- forward.
    entailer!. 
    destruct (pointer_le_bool (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q) eqn:e; auto.
    rewrite H in H1.
    destruct (sem_cmp_pp Cle
    (Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) q) eqn:e2; try discriminate; try contradiction.
    destruct v; try discriminate; try contradiction.
    apply typed_true_tint_Vint in H1.
    assert (i = Int.zero \/ i = Int.one). {
        apply cmp_le_is_either_0_or_1 with (p:= Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) (q:=q); auto.
    }
    destruct H2; try contradiction.
    unfold pointer_le_bool in e. unfold pointer_cmp_bool in e.
    unfold pointer_comparison in e.
    rewrite H0 in e. rewrite H in e. rewrite H2 in e.
    try discriminate.
- forward. entailer!.
    destruct (pointer_le_bool (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q) eqn:e; auto.
    rewrite H in H1.
    destruct (sem_cmp_pp Cle
    (Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) q) eqn:e2; try discriminate; try contradiction.
    destruct v; try discriminate; try contradiction.
    apply typed_false_tint_Vint in H1.
    assert (i = Int.zero \/ i = Int.one). {
        apply cmp_le_is_either_0_or_1 with (p:= Vptr b (Ptrofs.add p (Ptrofs.of_ints (Int.repr 4096)))) (q:=q); auto.
    }
    destruct H2; try contradiction.
    +unfold pointer_le_bool in e. unfold pointer_cmp_bool in e.
    unfold pointer_comparison in e.
    assert (sem_cmp_pp Cle (Vptr b (Ptrofs.add p (Ptrofs.repr PGSIZE))) q =
    sem_cmp_pp Cle (Vptr b (Ptrofs.add p
        (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 4096))))) q
    ) by auto. 
    rewrite H3 in e. rewrite H in e. rewrite H2 in e.
    try discriminate. 
    + rewrite H1 in H2. inversion H2.
Qed.


Lemma body_while_1: semax_body Vprog Gprog f_while_1 while_1_spec.
Proof. start_function. forward.
forward_while
 (EX i: Z,
   PROP  (0 <= i <= n)
   LOCAL (temp _s (Vint (Int.repr i)); temp _n (Vint (Int.repr n)))
   SEP   ()).
   - Exists 0; entailer.
   - entailer.
   - forward; entailer!. EExists. inversion HRE. entailer!. rep_lia.
   - forward. assert (i = n) by lia. Exists i. entailer!. (* *)
Qed. 


Lemma body_while_1_1: semax_body Vprog Gprog f_while_1_1 while_1_1_spec.
Proof. start_function. forward.
forward_while
 (EX i: Z,
   PROP  (0 <= i <= n + 1)
   LOCAL (temp _s (Vint (Int.repr i)); temp _n (Vint (Int.repr n)))
   SEP ()).
   - Exists 0; entailer.
   - entailer.
   - forward; entailer. try rep_lia. Exists (i + 1). entailer!. 
   - forward. assert (i = n + 1) by lia. Exists i. entailer!. (* *)
Qed. 


Lemma body_for_1: semax_body Vprog Gprog f_for_1 for_1_spec.
Proof. start_function. forward. 
forward_loop
(EX i: Z,
  PROP (0 <= i <= n)
  LOCAL (temp _s (Vint (Int.repr i)); temp _n (Vint (Int.repr n)))
  SEP ())
break:
(EX s_final: Z,
  PROP (s_final = n)
  LOCAL (temp _s (Vint (Int.repr s_final)); temp _n (Vint (Int.repr n)))
  SEP ()).
  - Exists 0; entailer.
  - Intros i. forward_if. 
    + forward. Exists (i+1). entailer.
    + forward. assert (i = n) by lia. Exists i. entailer.
  - Intros s_final. forward. EExists. entailer!.
Qed.

Lemma body_for_1_1: semax_body Vprog Gprog f_for_1_1 for_1_1_spec.
Proof. start_function. forward. (*unfold abbreviate in POSTCONDITION.*)
    forward_loop
    (EX i: Z,
    PROP (0 <= i <= n + 1)
    LOCAL (temp _s (Vint (Int.repr i)); temp _n (Vint (Int.repr n)))
    SEP ())
    break:
    (EX s_final: Z,
    PROP (s_final = Z.add n 1)
    LOCAL (temp _s (Vint (Int.repr s_final)); temp _n (Vint (Int.repr n)))
    SEP ()).
   - Exists 0; entailer.
   - Intros i. forward_if. 
   + forward. Exists (i+1). entailer.
   + forward. assert (i = n + 1) by lia. Exists i. entailer.
   -  Intros s_final. forward. EExists. entailer!. 
Qed. 





(*** working in progress *)


Lemma body_for_2: semax_body Vprog Gprog f_for_2 for_2_spec.
Proof. start_function. forward. 

    forward_loop
    (* loop inv. *)
    (EX s_start: Z,  EX p_s_temp,
    PROP (0 <= s_start <= Ptrofs.unsigned (Ptrofs.sub p_e p_s))
    LOCAL (temp _s (Vint (Int.repr s_start)); 
           temp _pa_start (Vptr b_s p_s_temp);
           temp _pa_end (Vptr b_e p_e))
    SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s_temp (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e)))

    break:

    (* loop post *)
    (EX s_final: Z, EX p_s_final,
    PROP (0 <= s_final <= Int.max_signed /\ 
        PGSIZE * s_final <= Ptrofs.unsigned (Ptrofs.sub p_e p_s))
    LOCAL (temp _s (Vint (Int.repr s_final)); 
        temp _pa_start (Vptr b_s p_s_final);
            temp _pa_end (Vptr b_e p_e))
    SEP (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s_final (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e))).

  - Exists 0; EExists. entailer!.
  - Intros i. Intros p_s_temp. forward_if. 
    + forward. entailer!. admit. forward. EExists. EExists. entailer!. admit. entailer!. admit.
    + forward. EExists. EExists. entailer. admit. (* helpt to insert denote.. in the post condition after break*)
  - Intros s_final. Intros p_s_final. forward. EExists. entailer. admit.
Admitted.

NÅET HERTIL1!!!!
Jeg er i gang med forloop og at tælle sider. s er så mange gange vi får kaldt kfree..
men jeg er i tvivl om, hvordan for_loop skal være og om min pre-condition er korrekt.

  

Lemma body_while_2: semax_body Vprog Gprog f_while_2 while_2_spec.
Proof. start_function. 
forward_while
 (EX p_s_tmp: ptrofs,
   PROP  (

        0 <= Ptrofs.unsigned (Ptrofs.sub p_e p_s_tmp) <= Int.max_signed
            )
   LOCAL (temp _pa_start (Vptr b_s p_s_tmp);  temp _pa_end (Vptr b_e p_e))
   SEP   (denote_tc_test_order ((Vptr b_s (Ptrofs.add p_s_tmp (Ptrofs.repr (PGSIZE))))) (Vptr b_e p_e))).
   - EExists. entailer!.
   - entailer.
   - forward; entailer!. Exists ((Ptrofs.add p_s_tmp (Ptrofs.repr PGSIZE))). inversion HRE. entailer!. entailer!; try rep_lia. inversion HRE. try rep_lia.



  
  forward. entailer. Exists (i+1). Exists ((Ptrofs.add p_s_temp (Ptrofs.repr PGSIZE))).
    entailer!. split; try rep_lia. destruct H0; try rep_lia
  + forward. assert (i = n) by lia. Exists i. entailer.
- Intros s_final. forward. EExists. entailer!.


forward_loop
(EX i: Z,
  PROP (0 <= i <= n)
  LOCAL (temp _s (Vint (Int.repr i)); temp _n (Vint (Int.repr n)))
  SEP ())
break:
(EX s_final: Z,
  PROP (s_final = n)
  LOCAL (temp _s (Vint (Int.repr s_final)); temp _n (Vint (Int.repr n)))
  SEP ()).
  - Exists 0; entailer.
  - Intros i. forward_if. 
    + forward. Exists (i+1). entailer.
    + forward. assert (i = n) by lia. Exists i. entailer.
  - Intros s_final. forward. EExists. entailer!.
Qed.
