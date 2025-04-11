Require Import VST.floyd.proofauto.

Require Import VC.tactics.
Require Import VC.ASI_kalloc.
Require Import VC.kalloc.
Require Import VC.kallocfun.


(* THIS SHOULD CONTAIN ANY INTERNAL FUNCTIONS... I DON'T HAVE ANY *)
Definition kalloc_token_sz (sh: share) (n: Z) (p: val) : mpred :=
  !! ((*field_compatible t_run [] p /\*)
      0 < n <= PGSIZE
      /\ malloc_compatible (n) p 
      /\ malloc_compatible (PGSIZE) p
      /\ writable_share sh
      (*/\  maybe some alignment and physical address checks here *))
  && memory_block sh (n) (p).

Lemma kalloc_token_sz_valid_pointer:
  forall (sh : share) (sz : Z) (p : val),
  kalloc_token_sz sh sz p |-- valid_pointer p.
Proof.
  intros. 
  unfold kalloc_token_sz. entailer.
Qed.

Lemma  kalloc_token_sz_local_facts : 
 forall (sh : share) (n:Z) (p : val) ,
   kalloc_token_sz sh n p |-- (!! (
    0 < n <= PGSIZE
    /\ malloc_compatible (n) p 
    /\ malloc_compatible (PGSIZE) p
    /\ writable_share sh
    /\ malloc_compatible n p) && memory_block sh (n) (p)).
Proof.
  intros. 
  unfold kalloc_token_sz. simpl. entailer.
Qed.

Lemma kalloc_token_sz_split:
forall  (sh: share) (n: Z) (p: val),
  kalloc_token_sz sh n p =
  !! ((*field_compatible t_run [] p /\*)
  0 < n <= PGSIZE
  /\ malloc_compatible (n) p 
  /\ malloc_compatible (PGSIZE) p
  /\ writable_share sh
  (*/\  maybe some alignment and physical address checks here *))
  && memory_block sh (n) (p).
Proof.
  intros. apply pred_ext.
  - unfold kalloc_token_sz. entailer.
  - unfold kalloc_token_sz. entailer!.
Qed.

Fixpoint  kalloc_tokens_sz (sh: share) (type_sz: Z) (p: val) (pgsize: Z) (n:nat): mpred :=
  match n with
  | S n' => 
      sepcon
      (kalloc_token_sz sh type_sz p)
      (kalloc_tokens_sz sh type_sz (offset_val pgsize p) pgsize n') (* Move to the next slot *)
  | O => !! (p = nullval) && emp
  end.

Definition  kalloc_tokens_sz_range (sh: share) (type_sz:Z) (p_start p_end: val) (pgsize: Z) := (* size is pgsize, sz is size of token*)
    match p_start, p_end with
    | Vptr b_s p_s, Vptr b_e p_e =>
      if (sameblock p_start p_end) then
         kalloc_tokens_sz sh type_sz p_start pgsize (Z.to_nat (compute_c p_start p_end pgsize))
      else !! (p_start = nullval) && emp
    | _ , _ => !! (p_start = nullval) && emp
    end.

Arguments  kalloc_tokens_sz_range sh type_sz p_start p_end pgsize : simpl never.

Lemma  kalloc_tokens_sz_local_prop: forall sh type_sz n p pgsize, 
   kalloc_tokens_sz sh type_sz p pgsize n |--  !! (is_pointer_or_null p /\ (n=0<->p=nullval) /\ (n>0<->isptr p))%nat.
Proof.
  intros.
  generalize dependent p.
  induction n as [| n' IH].
  - unfold  kalloc_tokens_sz. entailer!. split; split; intros; auto; auto_contradict; try rep_lia.
  - unfold  kalloc_tokens_sz; fold  kalloc_tokens_sz. intros. sep_apply IH. entailer!. destruct p; auto_contradict.
  split; split; intros; try rep_lia; auto; auto_contradict.
  + split; intros; auto_contradict.
  + split; intros; auto; rep_lia.
Qed.
#[export] Hint Resolve  kalloc_tokens_sz_local_prop : saturate_local.

Definition kfree_loop_spec' (K:KallocFreeAPD) {cs: compspecs} := 
  DECLARE _kfree_loop
  WITH sh : share, pa1:val, original_freelist_pointer:val, xx:Z, gv:globals, ls : list val, n:Z, type_sz:Z, pgsize:Z
  PRE [ tptr tvoid, tint ]
      PROP(
          isptr pa1 /\
          Int.min_signed <= Int.signed (Int.repr n) + Int.signed (Int.repr 1) <= Int.max_signed /\
          0 <= n <= Int.max_signed
      ) 
      PARAMS (pa1; Vint (Int.repr n)) GLOBALS(gv)
      SEP (
           kalloc_tokens_sz sh type_sz pa1 pgsize (Z.to_nat n)%nat *
          ASI_kalloc.mem_mgr K gv sh ls xx original_freelist_pointer
      )
  POST [ tvoid ]
      EX head, EX added_elem, (* TODO: fix top and next is the same?? *)
      PROP( 
          added_elem = (pointers_with_original_head (Z.to_nat n) (pa1) PGSIZE original_freelist_pointer) /\
          head = (hd nullval ((pointers_with_original_head (Z.to_nat n+1) (pa1) PGSIZE original_freelist_pointer)++ls))
          )
          RETURN () (* we return the head like in the pop function*)
          SEP 
          (
            ASI_kalloc.mem_mgr K gv sh (added_elem++ls) xx head
          ).

(***** kalloc token size ******)

Definition Tok_APD := Build_KallocTokenAPD kalloc_token_sz kalloc_token_sz_valid_pointer
  kalloc_token_sz_local_facts.

Definition mem_mgr (gv: globals) (sh : share) (ls: list val) (xx:Z) (original_freelist_pointer:val): mpred := (* I am unsure how to access all these elements.. *)
    !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
      (freelistrep sh ls original_freelist_pointer)).

(************ lemmas etc. *************)
Lemma mem_mgr_split: 
 forall (gv:globals) (sh:share) (ls: list val) (xx:Z) (original_freelist_pointer:val),
  mem_mgr gv sh ls xx original_freelist_pointer
  = 
  !! (writable_share sh /\
        is_pointer_or_null original_freelist_pointer /\
              (((ls = nil) /\ original_freelist_pointer = nullval) \/ 
              ((ls <> nil) /\ isptr original_freelist_pointer))
        ) &&
      (sepcon (data_at sh t_struct_kmem (Vint (Int.repr xx), original_freelist_pointer) (gv _kmem))
      (freelistrep sh ls original_freelist_pointer)).
Proof.
  intros. apply pred_ext.
  - unfold mem_mgr. entailer!.
  - unfold mem_mgr. entailer!.
Qed.

(************ lemmas etc. end *************)

Definition KF_APD := Build_KallocFreeAPD Tok_APD mem_mgr.

(*+ specs of private functions *)


Definition MF_Vprog : varspecs. mk_varspecs prog. Defined.

Definition MF_internal_specs: funspecs :=
    [].
   (*++ _malloc _free.*)

(*Definition MF_Imports:funspecs := Mmap0_ASI _mmap0 _munmap.*)

Definition MF_Gprog:funspecs := (*MF_Imports ++*) MF_internal_specs.
(* I don't think I have any internal specs netiher MF imports..*)

Ltac start_function_hint ::= idtac. (* no hint reminder *)

