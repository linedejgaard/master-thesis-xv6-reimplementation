Require Import VST.floyd.proofauto.
Require Import VC.switch.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition twice_spec :=
  DECLARE _twice
    WITH n : Z
    PRE [ tint ]
      PROP  (Int.min_signed <= n+n <= Int.max_signed)
      PARAMS (Vint (Int.repr n))
      SEP ()
    POST [ tint ]
      PROP () RETURN (Vint (Int.repr (n+n)))
      SEP ().

Definition f_spec :=
    DECLARE _f
        WITH x : Z
        PRE [ tuint ]
        PROP  (0 <= x <= Int.max_unsigned)
        PARAMS (Vint (Int.repr x))
        SEP ()
      POST [ tint ]
        PROP () RETURN (Vint (Int.repr (1)))
        SEP ().


Definition Gprog : funspecs :=   ltac:(with_library prog [twice_spec; f_spec]).

Lemma body_twice: semax_body Vprog Gprog f_twice twice_spec.
Proof.
start_function.
forward_if (PROP() LOCAL (temp _n (Vint (Int.repr (n+n)))) SEP ()); repeat forward; entailer!.
Qed.

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function. 
Fail forward_if. 
forward_if (@FF (environ->mpred) _); (* this might be because all the cases leads to the same case.. *)
repeat forward.
Qed.




