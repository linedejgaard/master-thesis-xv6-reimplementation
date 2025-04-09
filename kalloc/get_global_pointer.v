From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "get_global_pointer.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _align_pointer : ident := $"align_pointer".
Definition _alloc : ident := $"alloc".
Definition _call_kfree1 : ident := $"call_kfree1".
Definition _call_kfree1_if_1 : ident := $"call_kfree1_if_1".
Definition _end : ident := $"end".
Definition _fl : ident := $"fl".
Definition _free : ident := $"free".
Definition _freelist : ident := $"freelist".
Definition _freelist1 : ident := $"freelist1".
Definition _freerange : ident := $"freerange".
Definition _freerange_no_loop : ident := $"freerange_no_loop".
Definition _freerange_no_loop_no_add : ident := $"freerange_no_loop_no_add".
Definition _get_freelist : ident := $"get_freelist".
Definition _get_freelist1 : ident := $"get_freelist1".
Definition _get_freelist1_input : ident := $"get_freelist1_input".
Definition _get_i : ident := $"get_i".
Definition _get_xx : ident := $"get_xx".
Definition _head : ident := $"head".
Definition _i : ident := $"i".
Definition _kalloc1 : ident := $"kalloc1".
Definition _kfree1 : ident := $"kfree1".
Definition _kmem : ident := $"kmem".
Definition _lst : ident := $"lst".
Definition _main : ident := $"main".
Definition _next : ident := $"next".
Definition _p : ident := $"p".
Definition _pa : ident := $"pa".
Definition _pa_end : ident := $"pa_end".
Definition _pa_start : ident := $"pa_start".
Definition _pointer : ident := $"pointer".
Definition _pointer_compare : ident := $"pointer_compare".
Definition _pointer_compare_0 : ident := $"pointer_compare_0".
Definition _pointer_compare_1 : ident := $"pointer_compare_1".
Definition _pointer_compare_10 : ident := $"pointer_compare_10".
Definition _pointer_compare_2 : ident := $"pointer_compare_2".
Definition _pointer_compare_3 : ident := $"pointer_compare_3".
Definition _pointer_compare_4 : ident := $"pointer_compare_4".
Definition _pointer_compare_5 : ident := $"pointer_compare_5".
Definition _pointer_compare_6 : ident := $"pointer_compare_6".
Definition _pointer_compare_7 : ident := $"pointer_compare_7".
Definition _pointer_compare_70 : ident := $"pointer_compare_70".
Definition _pointer_compare_8 : ident := $"pointer_compare_8".
Definition _pointer_compare_9 : ident := $"pointer_compare_9".
Definition _pointer_compare_values : ident := $"pointer_compare_values".
Definition _q : ident := $"q".
Definition _r : ident := $"r".
Definition _run : ident := $"run".
Definition _s : ident := $"s".
Definition _struct_kmem : ident := $"struct_kmem".
Definition _t : ident := $"t".
Definition _tail : ident := $"tail".
Definition _xx : ident := $"xx".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.

Definition v_freelist1 := {|
  gvar_info := (tptr (Tstruct _run noattr));
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get_freelist1 := {|
  fn_return := (tptr (Tstruct _run noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _run noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Evar _freelist1 (tptr (Tstruct _run noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _run noattr))))))
|}.

Definition f_get_freelist1_input := {|
  fn_return := (tptr (Tstruct _run noattr));
  fn_callconv := cc_default;
  fn_params := ((_fl, (tptr (Tstruct _run noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Etempvar _fl (tptr (Tstruct _run noattr)))))
|}.

Definition v_i := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get_i := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence (Sset _t'1 (Evar _i tint)) (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition v_kmem := {|
  gvar_info := (Tstruct _struct_kmem noattr);
  gvar_init := (Init_space 16 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get_xx := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _xx tint))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_get_freelist := {|
  fn_return := (tptr (Tstruct _run noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _run noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
      (tptr (Tstruct _run noattr))))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _run noattr))))))
|}.

Definition f_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) ::
                (_tail, (tptr (Tstruct _run noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _run noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Ecast (Etempvar _pa (tptr tvoid)) (tptr (Tstruct _run noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _run noattr)))
          (Tstruct _run noattr)) _next (tptr (Tstruct _run noattr)))
      (Etempvar _tail (tptr (Tstruct _run noattr))))
    (Sset _tail (Etempvar _r (tptr (Tstruct _run noattr))))))
|}.

Definition f_alloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_lst, (tptr (Tstruct _run noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_head, (tptr (Tstruct _run noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _head (Etempvar _lst (tptr (Tstruct _run noattr))))
  (Ssequence
    (Sifthenelse (Etempvar _head (tptr (Tstruct _run noattr)))
      (Sset _lst
        (Efield
          (Ederef (Etempvar _head (tptr (Tstruct _run noattr)))
            (Tstruct _run noattr)) _next (tptr (Tstruct _run noattr))))
      Sskip)
    (Sreturn (Some (Ecast (Etempvar _head (tptr (Tstruct _run noattr)))
                     (tptr (Tstruct _run noattr)))))))
|}.

Definition f_kfree1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _run noattr))) ::
               (_t'1, (tptr (Tstruct _run noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Ecast (Etempvar _pa (tptr tvoid)) (tptr (Tstruct _run noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
          (tptr (Tstruct _run noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _run noattr)))
            (Tstruct _run noattr)) _next (tptr (Tstruct _run noattr)))
        (Etempvar _t'1 (tptr (Tstruct _run noattr)))))
    (Sassign
      (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
        (tptr (Tstruct _run noattr)))
      (Etempvar _r (tptr (Tstruct _run noattr))))))
|}.

Definition f_kalloc1 := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _run noattr))) ::
               (_t'1, (tptr (Tstruct _run noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _r
    (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
      (tptr (Tstruct _run noattr))))
  (Ssequence
    (Sifthenelse (Etempvar _r (tptr (Tstruct _run noattr)))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _r (tptr (Tstruct _run noattr)))
              (Tstruct _run noattr)) _next (tptr (Tstruct _run noattr))))
        (Sassign
          (Efield (Evar _kmem (Tstruct _struct_kmem noattr)) _freelist
            (tptr (Tstruct _run noattr)))
          (Etempvar _t'1 (tptr (Tstruct _run noattr)))))
      Sskip)
    (Sreturn (Some (Ecast (Etempvar _r (tptr (Tstruct _run noattr)))
                     (tptr tvoid))))))
|}.

Definition f_call_kfree1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None (Evar _kfree1 (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
  ((Etempvar _pa (tptr tvoid)) :: nil))
|}.

Definition f_call_kfree1_if_1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Etempvar _pa (tptr tvoid))
  (Scall None
    (Evar _kfree1 (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _pa (tptr tvoid)) :: nil))
  Sskip)
|}.

Definition f_pointer_compare_0 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tint)) :: (_q, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oeq (Etempvar _p (tptr tint))
                 (Etempvar _q (tptr tint)) tint)))
|}.

Definition f_pointer_compare_1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tschar)) :: (_q, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oeq (Etempvar _p (tptr tschar))
                 (Etempvar _q (tptr tschar)) tint)))
|}.

Definition f_pointer_compare_2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tint)) :: (_q, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Ole (Etempvar _p (tptr tint))
                 (Etempvar _q (tptr tint)) tint)))
|}.

Definition f_pointer_compare_3 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tint)) :: (_q, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _p (tptr tint))
                 (Etempvar _q (tptr tint)) tint)
    (Sreturn (Some (Econst_int (Int.repr 42) tint)))
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_pointer_compare_4 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tschar)) :: (_q, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _p (tptr tschar))
                 (Etempvar _q (tptr tschar)) tint)
    (Sreturn (Some (Econst_int (Int.repr 42) tint)))
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_pointer_compare_5 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: (_q, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _p (tptr tvoid))
                 (Etempvar _q (tptr tvoid)) tint)
    (Sreturn (Some (Econst_int (Int.repr 42) tint)))
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_pointer_compare_6 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: (_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Ecast (Etempvar _pa (tptr tvoid)) (tptr tschar))
                 (Etempvar _end (tptr tvoid)) tint)
    (Sreturn (Some (Econst_int (Int.repr 42) tint)))
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_pointer_compare_70 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: (_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Etempvar _pa (tptr tvoid))
    (Sifthenelse (Etempvar _end (tptr tvoid))
      (Sreturn (Some (Econst_int (Int.repr 42) tint)))
      Sskip)
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_freerange_no_loop_no_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa_start, (tptr tvoid)) :: (_pa_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Ole (Etempvar _pa_start (tptr tvoid))
               (Etempvar _pa_end (tptr tvoid)) tint)
  (Scall None
    (Evar _kfree1 (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
    ((Etempvar _pa_start (tptr tvoid)) :: nil))
  Sskip)
|}.

Definition f_pointer_compare_7 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: (_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Olt
                   (Ecast (Etempvar _pa (tptr tvoid)) (tptr tschar))
                   (Etempvar _end (tptr tvoid)) tint)
      (Sset _t'1 (Econst_int (Int.repr 1) tint))
      (Sset _t'1
        (Ecast
          (Ebinop Oeq (Etempvar _pa (tptr tvoid))
            (Etempvar _end (tptr tvoid)) tint) tbool)))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Econst_int (Int.repr 42) tint)))
      Sskip))
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_pointer_compare_8 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: (_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Ebinop Omod (Ecast (Etempvar _pa (tptr tvoid)) tulong)
                   (Econst_int (Int.repr 4096) tint) tulong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sreturn (Some (Econst_int (Int.repr 42) tint)))
    Sskip)
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_pointer_compare_9 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: (_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop One
                   (Ebinop Omod (Ecast (Etempvar _pa (tptr tvoid)) tulong)
                     (Econst_int (Int.repr 4096) tint) tulong)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sset _t'1 (Econst_int (Int.repr 1) tint))
      (Sset _t'1
        (Ecast
          (Ebinop Olt (Ecast (Etempvar _pa (tptr tvoid)) (tptr tschar))
            (Etempvar _end (tptr tvoid)) tint) tbool)))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Econst_int (Int.repr 42) tint)))
      Sskip))
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_pointer_compare_10 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pa, (tptr tvoid)) :: (_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop One
                     (Ebinop Omod (Ecast (Etempvar _pa (tptr tvoid)) tulong)
                       (Econst_int (Int.repr 4096) tint) tulong)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Sset _t'1
          (Ecast
            (Ebinop Olt (Ecast (Etempvar _pa (tptr tvoid)) (tptr tschar))
              (Etempvar _end (tptr tvoid)) tint) tbool)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sset _t'2 (Econst_int (Int.repr 1) tint))
        (Sset _t'2
          (Ecast
            (Ebinop Oge (Ecast (Etempvar _pa (tptr tvoid)) tulong)
              (Ebinop Oadd (Econst_long (Int64.repr 2147483648) tlong)
                (Ebinop Omul
                  (Ebinop Omul (Econst_int (Int.repr 128) tint)
                    (Econst_int (Int.repr 1024) tint) tint)
                  (Econst_int (Int.repr 1024) tint) tint) tlong) tint) tbool))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Sreturn (Some (Econst_int (Int.repr 42) tint)))
      Sskip))
  (Sreturn (Some (Econst_int (Int.repr 13) tint))))
|}.

Definition f_align_pointer := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pointer, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tschar)) :: nil);
  fn_body :=
(Sset _p
  (Ecast
    (Ebinop Oand
      (Ebinop Osub
        (Ebinop Oadd (Ecast (Etempvar _p (tptr tschar)) tulong)
          (Econst_int (Int.repr 4096) tint) tulong)
        (Econst_int (Int.repr 1) tint) tulong)
      (Eunop Onotint
        (Ebinop Osub (Econst_int (Int.repr 4096) tint)
          (Econst_int (Int.repr 1) tint) tint) tint) tulong) (tptr tschar)))
|}.

Definition f_pointer_compare := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pa_start, (tptr tvoid)) :: (_pa_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, (tptr tschar)) :: (_t, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Ecast (Etempvar _pa_start (tptr tvoid)) (tptr tschar)))
  (Ssequence
    (Sset _t (Ecast (Etempvar _pa_end (tptr tvoid)) (tptr tschar)))
    (Ssequence
      (Sifthenelse (Ebinop Ole (Etempvar _s (tptr tschar))
                     (Etempvar _t (tptr tschar)) tint)
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_freerange_no_loop := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa_start, (tptr tvoid)) :: (_pa_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Ecast (Etempvar _pa_start (tptr tvoid)) (tptr tschar)))
  (Sifthenelse (Ebinop Ole
                 (Ebinop Oadd (Etempvar _p (tptr tschar))
                   (Econst_int (Int.repr 4096) tint) (tptr tschar))
                 (Ecast (Etempvar _pa_end (tptr tvoid)) (tptr tschar)) tint)
    (Scall None
      (Evar _kfree1 (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
      ((Etempvar _p (tptr tschar)) :: nil))
    Sskip))
|}.

Definition f_freerange := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pa_start, (tptr tvoid)) :: (_pa_end, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ecast
      (Ebinop Oand
        (Ebinop Osub
          (Ebinop Oadd (Ecast (Etempvar _pa_start (tptr tvoid)) tulong)
            (Econst_int (Int.repr 4096) tint) tulong)
          (Econst_int (Int.repr 1) tint) tulong)
        (Eunop Onotint
          (Ebinop Osub (Econst_int (Int.repr 4096) tint)
            (Econst_int (Int.repr 1) tint) tint) tint) tulong) (tptr tschar)))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Ole
                     (Ebinop Oadd (Etempvar _p (tptr tschar))
                       (Econst_int (Int.repr 4096) tint) (tptr tschar))
                     (Ecast (Etempvar _pa_end (tptr tvoid)) (tptr tschar))
                     tint)
        Sskip
        Sbreak)
      (Scall None
        (Evar _kfree1 (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
        ((Etempvar _p (tptr tschar)) :: nil)))
    (Sset _p
      (Ebinop Oadd (Etempvar _p (tptr tschar))
        (Econst_int (Int.repr 4096) tint) (tptr tschar)))))
|}.

Definition f_pointer_compare_values := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tschar)) :: (_q, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Ederef (Etempvar _p (tptr tschar)) tschar))
  (Ssequence
    (Sset _t'2 (Ederef (Etempvar _q (tptr tschar)) tschar))
    (Sreturn (Some (Ebinop Oeq (Etempvar _t'1 tschar) (Etempvar _t'2 tschar)
                     tint)))))
|}.

Definition composites : list composite_definition :=
(Composite _run Struct
   (Member_plain _next (tptr (Tstruct _run noattr)) :: nil)
   noattr ::
 Composite _struct_kmem Struct
   (Member_plain _xx tint ::
    Member_plain _freelist (tptr (Tstruct _run noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_freelist1, Gvar v_freelist1) ::
 (_get_freelist1, Gfun(Internal f_get_freelist1)) ::
 (_get_freelist1_input, Gfun(Internal f_get_freelist1_input)) ::
 (_i, Gvar v_i) :: (_get_i, Gfun(Internal f_get_i)) ::
 (_kmem, Gvar v_kmem) :: (_get_xx, Gfun(Internal f_get_xx)) ::
 (_get_freelist, Gfun(Internal f_get_freelist)) ::
 (_free, Gfun(Internal f_free)) :: (_alloc, Gfun(Internal f_alloc)) ::
 (_kfree1, Gfun(Internal f_kfree1)) ::
 (_kalloc1, Gfun(Internal f_kalloc1)) ::
 (_call_kfree1, Gfun(Internal f_call_kfree1)) ::
 (_call_kfree1_if_1, Gfun(Internal f_call_kfree1_if_1)) ::
 (_pointer_compare_0, Gfun(Internal f_pointer_compare_0)) ::
 (_pointer_compare_1, Gfun(Internal f_pointer_compare_1)) ::
 (_pointer_compare_2, Gfun(Internal f_pointer_compare_2)) ::
 (_pointer_compare_3, Gfun(Internal f_pointer_compare_3)) ::
 (_pointer_compare_4, Gfun(Internal f_pointer_compare_4)) ::
 (_pointer_compare_5, Gfun(Internal f_pointer_compare_5)) ::
 (_pointer_compare_6, Gfun(Internal f_pointer_compare_6)) ::
 (_pointer_compare_70, Gfun(Internal f_pointer_compare_70)) ::
 (_freerange_no_loop_no_add, Gfun(Internal f_freerange_no_loop_no_add)) ::
 (_pointer_compare_7, Gfun(Internal f_pointer_compare_7)) ::
 (_pointer_compare_8, Gfun(Internal f_pointer_compare_8)) ::
 (_pointer_compare_9, Gfun(Internal f_pointer_compare_9)) ::
 (_pointer_compare_10, Gfun(Internal f_pointer_compare_10)) ::
 (_align_pointer, Gfun(Internal f_align_pointer)) ::
 (_pointer_compare, Gfun(Internal f_pointer_compare)) ::
 (_freerange_no_loop, Gfun(Internal f_freerange_no_loop)) ::
 (_freerange, Gfun(Internal f_freerange)) ::
 (_pointer_compare_values, Gfun(Internal f_pointer_compare_values)) :: nil).

Definition public_idents : list ident :=
(_pointer_compare_values :: _freerange :: _freerange_no_loop ::
 _pointer_compare :: _align_pointer :: _pointer_compare_10 ::
 _pointer_compare_9 :: _pointer_compare_8 :: _pointer_compare_7 ::
 _freerange_no_loop_no_add :: _pointer_compare_70 :: _pointer_compare_6 ::
 _pointer_compare_5 :: _pointer_compare_4 :: _pointer_compare_3 ::
 _pointer_compare_2 :: _pointer_compare_1 :: _pointer_compare_0 ::
 _call_kfree1_if_1 :: _call_kfree1 :: _kalloc1 :: _kfree1 :: _alloc ::
 _free :: _get_freelist :: _get_xx :: _kmem :: _get_i :: _i ::
 _get_freelist1_input :: _get_freelist1 :: _freelist1 :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


