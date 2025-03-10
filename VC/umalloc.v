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
  Definition source_file := "user/umalloc.c".
  Definition normalized := true.
End Info.

Definition __198 : ident := $"_198".
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
Definition _ap : ident := $"ap".
Definition _base : ident := $"base".
Definition _bp : ident := $"bp".
Definition _free : ident := $"free".
Definition _freep : ident := $"freep".
Definition _header : ident := $"header".
Definition _hp : ident := $"hp".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _morecore : ident := $"morecore".
Definition _nbytes : ident := $"nbytes".
Definition _nu : ident := $"nu".
Definition _nunits : ident := $"nunits".
Definition _p : ident := $"p".
Definition _prevp : ident := $"prevp".
Definition _ptr : ident := $"ptr".
Definition _s : ident := $"s".
Definition _sbrk : ident := $"sbrk".
Definition _size : ident := $"size".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_base := {|
  gvar_info := (Tunion _header noattr);
  gvar_init := (Init_space 16 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_freep := {|
  gvar_info := (tptr (Tunion _header noattr));
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ap, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_bp, (tptr (Tunion _header noattr))) ::
               (_p, (tptr (Tunion _header noattr))) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'17, (tptr (Tunion _header noattr))) ::
               (_t'16, (tptr (Tunion _header noattr))) ::
               (_t'15, (tptr (Tunion _header noattr))) :: (_t'14, tuint) ::
               (_t'13, (tptr (Tunion _header noattr))) :: (_t'12, tuint) ::
               (_t'11, (tptr (Tunion _header noattr))) ::
               (_t'10, (tptr (Tunion _header noattr))) ::
               (_t'9, (tptr (Tunion _header noattr))) ::
               (_t'8, (tptr (Tunion _header noattr))) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tunion _header noattr))) :: (_t'3, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _bp
    (Ebinop Osub
      (Ecast (Etempvar _ap (tptr tvoid)) (tptr (Tunion _header noattr)))
      (Econst_int (Int.repr 1) tint) (tptr (Tunion _header noattr))))
  (Ssequence
    (Ssequence
      (Sset _p (Evar _freep (tptr (Tunion _header noattr))))
      (Sloop
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Ogt
                           (Etempvar _bp (tptr (Tunion _header noattr)))
                           (Etempvar _p (tptr (Tunion _header noattr))) tint)
              (Ssequence
                (Sset _t'17
                  (Efield
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                        (Tunion _header noattr)) _s (Tstruct __198 noattr))
                    _ptr (tptr (Tunion _header noattr))))
                (Sset _t'1
                  (Ecast
                    (Ebinop Olt (Etempvar _bp (tptr (Tunion _header noattr)))
                      (Etempvar _t'17 (tptr (Tunion _header noattr))) tint)
                    tbool)))
              (Sset _t'1 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
              Sskip
              Sbreak))
          (Ssequence
            (Ssequence
              (Sset _t'15
                (Efield
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                      (Tunion _header noattr)) _s (Tstruct __198 noattr))
                  _ptr (tptr (Tunion _header noattr))))
              (Sifthenelse (Ebinop Oge
                             (Etempvar _p (tptr (Tunion _header noattr)))
                             (Etempvar _t'15 (tptr (Tunion _header noattr)))
                             tint)
                (Sifthenelse (Ebinop Ogt
                               (Etempvar _bp (tptr (Tunion _header noattr)))
                               (Etempvar _p (tptr (Tunion _header noattr)))
                               tint)
                  (Sset _t'2 (Ecast (Econst_int (Int.repr 1) tint) tbool))
                  (Ssequence
                    (Ssequence
                      (Sset _t'16
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tunion _header noattr)))
                              (Tunion _header noattr)) _s
                            (Tstruct __198 noattr)) _ptr
                          (tptr (Tunion _header noattr))))
                      (Sset _t'2
                        (Ecast
                          (Ebinop Olt
                            (Etempvar _bp (tptr (Tunion _header noattr)))
                            (Etempvar _t'16 (tptr (Tunion _header noattr)))
                            tint) tbool)))
                    (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool))))
                (Sset _t'2 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'2 tint) Sbreak Sskip)))
        (Sset _p
          (Efield
            (Efield
              (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                (Tunion _header noattr)) _s (Tstruct __198 noattr)) _ptr
            (tptr (Tunion _header noattr))))))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Efield
              (Ederef (Etempvar _bp (tptr (Tunion _header noattr)))
                (Tunion _header noattr)) _s (Tstruct __198 noattr)) _size
            tuint))
        (Ssequence
          (Sset _t'8
            (Efield
              (Efield
                (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                  (Tunion _header noattr)) _s (Tstruct __198 noattr)) _ptr
              (tptr (Tunion _header noattr))))
          (Sifthenelse (Ebinop Oeq
                         (Ebinop Oadd
                           (Etempvar _bp (tptr (Tunion _header noattr)))
                           (Etempvar _t'7 tuint)
                           (tptr (Tunion _header noattr)))
                         (Etempvar _t'8 (tptr (Tunion _header noattr))) tint)
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Efield
                      (Ederef (Etempvar _bp (tptr (Tunion _header noattr)))
                        (Tunion _header noattr)) _s (Tstruct __198 noattr))
                    _size tuint))
                (Ssequence
                  (Sset _t'13
                    (Efield
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                          (Tunion _header noattr)) _s (Tstruct __198 noattr))
                      _ptr (tptr (Tunion _header noattr))))
                  (Ssequence
                    (Sset _t'14
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _t'13 (tptr (Tunion _header noattr)))
                            (Tunion _header noattr)) _s
                          (Tstruct __198 noattr)) _size tuint))
                    (Sassign
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _bp (tptr (Tunion _header noattr)))
                            (Tunion _header noattr)) _s
                          (Tstruct __198 noattr)) _size tuint)
                      (Ebinop Oadd (Etempvar _t'12 tuint)
                        (Etempvar _t'14 tuint) tuint)))))
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                        (Tunion _header noattr)) _s (Tstruct __198 noattr))
                    _ptr (tptr (Tunion _header noattr))))
                (Ssequence
                  (Sset _t'11
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _t'10 (tptr (Tunion _header noattr)))
                          (Tunion _header noattr)) _s (Tstruct __198 noattr))
                      _ptr (tptr (Tunion _header noattr))))
                  (Sassign
                    (Efield
                      (Efield
                        (Ederef (Etempvar _bp (tptr (Tunion _header noattr)))
                          (Tunion _header noattr)) _s (Tstruct __198 noattr))
                      _ptr (tptr (Tunion _header noattr)))
                    (Etempvar _t'11 (tptr (Tunion _header noattr)))))))
            (Ssequence
              (Sset _t'9
                (Efield
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                      (Tunion _header noattr)) _s (Tstruct __198 noattr))
                  _ptr (tptr (Tunion _header noattr))))
              (Sassign
                (Efield
                  (Efield
                    (Ederef (Etempvar _bp (tptr (Tunion _header noattr)))
                      (Tunion _header noattr)) _s (Tstruct __198 noattr))
                  _ptr (tptr (Tunion _header noattr)))
                (Etempvar _t'9 (tptr (Tunion _header noattr))))))))
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Efield
                (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                  (Tunion _header noattr)) _s (Tstruct __198 noattr)) _size
              tuint))
          (Sifthenelse (Ebinop Oeq
                         (Ebinop Oadd
                           (Etempvar _p (tptr (Tunion _header noattr)))
                           (Etempvar _t'3 tuint)
                           (tptr (Tunion _header noattr)))
                         (Etempvar _bp (tptr (Tunion _header noattr))) tint)
            (Ssequence
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                        (Tunion _header noattr)) _s (Tstruct __198 noattr))
                    _size tuint))
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Efield
                        (Ederef (Etempvar _bp (tptr (Tunion _header noattr)))
                          (Tunion _header noattr)) _s (Tstruct __198 noattr))
                      _size tuint))
                  (Sassign
                    (Efield
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                          (Tunion _header noattr)) _s (Tstruct __198 noattr))
                      _size tuint)
                    (Ebinop Oadd (Etempvar _t'5 tuint) (Etempvar _t'6 tuint)
                      tuint))))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Efield
                      (Ederef (Etempvar _bp (tptr (Tunion _header noattr)))
                        (Tunion _header noattr)) _s (Tstruct __198 noattr))
                    _ptr (tptr (Tunion _header noattr))))
                (Sassign
                  (Efield
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                        (Tunion _header noattr)) _s (Tstruct __198 noattr))
                    _ptr (tptr (Tunion _header noattr)))
                  (Etempvar _t'4 (tptr (Tunion _header noattr))))))
            (Sassign
              (Efield
                (Efield
                  (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                    (Tunion _header noattr)) _s (Tstruct __198 noattr)) _ptr
                (tptr (Tunion _header noattr)))
              (Etempvar _bp (tptr (Tunion _header noattr))))))
        (Sassign (Evar _freep (tptr (Tunion _header noattr)))
          (Etempvar _p (tptr (Tunion _header noattr))))))))
|}.

Definition f_morecore := {|
  fn_return := (tptr (Tunion _header noattr));
  fn_callconv := cc_default;
  fn_params := ((_nu, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tschar)) ::
               (_hp, (tptr (Tunion _header noattr))) ::
               (_t'1, (tptr tschar)) ::
               (_t'2, (tptr (Tunion _header noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _nu tuint)
                 (Econst_int (Int.repr 4096) tint) tint)
    (Sset _nu (Econst_int (Int.repr 4096) tint))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _sbrk (Tfunction (tint :: nil) (tptr tschar) cc_default))
        ((Ebinop Omul (Etempvar _nu tuint)
           (Esizeof (Tunion _header noattr) tulong) tulong) :: nil))
      (Sset _p (Etempvar _t'1 (tptr tschar))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr tschar))
                     (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                       (tptr tschar)) tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip)
      (Ssequence
        (Sset _hp
          (Ecast (Etempvar _p (tptr tschar)) (tptr (Tunion _header noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Efield
                (Ederef (Etempvar _hp (tptr (Tunion _header noattr)))
                  (Tunion _header noattr)) _s (Tstruct __198 noattr)) _size
              tuint) (Etempvar _nu tuint))
          (Ssequence
            (Scall None
              (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
              ((Ecast
                 (Ebinop Oadd (Etempvar _hp (tptr (Tunion _header noattr)))
                   (Econst_int (Int.repr 1) tint)
                   (tptr (Tunion _header noattr))) (tptr tvoid)) :: nil))
            (Ssequence
              (Sset _t'2 (Evar _freep (tptr (Tunion _header noattr))))
              (Sreturn (Some (Etempvar _t'2 (tptr (Tunion _header noattr))))))))))))
|}.

Definition f_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_nbytes, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tunion _header noattr))) ::
               (_prevp, (tptr (Tunion _header noattr))) ::
               (_nunits, tuint) :: (_t'5, (tptr (Tunion _header noattr))) ::
               (_t'4, (tptr (Tunion _header noattr))) ::
               (_t'3, (tptr (Tunion _header noattr))) ::
               (_t'2, (tptr (Tunion _header noattr))) ::
               (_t'1, (tptr (Tunion _header noattr))) ::
               (_t'12, (tptr (Tunion _header noattr))) ::
               (_t'11, (tptr (Tunion _header noattr))) :: (_t'10, tuint) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, (tptr (Tunion _header noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _nunits
    (Ecast
      (Ebinop Oadd
        (Ebinop Odiv
          (Ebinop Osub
            (Ebinop Oadd (Etempvar _nbytes tuint)
              (Esizeof (Tunion _header noattr) tulong) tulong)
            (Econst_int (Int.repr 1) tint) tulong)
          (Esizeof (Tunion _header noattr) tulong) tulong)
        (Econst_int (Int.repr 1) tint) tulong) tuint))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'12 (Evar _freep (tptr (Tunion _header noattr))))
          (Sset _t'3
            (Ecast (Etempvar _t'12 (tptr (Tunion _header noattr)))
              (tptr (Tunion _header noattr)))))
        (Sset _prevp (Etempvar _t'3 (tptr (Tunion _header noattr)))))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'3 (tptr (Tunion _header noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Ecast
                      (Eaddrof (Evar _base (Tunion _header noattr))
                        (tptr (Tunion _header noattr)))
                      (tptr (Tunion _header noattr))))
                  (Sset _prevp
                    (Etempvar _t'1 (tptr (Tunion _header noattr)))))
                (Sset _t'2
                  (Ecast (Etempvar _t'1 (tptr (Tunion _header noattr)))
                    (tptr (Tunion _header noattr)))))
              (Sassign (Evar _freep (tptr (Tunion _header noattr)))
                (Etempvar _t'2 (tptr (Tunion _header noattr)))))
            (Sassign
              (Efield
                (Efield (Evar _base (Tunion _header noattr)) _s
                  (Tstruct __198 noattr)) _ptr
                (tptr (Tunion _header noattr)))
              (Etempvar _t'2 (tptr (Tunion _header noattr)))))
          (Sassign
            (Efield
              (Efield (Evar _base (Tunion _header noattr)) _s
                (Tstruct __198 noattr)) _size tuint)
            (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Ssequence
      (Sset _p
        (Efield
          (Efield
            (Ederef (Etempvar _prevp (tptr (Tunion _header noattr)))
              (Tunion _header noattr)) _s (Tstruct __198 noattr)) _ptr
          (tptr (Tunion _header noattr))))
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                      (Tunion _header noattr)) _s (Tstruct __198 noattr))
                  _size tuint))
              (Sifthenelse (Ebinop Oge (Etempvar _t'7 tuint)
                             (Etempvar _nunits tuint) tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _p (tptr (Tunion _header noattr)))
                            (Tunion _header noattr)) _s
                          (Tstruct __198 noattr)) _size tuint))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                                   (Etempvar _nunits tuint) tint)
                      (Ssequence
                        (Sset _t'11
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tunion _header noattr)))
                                (Tunion _header noattr)) _s
                              (Tstruct __198 noattr)) _ptr
                            (tptr (Tunion _header noattr))))
                        (Sassign
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _prevp (tptr (Tunion _header noattr)))
                                (Tunion _header noattr)) _s
                              (Tstruct __198 noattr)) _ptr
                            (tptr (Tunion _header noattr)))
                          (Etempvar _t'11 (tptr (Tunion _header noattr)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'10
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tunion _header noattr)))
                                  (Tunion _header noattr)) _s
                                (Tstruct __198 noattr)) _size tuint))
                          (Sassign
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tunion _header noattr)))
                                  (Tunion _header noattr)) _s
                                (Tstruct __198 noattr)) _size tuint)
                            (Ebinop Osub (Etempvar _t'10 tuint)
                              (Etempvar _nunits tuint) tuint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'9
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _p (tptr (Tunion _header noattr)))
                                    (Tunion _header noattr)) _s
                                  (Tstruct __198 noattr)) _size tuint))
                            (Sset _p
                              (Ebinop Oadd
                                (Etempvar _p (tptr (Tunion _header noattr)))
                                (Etempvar _t'9 tuint)
                                (tptr (Tunion _header noattr)))))
                          (Sassign
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _p (tptr (Tunion _header noattr)))
                                  (Tunion _header noattr)) _s
                                (Tstruct __198 noattr)) _size tuint)
                            (Etempvar _nunits tuint))))))
                  (Ssequence
                    (Sassign (Evar _freep (tptr (Tunion _header noattr)))
                      (Etempvar _prevp (tptr (Tunion _header noattr))))
                    (Sreturn (Some (Ecast
                                     (Ebinop Oadd
                                       (Etempvar _p (tptr (Tunion _header noattr)))
                                       (Econst_int (Int.repr 1) tint)
                                       (tptr (Tunion _header noattr)))
                                     (tptr tvoid))))))
                Sskip))
            (Ssequence
              (Sset _t'6 (Evar _freep (tptr (Tunion _header noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _p (tptr (Tunion _header noattr)))
                             (Etempvar _t'6 (tptr (Tunion _header noattr)))
                             tint)
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _morecore (Tfunction (tuint :: nil)
                                          (tptr (Tunion _header noattr))
                                          cc_default))
                        ((Etempvar _nunits tuint) :: nil))
                      (Sset _t'5
                        (Ecast (Etempvar _t'4 (tptr (Tunion _header noattr)))
                          (tptr (Tunion _header noattr)))))
                    (Sset _p (Etempvar _t'5 (tptr (Tunion _header noattr)))))
                  (Sifthenelse (Ebinop Oeq
                                 (Etempvar _t'5 (tptr (Tunion _header noattr)))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    Sskip))
                Sskip))))
        (Ssequence
          (Sset _prevp (Etempvar _p (tptr (Tunion _header noattr))))
          (Sset _p
            (Efield
              (Efield
                (Ederef (Etempvar _p (tptr (Tunion _header noattr)))
                  (Tunion _header noattr)) _s (Tstruct __198 noattr)) _ptr
              (tptr (Tunion _header noattr)))))))))
|}.

Definition composites : list composite_definition :=
(Composite __198 Struct
   (Member_plain _ptr (tptr (Tunion _header noattr)) ::
    Member_plain _size tuint :: nil)
   noattr ::
 Composite _header Union
   (Member_plain _s (Tstruct __198 noattr) :: Member_plain _x tlong :: nil)
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
 (_sbrk,
   Gfun(External (EF_external "sbrk"
                   (mksignature (AST.Xint :: nil) AST.Xptr cc_default))
     (tint :: nil) (tptr tschar) cc_default)) :: (_base, Gvar v_base) ::
 (_freep, Gvar v_freep) :: (_free, Gfun(Internal f_free)) ::
 (_morecore, Gfun(Internal f_morecore)) ::
 (_malloc, Gfun(Internal f_malloc)) :: nil).

Definition public_idents : list ident :=
(_malloc :: _free :: _sbrk :: ___builtin_debug ::
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


