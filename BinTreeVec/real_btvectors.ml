(* ========================================================================= *)
(* Binary tree real vectors and matrices.                                    *)
(*                                                                           *)
(* (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018                  *)
(* (c) Copyright, Marco Maggesi 2025                                         *)
(* ========================================================================= *)

(*---------------------------------------------------------------------------*)
(* Basic algebraic operations on real btvectors.                             *)
(*---------------------------------------------------------------------------*)

let VECTOR_ADD_ARITH = prove
 (`(!x:real y. vecx x + vecx y = vecx (x + y)) /\
   (!x x' y y':real^N. vec0 x y + vec0 x' y' = vec0 (x + x') (y + y')) /\
   (!x x' y y':real^N a a'. vec1 x y a + vec1 x' y' a' =
                            vec1 (x + x') (y + y') (a + a'))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; VECTOR_ADD_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  MATCH_MP_TAC FORALL_BINARY_THM THEN
  SIMP_TAC[VECX_COMPONENT0; VEC0_COMPONENT0_BINARY;
    VEC1_COMPONENT0_BINARY; VECTOR_ADD_COMPONENT0; NUM_LT_BINARY] THEN
  MESON_TAC[]);;

let VECTOR_SUB_ARITH = prove
 (`(!x:real y. vecx x - vecx y = vecx (x - y)) /\
   (!x x' y y':real^N. vec0 x y - vec0 x' y' = vec0 (x - x') (y - y')) /\
   (!x x' y y':real^N a a'. vec1 x y a - vec1 x' y' a' =
                            vec1 (x - x') (y - y') (a - a'))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; VECTOR_SUB_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  MATCH_MP_TAC FORALL_BINARY_THM THEN
  SIMP_TAC[VECX_COMPONENT0; VEC0_COMPONENT0_BINARY;
    VEC1_COMPONENT0_BINARY; VECTOR_SUB_COMPONENT0; NUM_LT_BINARY] THEN
  MESON_TAC[]);;

let VECTOR_NEG_ARITH = prove
 (`(!x:real. --vecx x = vecx (--x)) /\
   (!x y:real^N. --vec0 x y = vec0 (--x) (--y)) /\
   (!x y:real^N a. --vec1 x y a = vec1 (--x) (--y) (--a))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; VECTOR_NEG_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  MATCH_MP_TAC FORALL_BINARY_THM THEN
  SIMP_TAC[VECX_COMPONENT0; VEC0_COMPONENT0_BINARY;
    VEC1_COMPONENT0_BINARY; VECTOR_NEG_COMPONENT0; NUM_LT_BINARY] THEN
  MESON_TAC[]);;

let VECTOR_CMUL_ARITH = prove
 (`(!c x:real. c % vecx x = vecx (c * x)) /\
   (!c x y:real^N. c % vec0 x y = vec0 (c % x) (c % y)) /\
   (!c x y:real^N a. c % vec1 x y a = vec1 (c % x) (c % y) (c * a))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; VECTOR_MUL_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  MATCH_MP_TAC FORALL_BINARY_THM THEN
  SIMP_TAC[VECX_COMPONENT0; VEC0_COMPONENT0_BINARY;
    VEC1_COMPONENT0_BINARY; VECTOR_MUL_COMPONENT0; NUM_LT_BINARY] THEN
  MESON_TAC[]);;

let DOT_ARITH = prove
 (`(!a b:real. (vecx a) dot (vecx b) = a * b) /\
   (!x x' y y':real^N. vec0 x y dot vec0 x' y' = x dot x' + y dot y') /\
   (!x x' y y':real^N a b.
      vec1 x y a dot vec1 x' y' b = x dot x' + y dot y' + a * b)`,
  REWRITE_TAC[DOT0] THEN CONJ_TAC THENL
  [REWRITE_TAC[VECX_COMPONENT0; DIMINDEX_1; SUM_NUMSEG_LT]; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIMINDEX_TYBIT1; SUM_NUMSEG_LT] THEN
  SIMP_TAC[SUM_EQ; FORALL_IN_GSPEC;
           VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY;
           LE_REFL; LT_IMP_LE; ARITH_RULE `i:num < n ==> ~(i = n)`;
           REAL_ADD_AC]);;

let NORM_POW_2_ARITH = prove
 (`(!x:real. norm (vecx x) pow 2 = x pow 2) /\
   (!x y:real^N. norm (vec0 x y) pow 2 = norm x pow 2 + norm y pow 2) /\
   (!x y:real^N a.
     norm (vec1 x y a) pow 2 = norm x pow 2 + norm y pow 2 + a pow 2)`,
  REWRITE_TAC[NORM_POW_2; REAL_POW_2; DOT_ARITH]);;

let COLUMN_ARITH = prove
 (`(!u:real^N j. column j (vecx u) = vecx (u$j)) /\
   (!A B:real^N^M j.
      column j (vec0 A B) = vec0 (column j A) (column j B)) /\
   (!A B:real^N^M u j.
      column j (vec1 A B u) = vec1 (column j A) (column j B) (u$j))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[CART_EQ] THEN
  SIMP_TAC[COLUMN_COMPONENT; INDEX_EQ_COMPONENT0] THEN
  REWRITE_TAC[VECX_COMPONENT0] THEN
  (SUBGOAL_THEN
     `!P n. (!i. 1 <= i /\ i <= n ==> P i) <=> (!i. i < n ==> P (i + 1))`
     (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ARITH_RULE `i < n <=> 1 <= i + 1 /\ i + 1 <= n`] THEN
    REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
     SUBGOAL_THEN `i = (i - 1) + 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC]) THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIMINDEX_TYBIT1;
              ARITH_RULE `(i + 1) - 1 = i`] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `i:num` NUM_CASES_BINARY) THEN
  REWRITE_TAC[NUM_LT_BINARY] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY] THEN
  REWRITE_TAC[component0] THEN NUM_REDUCE_TAC THEN
  ASM_SIMP_TAC[COLUMN_COMPONENT; LE_REFL; DIMINDEX_GE_1;
           ARITH_RULE `1 <= i + 1 /\ (i:num < n ==> i + 1 <= n)`] THEN
  REWRITE_TAC[LE_LT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[COLUMN_COMPONENT;
               ARITH_RULE `i:num < n ==> ~(i = n)`;
               ARITH_RULE `1 <= i + 1 /\ (i:num < n ==> i + 1 <= n)`]);;

(*---------------------------------------------------------------------------*)
(* Basic algebraic operations on real btmatrices.                            *)
(*---------------------------------------------------------------------------*)

let MATRIX_ADD_ARITH = prove
 (`(!u v:real^N. vecx u + vecx v = vecx (u + v)) /\
   (!A A' B B':real^N^M. vec0 A B + vec0 A' B' = vec0 (A + A') (B + B')) /\
   (!A A' B B':real^N^M u u'. vec1 A B u + vec1 A' B' u' =
                              vec1 (A + A') (B + B') (u + u'))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; MATRIX_ADD_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[FORALL_LT_BINARY; VECX_COMPONENT0] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY;
    MATRIX_ADD_COMPONENT0; VECTOR_ADD_COMPONENT0;
    MESON [] `(if b then u else v:real^N)$.i = if b then u$.i else v$.i`] THEN
  MESON_TAC[]);;

let MATRIX_SUB_ARITH = prove
 (`(!u v:real^N. vecx u - vecx v = vecx (u - v)) /\
   (!A A' B B':real^N^M. vec0 A B - vec0 A' B' = vec0 (A - A') (B - B')) /\
   (!A A' B B':real^N^M u u'. vec1 A B u - vec1 A' B' u' =
                              vec1 (A - A') (B - B') (u - u'))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; MATRIX_SUB_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[FORALL_LT_BINARY; VECX_COMPONENT0] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY;
    MATRIX_SUB_COMPONENT0; VECTOR_SUB_COMPONENT0;
    MESON [] `(if b then u else v:real^N)$.i = if b then u$.i else v$.i`] THEN
  MESON_TAC[]);;

let MATRIX_NEG_ARITH = prove
 (`(!u:real^N. --vecx u = vecx(--u)) /\
   (!A B:real^N^M. --vec0 A B = vec0 (--A) (--B)) /\
   (!A B:real^N^M u. --vec1 A B u = vec1 (--A) (--B) (--u))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; MATRIX_NEG_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[FORALL_LT_BINARY; VECX_COMPONENT0] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY;
    MATRIX_NEG_COMPONENT0; VECTOR_NEG_COMPONENT0;
    MESON [] `(if b then u else v:real^N)$.i = if b then u$.i else v$.i`] THEN
  MESON_TAC[]);;

let MATRIX_CMUL_ARITH = prove
 (`(!c u:real^N. c %% vecx u = vecx(c % u)) /\
   (!c A B:real^N^M. c %% vec0 A B = vec0 (c %% A) (c %% B)) /\
   (!c A B:real^N^M u. c %% vec1 A B u = vec1 (c %% A) (c %% B) (c % u))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; MATRIX_CMUL_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[FORALL_LT_BINARY; VECX_COMPONENT0] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY;
    MATRIX_CMUL_COMPONENT0; VECTOR_MUL_COMPONENT0;
    MESON [] `(if b then u else v:real^N)$.i = if b then u$.i else v$.i`] THEN
  MESON_TAC[]);;

let MATRIX_MUL_ARITH = prove
 (`(!u:real^N A:real^M^N. vecx u ** A = vecx(u ** A)) /\
   (!A B:real^N^M C:real^P^N. vec0 A B ** C = vec0 (A ** C) (B ** C)) /\
   (!A B:real^N^M u C:real^P^N.
      vec1 A B u ** C = vec1 (A ** C) (B ** C) (u ** C))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[CART_EQ0] THEN
  SIMP_TAC[MATRIX_MUL_COMPONENT0] THEN
  REWRITE_TAC[DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1;
              FORALL_LT_BINARY; VECX_COMPONENT0] THEN
  SIMP_TAC[VECTOR_MATRIX_MUL_COMPONENT0; DOT0; VEC0_COMPONENT0_BINARY;
    VEC1_COMPONENT0_BINARY; MATRIX_MUL_COMPONENT0] THEN REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
   ASM_SIMP_TAC[COLUMN_COMPONENT0];
   FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [LE_LT]) THEN
   ASM_SIMP_TAC[MATRIX_MUL_COMPONENT0; VECTOR_MATRIX_MUL_COMPONENT0;
     COLUMN_COMPONENT0; DOT0; ARITH_RULE `i:num < n ==> ~(i = n)`]]);;

let MATRIX_VECTOR_MUL_ARITH = prove
 (`(!u:real^N x:real^N. vecx u ** x = vecx (u dot x)) /\
   (!A B:real^N^M x:real^N. vec0 A B ** x = vec0 (A ** x) (B ** x)) /\
   (!A B:real^N^M u x:real^N. vec1 A B u ** x =
                              vec1 (A ** x) (B ** x) (u dot x))`,
  REWRITE_TAC[CART_EQ0; VECX_COMPONENT0] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT0] THEN
  REWRITE_TAC[DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[FORALL_LT_BINARY; VECX_COMPONENT0] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY;
           MATRIX_VECTOR_MUL_COMPONENT0] THEN
  REWRITE_TAC[LE_LT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT0;
               ARITH_RULE `i:num < n ==> ~(i = n)`]);;

let VECTOR_MATRIX_MUL_ARITH = prove
 (`(!a u:real^N. vecx a ** vecx u = a % u) /\
   (!u v:real^N A B:real^M^N.
      vector_matrix_mul (vec0 u v) (vec0 A B) =
      vector_matrix_mul u A + vector_matrix_mul v B) /\
   (!u v:real^N a A B:real^M^N w.
      vector_matrix_mul (vec1 u v a) (vec1 A B w) =
      vector_matrix_mul u A + vector_matrix_mul v B + a % w)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[CART_EQ0] THEN
  SIMP_TAC[VECTOR_MATRIX_MUL_COMPONENT0; COLUMN_ARITH; DOT_ARITH;
           VECTOR_MUL_COMPONENT0; VECTOR_ADD_COMPONENT0] THEN
  REWRITE_TAC[component0]);;

(* ------------------------------------------------------------------------- *)
(* Sums of vectors.                                                          *)
(* ------------------------------------------------------------------------- *)

let VSUM_NUMSEG_LT = prove
 (`(!f. vsum {i | i < 0} f = vec 0:real^N) /\
   (!f. vsum {i | i < 1} f = f 0:real^N) /\
   (!n f. vsum {i | i < n + 1} f = f n + vsum {i | i < n} f:real^N) /\
   (!n f. vsum {i | i < 2 * n} f =
          vsum {i | i < n} (\i. f(2 * i)) +
          vsum {i | i < n} (\i. f(2 * i + 1)):real^N)`,
  REWRITE_TAC[CART_EQ; vsum; VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[LAMBDA_BETA; SUM_NUMSEG_LT]);;

(* ------------------------------------------------------------------------- *)
(* Extend the conversion net for VECTOR_REDUCE_CONV.                         *)
(* ------------------------------------------------------------------------- *)

let real_matrix_net =
  let thl = [VECTOR_ADD_ARITH; VECTOR_SUB_ARITH; VECTOR_NEG_ARITH;
             VECTOR_CMUL_ARITH; DOT_ARITH; COLUMN_ARITH; MATRIX_ADD_ARITH;
             MATRIX_SUB_ARITH; MATRIX_NEG_ARITH; MATRIX_CMUL_ARITH;
             MATRIX_MUL_ARITH; VECTOR_MATRIX_MUL_ARITH;
             MATRIX_VECTOR_MUL_ARITH] in
  let thl_canon = itlist (mk_rewrites false) thl [] in
  itlist (net_of_thm false) thl_canon empty_net;;

vector_net := merge_nets (!vector_net, real_matrix_net);;
