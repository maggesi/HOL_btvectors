(* ========================================================================= *)
(* Zero-based indexed matrices.                                              *)
(*                                                                           *)
(* Vectors and matrices in HOL Light uses one-based indexes by default.      *)
(* This file provides some basic constants and theorems to work with HOL     *)
(* real matrices using zero-indexes instead.                                 *)
(*                                                                           *)
(* Se also the anologous theorems for vectors in the vector0.ml file.        *)
(* We keep the code of vectors and matrices separated becose the latter      *)
(* requires the library of multivariate calculus.                            *)
(*                                                                           *)
(* (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018                  *)
(* (c) Copyright, Marco Maggesi 2025                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic algebraic operations on real vectors.                               *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ADD_COMPONENT0 = prove
 (`!x y:real^N i. (x + y) $. i = x $. i + y $. i`,
  REWRITE_TAC[component0; VECTOR_ADD_COMPONENT]);;

let VECTOR_SUB_COMPONENT0 = prove
 (`!x y:real^N i. (x - y) $. i = x $. i - y $. i`,
  REWRITE_TAC[component0; VECTOR_SUB_COMPONENT]);;

let VECTOR_NEG_COMPONENT0 = prove
 (`!x:real^N i. (--x) $. i = -- (x $. i)`,
  REWRITE_TAC[component0; VECTOR_NEG_COMPONENT]);;

let VECTOR_MUL_COMPONENT0 = prove
 (`!c x:real^N i. (c % x) $. i = c * (x $. i)`,
  REWRITE_TAC[component0; VECTOR_MUL_COMPONENT]);;

let DOT0 = prove
 (`!x y:real^N. x dot y = sum {i | i < dimindex(:N)} (\i. x$.i * y$.i)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[dot; component0] THEN
  SIMP_TAC[SUM_OFFSET_0; DIMINDEX_GE_1] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN GEN_TAC THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` MP_TAC THENL
  [REWRITE_TAC[DIMINDEX_GE_1]; ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Miscellanea on vectors and matrices.                                      *)
(* ------------------------------------------------------------------------- *)

let MATRIX_MUL_COMPONENT_ALT = prove
 (`!A:real^N^M B:real^P^N i j.
     1 <= i /\ i <= dimindex (:M) /\
     1 <= j /\ j <= dimindex (:P)
     ==> (A ** B)$i$j =
         sum (1..dimindex(:N)) (\k. A$i$k * B$k$j)`,
  SIMP_TAC[matrix_mul; LAMBDA_BETA]);;

let VECTOR_MATRIX_MUL_COMPONENT = prove
 (`!u:real^N A:real^M^N i. 1 <= i /\ i <= dimindex(:M)
                           ==> (u ** A)$i = u dot (column i A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[vector_matrix_mul; dot] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[IN_NUMSEG; ETA_AX; column] THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Basic algebraic operations on real matrices.                              *)
(* ------------------------------------------------------------------------- *)

let COLUMN_COMPONENT = prove
 (`!A:real^M^N i j.
     1 <= i /\ i <= dimindex (:N)
     ==> column j A$i = A$i$j`,
  SIMP_TAC[column; LAMBDA_BETA]);;

let COLUMN_COMPONENT0 = prove
 (`!A:real^M^N i j.
     i < dimindex (:N)
     ==> column (j + 1) A$.i = A$.i$.j`,
  REWRITE_TAC[column; component0] THEN
  SIMP_TAC[LAMBDA_BETA; ARITH_RULE `1 <= i + 1 /\ (i < n ==> i + 1 <= n)`]);;

let MATRIX_ADD_COMPONENT0 = prove
 (`!A B:real^M^N i j. (A + B)$.i$.j = A$.i$.j + B$.i$.j`,
  REWRITE_TAC[component0; MATRIX_ADD_COMPONENT]);;

let MATRIX_SUB_COMPONENT0 = prove
 (`!A B:real^M^N i j. (A - B)$.i$.j = A$.i$.j - B$.i$.j`,
  REWRITE_TAC[component0; MATRIX_SUB_COMPONENT]);;

let MATRIX_NEG_COMPONENT0 = prove
 (`!A:real^M^N i j. (--A)$.i$.j = --(A$.i$.j)`,
  REWRITE_TAC[component0; MATRIX_NEG_COMPONENT]);;

let MATRIX_CMUL_COMPONENT0 = prove
 (`!c A:real^M^N i j. (c %% A)$.i$.j = c * (A$.i$.j)`,
  REWRITE_TAC[component0; MATRIX_CMUL_COMPONENT]);;

let MATRIX_VECTOR_MUL_COMPONENT0 = prove
 (`!A:real^N^M x:real^N k. k < dimindex (:M) ==> (A ** x) $. k = A $. k dot x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[component0] THEN
  MATCH_MP_TAC MATRIX_VECTOR_MUL_COMPONENT THEN ASM_ARITH_TAC);;

let VECTOR_MATRIX_MUL_COMPONENT0 = prove
 (`!u:real^N A:real^M^N i. i < dimindex(:M)
                           ==> (u ** A)$.i = u dot (column (i + 1) A)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[component0] THEN
  MATCH_MP_TAC VECTOR_MATRIX_MUL_COMPONENT THEN ASM_ARITH_TAC);;

let MATRIX_MUL_COMPONENT0 = prove
 (`!A:real^N^M B:real^P^N i j.
     i < dimindex (:M) /\
     j < dimindex (:P)
     ==> (A ** B)$.i$.j =
         sum {i | i < dimindex(:N)} (\k. A$.i$.k * B$.k$.j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[component0; MATRIX_MUL_COMPONENT_ALT;
               ARITH_RULE `1 <= i + 1 /\ (i < n ==> i + 1 <= n)`] THEN
  SIMP_TAC[SUM_OFFSET_0; DIMINDEX_GE_1] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` MP_TAC THENL
  [REWRITE_TAC[DIMINDEX_GE_1]; ARITH_TAC]);;
