(************************************************************************)
(* Parts taken from classfun.v:                                         *)
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)
(*                                                                      *)
(* (c) Copyright 2015, CRI, MINES ParisTech, PSL Research University    *)
(* All rights reserved.                                                 *)
(* You may distribute this file under the terms of the CeCILL-B license *)
(************************************************************************)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice.
Require Import fintype tuple finfun bigop prime ssralg poly.
Require Import finset fingroup perm finalg.
Require Import matrix mxalgebra vector ssrnum zmodp ssrint intdiv algC cyclotomic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* An exploration of basic DFT theory using MathComp.                         *)
(* This file is self-contained.                                               *)
(*                                                                            *)
(* Talk at Coq Workshop 2015 @ Sophia AntiPolis, France                       *)
(*                                                                            *)
(* This development consists of three main separate sections:                 *)
(*                                                                            *)
(* + Development of an inner product for vectors of albraic numbers:          *)
(*   Here we have copied straight the definitions and proofs of the inner     *)
(*   product of classfun.v in MathComp                                        *)
(*                                                                            *)
(* + Some additional lemmas about primitive roots of the unity:               *)
(*   All the important theorems are already in mathcomp, however, we prove    *)
(*   some extra facts for conveninece, in particular a lighter version of     *)
(*   orthogonality than the one in classfun                                   *)
(*                                                                            *)
(* + The DFT theory itself:                                                   *)
(*   The development is straightforward and is mainly meant as a demo.        *)
(*                                                                            *)
(*   We provide two (equivalent) definitions, "dft" in \sum form and W        *)
(*   in matrix form, thus used by "W *m x".                                   *)
(*                                                                            *)
(*   We follow https://ccrma.stanford.edu/~jos/mdft/ most of the time,        *)
(*   to develop circular signal theory, shifting, convolution, and the        *)
(*   unitary character of the DFT.                                            *)
(*                                                                            *)
(*   As an extra, we prove that any unitary matrix is an isometry wrt the     *)
(*   inner product, lemma of which the typical DFT energy theorem's are       *)
(*   corollaries.                                                             *)
(*                                                                            *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Open Scope ring_scope.

(* Auxiliary Algebra lemmas *)
Section AlgAux.

(*
 * The lemmas below are not in Mathcomp, could they be candidates?
 **)

Lemma eq_mulr (R : unitRingType) (x y z : R) (y_unit : y \is a GRing.unit) :
  (x * y == z) = (x == z / y).
Proof. by rewrite -(can_eq (divrK y_unit)) -mulrA divrr ?mulr1. Qed.

Lemma eq_mull (R : comUnitRingType) (x y z : R) (x_unit : x \is a GRing.unit) :
  (x * y == z) = (y == z / x).
Proof. by rewrite mulrC eq_mulr. Qed.

(* Explicit sum of geometric series. *)
Lemma sumr_expr (F : fieldType) n (r : F) (r_neq1 : r != 1) :
  \sum_(0 <= i < n) r ^+ i = (1 - r ^+ n) / (1 - r).
Proof.
apply/eqP; rewrite -eq_mulr; last by rewrite unitfE subr_eq add0r eq_sym.
by rewrite -opprB subrX1 -mulNr -opprB opprK mulrC big_mkord.
Qed.

Lemma sum1_expr (F : fieldType) n : \sum_(0 <= i < n) 1 ^+ i = n%:R :> F.
Proof.
rewrite (eq_bigr _ (fun i _ => expr1n _ i)).
by rewrite big_mkord sumr_const card_ord.
Qed.

End AlgAux.

(* Auxiliary Matrix Lemmas. *)
Section MxAux.

Variables (R : ringType) (m n : nat).
Implicit Types (A B : 'M[R]_(m,n)).

(* Can we improve this proof? [EG: hard to do better]... *)
Lemma mx0P A : reflect (exists i , A i.1 i.2 != 0) (A != 0).
Proof.
apply/(iffP idP) => [/eqP H | [[i j]] /eqP H]; last first.
  by apply/eqP=> /matrixP /(_ i j); rewrite mxE.
apply/existsP; rewrite -negb_forall; apply/negP=> /forallP /= Hn.
by apply/H/matrixP=> i j; have/eqP := Hn (i, j); rewrite mxE.
Qed.

End MxAux.

(* Inner product for vectors of algebraic numbers and its properties.
 *
 * This whole section is basically a vanilla copy from classfun.v.
 *)

Section InnerProduct.

Notation C := algC.

Variable n : nat.
Implicit Types u v : 'cV[C]_n.

(* Inner product notation as in classfun *)
(* Reserved Notation "'[ u , v ]" *)
(*   (at level 80, format "'[hv' ''[' u , '/ '  v ] ']'"). *)

(* XXX: Issues with naming. Why vdot, why not dotu as in addr? *)

(* Inner product specialized to vectors of algebraic numbers *)
Definition vdot u v := \sum_i u i 0 * (v i 0)^*.

(* Protected&reversed version for the Additive, etc... instances *)
Definition vdotr_head k u v := let: tt := k in vdot v u.
Definition vnorm_head k u   := let: tt := k in vdot u u.

Notation "''[' u , v ]" := (vdot u v) : ring_scope.
(* Recall: This is the squared norm *)
Notation "''[' u ]" := '[u, u] : ring_scope.

Notation vdotr := (vdotr_head tt).
Notation vnorm := (vnorm_head tt).

Lemma vnorm1 : '[const_mx 1] = n%:R.
Proof.
transitivity (\sum_(i < n) (@GRing.one [ringType of C])).
  by apply: eq_bigr => i _; rewrite !mxE mul1r rmorph1.
by rewrite sumr_const cardT size_enum_ord.
Qed.

Lemma vdotrE u v : vdotr v u = '[u, v]. Proof. by []. Qed.

(* Conjugate of a matrix. *)
Definition conjM m n (A : 'M_(m,n)) := map_mx conjC A^T.

Lemma conjMK m (A : 'M_(m,n)) : conjM (conjM A) = A.
Proof.
by rewrite /conjM map_trmx trmxK; apply/matrixP=> i j; rewrite !mxE conjCK.
Qed.

(* Relation to matrix multiplication *)
Lemma vdot_def (u v : 'cV_n) : '[u,v]%:M = conjM v *m u.
Proof.
rewrite [_*m_]mx11_scalar; apply/congr1; rewrite !mxE.
by apply: eq_bigr => k _; rewrite !mxE mulrC.
Qed.

Lemma vdotr_is_linear u : linear (vdotr u : 'cV_n -> algC^o).
Proof.
move=> a v w; rewrite linear_sum -big_split; apply: eq_bigr => x _ /=.
by rewrite !mxE mulrDl -mulrA.
Qed.
Canonical vdotr_additive u := Additive (vdotr_is_linear u).
Canonical vdotr_linear   u := Linear   (vdotr_is_linear u).

Lemma vdot0l u : '[0,u] = 0.
Proof. by rewrite -vdotrE linear0. Qed.
Lemma vdotNl u v : '[- u, v] = - '[u, v].
Proof. by rewrite -vdotrE linearN. Qed.
Lemma vdotDl u v w : '[u + v, w] = '[u, w] + '[v, w].
Proof. by rewrite -vdotrE linearD. Qed.
Lemma vdotBl u v w : '[u - v, w] = '[u, w] - '[v, w].
Proof. by rewrite -vdotrE linearB. Qed.
Lemma vdotMnl u v m : '[u *+ m, v] = '[u, v] *+ m.
Proof. by rewrite -!vdotrE linearMn. Qed.
Lemma vdotZl a u v : '[a *: u, v] = a * '[u, v].
Proof. by rewrite -vdotrE linearZ. Qed.

Lemma vdotC u v : '[u,v] = '[v,u]^*.
Proof.
by rewrite rmorph_sum; apply: eq_bigr => i _; rewrite rmorphM conjCK mulrC.
Qed.

Lemma vdotBr u v w : '[u, v - w] = '[u, v] - '[u, w].
Proof. by rewrite !(vdotC u) -rmorphB vdotBl. Qed.
Canonical vdot_additive u := Additive (vdotBr u).

Lemma vdot0r u : '[u,0] = 0.
Proof. exact: raddf0. Qed.
Lemma vdotNr u v : '[u, - v] = - '[u, v].
Proof. exact: raddfN. Qed.
Lemma vdotDr u v w : '[u, v + w] = '[u, v] + '[u, w].
Proof. exact: raddfD. Qed.
Lemma vdotMnr u v m : '[u, v *+ m] = '[u, v] *+ m.
Proof. exact: raddfMn. Qed.
Lemma vdotZr a u v : '[u, a *: v] = a^* * '[u, v].
Proof. by rewrite !(vdotC u) vdotZl rmorphM. Qed.

(* Order properties *)
Lemma vnorm_ge0 x : 0 <= '[x].
Proof. by rewrite sumr_ge0 // => i _; exact: mul_conjC_ge0. Qed.

Lemma vnorm_eq0 u : ('[u] == 0) = (u == 0).
Proof.
apply/idP/eqP=> [|->]; last by rewrite vdot0r.
move/eqP/psumr_eq0P=> /= u0; apply/matrixP=> i j.
apply/eqP; rewrite ord1 !mxE -mul_conjC_eq0.
by rewrite u0 // => y _; exact: mul_conjC_ge0.
Qed.

Lemma vnorm_gt0 u : ('[u] > 0) = (u != 0).
Proof. by rewrite ltr_def vnorm_ge0 vnorm_eq0 andbT. Qed.

(* Not the best proof. *)
Lemma vnorm_eq0' x : ('[x,x] == 0) = (x == 0).
Proof.
rewrite psumr_eq0; last by move=> ? ?; rewrite mul_conjC_ge0.
apply/allP; case: eqP => [->| /eqP H].
  by move=> i /= _; rewrite mul_conjC_eq0 mxE.
have [[i j] /= Hi] := (mx0P _ H).
move/(_ i); rewrite mem_index_enum.
by apply/implyP; rewrite ord1 mul_conjC_eq0 in Hi *.
Qed.

Lemma vnormZ a u : '[a *: u]= `|a| ^+ 2 * '[u].
Proof. by rewrite vdotZl vdotZr mulrA normCK. Qed.

Lemma vnormN u : '[- u] = '[u].
Proof. by rewrite vdotNl raddfN opprK. Qed.

Lemma vnormD u v :
  let d := '[u, v] in '[u + v] = '[u] + '[v] + (d + d^*).
Proof. by rewrite /= addrAC -vdotC vdotDl !vdotDr !addrA. Qed.

Lemma vnormB u v :
  let d := '[u, v] in '[u - v] = '[u] + '[v] - (d + d^*).
Proof. by rewrite /= vnormD vnormN vdotNr rmorphN -opprD. Qed.

(* pythagorean property *)
Lemma vnormDd u v : '[u, v] = 0 -> '[u + v] = '[u] + '[v].
Proof. by move=> ouv; rewrite vnormD ouv rmorph0 !addr0. Qed.

Lemma vnormBd u v : '[u, v] = 0 -> '[u - v] = '[u] + '[v].
Proof. by move=> ouv; rewrite vnormDd ?vnormN // vdotNr ouv oppr0. Qed.

(* Proof from classfun.v *)
Lemma vCauchySchwarz u v :
  `|'[u, v]| ^+ 2 <= '[u] * '[v] ?= iff ~~ free ([:: u; v]).
Proof.
rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC.
have [-> | nz_psi] /= := altP (v =P 0).
  by apply/lerifP; rewrite !vdot0r normCK mul0r mulr0.
without loss ou: u / '[u, v] = 0.
  move=> IHo; pose a := '[u, v] / '[v]; pose u1 := u - a *: v.
  have ou: '[u1, v] = 0.
     by rewrite vdotBl vdotZl divfK ?vnorm_eq0 ?subrr //.
  rewrite (canRL (subrK _) (erefl u1)) rpredDr ?rpredZ ?memv_line //.
  rewrite vdotDl ou add0r vdotZl normrM (ger0_norm (vnorm_ge0 _)).
  rewrite exprMn mulrA -vnormZ vnormDd; last by rewrite vdotZr ou mulr0.
  by have:= IHo _ ou; rewrite mulrDl -lerif_subLR subrr ou normCK mul0r.
rewrite ou normCK mul0r; split; first by rewrite mulr_ge0 ?vnorm_ge0.
rewrite eq_sym mulf_eq0 orbC vnorm_eq0 (negPf nz_psi) /=.
apply/idP/idP=> [|/vlineP[a {2}->]]; last by rewrite vdotZr ou mulr0.
by rewrite vnorm_eq0 => /eqP->; apply: rpred0.
Qed.

Lemma vCauchySchwarz_sqrt u v :
  `|'[u, v]| <= sqrtC '[u] * sqrtC '[v] ?= iff ~~ free [:: u; v].
Proof.
rewrite -(sqrCK (normr_ge0 _)) -sqrtCM ?qualifE ?vnorm_ge0 //.
rewrite (mono_in_lerif ler_sqrtC) 1?rpredM ?qualifE ?normr_ge0 ?vnorm_ge0 //.
exact: vCauchySchwarz.
Qed.

Lemma v_triangle_lerif u v :
  sqrtC '[u + v] <= sqrtC '[u] + sqrtC '[v]
           ?= iff ~~ free [:: u; v] && (0 <= coord [tuple v] 0 u).
Proof.
rewrite -(mono_in_lerif ler_sqr) ?rpredD ?qualifE ?sqrtC_ge0 ?vnorm_ge0 //.
rewrite andbC sqrrD !sqrtCK addrAC vnormD (mono_lerif (ler_add2l _)).
rewrite -mulr_natr -[_ + _](divfK (negbT (eqC_nat 2 0))) -/('Re _).
rewrite (mono_lerif (ler_pmul2r _)) ?ltr0n //.
have:= lerif_trans (lerif_Re_Creal '[u, v]) (vCauchySchwarz_sqrt u v).
congr (_ <= _ ?= iff _); apply: andb_id2r.
rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC.
have [-> | nz_psi] := altP (v =P 0); first by rewrite vdot0r coord0.
case/vlineP=> [x ->]; rewrite vdotZl linearZ pmulr_lge0 ?vnorm_gt0 //=.
by rewrite (coord_free 0) ?seq1_free // eqxx mulr1.
Qed.

Definition isometry M := forall u v, '[M u, M v] = '[u, v].

(*******************************************************************************)
(* Stuff from the previous development and proof, still dunno what to do       *)
(*******************************************************************************)

(* Remove? *)
Lemma vnorm_parallelogram x y : 2%:R*'[x] + 2%:R*'[y] = '[x+y] + '[x-y].
Proof. by rewrite vnormD vnormB addrACA subrr addr0 addrACA !mulr_natl. Qed.

Lemma normx_parallelogram_l x y : '[x-y] = 2%:R*'[x] + 2%:R*'[y] - '[x+y].
Proof. by apply/eqP; rewrite -subr_eq opprK vnorm_parallelogram addrC. Qed.

Lemma vnorm_parallelogram_r x y : '[x+y] = 2%:R*'[x] + 2%:R*'[y] - '[x-y].
Proof. by apply/eqP; rewrite -subr_eq opprK vnorm_parallelogram addrC. Qed.

(* Extra? *)
Lemma vnorm_norm x : `|'[x]| = '[x].
Proof. by rewrite ger0_norm ?vnorm_ge0. Qed.
Lemma vnorm_conjC x : '[x]^* = '[x].
Proof. by rewrite conj_Creal ?realE ?vnorm_ge0. Qed.

Lemma addxxC (x : C) : x + x^* = 'Re x *+ 2.
Proof.
rewrite {1 2}[x]algCrect rmorphD rmorphM conjCi.
by rewrite !conj_Creal ?Creal_Im ?Creal_Re // addrA addrAC mulNr addrK.
Qed.

Lemma vdotDC u v : '[u,v] + '[v,u] = 'Re '[u,v] *+ 2.
Proof. by rewrite ['[v,_]]vdotC addxxC. Qed.

Lemma vdot_neq0l u v : '[u,v] != 0 -> u != 0.
Proof. by apply/contra=> /eqP->; rewrite vdot0l. Qed.
Lemma vdot_neq0r u v : '[u,v] != 0 -> v != 0.
Proof. by apply/contra=> /eqP->; rewrite vdot0r. Qed.
Lemma vdot_neq0 u v : '[u,v] != 0 -> (u != 0) && (v != 0).
Proof. by move=> ouv; rewrite ?(vdot_neq0l ouv, vdot_neq0r ouv). Qed.

End InnerProduct.

Notation "''[' u , v ]" := (vdot u v) : ring_scope.
Notation "''[' u ]" := '[u, u] : ring_scope.

(* Some additional properties of the primitive n.-roots of the unity. We
 * assume n > 1, n = {0,1} is not very interesting.
 *)

Section PrimitiveRoot.

Variable N : nat.
Notation n := N.+2.
Variable F : fieldType.
Variable z : F.
Hypothesis zP : n.-primitive_root z.

Lemma z_neq1 : z != 1.
Proof. by rewrite (eq_prim_root_expr zP 1 0). Qed.

Lemma z_expr_neq1 i : (0 < i < n)%N -> z ^+ i != 1.
Proof.
by case/andP=>??; rewrite (eq_prim_root_expr zP i 0) eqn_mod_dvd ?subn0 ?gtnNdvd.
Qed.

Lemma unitrzn : z ^+ n \is a GRing.unit.
Proof. by rewrite prim_expr_order ?unitr1. Qed.

Lemma unitrz : z \is a GRing.unit.
Proof. by rewrite -(unitrX_pos _ (ltn0Sn n.-1)) ?unitrzn. Qed.

Lemma z_neq0 : z != 0.
Proof. by rewrite -unitfE unitrz. Qed.

Lemma sum_expr_z_zero : \sum_(0 <= j < n) z ^+ j = 0.
Proof. by rewrite sumr_expr ?z_neq1 ?prim_expr_order ?subrr ?mul0r. Qed.

Lemma prim_expr_oppr (i : 'I_n) : z ^+ (-i) = z ^- i.
Proof.
rewrite -[z^-i]mul1r -(prim_expr_order zP) -exprB ?unitrz ?prim_expr_mod //.
by rewrite ltnW ?ltn_ord.
Qed.

(* XXX: These two lemmas should be rethought *)
Lemma prim_expr_addn (i j : 'I_n) : z ^+ (i + j) = z ^+ (i + j)%R.
Proof. by rewrite prim_expr_mod. Qed.

Lemma prim_expr_muln (i j : 'I_n) : z ^+ (i * j) = z ^+ (i * j)%R.
Proof. by rewrite prim_expr_mod. Qed.

End PrimitiveRoot.

(* XXX: Hints don't work well in our context... *)
Hint Resolve z_neq0 z_neq1 unitrz unitrzn.

(* We also define cyclic exponentiation, not very clear how
 * much we gain from it for now...
 *)

Reserved Notation "x @+ n" (at level 29, left associativity).
Reserved Notation "x @- n" (at level 29, left associativity).

Section CyclicExp.

Section Def.
Variable n : nat.
Variable F : fieldType.

Definition expz_def (z : F) (i : 'I_n) := z ^+ i.

Definition expz := nosimpl expz_def.

End Def.

Section Theory.

Variable N' : nat.
Notation N := N'.+2.
Variable F : fieldType.

(* z is a n-primitive root *)
Variable z : F.
Hypothesis zP : N.-primitive_root z.

Local Notation "x @+ n" := (expz x n) : ring_scope.
Local Notation "x @- n" := (expz x (-n)) : ring_scope.

Implicit Types (m n : 'I_N).

Lemma expzE n : z @+ n = z ^+ n.
Proof. by []. Qed.

Lemma expz0 : z @+ (@ord0 N'.+1) = 1.
Proof. by rewrite !expzE expr0. Qed.

Lemma expzD m n : z @+ (m + n) = z @+ m * z @+ n.
Proof. by rewrite !expzE prim_expr_mod ?exprD. Qed.

(* About exprB. *)
(* x ^+ (m - n) = x ^+ m / x ^+ n *)
(* Lemma expzB m n : z @+ (m + n) = z @+ m * z @+ n. *)
(* Proof. by rewrite !expzE prim_expr_mod ?exprD. Qed. *)

Lemma expzM m n : z @+ (m * n) = z @+ m @+ n.
Proof. by rewrite !expzE prim_expr_mod ?exprM. Qed.

Lemma expzV n : (z @+ n)^-1 = z @- n.
Proof.
rewrite !expzE prim_expr_mod // exprB; last exact: unitrz.
  by rewrite (prim_expr_order zP) // div1r.
by rewrite ltnW ?ltn_ord.
Qed.

End Theory.
End CyclicExp.

Notation "x @+ n" := (expz x n)    : ring_scope.
Notation "x @- n" := (expz x (-n)) : ring_scope.

Section PrimitiveNumRoot.

Variable N : nat.
Notation n := N.+2.
Variable R : numDomainType.
Variable z : R.
Hypothesis zP : n.-primitive_root z.

(* Norms and primitive roots *)
Lemma norm_prim : `|z| = 1.
Proof.
apply: (pexpIrn (ltn0Sn n.-1)); rewrite ?nnegrE ?normr_ge0 //.
by rewrite -normrX prim_expr_order ?expr1n ?normr1.
Qed.

Lemma norm_primX k : `|z^+k| = 1.
Proof. by rewrite normrX norm_prim expr1n. Qed.

(* Lemma norm_neg : z *)
End PrimitiveNumRoot.

(* Concrete, complex primitive root *)

Section PrimitiveRootC.

Variable N : nat.
Notation n := N.+2.

Definition p_root :=
  let: exist z _ := C_prim_root_exists (ltn0Sn n.-1) in z.

Notation z := p_root.

Lemma zP : n.-primitive_root p_root.
Proof. by rewrite /p_root; case: (C_prim_root_exists _). Qed.

Lemma conj_zP : n.-primitive_root z^*.
Proof. by rewrite fmorph_primitive_root zP. Qed.

Hint Resolve zP conj_zP.

(* Conjugate and algebraic primitive roots *)
Lemma prim_conj : z^* = z^-1.
Proof. by rewrite invC_norm (norm_prim zP) expr2 mul1r invr1 mul1r. Qed.

Lemma prim_expr_conj k : (z ^+ k)^* = z ^- k.
Proof. by rewrite rmorphX prim_conj exprVn. Qed.

Lemma expz_conjC (k : 'I_n) : (z @+ k)^* = z @- k.
Proof. by rewrite -expzV // rmorphX -exprVn prim_conj. Qed.

(* Lemma prim_expr_ord_conj k : (z ^+ k)^* = z ^+ (- k). *)
(* Proof. by rewrite rmorphX prim_conj exprVn. Qed. *)

(* Orthogonality and (vector) norm *)
Lemma prim_exprnX i : z ^+ n ^+ i = 1.
Proof. by rewrite (prim_expr_order zP) expr1n. Qed.

Lemma prim_exprXn i : z ^+ i ^+ n = 1.
Proof. by rewrite exprAC prim_exprnX. Qed.

Lemma inner_z (i j : 'I_n) : \sum_(k < n) (z ^+ (i * k)) * (z ^+ (j * k))^* = n%:R * (i == j)%:R.
Proof.
transitivity (\sum_(k < n) z^+(i - j)%R ^+ k).
  apply: eq_bigr => k _.
  rewrite prim_expr_conj !prim_expr_muln -?prim_expr_oppr //.
  rewrite -exprD prim_expr_addn //.
  by rewrite -mulrBl -prim_expr_muln // exprM.
case: eqP => [->| /eqP Hneq ].
  by rewrite subrr expr0 -(big_mkord predT) sum1_expr mulr_natr.
rewrite mulr_natr mulr0n -(big_mkord predT) sumr_expr.
  by rewrite exprAC (prim_expr_order zP) expr1n subrr mul0r.
rewrite (z_expr_neq1 zP) // ltn_ord andbT ltn_neqAle.
by rewrite -subr_eq0 eq_sym in Hneq; rewrite Hneq.
Qed.

(* A tad shorter using cyclic exponentiation. *)
Lemma inner_z' (i j : 'I_n) :
  \sum_(k < n) (z @+ (i * k)) * (z @+ (j * k))^* = n%:R * (i == j)%:R.
Proof.
transitivity (\sum_(k < n) z @+ (i - j) @+ k).
  by apply: eq_bigr => k _; rewrite expz_conjC -expzD -?expzM ?mulrBl.
rewrite -subr_eq0; case: eqP => [->| /eqP Hneq].
  by rewrite expz0 -(big_mkord predT) sum1_expr mulr_natr.
rewrite mulr_natr mulr0n -(big_mkord predT) sumr_expr.
  by rewrite exprAC (prim_expr_order zP) expr1n subrr mul0r.
by rewrite (z_expr_neq1 zP) // ltn_ord andbT ltn_neqAle eq_sym Hneq.
Qed.

(* Some facts about unity roots of even order. *)
Local Open Scope nat.
Lemma mod_sub_transfer (k m : 'I_n) (H : (k <= m) ) :
   (m - k)%R == m - k %[mod n].
Proof.
rewrite modn_mod /= -[(m-k)%%n]modnDl.
rewrite addnBA ?[n+m]addnC -?addnBA //; last by rewrite ltnW.
by rewrite eqn_modDl modn_mod.
Qed.
Local Open Scope ring_scope.

Lemma expcB (k m : 'I_n) : z @+ (k - m) = (z @+ k / z @+ m).
Proof.
apply/eqP; case: (k < m)%N / leqP => [H|H].
  by rewrite expzE -exprB ?(unitrz zP, eq_prim_root_expr zP, mod_sub_transfer).
rewrite -(inj_eq invr_inj) invf_div expzV //.
rewrite opprB !expzE -exprB 1?ltnW ?(unitrz zP) //.
by rewrite (eq_prim_root_expr zP) mod_sub_transfer // ltnW.
Qed.

Lemma two_unity_root (i : algC) : 2.-unity_root i = (i \in [:: -1; 1]).
apply: mem_unity_roots => //=; last first.
  by rewrite inE // andbT eq_sym -addr_eq0 (_ : 1 + 1 = 2%:R) ?pnatr_eq0.
by rewrite !unity_rootE !exprS !expr0 !mulr1 mulrNN mulr1 eqxx.
Qed.

Lemma leq_half n : (n./2 <= n)%N.
Proof. by rewrite -{2}[n]doubleK half_leq // -muln2 leq_pmulr. Qed.

(* Facts for roots of even order *)
Section EvenTheory.
(* XXX: A better formulation than n_e would be to require the primitive root
   to be of order n.*2...
*)
Variable (n_e : ~~ odd n).

Lemma divz2 : z ^+ (n./2)%N = -1.
Proof.
have eon : 0%N = odd n :> nat by case: odd n_e.
have/unity_rootP : z ^+ n./2 ^+ 2 = 1.
  by rewrite -exprM muln2 -[_.*2]add0n eon odd_double_half prim_expr_order.
rewrite two_unity_root !inE; case/orP=> /eqP //.
suff/eqP : z ^+ n./2 != 1 by [].
by apply: (z_expr_neq1 zP); rewrite /= !ltnS leq_half.
Qed.

Lemma expz_oppC (k : 'I_n) : z @+ k = - (z @+ (k + inord n./2)).
Proof.
apply/eqP; rewrite -mulN1r eq_sym eq_mulr ?(unitrX, unitrz zP) //.
rewrite -expcB ?opprD ?addNKr ?(z_neq0 zP) // -expzV // expzE.
(* XXX: warning about the unfold_in comment *)
by rewrite insubdK ?divz2 ?invrN1 // unfold_in 2!ltnS leq_half.
Qed.
End EvenTheory.

End PrimitiveRootC.

Implicit Arguments zP [N].
Implicit Arguments conj_zP [N].
Hint Resolve zP conj_zP.

(* Theory of periodic, finite signals. *)
(* We follow https://ccrma.stanford.edu/~jos/mdft/ *)
Section Signals.

Variable N' : nat.
Notation N := N'.+2.
Variable R : comRingType.

(* We represent signals as n x 1 matrices *)
Notation S := 'cV[R]_N.

Implicit Types x y : S.
Implicit Types n m : 'I_N.

(* Flip and shift of a signal *)
Definition flips x := \col_k (x (-k) 0).

Lemma flipsE x i j : (flips x) i j = x (-i) 0.
Proof. by rewrite mxE. Qed.

Lemma flipsK : involutive flips.
Proof. by move=> x; apply/matrixP=> i j; rewrite !mxE opprK ord1. Qed.

Lemma flipsI : injective flips.
Proof. exact: (inv_inj flipsK). Qed.

Definition shifts x n := \col_k (x (k - n) 0).

Lemma shiftsE x n i j : (shifts x n) i j = x (i - n) 0.
Proof. by rewrite mxE. Qed.

Lemma shifts_bij n : bijective (shifts^~n).
Proof.
by exists (shifts^~(-n)); move=> ? /=; apply/matrixP=> ? ?;
rewrite !mxE opprK ord1 ?(addrK,addrNK).
Qed.

Lemma shiftsI n : injective (shifts^~n).
Proof. exact: (bij_inj (shifts_bij _)). Qed.

(* Definition as a permutation matrix *)
Definition perm_n (n : 'I_N) : 'S_N := perm (addrI n).
Definition shift_mx x n := row_perm (perm_n n) x.

(* Circular convolution of two signals *)
Definition convs x y := \col_k \sum_m x m 0 * y (k-m) 0.

Lemma convsC : commutative convs.
Proof.
move=> x y; apply/matrixP=> n k; rewrite !mxE {k}.
rewrite (reindex_inj (inj_comp (addrI n) oppr_inj)).
by apply/eq_bigr=> m _; rewrite opprD addNKr opprK mulrC.
Qed.

(* TODO: Convolution in terms of the inner product:
   https://ccrma.stanford.edu/~jos/mdft/Inner_Product.html
*)

End Signals.

(*
  We develop both forms of the DFT. For the matrix form we have
  opted for an explicit form instead of defining Vandermonde
  matrices.
*)

Section Dft.

Variable N' : nat.
Notation N := N'.+2.
Notation R := algC.
Notation S := 'cV[R]_N.

Notation "'ω" := (@p_root N').

Implicit Types x y : S.

(* The DFT matrix itself. *)
Definition W := \matrix_(i < N, j < N) 'ω ^+ (i*j).

(* W is symmetric *)
Lemma tr_W : W^T = W.
Proof. by apply/matrixP=> i j; rewrite !mxE mulnC. Qed.

Lemma vdot_hermitl n (A : 'M_n) u v : '[u, A *m v]%:M = '[conjM A *m u, v]%:M :> 'M_1.
Proof. by rewrite !vdot_def /conjM trmx_mul map_mxM mulmxA. Qed.

Lemma vdot_hermitr n (A : 'M_n) u v : '[A *m u, v]%:M = '[u, conjM A *m v]%:M :> 'M_1.
Proof. by rewrite vdot_hermitl conjMK. Qed.

Lemma mx11_scalarP (F : ringType) n (A B : F) : A = B <-> A%:M = B%:M :> 'M_n.+1.
Proof.
by split=>[->//|]; move/matrixP/(_ 0 0); rewrite !mxE eqxx.
Qed.

Lemma mxlift_inj (R : ringType) (x y : R) : x%:M = y%:M :> 'M_1 -> x = y.
Proof. by rewrite -mx11_scalarP. Qed.

Lemma mulmxP (K : fieldType) (m n : nat) (A B : 'M[K]_(m, n)) :
  reflect (forall u : 'rV__, u *m A = u *m B) (A == B).
Proof.
apply/(iffP eqP)=> [-> //|eqAB].
apply/(@row_full_inj _ _ _ _ 1%:M); first by rewrite row_full_unit unitmx1.
by apply/row_matrixP=> i; rewrite !row_mul eqAB.
Qed.

Definition to_mx1 (R : ringType) := congr1 (@scalar_mx R 1).

(* The inner product is preserved '[A *m u, A *m v] = '[u,v] iif A * A^* == 1 *)
Lemma unitary_dotP n (A : 'M_n) :
  reflect (isometry (mulmx A)) (conjM A *m A == 1%:M).
Proof.
rewrite /isometry; apply/(iffP eqP)=> [aa1 u v|auv].
  by apply/mxlift_inj; rewrite vdot_hermitl mulmxA aa1 mul1mx.
apply/eqP/mulmxP=> u; apply/trmx_inj/eqP/mulmxP=> v; apply/trmx_inj.
have/to_mx1 := auv v^T (conjM u).
by rewrite !trmx_mul !trmxK mulmx1 !vdot_hermitl !vdot_def conjMK !mulmxA .
Qed.

(*
Print Assumptions unitary_dotP.
Closed under the global context
*)

Lemma unitary_W : W *m conjM W = N%:R%:M.
Proof.
apply/matrixP=> i j; rewrite !mxE.
transitivity (\sum_(k < N) 'ω ^+ (i * k) * ('ω ^+ (j * k))^*).
  by apply/eq_bigr=> k _; rewrite !mxE.
by rewrite inner_z mulr_natr.
Qed.

(* XXX: proof using unitary_W and trmx_mul *)
Lemma unitary_W0 : conjM W *m W = N%:R%:M.
Proof.
by rewrite /conjM -map_trmx -{2}tr_W -trmx_mul -{2}tr_W unitary_W tr_scalar_mx.
Qed.

Lemma unitaryC : conjM W *m W = W *m conjM W.
Proof. by rewrite unitary_W unitary_W0. Qed.

Lemma unitary_dft m n : '[W *m m, W *m n] = N%:R * '[m,n].
Proof.
(* by rewrite vdot_hermit mulmxA unitary_W0 mul_scalar_mx vdotZl.*)
apply/eqP.
have uN : (N%:R : algC) \is a GRing.unit by rewrite ?unitfE ?pnatr_eq0.
have uSN: sqrtC N%:R    \is a GRing.unit by rewrite ?unitfE sqrtC_eq0 ?pnatr_eq0.
rewrite eq_sym eq_mull // mulrC -[N%:R]sqrtCK expr2.
rewrite invrM // -mulrA -vdotZl -{1}[(sqrtC _)^-1]conjCK -vdotZr.
rewrite geC0_conj ?invr_ge0 ?sqrtC_ge0 ?ler0n // !scalemxAl eq_sym.
apply/eqP/unitary_dotP.
rewrite /conjM !linearZ /= map_mxZ -scalemxAl scalerA.
rewrite geC0_conj ?invr_ge0 ?sqrtC_ge0 ?ler0n // unitary_W0.
by rewrite -invrM // -expr2 sqrtCK scale_scalar_mx mulrC divrr.
Qed.

(*
Print Assumptions unitary_dft.
Section Variables:
N' : nat
*)

Lemma dft_energy m : '[m] = 1/N%:R * '[W *m m].
Proof. by rewrite unitary_dft mulrA divrK ?mul1r // unitfE pnatr_eq0. Qed.

(* DFT in sum form *)
Definition dft x k := \sum_n (x n 0) * 'ω ^+ (k*n).

Lemma dftE x k : (W *m x) k 0 = dft x k.
Proof. by rewrite !mxE; apply/eq_bigr=> n _; rewrite !mxE mulrC. Qed.

End Dft.

Implicit Arguments W [N'].

(* Some simple examples *)
Section DFTExamples.

Let N := 4.
Notation "'ω" := (@p_root 2).
Notation R := algC.
Notation S := 'cV[R]_N.

Definition dc_signal : S := \col_j 1.

Lemma dcD : dft dc_signal 0 = 4%:R.
Proof.
by rewrite /dft !big_ord_recl big_ord0 /= !mxE !mul1r !muln0 !expr0 addr0.
Qed.

Definition hf_signal : S := \col_j (-1) ^+ j.

(* XXX: We should take the norm of the resulting DFT complex *)
Lemma hfD : dft hf_signal 2 = 4%:R.
Proof.
rewrite /dft !big_ord_recl big_ord0 /= !mxE !expr0 !exprS !mulr1 addr0.
rewrite -['ω]expr1 -!exprS -!exprM !mul1n !(mulN1r, mul1r,mulr1, opprK).
rewrite (_ : 6 = (2 + 4)%N) // exprD !(prim_expr_order zP) mulr1.
have-> : 'ω ^+ 2 = -1 by apply: divz2.
by rewrite opprK.
Qed.

Lemma hfD0 : dft hf_signal 0 = 0.
Proof.
rewrite /dft !big_ord_recl big_ord0 /= !mxE !expr0 !exprS !mulr1 addr0.
by rewrite ?(mulN1r, opprK, addrA, addrK, subrr).
Qed.

Lemma hfD1 : dft hf_signal 1 = 0.
Proof.
rewrite /dft !big_ord_recl big_ord0 /= !mxE !expr0 !exprS !mul1r !mulr1 addr0.
rewrite ?(mul1r, mulN1r, opprK, addrA, addrK, subrr).
rewrite -!expr2 mulrC -exprSr divz2 //.
rewrite -addrA addrAC addrA subrr add0r.
(* Should be yet easier to prove *)
have {2}-> : 'ω = - 'ω ^+ 3.
  have Uw : 'ω = 'ω @+ (@inord 3 1) by rewrite expzE // insubdK.
    by rewrite {1}Uw expz_oppC ?expzE //= !insubdK //.
by rewrite opprK addrC subrr.
Qed.

(* Print Assumptions hfD.
   Closed under the global context
*)

End DFTExamples.

(* DFT properties for the sum form *)
Section DftSum.

Variable N' : nat.
Notation N := N'.+2.
Notation R := algC.
Notation S := 'cV[R]_N.
Notation "'ω" := (@p_root N').
Implicit Types x y : S.

(* Linearity & scaling *)
Lemma dft_sum x y k : dft (x + y) k = dft x k + dft y k.
Proof. by rewrite -big_split /=; apply/eq_bigr=> i _; rewrite -mulrDl mxE. Qed.

Lemma dft_scale a x k : a * dft x k = dft (a *: x) k.
Proof. by rewrite mulr_sumr; apply/eq_bigr=> ? _; rewrite mxE mulrA. Qed.

Lemma dft_shifts x m k : dft (shifts x m) k = 'ω ^+ (k * m) * dft x k.
Proof.
rewrite /dft (reindex_inj (addIr m)) mulr_sumr.
apply/eq_bigr => i _; rewrite shiftsE.
by rewrite addrK mulrCA mulnC !exprM prim_expr_mod // exprAC addnC exprD.
Qed.

Require Import finalg.

Lemma dft_flips x (k : 'I_N) : dft (flips x) k = dft x (-k).
Proof.
rewrite /dft (reindex_inj oppr_inj).
by apply/eq_bigr=> i _; rewrite flipsE opprK !prim_expr_muln ?mulrN ?mulNr.
Qed.

(* We could put in form as in:
   https://ccrma.stanford.edu/~jos/mdft/Conjugation_Reversal.html
 *)

Lemma dft_conj x (k : 'I_N) : dft (map_mx conjC x) k = (dft x (-k))^*.
Proof.
rewrite (big_morph _ (rmorphD conjC) (rmorph0 _)).
apply/eq_bigr => i _; rewrite rmorphM mxE.
by rewrite prim_expr_conj !prim_expr_muln ?(mulNr, prim_expr_oppr, invrK).
Qed.

Lemma conj_dft x (k : 'I_N) : dft (map_mx conjC (flips x)) k = (dft x k)^*.
Proof. by rewrite (dft_conj (flips x) k) dft_flips opprK. Qed.

(* (Circular) Convolution theorem. *)
(* XXX: Clean this up a bit more *)
Lemma dft_convs x y k : dft (convs x y) k = dft x k * dft y k.
Proof.
rewrite /dft (eq_bigr (fun i => \sum_m x m 0 * y (i - m) 0 * 'ω ^+ (k*i)));
  last by move=> ? ?; rewrite !mxE mulr_suml.
rewrite big_distrlr /= exchange_big.
apply/eq_bigr=> i _; rewrite -!mulr_sumr -mulrA -dft_shifts mulr_sumr.
by apply/eq_bigr => j _; rewrite shiftsE mulrA.
Qed.

(*
Print Assumptions dft_convs.
Section Variables:
N' : nat
*)
End DftSum.

(* Lemmas about the DFT in matrix form:
   https://ccrma.stanford.edu/~jos/mdft/Matrix_Formulation_DFT.html
*)
Section DftMatrix.

Variable N' : nat.
Notation N := N'.+2.
Notation R := algC.
Notation S := 'cV[R]_N.
Notation "'ω" := (@p_root N').
Implicit Types x y : S.

(* Linearity *)
Lemma dftDr x y : W *m (x + y) = W *m x + W *m y.
Proof. exact: linearD. Qed.

Lemma dftScale a x : a *: (W *m x) = W *m (a *: x) .
Proof. by rewrite linearZ. Qed.

(* Shift *)

(* Lemma dft_shifts x m k : dft (shifts x m) k = 'ω ^+ (k * m) * dft x k. *)
(* This could be a matrix rotation *)
Lemma dft_shift x m : W *m (shifts x m) = \col_k ('ω ^+ (k * m) * (W *m x) k 0).
Proof. by apply/matrixP=> k o; rewrite ord1 dftE dft_shifts -dftE !mxE. Qed.

(* Inverse DFT. *)
Lemma unitary_inv n (A : 'M_n) (aa1 : A *m conjM A = 1%:M) : invmx A = conjM A.
Proof.
case/mulmx1_unit: (aa1) => a_u ca_u; apply/eqP.
by rewrite -(can_eq (mulKmx a_u)) aa1 mulmxV.
Qed.

End DftMatrix.

