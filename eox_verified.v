(** * EOX: Exposure-Oriented Extinction Game Theory Framework

    A complete formalization of the EOX game with asymptotic null-exposure dominance,
    discrete extinction theorems, and comparative statics - all without axioms.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Ranalysis.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Set Warnings "-ambiguous-paths".
Require Import Coquelicot.Coquelicot.
Set Warnings "ambiguous-paths".
Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.
Generalizable All Variables.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ** 0. Preamble & Shared Utilities *)

(** *** Standard predicates *)
Definition nondecreasing (f : R -> R) := forall x y, x <= y -> f x <= f y.
Definition increasing (f : R -> R) := forall x y, x < y -> f x < f y.
Definition nonneg (x : R) := 0 <= x.

(** *** Notations *)
Notation "x ⩽ y" := (x <= y)%R (at level 70).
Notation "x ≥ 0" := (0 <= x)%R (at level 70).

(** *** Fundamental helper lemmas *)

(** exp(t) ≥ 1 + t for all t *)
Lemma exp_ge_1_plus : forall t : R, 1 + t <= exp t.
Proof.
  intro t.
  destruct (Rle_dec 0 t) as [Ht_nonneg | Ht_neg].
  - destruct (Req_dec t 0) as [Heq | Hneq].
    + subst. rewrite Rplus_0_r, exp_0. lra.
    + apply Rlt_le. apply exp_ineq1. lra.
  - destruct (Req_dec t (-1)) as [Heq_m1 | Hneq_m1].
    + subst. simpl. assert (Hexp1 : exp 1 > 0) by apply exp_pos.
      assert (Hexp_m1 : exp (-1) = / exp 1).
      { assert (Hprod : exp (-1) * exp 1 = 1).
        { rewrite <- exp_plus. ring_simplify (-1 + 1). apply exp_0. }
        apply Rmult_eq_reg_r with (r := exp 1).
        - rewrite Rinv_l; [exact Hprod | apply Rgt_not_eq; exact Hexp1].
        - apply Rgt_not_eq. exact Hexp1. }
      replace (1 + -1) with 0 by ring.
      rewrite Hexp_m1.
      apply Rlt_le. apply Rinv_0_lt_compat. exact Hexp1.
    + destruct (Rle_dec (-1) t) as [Ht_ge_m1 | Ht_lt_m1].
      * assert (Ht_gt_m1 : -1 < t) by lra.
        pose proof (MVT_cor2 exp (fun x => exp x) t 0) as HMVT.
        assert (Hderiv : forall c, t <= c <= 0 -> derivable_pt_lim exp c (exp c)).
        { intros c _. apply derivable_pt_lim_exp. }
        assert (Ht_lt_0 : t < 0) by lra.
        assert (Hexists : exists c, exp 0 - exp t = exp c * (0 - t) /\ t < c < 0).
        { apply HMVT. lra. assumption. }
        destruct Hexists as [c [Heq [Hc1 Hc2]]].
        assert (Heq2 : exp t - exp 0 = exp c * t).
        { assert (H1 : exp 0 - exp t = - (exp t - exp 0)) by ring.
          assert (H2 : 0 - t = - t) by ring.
          rewrite H1, H2 in Heq.
          assert (H3 : - (exp t - exp 0) = exp c * (- t)) by exact Heq.
          apply Ropp_eq_compat in H3.
          replace (- - (exp t - exp 0)) with (exp t - exp 0) in H3 by ring.
          replace (- (exp c * - t)) with (exp c * t) in H3 by ring.
          exact H3. }
        assert (Heq3 : exp t = 1 + exp c * t).
        { rewrite exp_0 in Heq2.
          assert (Hsimpl : exp t - 1 = exp c * t) by (rewrite <- Heq2; ring).
          lra. }
        assert (Hc_bounds : t < c < 0) by (split; [exact Hc1 | exact Hc2]).
        assert (Hexp_c_lt_1 : exp c < 1).
        { assert (Hc_neg : c < 0) by lra.
          apply exp_increasing in Hc_neg.
          rewrite exp_0 in Hc_neg.
          exact Hc_neg. }
        rewrite Heq3.
        assert (Hgoal_strict : t < t * exp c).
        { apply Ropp_lt_cancel.
          replace (- t) with (- t * 1) by ring.
          replace (- (t * exp c)) with (- t * exp c) by ring.
          apply Rmult_lt_compat_l.
          - lra.
          - exact Hexp_c_lt_1. }
        assert (Hfinal : 1 + t < 1 + exp c * t).
        { replace (exp c * t) with (t * exp c) by ring.
          apply Rplus_lt_compat_l. exact Hgoal_strict. }
        apply Rlt_le. exact Hfinal.
      * apply Rle_trans with (r2 := 0); [lra | apply Rlt_le; apply exp_pos].
Qed.

(** For 0 ≤ y ≤ 1: 1 - y ≤ exp(-y) *)
Lemma one_minus_le_exp : forall y : R, 0 <= y <= 1 -> 1 - y <= exp (- y).
Proof.
  intros y [Hy0 Hy1].
  assert (H : 1 + (- y) <= exp (- y)).
  { apply exp_ge_1_plus. }
  lra.
Qed.

(** For 0 < y < 1: ln(1 - y) ≤ -y *)
Lemma log_one_minus_le_opp : forall y : R, 0 < y < 1 -> ln (1 - y) <= - y.
Proof.
  intros y [Hy0 Hy1].
  assert (H1my_pos : 0 < 1 - y) by lra.
  assert (Hexp : 1 - y <= exp (- y)).
  { apply one_minus_le_exp. lra. }
  assert (Hln_ineq : ln (1 - y) <= ln (exp (- y))).
  { assert (Hexp_pos : 0 < exp (- y)) by apply exp_pos.
    destruct (Rle_lt_or_eq_dec (1 - y) (exp (- y)) Hexp) as [Hlt | Heq].
    - apply Rlt_le. apply ln_increasing; lra.
    - rewrite Heq. apply Req_le. reflexivity. }
  rewrite ln_exp in Hln_ineq.
  exact Hln_ineq.
Qed.

Lemma fold_right_Rmult_nonneg : forall (l : list R),
  (forall x, In x l -> 0 <= x) -> 0 <= fold_right Rmult 1 l.
Proof.
  induction l as [| h t IH]; intros H.
  - simpl. lra.
  - simpl. apply Rmult_le_pos.
    + apply H. simpl. left. reflexivity.
    + apply IH. intros x Hx. apply H. simpl. right. assumption.
Qed.

Lemma seq_S : forall start len,
  seq start (S len) = start :: seq (S start) len.
Proof.
  intros. reflexivity.
Qed.

Lemma fold_right_Rmult_app : forall l1 l2,
  fold_right Rmult 1 (l1 ++ l2) = fold_right Rmult 1 l1 * fold_right Rmult 1 l2.
Proof.
  induction l1; intros l2.
  - simpl. ring.
  - simpl. rewrite IHl1. ring.
Qed.

Lemma seq_last : forall (start len : nat),
  seq start (S len) = seq start len ++ [(start + len)%nat].
Proof.
  intros start len. revert start.
  induction len; intros start.
  - simpl. f_equal. lia.
  - rewrite seq_S at 1. simpl app.
    f_equal. rewrite IHlen.
    simpl app. f_equal. f_equal. lia.
Qed.

(** Product of (1 - p_i) upper bounded by exp(- sum p_i) when p_i in [0,1] *)
Lemma prod_one_minus_le_exp_sum : forall (n : nat) (p : nat -> R),
  (n > 0)%nat ->
  (forall i, (i < n)%nat -> 0 <= p i <= 1) ->
  fold_right Rmult 1 (map (fun i => 1 - p i) (seq 0 n)) <=
  exp (- sum_f_R0 p (pred n)).
Proof.
  induction n as [| n IH]; intros p Hn Hp.
  - lia.
  - destruct n as [| n'].
    + simpl seq. simpl map. simpl fold_right.
      assert (H_pred : pred 1 = 0%nat) by reflexivity.
      rewrite H_pred.
      unfold sum_f_R0. simpl.
      rewrite Rmult_1_r.
      assert (Hp0 : 0 <= p 0%nat <= 1) by (apply Hp; lia).
      apply one_minus_le_exp. assumption.
    + assert (Hn' : (S n' > 0)%nat) by lia.
      assert (Hp_n : forall i, (i < S n')%nat -> 0 <= p i <= 1).
      { intros i Hi. apply Hp. lia. }
      specialize (IH p Hn' Hp_n).
      assert (HpSn' : 0 <= p (S n') <= 1).
      { apply Hp. lia. }
      assert (H1 : 1 - p (S n') <= exp (- p (S n'))).
      { apply one_minus_le_exp. assumption. }
      assert (Hprod_nonneg : 0 <= fold_right Rmult 1 (map (fun i : nat => 1 - p i) (seq 0 (S n')))).
      { apply fold_right_Rmult_nonneg.
        intros x Hx. apply in_map_iff in Hx.
        destruct Hx as [i [Heq Hin]]. subst.
        apply in_seq in Hin.
        assert (Hi : (i < S n')%nat) by lia.
        specialize (Hp_n i Hi).
        lra. }
      assert (HpSn'_nonneg : 0 <= 1 - p (S n')) by lra.
      assert (H_RHS_form : exp (- sum_f_R0 p (pred (S (S n')))) = exp (- sum_f_R0 p n') * exp (- p (S n'))).
      { rewrite <- exp_plus. f_equal. simpl. lra. }
      rewrite H_RHS_form.
      rewrite (seq_last 0 (S n')).
      rewrite map_app. rewrite fold_right_Rmult_app.
      simpl fold_right. rewrite Rmult_1_r.
      replace (0 + S n')%nat with (S n') by lia.
      apply Rmult_le_compat; assumption || (apply Rlt_le; apply exp_pos).
Qed.

(** *** Additional Real Arithmetic Helper Lemmas *)

Lemma Rmin_le_compat_l : forall x y z, x <= y -> Rmin x z <= Rmin y z.
Proof.
  intros x y z Hxy.
  unfold Rmin. destruct (Rle_dec x z); destruct (Rle_dec y z); try lra.
Qed.

Lemma Rmin_le_compat_r : forall x y z, x <= y -> Rmin z x <= Rmin z y.
Proof.
  intros x y z Hxy.
  unfold Rmin. destruct (Rle_dec z x); destruct (Rle_dec z y); try lra.
Qed.

Lemma Rmin_lt_l : forall x y z, x < z -> y <= z -> Rmin x y < z.
Proof.
  intros x y z Hxz Hyz.
  unfold Rmin. destruct (Rle_dec x y); [assumption | lra].
Qed.

Lemma Rmin_lt_r : forall x y z, x <= z -> y < z -> Rmin x y < z.
Proof.
  intros x y z Hxz Hyz.
  unfold Rmin. destruct (Rle_dec x y); [lra | assumption].
Qed.

Lemma Rmin_pos : forall x y, 0 < x -> 0 < y -> 0 < Rmin x y.
Proof.
  intros x y Hx Hy.
  unfold Rmin. destruct (Rle_dec x y); assumption.
Qed.

Lemma Rmin_case_strong : forall x y (P : R -> Prop),
  (x <= y -> P x) -> (y < x -> P y) -> P (Rmin x y).
Proof.
  intros x y P Hle Hlt.
  unfold Rmin. destruct (Rle_dec x y); [apply Hle | apply Hlt]; lra.
Qed.

Lemma Rmin_glb : forall x y z, z <= x -> z <= y -> z <= Rmin x y.
Proof.
  intros x y z Hx Hy.
  unfold Rmin. destruct (Rle_dec x y); assumption.
Qed.

Lemma Rmin_Rle_l : forall x y, Rmin x y <= x.
Proof.
  intros x y.
  unfold Rmin. destruct (Rle_dec x y); lra.
Qed.

Lemma Rmin_Rle_r : forall x y, Rmin x y <= y.
Proof.
  intros x y.
  unfold Rmin. destruct (Rle_dec x y); lra.
Qed.

Lemma Rplus_lt_reg_l : forall r x y, r + x < r + y -> x < y.
Proof.
  intros r x y H.
  apply Rplus_lt_compat_l with (r := -r) in H.
  ring_simplify in H.
  assumption.
Qed.

Lemma Rplus_le_reg_l : forall r x y, r + x <= r + y -> x <= y.
Proof.
  intros r x y H.
  apply Rplus_le_compat_l with (r := -r) in H.
  ring_simplify in H.
  assumption.
Qed.

Lemma Rplus_lt_reg_r : forall r x y, x + r < y + r -> x < y.
Proof.
  intros r x y H.
  apply Rplus_lt_compat_r with (r := -r) in H.
  ring_simplify in H.
  assumption.
Qed.

Lemma Rplus_le_reg_r : forall r x y, x + r <= y + r -> x <= y.
Proof.
  intros r x y H.
  apply Rplus_le_compat_r with (r := -r) in H.
  ring_simplify in H.
  assumption.
Qed.

Lemma Rlt_minus_l : forall x y z, x < y - z -> x + z < y.
Proof.
  intros x y z H.
  apply Rplus_lt_compat_r with (r := z) in H.
  ring_simplify in H.
  assumption.
Qed.

Lemma Rlt_minus_r : forall x y z, x - z < y -> x < y + z.
Proof.
  intros x y z H.
  apply Rplus_lt_compat_r with (r := z) in H.
  replace (x - z + z) with x in H by ring.
  replace (y + z) with (y + z) in H by ring.
  assumption.
Qed.

Lemma Rle_minus_l : forall x y z, x <= y - z -> x + z <= y.
Proof.
  intros x y z H.
  apply Rplus_le_compat_r with (r := z) in H.
  replace (x + z) with (x + z) in H by ring.
  replace (y - z + z) with y in H by ring.
  assumption.
Qed.

Lemma Rle_minus_r : forall x y z, x - z <= y -> x <= y + z.
Proof.
  intros x y z H.
  apply Rplus_le_compat_r with (r := z) in H.
  replace (x - z + z) with x in H by ring.
  replace (y + z) with (y + z) in H by ring.
  assumption.
Qed.

Lemma Rminus_lt : forall x y z, x - y < z -> x < z + y.
Proof.
  intros x y z H.
  apply Rlt_minus_r. assumption.
Qed.

Lemma Rminus_le : forall x y z, x - y <= z -> x <= z + y.
Proof.
  intros x y z H.
  apply Rle_minus_r. assumption.
Qed.

Lemma Rlt_minus_swap : forall x y, x < y -> 0 < y - x.
Proof.
  intros x y H.
  apply Rplus_lt_reg_l with (r := x).
  ring_simplify.
  assumption.
Qed.

Lemma Rle_minus_swap : forall x y, x <= y -> 0 <= y - x.
Proof.
  intros x y H.
  apply Rplus_le_reg_l with (r := x).
  ring_simplify.
  assumption.
Qed.

Lemma Rgt_minus : forall x y, x > y -> x - y > 0.
Proof.
  intros x y H.
  unfold Rgt in *.
  apply Rlt_minus_swap.
  assumption.
Qed.

Lemma Rge_minus : forall x y, x >= y -> x - y >= 0.
Proof.
  intros x y H.
  unfold Rge in *.
  destruct H as [H | H].
  - left. apply Rgt_minus. assumption.
  - right. subst. ring.
Qed.

Lemma Rminus_gt_0_lt : forall x y, 0 < x - y -> y < x.
Proof.
  intros x y H.
  apply Rplus_lt_reg_l with (r := -y).
  ring_simplify.
  replace (-y + x) with (x - y) by ring.
  assumption.
Qed.

Lemma Rminus_ge_0_le : forall x y, 0 <= x - y -> y <= x.
Proof.
  intros x y H.
  apply Rplus_le_reg_l with (r := -y).
  ring_simplify.
  replace (-y + x) with (x - y) by ring.
  assumption.
Qed.

Lemma Rlt_add_compat : forall a b c d, a < b -> c < d -> a + c < b + d.
Proof.
  intros a b c d Hab Hcd.
  apply Rlt_trans with (r2 := b + c).
  - apply Rplus_lt_compat_r. assumption.
  - apply Rplus_lt_compat_l. assumption.
Qed.

Lemma Rle_add_compat : forall a b c d, a <= b -> c <= d -> a + c <= b + d.
Proof.
  intros a b c d Hab Hcd.
  apply Rle_trans with (r2 := b + c).
  - apply Rplus_le_compat_r. assumption.
  - apply Rplus_le_compat_l. assumption.
Qed.

Lemma Rmult_le_0_compat : forall a b, 0 <= a -> 0 <= b -> 0 <= a * b.
Proof.
  intros a b Ha Hb.
  apply Rmult_le_pos; assumption.
Qed.

Lemma Rmult_lt_0_compat : forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  apply Rmult_lt_0_compat; assumption.
Qed.

Lemma Rdiv_pos : forall x y, 0 < x -> 0 < y -> 0 < x / y.
Proof.
  intros x y Hx Hy.
  unfold Rdiv.
  apply Rmult_lt_0_compat; [assumption | apply Rinv_0_lt_compat; assumption].
Qed.

Lemma Rdiv_le_pos : forall x y, 0 <= x -> 0 < y -> 0 <= x / y.
Proof.
  intros x y Hx Hy.
  unfold Rdiv.
  apply Rmult_le_pos; [assumption | apply Rlt_le; apply Rinv_0_lt_compat; assumption].
Qed.

Lemma Rle_lt_or_eq_dec : forall r1 r2 : R, r1 <= r2 -> {r1 < r2} + {r1 = r2}.
Proof.
  intros r1 r2 H.
  destruct (Rlt_le_dec r1 r2) as [Hlt | Hge].
  - left. assumption.
  - right. apply Rle_antisym; assumption.
Qed.

Lemma Rlt_le_weak : forall x y, x < y -> x <= y.
Proof.
  intros x y H.
  apply Rlt_le. assumption.
Qed.

Lemma Rgt_ge_weak : forall x y, x > y -> x >= y.
Proof.
  intros x y H.
  unfold Rge, Rgt in *.
  left. assumption.
Qed.

(** *** Helper lemma for strict inequality from limits *)

Lemma strict_ineq_from_limit : forall (f : R -> R) (a b eps : R),
  f a > b -> eps > 0 -> eps < f a - b -> f a > b + eps.
Proof.
  intros f a b eps Hf Heps Hdiff.
  assert (Hrw : b + eps < b + (f a - b)).
  { apply Rplus_lt_compat_l. assumption. }
  replace (b + (f a - b)) with (f a) in Hrw by ring.
  assumption.
Qed.

(** *** Coquelicot filter lemmas for limits *)

(** Scaling to +∞: if A(h) → +∞ and c > 0, then c·A(h) → +∞ *)
Lemma filterlim_scale_to_pinf : forall (A : R -> R) (c : R),
  c > 0 ->
  filterlim A (Rbar_locally p_infty) (Rbar_locally p_infty) ->
  filterlim (fun h => c * A h) (Rbar_locally p_infty) (Rbar_locally p_infty).
Proof.
  intros A c Hc HA.
  unfold filterlim, filter_le, filtermap in *.
  intros P HP.
  assert (HP' : Rbar_locally p_infty (fun x => P (c * x))).
  { destruct HP as [M HM].
    exists (M / c).
    intros x Hx.
    apply HM.
    assert (Hcx : M < c * x).
    { apply Rmult_lt_compat_l with (r := c) in Hx; [|assumption].
      unfold Rdiv in Hx.
      rewrite Rmult_comm in Hx.
      rewrite Rmult_assoc in Hx.
      rewrite Rinv_l in Hx; [|apply Rgt_not_eq; assumption].
      rewrite Rmult_1_r in Hx.
      assumption. }
    assumption. }
  specialize (HA (fun x => P (c * x)) HP').
  destruct HA as [M HM].
  exists M.
  intros x Hx.
  apply HM. assumption.
Qed.

(** Composition of limits via filters *)
Lemma filterlim_comp_2 : forall {U V W : Type} (f : U -> V) (g : V -> W)
  (F : (U -> Prop) -> Prop) (G : (V -> Prop) -> Prop) (H : (W -> Prop) -> Prop),
  filterlim f F G ->
  filterlim g G H ->
  filterlim (fun x => g (f x)) F H.
Proof.
  intros U V W f g F G H Hf Hg.
  apply filterlim_comp with (G := G); assumption.
Qed.

(** ** 1. Core Parameter Bundle (EOX_Params) *)

Record EOX_Params := {
  A : Type;
  A_inhabited : { a0 : A | True };

  T : A -> R;
  T_nonneg : forall a, 0 <= T a;

  A0 : { a0 : A | T a0 = 0 };

  phi : R -> R;
  phi_domain : forall x, 0 <= x -> 0 <= phi x;
  phi_increasing0 : forall x y, 0 <= x -> 0 <= y -> x <= y -> phi x <= phi y;
  phi_zero : phi 0 = 0;
  phi_pos : forall x, x > 0 -> phi x > 0;

  g : R -> R;
  g_bounds : forall x, 0 <= x -> 0 <= g x <= 1;
  g_zero : g 0 = 0;
  g_pos : forall x, x > 0 -> g x > 0;
  g_nondecreasing : nondecreasing g;
  g_tendsto_1 : filterlim g (Rbar_locally p_infty) (locally 1);

  g_hazard_lb : { lambda : R | lambda > 0 /\ forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= g x };

  A_sum : R -> R;
  A_sum_nonneg : forall h, 0 <= h -> 0 <= A_sum h;
  A_sum_nondecreasing : nondecreasing A_sum;
  A_sum_unbounded : forall M, exists h, 0 <= h /\ A_sum h >= M;
  A_sum_to_infty : filterlim A_sum (Rbar_locally p_infty) (Rbar_locally p_infty);

  V : R;
  V_pos : V > 0;

  C : A -> R;
  C_nonneg : forall a, 0 <= C a;

  V_margin : V - C (proj1_sig A0) > 0
}.

(** Derived lemma: phi(T(a)) > 0 when T(a) > 0 *)
Lemma phi_T_pos (P : EOX_Params) : forall a, T P a > 0 -> phi P (T P a) > 0.
Proof.
  intros a HT.
  apply phi_pos.
  assumption.
Qed.

(** ** 2. EOX One-Shot Game at Horizon h *)

Section OneShot.

Context (P : EOX_Params).

(** *** Elimination probability at horizon h for action a *)
Definition elim_prob (h : R) (a : A P) : R :=
  g P (phi P (T P a) * A_sum P h).

(** *** Payoff = survival value - cost *)
Definition payoff (h : R) (a : A P) : R :=
  (1 - elim_prob h a) * V P - C P a.

(** *** Properties of elim_prob *)

Lemma EOX_elim_prob_bounds : forall h a, 0 <= h -> 0 <= elim_prob h a <= 1.
Proof.
  intros h a Hh.
  unfold elim_prob.
  assert (H_product_nonneg : 0 <= phi P (T P a) * A_sum P h).
  { apply Rmult_le_pos.
    - apply phi_domain. apply T_nonneg.
    - apply A_sum_nonneg. assumption. }
  apply g_bounds. assumption.
Qed.

Lemma EOX_elim_prob_null_exposure : forall h,
  0 <= h -> elim_prob h (proj1_sig (A0 P)) = 0.
Proof.
  intros h Hh.
  unfold elim_prob.
  destruct (A0 P) as [a0 Ha0]; simpl.
  rewrite Ha0.
  rewrite phi_zero.
  rewrite Rmult_0_l.
  apply g_zero.
Qed.

Lemma EOX_elim_prob_monotone_in_T : forall h a1 a2,
  0 <= h ->
  T P a1 <= T P a2 ->
  elim_prob h a1 <= elim_prob h a2.
Proof.
  intros h a1 a2 Hh HT.
  unfold elim_prob.
  assert (H_phi_mono : phi P (T P a1) <= phi P (T P a2)).
  { apply phi_increasing0.
    - apply T_nonneg.
    - apply T_nonneg.
    - assumption. }
  assert (H_A_nonneg : 0 <= A_sum P h).
  { apply A_sum_nonneg. assumption. }
  assert (H_product_mono : phi P (T P a1) * A_sum P h <= phi P (T P a2) * A_sum P h).
  { apply Rmult_le_compat_r; assumption. }
  apply g_nondecreasing.
  assumption.
Qed.

(** *** Properties of payoff *)

Lemma EOX_payoff_null_exposure_constant : forall h,
  0 <= h ->
  payoff h (proj1_sig (A0 P)) = V P - C P (proj1_sig (A0 P)).
Proof.
  intros h Hh.
  unfold payoff.
  rewrite EOX_elim_prob_null_exposure; [| assumption].
  ring.
Qed.

(** *** Asymptotic behavior: elim_prob → 1 when T(a) > 0 *)

Lemma EOX_elim_prob_tends_to_1 : forall a,
  T P a > 0 ->
  filterlim (fun h => elim_prob h a) (Rbar_locally p_infty) (locally 1).
Proof.
  intros a HTa.
  unfold elim_prob.
  assert (Hc_pos : phi P (T P a) > 0).
  { apply phi_T_pos. assumption. }
  assert (H_scale : filterlim (fun h => phi P (T P a) * A_sum P h)
                               (Rbar_locally p_infty)
                               (Rbar_locally p_infty)).
  { apply filterlim_scale_to_pinf.
    - assumption.
    - apply A_sum_to_infty. }
  apply filterlim_comp_2 with (G := Rbar_locally p_infty).
  - assumption.
  - apply g_tendsto_1.
Qed.

(** *** Quantitative version: explicit epsilon-delta form *)

Lemma EOX_elim_prob_tends_to_1_explicit : forall a eps,
  T P a > 0 ->
  eps > 0 ->
  exists H, 0 <= H /\ forall h, H <= h -> 1 - eps < elim_prob h a <= 1.
Proof.
  intros a eps HTa Heps.
  assert (H_lim : filterlim (fun h => elim_prob h a) (Rbar_locally p_infty) (locally 1)).
  { apply EOX_elim_prob_tends_to_1. assumption. }
  unfold filterlim, filter_le, filtermap in H_lim.
  pose (eps' := mkposreal eps Heps).
  assert (H_ball : locally 1 (ball 1 eps')).
  { exists eps'. intros y Hy. exact Hy. }
  specialize (H_lim (ball 1 eps') H_ball).
  destruct H_lim as [M HM].
  exists (Rmax (M + 1) 0). split; [apply Rmax_r |].
  intros h Hh.
  assert (Hh_M : M < h).
  { apply Rlt_le_trans with (r2 := M + 1); [lra |].
    apply Rle_trans with (r2 := Rmax (M + 1) 0); [apply Rmax_l | exact Hh]. }
  specialize (HM h Hh_M).
  unfold ball, AbsRing_ball, abs, minus, plus, opp in HM. simpl in HM.
  assert (Hbounds : 0 <= elim_prob h a <= 1).
  { apply EOX_elim_prob_bounds.
    apply Rle_trans with (r2 := Rmax (M + 1) 0); [apply Rmax_r | exact Hh]. }
  split; [| apply Hbounds].
  apply Rabs_def2 in HM.
  destruct HM as [HM1 HM2].
  unfold eps', minus, plus, opp in HM2. simpl in HM2.
  assert (Hgoal : 1 - eps < elim_prob h a).
  { assert (H_ineq : - eps < elim_prob h a + -1) by exact HM2.
    apply Rplus_lt_compat_r with (r := 1) in H_ineq.
    ring_simplify in H_ineq. ring_simplify. exact H_ineq. }
  exact Hgoal.
Qed.

(** *** Lower bound via exposure threshold *)

Lemma EOX_elim_prob_lower_bound_by_threshold : forall a h gamma,
  0 <= h ->
  gamma > 0 ->
  phi P (T P a) >= gamma ->
  elim_prob h a >= g P (gamma * A_sum P h).
Proof.
  intros a h gamma Hh Hgamma Hphi.
  unfold elim_prob.
  assert (H_A_nonneg : 0 <= A_sum P h) by (apply A_sum_nonneg; exact Hh).
  assert (H_phi_le : gamma <= phi P (T P a)) by (apply Rge_le; exact Hphi).
  assert (H_prod_mono : gamma * A_sum P h <= phi P (T P a) * A_sum P h).
  { apply Rmult_le_compat_r; [exact H_A_nonneg | exact H_phi_le]. }
  assert (H_g_mono : g P (gamma * A_sum P h) <= g P (phi P (T P a) * A_sum P h)).
  { apply g_nondecreasing. exact H_prod_mono. }
  apply Rle_ge. exact H_g_mono.
Qed.

(** *** Combining threshold and convergence: quantitative approach to certainty *)

Lemma EOX_elim_prob_threshold_convergence : forall a eps gamma,
  eps > 0 ->
  gamma > 0 ->
  phi P (T P a) >= gamma ->
  exists H, 0 <= H /\ forall h, H <= h -> g P (gamma * A_sum P h) > 1 - eps ->
    elim_prob h a > 1 - eps.
Proof.
  intros a eps gamma Heps Hgamma Hphi.
  exists 0. split; [lra |].
  intros h Hh Hg_bound.
  assert (H_lower : elim_prob h a >= g P (gamma * A_sum P h)).
  { apply EOX_elim_prob_lower_bound_by_threshold; [lra | exact Hgamma | exact Hphi]. }
  apply Rlt_le_trans with (r2 := g P (gamma * A_sum P h)).
  - exact Hg_bound.
  - apply Rge_le. exact H_lower.
Qed.

(** *** Explicit horizon for threshold-based elimination via unbounded accumulation *)

Lemma EOX_elim_prob_threshold_explicit_horizon : forall a eps gamma,
  eps > 0 ->
  gamma > 0 ->
  phi P (T P a) >= gamma ->
  exists H, 0 <= H /\ forall h, H <= h -> elim_prob h a > 1 - eps.
Proof.
  intros a eps gamma Heps Hgamma Hphi.
  pose (eps' := mkposreal eps Heps).
  assert (H_g_lim : filterlim (fun h => g P (gamma * A_sum P h)) (Rbar_locally p_infty) (locally 1)).
  { assert (H_scale : filterlim (fun h => gamma * A_sum P h) (Rbar_locally p_infty) (Rbar_locally p_infty)).
    { apply filterlim_scale_to_pinf; [exact Hgamma | apply A_sum_to_infty]. }
    apply filterlim_comp_2 with (G := Rbar_locally p_infty); [exact H_scale | apply g_tendsto_1]. }
  unfold filterlim, filter_le, filtermap in H_g_lim.
  assert (H_ball : locally 1 (ball 1 eps')).
  { exists eps'. intros y Hy. exact Hy. }
  specialize (H_g_lim (ball 1 eps') H_ball).
  destruct H_g_lim as [M HM].
  exists (Rmax (M + 1) 0). split; [apply Rmax_r |].
  intros h Hh.
  assert (Hh_M : M < h).
  { apply Rlt_le_trans with (r2 := M + 1); [lra |].
    apply Rle_trans with (r2 := Rmax (M + 1) 0); [apply Rmax_l | exact Hh]. }
  specialize (HM h Hh_M).
  unfold ball, AbsRing_ball, abs, minus, plus, opp in HM. simpl in HM.
  assert (H_g_close : 1 - eps < g P (gamma * A_sum P h)).
  { apply Rabs_def2 in HM. destruct HM as [HM1 HM2].
    unfold eps' in HM2. simpl in HM2.
    assert (H_ineq : - eps < g P (gamma * A_sum P h) + -1) by exact HM2.
    apply Rplus_lt_compat_r with (r := 1) in H_ineq.
    ring_simplify in H_ineq. ring_simplify. exact H_ineq. }
  assert (H_lower : elim_prob h a >= g P (gamma * A_sum P h)).
  { apply EOX_elim_prob_lower_bound_by_threshold.
    - apply Rle_trans with (r2 := Rmax (M + 1) 0); [apply Rmax_r | exact Hh].
    - exact Hgamma.
    - exact Hphi. }
  apply Rlt_le_trans with (r2 := g P (gamma * A_sum P h)); [exact H_g_close | apply Rge_le; exact H_lower].
Qed.

(** *** Survival probability decays when exposure exceeds threshold *)

Lemma EOX_survival_prob_decay_by_threshold : forall a h gamma,
  0 <= h ->
  gamma > 0 ->
  phi P (T P a) >= gamma ->
  1 - elim_prob h a <= 1 - g P (gamma * A_sum P h).
Proof.
  intros a h gamma Hh Hgamma Hphi.
  assert (H_lower : elim_prob h a >= g P (gamma * A_sum P h)).
  { apply EOX_elim_prob_lower_bound_by_threshold; assumption. }
  assert (H_bounds : 0 <= elim_prob h a <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (H_g_bounds : 0 <= g P (gamma * A_sum P h) <= 1).
  { apply g_bounds. apply Rmult_le_pos.
    - apply Rlt_le. exact Hgamma.
    - apply A_sum_nonneg. exact Hh. }
  apply Rge_le in H_lower.
  assert (H_survival : 1 - elim_prob h a <= 1 - g P (gamma * A_sum P h)).
  { apply Ropp_le_contravar in H_lower.
    apply Rplus_le_compat_l with (r := 1) in H_lower.
    replace (1 + - elim_prob h a) with (1 - elim_prob h a) in H_lower by ring.
    replace (1 + - g P (gamma * A_sum P h)) with (1 - g P (gamma * A_sum P h)) in H_lower by ring.
    exact H_lower. }
  exact H_survival.
Qed.

(** *** Survival probability tends to zero when exposure exceeds threshold *)

Lemma EOX_survival_prob_to_zero : forall a gamma,
  gamma > 0 ->
  phi P (T P a) >= gamma ->
  is_lim (fun h => 1 - elim_prob h a) p_infty 0.
Proof.
  intros a gamma Hgamma Hphi.
  assert (H_g_to_1 : is_lim (fun h => g P (gamma * A_sum P h)) p_infty 1).
  { assert (H_scale : filterlim (fun h => gamma * A_sum P h) (Rbar_locally p_infty) (Rbar_locally p_infty)).
    { apply filterlim_scale_to_pinf; [exact Hgamma | apply A_sum_to_infty]. }
    unfold is_lim.
    apply filterlim_comp_2 with (G := Rbar_locally p_infty); [exact H_scale | apply g_tendsto_1]. }
  unfold is_lim, filterlim, filter_le, filtermap.
  intros Q HQ.
  destruct HQ as [eps Heps].
  unfold is_lim, filterlim, filter_le, filtermap in H_g_to_1.
  pose (eps' := mkposreal eps (cond_pos eps)).
  assert (H_ball : locally 1 (ball 1 eps')).
  { exists eps'. intros y Hy. exact Hy. }
  specialize (H_g_to_1 (ball 1 eps') H_ball).
  destruct H_g_to_1 as [M HM].
  exists (Rmax M 0). intros h Hh.
  apply Heps.
  unfold ball, AbsRing_ball, abs, minus, plus, opp. simpl.
  assert (Hh_M : M < h).
  { apply Rle_lt_trans with (r2 := Rmax M 0); [apply Rmax_l | exact Hh]. }
  specialize (HM h Hh_M).
  unfold ball, AbsRing_ball, abs, minus, plus, opp in HM. simpl in HM.
  assert (H_surv_bound : 1 - elim_prob h a <= 1 - g P (gamma * A_sum P h)).
  { apply EOX_survival_prob_decay_by_threshold.
    - apply Rle_trans with (r2 := Rmax M 0); [apply Rmax_r | apply Rlt_le; exact Hh].
    - exact Hgamma.
    - exact Hphi. }
  assert (H_surv_nonneg : 0 <= 1 - elim_prob h a).
  { assert (Hh_nonneg : 0 <= h) by (apply Rle_trans with (r2 := Rmax M 0); [apply Rmax_r | apply Rlt_le; exact Hh]).
    assert (Hb : 0 <= elim_prob h a <= 1) by (apply EOX_elim_prob_bounds; exact Hh_nonneg).
    lra. }
  assert (H_goal : Rabs (1 - elim_prob h a - 0) < eps).
  { replace (1 - elim_prob h a - 0) with (1 - elim_prob h a) by ring.
    rewrite Rabs_right by (apply Rle_ge; exact H_surv_nonneg).
    assert (H_g_close : Rabs (g P (gamma * A_sum P h) - 1) < eps) by exact HM.
    apply Rabs_def2 in H_g_close.
    destruct H_g_close as [Hg1 Hg2].
    assert (H_1mg_small : 1 - g P (gamma * A_sum P h) < eps) by lra.
    apply Rle_lt_trans with (r2 := 1 - g P (gamma * A_sum P h)); [exact H_surv_bound | exact H_1mg_small]. }
  exact H_goal.
Qed.

(** *** Unbounded accumulation with threshold implies g-values can be made arbitrarily close to 1 *)

Lemma EOX_g_threshold_approaches_1 : forall gamma eps,
  gamma > 0 ->
  eps > 0 ->
  exists H, 0 <= H /\ forall h, H <= h -> g P (gamma * A_sum P h) > 1 - eps.
Proof.
  intros gamma eps Hgamma Heps.
  assert (H_lim : filterlim (fun h => g P (gamma * A_sum P h)) (Rbar_locally p_infty) (locally 1)).
  { assert (H_scale : filterlim (fun h => gamma * A_sum P h) (Rbar_locally p_infty) (Rbar_locally p_infty)).
    { apply filterlim_scale_to_pinf; [exact Hgamma | apply A_sum_to_infty]. }
    apply filterlim_comp_2 with (G := Rbar_locally p_infty); [exact H_scale | apply g_tendsto_1]. }
  unfold filterlim, filter_le, filtermap in H_lim.
  pose (eps' := mkposreal eps Heps).
  assert (H_ball : locally 1 (ball 1 eps')).
  { exists eps'. intros y Hy. exact Hy. }
  specialize (H_lim (ball 1 eps') H_ball).
  destruct H_lim as [M HM].
  exists (Rmax (M + 1) 0). split; [apply Rmax_r |].
  intros h Hh.
  assert (Hh_M : M < h).
  { apply Rlt_le_trans with (r2 := M + 1); [lra |].
    apply Rle_trans with (r2 := Rmax (M + 1) 0); [apply Rmax_l | exact Hh]. }
  specialize (HM h Hh_M).
  unfold ball, AbsRing_ball, abs, minus, plus, opp in HM. simpl in HM.
  apply Rabs_def2 in HM.
  destruct HM as [HM1 HM2].
  unfold eps' in HM2. simpl in HM2.
  assert (H_ineq : - eps < g P (gamma * A_sum P h) + -1) by exact HM2.
  apply Rplus_lt_compat_r with (r := 1) in H_ineq.
  ring_simplify in H_ineq. ring_simplify. exact H_ineq.
Qed.

(** *** Payoff limit for positive exposure *)

Lemma EOX_payoff_limit_pos_exposure : forall a,
  T P a > 0 ->
  is_lim (fun h => payoff h a) p_infty (- C P a).
Proof.
  intros a HTa.
  assert (H_elim_lim : filterlim (fun h => elim_prob h a) (Rbar_locally p_infty) (locally 1)).
  { apply EOX_elim_prob_tends_to_1. assumption. }
  assert (H_V_pos : V P > 0) by apply V_pos.
  unfold is_lim, filterlim, filter_le, filtermap.
  intros Q HQ.
  assert (H_eps : exists eps, eps > 0 /\ (forall y, Rabs (y - (- C P a)) < eps -> Q y)).
  { destruct HQ as [eps Heps].
    exists (pos eps). split.
    - apply (cond_pos eps).
    - intros y Hy.
      apply Heps.
      unfold ball, AbsRing_ball, abs, minus, plus, opp. simpl.
      exact Hy. }
  destruct H_eps as [eps [Heps HepsQ]].
  pose (eps'_val := eps / (2 * V P)).
  assert (H_eps'_pos : eps'_val > 0).
  { unfold eps'_val. apply Rmult_lt_0_compat; [assumption | apply Rinv_0_lt_compat; lra]. }
  pose (eps' := mkposreal eps'_val H_eps'_pos).
  assert (H_ball : locally 1 (ball 1 eps')).
  { exists eps'. intros y Hy. assumption. }
  unfold filterlim, filter_le, filtermap in H_elim_lim.
  specialize (H_elim_lim (ball 1 eps') H_ball).
  destruct H_elim_lim as [M HM].
  exists (Rmax M 0).
  intros h Hh.
  assert (Hh_M : M < h).
  { apply Rle_lt_trans with (r2 := Rmax M 0); [apply Rmax_Rle; left; lra | exact Hh]. }
  specialize (HM h Hh_M).
  apply HepsQ.
  unfold payoff.
  replace ((1 - elim_prob h a) * V P - C P a - (- C P a)) with ((1 - elim_prob h a) * V P) by ring.
  rewrite Rabs_mult.
  assert (H_bounds : 0 <= elim_prob h a <= 1).
  { apply EOX_elim_prob_bounds. apply Rle_trans with (r2 := Rmax M 0); [apply Rmax_r | apply Rlt_le; assumption]. }
  rewrite Rabs_right by (apply Rle_ge; lra).
  rewrite Rabs_right by (apply Rle_ge; apply Rlt_le; assumption).
  unfold ball, AbsRing_ball, abs, minus, plus, opp in HM. simpl in HM.
  assert (H_close : Rabs (elim_prob h a - 1) < eps'_val) by (unfold eps' in HM; simpl in HM; exact HM).
  assert (H_1m_bound : 1 - elim_prob h a < eps'_val).
  { apply Rabs_def2 in H_close. lra. }
  apply Rmult_lt_compat_r with (r := V P) in H_1m_bound; [|assumption].
  unfold eps'_val in H_1m_bound.
  replace (eps / (2 * V P) * V P) with (eps / 2) in H_1m_bound by (field; apply Rgt_not_eq; assumption).
  lra.
Qed.

(** *** Full Asymptotic Null-Exposure Dominance *)

Theorem EOX_asymptotic_null_dominance_pointwise :
  forall a,
    C P (proj1_sig (A0 P)) <= C P a ->
    (T P a = 0 /\ C P (proj1_sig (A0 P)) = C P a) \/
    exists H : R, 0 <= H /\ forall h, H <= h -> payoff h (proj1_sig (A0 P)) > payoff h a.
Proof.
  intros a HC_assumption.
  pose (a0 := proj1_sig (A0 P)).
  assert (Ha0_def : a0 = proj1_sig (A0 P)) by reflexivity.
  assert (HT_a0 : T P a0 = 0).
  { rewrite Ha0_def. destruct (A0 P) as [a0' Ha0']. simpl. assumption. }
  pose (m := V P - C P a0).
  assert (Hm_pos : m > 0) by (unfold m; apply V_margin).
  assert (H_payoff_a0 : forall h, 0 <= h -> payoff h a0 = m).
  { intros h Hh. unfold m, a0. apply EOX_payoff_null_exposure_constant. assumption. }
  destruct (Req_dec (T P a) 0) as [HT_eq0 | HT_neq0].
  - destruct (Rtotal_order (C P a0) (C P a)) as [HC_lt | [HC_eq | HC_gt]].
    + right. exists 0. split; [lra |]. intros h Hh.
      rewrite H_payoff_a0 by lra.
      unfold payoff, elim_prob.
      rewrite HT_eq0, phi_zero, Rmult_0_l, g_zero.
      replace ((1 - 0) * V P - C P a) with (V P - C P a) by ring.
      unfold m, a0 in *.
      assert (H_ineq : V P - C P (proj1_sig (A0 P)) > V P - C P a).
      { apply Ropp_lt_contravar in HC_lt.
        apply Rplus_lt_compat_l with (r := V P) in HC_lt.
        replace (V P + - C P (proj1_sig (A0 P))) with (V P - C P (proj1_sig (A0 P))) in HC_lt by ring.
        replace (V P + - C P a) with (V P - C P a) in HC_lt by ring.
        exact HC_lt. }
      exact H_ineq.
    + left. split; assumption.
    + unfold a0 in HC_gt.
      assert (H_contr : C P (proj1_sig (A0 P)) <= C P a) by exact HC_assumption.
      lra.
  - right.
    assert (HTa_pos : T P a > 0).
    { destruct (Rlt_le_dec 0 (T P a)) as [Hlt | Hge].
      - assumption.
      - assert (Heq : T P a = 0) by (apply Rle_antisym; [assumption | apply T_nonneg]).
        contradiction. }
    assert (H_lim : is_lim (fun h => payoff h a) p_infty (- C P a)).
    { apply EOX_payoff_limit_pos_exposure. assumption. }
    unfold is_lim, filterlim, filter_le, filtermap in H_lim.
    pose (eps_val := m / 2).
    assert (Heps_pos : eps_val > 0) by (unfold eps_val; lra).
    pose (eps_real := mkposreal eps_val Heps_pos).
    assert (H_ball : locally (- C P a) (ball (- C P a) eps_real)).
    { exists eps_real. intros y Hy. exact Hy. }
    specialize (H_lim (ball (- C P a) eps_real) H_ball).
    destruct H_lim as [M HM].
    exists (Rmax (M + 1) 0). split; [apply Rmax_r |]. intros h Hh.
    assert (Hh_M : M < h).
    { apply Rlt_le_trans with (r2 := M + 1); [lra |].
      apply Rle_trans with (r2 := Rmax (M + 1) 0); [apply Rmax_Rle; left; lra | assumption]. }
    specialize (HM h Hh_M).
    unfold ball, AbsRing_ball, abs, minus, plus, opp in HM. simpl in HM.
    assert (H_bound : Rabs (payoff h a - (- C P a)) < eps_val) by exact HM.
    assert (H_ineq : payoff h a < - C P a + eps_val).
    { assert (Habs : payoff h a - (- C P a) < eps_val).
      { apply Rle_lt_trans with (r2 := Rabs (payoff h a - (- C P a))).
        - apply Rle_abs.
        - assumption. }
      lra. }
    assert (Hh_nonneg : 0 <= h).
    { apply Rle_trans with (r2 := Rmax (M + 1) 0); [apply Rmax_r | assumption]. }
    rewrite H_payoff_a0 by exact Hh_nonneg.
    apply Rlt_trans with (r2 := - C P a + eps_val).
    - exact H_ineq.
    - unfold eps_val, m, a0.
      assert (HVm : V P - C P (proj1_sig (A0 P)) > 0) by apply Hm_pos.
      pose proof Hm_pos as Hpos.
      assert (H_ineq_goal : - C P a + (V P - C P (proj1_sig (A0 P))) / 2 < V P - C P (proj1_sig (A0 P))).
      { unfold Rdiv.
        replace (- C P a + (V P - C P (proj1_sig (A0 P))) * / 2) with ((V P - C P (proj1_sig (A0 P))) * / 2 - C P a) by ring.
        replace (V P - C P (proj1_sig (A0 P))) with ((V P - C P (proj1_sig (A0 P))) * / 2 + (V P - C P (proj1_sig (A0 P))) * / 2) at 2 by field.
        apply Rplus_lt_compat_l.
        apply Ropp_lt_cancel.
        replace (- ((V P - C P (proj1_sig (A0 P))) * / 2)) with (- (V P - C P (proj1_sig (A0 P))) * / 2) by ring.
        replace (- - C P a) with (C P a) by ring.
        assert (H_half_pos : 0 < (V P - C P (proj1_sig (A0 P))) * / 2).
        { apply Rmult_lt_0_compat; [exact HVm | apply Rinv_0_lt_compat; lra]. }
        assert (H_goal : - (V P - C P (proj1_sig (A0 P))) * / 2 < C P a).
        { apply Rlt_le_trans with (r2 := 0).
          - assert (Hc_nonneg := C_nonneg P (proj1_sig (A0 P))).
            assert (HV_gt_C : V P > C P (proj1_sig (A0 P))).
            { assert (Hmargin := V_margin P). lra. }
            nra.
          - apply C_nonneg. }
        exact H_goal. }
      exact H_ineq_goal.
Qed.

Corollary EOX_exposure_cost_tradeoff_bound : forall a h,
  0 <= h ->
  T P a > 0 ->
  C P a >= C P (proj1_sig (A0 P)) ->
  payoff h a <= V P - C P (proj1_sig (A0 P)).
Proof.
  intros a h Hh HTa HC.
  unfold payoff.
  assert (H_elim_bounds : 0 <= elim_prob h a <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (H_V_pos : V P > 0) by apply V_pos.
  assert (H_survival_bound : (1 - elim_prob h a) * V P <= V P).
  { assert (H_factor : 1 - elim_prob h a <= 1) by lra.
    assert (HV_nonneg : 0 <= V P) by lra.
    assert (Hone_ge : 1 <= 1) by lra.
    nra. }
  lra.
Qed.

Corollary EOX_payoff_gap_grows : forall a,
  T P a > 0 ->
  C P (proj1_sig (A0 P)) <= C P a ->
  forall M, M < V P - C P (proj1_sig (A0 P)) + C P a ->
    exists H, 0 <= H /\ forall h, H <= h ->
      payoff h (proj1_sig (A0 P)) - payoff h a > M.
Proof.
  intros a HTa HC M HM_bound.
  assert (H_lim : is_lim (fun h => payoff h a) p_infty (- C P a)).
  { apply EOX_payoff_limit_pos_exposure. assumption. }
  assert (Hpayoff_a0_constant : forall h, 0 <= h ->
    payoff h (proj1_sig (A0 P)) = V P - C P (proj1_sig (A0 P))).
  { intros h Hh. apply EOX_payoff_null_exposure_constant. assumption. }
  pose (target_gap := V P - C P (proj1_sig (A0 P)) + C P a - M).
  assert (Htarget_pos : target_gap > 0) by (unfold target_gap; lra).
  pose (eps_val := target_gap / 2).
  assert (Heps_val_pos : eps_val > 0) by (unfold eps_val; lra).
  unfold is_lim, filterlim, filter_le, filtermap in H_lim.
  pose (eps := mkposreal eps_val Heps_val_pos).
  assert (H_ball : locally (- C P a) (ball (- C P a) eps)).
  { exists eps. intros y Hy. exact Hy. }
  specialize (H_lim (ball (- C P a) eps) H_ball).
  destruct H_lim as [H_M HM].
  exists (Rmax (H_M + 1) 0). split; [apply Rmax_r |].
  intros h Hh.
  assert (Hh_nonneg : 0 <= h).
  { apply Rle_trans with (r2 := Rmax (H_M + 1) 0); [apply Rmax_r | assumption]. }
  assert (Hh_M : H_M < h).
  { unfold Rmax in Hh.
    destruct (Rle_dec (H_M + 1) 0) as [HM_le_m1 | HM_gt_m1]; lra. }
  specialize (HM h Hh_M).
  rewrite Hpayoff_a0_constant by assumption.
  unfold ball, AbsRing_ball, abs, minus, plus, opp in HM. simpl in HM.
  unfold eps in HM. simpl in HM.
  assert (H_close : Rabs (payoff h a - (- C P a)) < eps_val) by exact HM.
  apply Rabs_def2 in H_close.
  destruct H_close as [H_lower H_upper].
  assert (H_payoff_bound : payoff h a < - C P a + eps_val) by lra.
  clear H_lower H_upper.
  unfold eps_val, target_gap in H_payoff_bound.
  assert (H_result : V P - C P (proj1_sig (A0 P)) - payoff h a > M).
  { assert (Hexp : V P - C P (proj1_sig (A0 P)) - payoff h a =
                    (V P - C P (proj1_sig (A0 P)) + C P a) - (payoff h a - (- C P a))) by ring.
    rewrite Hexp.
    lra. }
  exact H_result.
Qed.

End OneShot.

(** ** 3. Discrete "N-expanding observers" variant (EOX-N) *)

Section Discrete.

Context (P : EOX_Params).

Hypothesis A_sum_zero : A_sum P 0 = 0.

Hypothesis A_sum_subadditive : forall x y,
  0 <= x -> 0 <= y -> A_sum P (x + y) - A_sum P x <= A_sum P y.

Definition A_N (n : nat) : R := A_sum P (INR n).

Lemma A_N_nondec : forall n m, (n <= m)%nat -> A_N n <= A_N m.
Proof.
  intros n m Hnm.
  unfold A_N.
  apply A_sum_nondecreasing.
  apply le_INR.
  assumption.
Qed.

Lemma A_N_nonneg : forall n, 0 <= A_N n.
Proof.
  intro n.
  unfold A_N.
  apply A_sum_nonneg.
  apply pos_INR.
Qed.

Lemma A_N_zero : A_N 0%nat = 0.
Proof.
  unfold A_N.
  simpl.
  apply A_sum_zero.
Qed.

Lemma A_N_div_sum : forall M, exists N, A_N N >= M.
Proof.
  intro M.
  destruct (A_sum_unbounded P M) as [h [Hh HA]].
  exists (Z.to_nat (up h) + 1)%nat.
  unfold A_N.
  apply Rle_ge.
  apply Rle_trans with (r2 := A_sum P h).
  - apply Rge_le. assumption.
  - apply A_sum_nondecreasing.
    rewrite plus_INR. simpl INR at 2.
    assert (Hup : IZR (up h) > h) by apply archimed.
    assert (Hup_pos : (0 <= up h)%Z).
    { destruct (Z_le_gt_dec 0 (up h)) as [Hle | Hgt]; [assumption |].
      assert (Hh_neg : h < 0).
      { apply Rle_lt_trans with (r2 := IZR (up h)); [| apply IZR_lt; lia].
        apply Rlt_le. assumption. }
      lra. }
    rewrite INR_IZR_INZ.
    rewrite Z2Nat.id by assumption.
    lra.
Qed.

Definition Delta_A (n : nat) : R := A_N (S n) - A_N n.

Lemma Delta_A_nonneg : forall n, 0 <= Delta_A n.
Proof.
  intro n.
  unfold Delta_A.
  assert (H : A_N n <= A_N (S n)).
  { apply A_N_nondec. lia. }
  lra.
Qed.

Lemma sum_Delta_A : forall N,
  (N > 0)%nat ->
  sum_f_R0 Delta_A (pred N) = A_N N - A_N 0%nat.
Proof.
  induction N as [| N IH]; intros HN.
  - lia.
  - destruct N as [| N'].
    + simpl pred.
      unfold sum_f_R0. simpl. unfold Delta_A.
      rewrite A_N_zero.
      reflexivity.
    + assert (H_pred : pred (S (S N')) = S N') by reflexivity.
      rewrite H_pred.
      rewrite tech5.
      assert (HN' : (S N' > 0)%nat) by lia.
      assert (H_IH := IH HN').
      rewrite <- H_pred in H_IH.
      simpl pred in H_IH.
      rewrite H_IH.
      unfold Delta_A.
      ring.
Qed.

Definition p_n (a : nat -> A P) (n : nat) : R :=
  g P (phi P (T P (a n)) * Delta_A n).

Lemma p_n_bounds : forall a n, 0 <= p_n a n <= 1.
Proof.
  intros a n.
  unfold p_n.
  apply g_bounds.
  apply Rmult_le_pos.
  - apply phi_domain. apply T_nonneg.
  - apply Delta_A_nonneg.
Qed.

Definition S_N (a : nat -> A P) (N : nat) : R :=
  fold_right Rmult 1 (map (fun n => 1 - p_n a n) (seq 0 N)).

Lemma sum_f_R0_nonneg : forall (f : nat -> R) (n : nat),
  (forall k, (k <= n)%nat -> 0 <= f k) -> 0 <= sum_f_R0 f n.
Proof.
  intros f n Hf.
  induction n.
  - unfold sum_f_R0. simpl. apply Hf. lia.
  - rewrite tech5. apply Rplus_le_le_0_compat.
    + apply IHn. intros k Hk. apply Hf. lia.
    + apply Hf. lia.
Qed.

Lemma EOX_product_upper_bound : forall a N,
  (N > 0)%nat ->
  S_N a N <= exp (- sum_f_R0 (fun k => p_n a k) (pred N)).
Proof.
  intros a N HN.
  unfold S_N.
  apply prod_one_minus_le_exp_sum.
  - assumption.
  - intros i Hi.
    apply p_n_bounds.
Qed.

Lemma sum_bound_by_max : forall (f : nat -> R) (n : nat) (M : R),
  (forall k, (k <= n)%nat -> f k <= M) ->
  sum_f_R0 f n <= INR (S n) * M.
Proof.
  intros f n M Hbound.
  induction n.
  - unfold sum_f_R0. simpl.
    assert (Hf0 : f 0%nat <= M) by (apply Hbound; lia).
    replace (INR (S 0)) with 1 by (simpl; reflexivity).
    lra.
  - rewrite tech5.
    assert (IH : sum_f_R0 f n <= INR (S n) * M).
    { apply IHn. intros k Hk. apply Hbound. lia. }
    assert (Hfn : f (S n) <= M) by (apply Hbound; lia).
    assert (Hgoal : sum_f_R0 f n + f (S n) <= INR (S (S n)) * M).
    { assert (Heq : INR (S (S n)) * M = INR (S n) * M + M).
      { rewrite S_INR. ring. }
      rewrite Heq. lra. }
    assumption.
Qed.

Lemma A_N_gives_large_Delta_A_sum : forall M,
  M > 0 -> exists N, (N > 0)%nat /\ sum_f_R0 Delta_A (pred N) >= M.
Proof.
  intros M HM.
  destruct (A_N_div_sum (M + 1)) as [N HN].
  destruct N.
  - assert (Hcontra : A_N 0 >= M + 1) by exact HN.
    rewrite A_N_zero in Hcontra. lra.
  - exists (S N). split; [lia |].
    assert (H_pred_eq : pred (S N) = N) by reflexivity.
    rewrite H_pred_eq.
    assert (H_sum_eq : sum_f_R0 Delta_A N = A_N (S N) - A_N 0%nat).
    { rewrite <- H_pred_eq. apply sum_Delta_A. lia. }
    rewrite H_sum_eq. rewrite A_N_zero. lra.
Qed.

Lemma A_N_positive_increase_witness : forall K N,
  (K < N)%nat ->
  A_N K < A_N N ->
  exists j, (K <= j < N)%nat /\ Delta_A j > 0.
Proof.
  intros K N.
  revert K.
  induction N as [| N IH]; intros K HK_lt HK_increase.
  - lia.
  - destruct (Req_dec (Delta_A N) 0) as [Hzero | Hnonzero].
    + unfold Delta_A in Hzero.
      assert (HAN_eq : A_N (S N) = A_N N) by lra.
      assert (HK_lt_N : (K < N)%nat \/ K = N) by lia.
      destruct HK_lt_N as [Hlt | Heq].
      * destruct (IH K Hlt) as [j [Hj_range Hj_pos]].
        { rewrite <- HAN_eq. exact HK_increase. }
        exists j. split; [lia | exact Hj_pos].
      * subst. rewrite HAN_eq in HK_increase. lra.
    + assert (HDelta_sign : Delta_A N > 0 \/ Delta_A N < 0) by lra.
      destruct HDelta_sign as [Hpos | Hneg].
      * exists N. split; [lia | exact Hpos].
      * assert (H_mono : A_N N <= A_N (S N)) by (apply A_N_nondec; lia).
        unfold Delta_A in Hneg. lra.
Qed.

Lemma A_N_eventually_increasing : forall K,
  exists n, (n >= K)%nat /\ Delta_A n > 0.
Proof.
  intro K.
  destruct (A_N_div_sum (A_N K + 1)) as [N_large HN_large].
  assert (H_K_vs_N : (K < N_large)%nat \/ (K >= N_large)%nat) by lia.
  destruct H_K_vs_N as [Hlt | Hge].
  - assert (H_increase : A_N K < A_N N_large) by lra.
    edestruct A_N_positive_increase_witness as [j [Hj_range Hj_pos]].
    + exact Hlt.
    + exact H_increase.
    + exists j. split; [lia | exact Hj_pos].
  - assert (H_mono : A_N N_large <= A_N K) by (apply A_N_nondec; lia).
    lra.
Qed.

Lemma mult_sum_distr_R : forall (c : R) (f : nat -> R) (n : nat),
  c * sum_f_R0 f n = sum_f_R0 (fun k => c * f k) n.
Proof.
  intros c f n.
  induction n.
  - unfold sum_f_R0. simpl. ring.
  - rewrite tech5 at 1.
    rewrite Rmult_plus_distr_l.
    rewrite IHn.
    rewrite tech5 at 1.
    simpl.
    reflexivity.
Qed.

Lemma p_n_lower_bound_when_phi_large : forall a n gamma,
  gamma > 0 ->
  phi P (T P (a n)) >= gamma ->
  Delta_A n > 0 ->
  p_n a n >= g P (gamma * Delta_A n).
Proof.
  intros a n gamma Hgamma Hphi HDelta.
  unfold p_n.
  assert (H_ineq : gamma * Delta_A n <= phi P (T P (a n)) * Delta_A n).
  { apply Rmult_le_compat_r; [apply Delta_A_nonneg | lra]. }
  assert (H_mono : g P (gamma * Delta_A n) <= g P (phi P (T P (a n)) * Delta_A n)).
  { apply g_nondecreasing. exact H_ineq. }
  lra.
Qed.

Lemma p_n_sum_nonneg : forall a N,
  (N > 0)%nat -> 0 <= sum_f_R0 (fun k => p_n a k) (pred N).
Proof.
  intros a N HN.
  apply sum_f_R0_nonneg.
  intros n Hn.
  apply p_n_bounds.
Qed.

Lemma S_N_nonneg : forall a N,
  0 <= S_N a N.
Proof.
  intros a N.
  unfold S_N.
  apply fold_right_Rmult_nonneg.
  intros x Hx.
  apply in_map_iff in Hx.
  destruct Hx as [i [Heq Hin]]. subst.
  assert (Hp : 0 <= p_n a i <= 1) by apply p_n_bounds.
  lra.
Qed.

Lemma find_witness_with_positive_Delta : forall K,
  exists n, (n >= K)%nat /\ Delta_A n > 0.
Proof.
  apply A_N_eventually_increasing.
Qed.

Lemma sum_lower_bound_by_min : forall (f : nat -> R) (n : nat) (f_min : R),
  (forall k, (k <= n)%nat -> f k >= f_min) ->
  sum_f_R0 f n >= INR (S n) * f_min.
Proof.
  intros f n f_min Hbound.
  induction n.
  - unfold sum_f_R0. simpl.
    assert (Hf0 : f 0%nat >= f_min) by (apply Hbound; lia).
    replace (1 * f_min) with f_min by ring.
    assumption.
  - rewrite tech5.
    assert (IH : sum_f_R0 f n >= INR (S n) * f_min).
    { apply IHn. intros k Hk. apply Hbound. lia. }
    assert (Hfn : f (S n) >= f_min) by (apply Hbound; lia).
    assert (Heq : INR (S (S n)) * f_min = INR (S n) * f_min + f_min).
    { rewrite S_INR. ring. }
    rewrite Heq. lra.
Qed.

(** *** Discrete threshold lower bound: connects to continuous result *)

Lemma p_n_lower_bound_by_threshold : forall a n gamma,
  gamma > 0 ->
  phi P (T P (a n)) >= gamma ->
  Delta_A n > 0 ->
  p_n a n >= g P (gamma * Delta_A n).
Proof.
  intros a n gamma Hgamma Hphi HDelta.
  unfold p_n.
  assert (H_phi_le : gamma <= phi P (T P (a n))) by (apply Rge_le; exact Hphi).
  assert (H_Delta_nonneg : 0 <= Delta_A n) by (apply Rlt_le; exact HDelta).
  assert (H_prod_mono : gamma * Delta_A n <= phi P (T P (a n)) * Delta_A n).
  { apply Rmult_le_compat_r; [exact H_Delta_nonneg | exact H_phi_le]. }
  assert (H_g_mono : g P (gamma * Delta_A n) <= g P (phi P (T P (a n)) * Delta_A n)).
  { apply g_nondecreasing. exact H_prod_mono. }
  apply Rle_ge. exact H_g_mono.
Qed.

Lemma exp_sum_product : forall (f : nat -> R) (n : nat),
  fold_right Rmult 1 (map (fun k => exp (f k)) (seq 0 (S n))) =
  exp (sum_f_R0 f n).
Proof.
  intros f n.
  induction n.
  - simpl seq. simpl map. simpl fold_right.
    unfold sum_f_R0. simpl.
    ring.
  - assert (H_LHS : fold_right Rmult 1 (map (fun k : nat => exp (f k)) (seq 0 (S (S n)))) =
                    fold_right Rmult 1 (map (fun k : nat => exp (f k)) (seq 0 (S n))) * exp (f (S n))).
    { rewrite (seq_last 0 (S n)).
      replace (0 + S n)%nat with (S n) by lia.
      rewrite map_app.
      rewrite fold_right_Rmult_app.
      simpl fold_right.
      ring. }
    rewrite H_LHS.
    rewrite IHn.
    rewrite tech5.
    rewrite exp_plus.
    ring.
Qed.

Lemma sum_f_R0_monotone : forall (f g : nat -> R) (n : nat),
  (forall k, (k <= n)%nat -> f k <= g k) ->
  sum_f_R0 f n <= sum_f_R0 g n.
Proof.
  intros f g n Hfg.
  induction n.
  - unfold sum_f_R0. simpl. apply Hfg. lia.
  - rewrite tech5. rewrite (tech5 g).
    apply Rplus_le_compat.
    + apply IHn. intros k Hk. apply Hfg. lia.
    + apply Hfg. lia.
Qed.

(** *** Discrete Extinction: Decomposed into helper lemmas *)

Lemma hazard_lower_bound_single_step : forall (lambda : R) (x : R),
  lambda > 0 ->
  (forall y, 0 <= y -> 1 - exp (- (lambda * y)) <= g P y) ->
  0 <= x ->
  1 - g P x <= exp (- (lambda * x)).
Proof.
  intros lambda x Hlambda Hlb Hx.
  assert (H : 1 - exp (- (lambda * x)) <= g P x) by (apply Hlb; exact Hx).
  lra.
Qed.

Lemma one_minus_p_n_bound : forall (a : nat -> A P) (n : nat) (lambda : R),
  lambda > 0 ->
  (forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= g P x) ->
  1 - p_n a n <= exp (- (lambda * phi P (T P (a n)) * Delta_A n)).
Proof.
  intros a n lambda Hlambda Hlb.
  unfold p_n.
  assert (Hx : 0 <= phi P (T P (a n)) * Delta_A n).
  { apply Rmult_le_pos; [apply phi_domain; apply T_nonneg | apply Delta_A_nonneg]. }
  assert (H1 : 1 - g P (phi P (T P (a n)) * Delta_A n) <= exp (- (lambda * (phi P (T P (a n)) * Delta_A n)))).
  { apply hazard_lower_bound_single_step; assumption. }
  replace (- (lambda * phi P (T P (a n)) * Delta_A n)) with (- (lambda * (phi P (T P (a n)) * Delta_A n))) by ring.
  exact H1.
Qed.

Lemma product_of_one_minus_p_n_base : forall (a : nat -> A P) (lambda : R),
  lambda > 0 ->
  (forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= g P x) ->
  fold_right Rmult 1 (map (fun n => 1 - p_n a n) (seq 0 1)) <=
  fold_right Rmult 1 (map (fun n => exp (- lambda * phi P (T P (a n)) * Delta_A n)) (seq 0 1)).
Proof.
  intros a lambda Hlambda Hlb.
  assert (Hseq : seq 0 1 = [0%nat]) by reflexivity.
  rewrite Hseq.
  simpl map. simpl fold_right.
  rewrite Rmult_1_r. rewrite Rmult_1_r.
  unfold p_n.
  assert (Hx : 0 <= phi P (T P (a 0%nat)) * Delta_A 0%nat).
  { apply Rmult_le_pos; [apply phi_domain; apply T_nonneg | apply Delta_A_nonneg]. }
  assert (Hlb0 : 1 - exp (- (lambda * (phi P (T P (a 0%nat)) * Delta_A 0%nat))) <=
                 g P (phi P (T P (a 0%nat)) * Delta_A 0%nat)).
  { apply Hlb. exact Hx. }
  replace (- lambda * phi P (T P (a 0%nat)) * Delta_A 0%nat) with
          (- (lambda * (phi P (T P (a 0%nat)) * Delta_A 0%nat))) by ring.
  lra.
Qed.

Lemma product_of_one_minus_p_n_step : forall (a : nat -> A P) (N : nat) (lambda : R),
  lambda > 0 ->
  (forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= g P x) ->
  fold_right Rmult 1 (map (fun n => 1 - p_n a n) (seq 0 (S N))) <=
  fold_right Rmult 1 (map (fun n => exp (- lambda * phi P (T P (a n)) * Delta_A n)) (seq 0 (S N))) ->
  fold_right Rmult 1 (map (fun n => 1 - p_n a n) (seq 0 (S (S N)))) <=
  fold_right Rmult 1 (map (fun n => exp (- lambda * phi P (T P (a n)) * Delta_A n)) (seq 0 (S (S N)))).
Proof.
  intros a N lambda Hlambda Hlb IH.
  assert (H_seq_succ : seq 0 (S (S N)) = seq 0 (S N) ++ [S N]).
  { rewrite (seq_last 0 (S N)). replace (0 + S N)%nat with (S N) by lia. reflexivity. }
  rewrite H_seq_succ.
  rewrite (map_app (fun n => 1 - p_n a n)).
  rewrite (map_app (fun n => exp (- lambda * phi P (T P (a n)) * Delta_A n))).
  rewrite fold_right_Rmult_app. rewrite fold_right_Rmult_app.
  simpl fold_right. rewrite Rmult_1_r. rewrite Rmult_1_r.
  assert (H_LHS_nonneg : 0 <= fold_right Rmult 1 (map (fun n : nat => 1 - p_n a n) (seq 0 (S N)))).
  { apply fold_right_Rmult_nonneg.
    intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [i [Heq Hin]]. subst.
    assert (Hpi : 0 <= p_n a i <= 1) by apply p_n_bounds.
    lra. }
  assert (H_last_step_nonneg : 0 <= 1 - p_n a (S N)).
  { assert (Hpi : 0 <= p_n a (S N) <= 1) by apply p_n_bounds. lra. }
  assert (H_last_step : 1 - p_n a (S N) <= exp (- lambda * phi P (T P (a (S N))) * Delta_A (S N))).
  { unfold p_n.
    assert (Hx : 0 <= phi P (T P (a (S N))) * Delta_A (S N)).
    { apply Rmult_le_pos; [apply phi_domain; apply T_nonneg | apply Delta_A_nonneg]. }
    assert (Hlb_SN : 1 - exp (- (lambda * (phi P (T P (a (S N))) * Delta_A (S N)))) <=
                     g P (phi P (T P (a (S N))) * Delta_A (S N))).
    { apply Hlb. exact Hx. }
    replace (- lambda * phi P (T P (a (S N))) * Delta_A (S N)) with
            (- (lambda * (phi P (T P (a (S N))) * Delta_A (S N)))) by ring.
    lra. }
  apply Rmult_le_compat; [exact H_LHS_nonneg | exact H_last_step_nonneg | exact IH | exact H_last_step].
Qed.

Lemma product_of_one_minus_p_n_induction : forall (a : nat -> A P) (N : nat) (lambda : R),
  lambda > 0 ->
  (forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= g P x) ->
  fold_right Rmult 1 (map (fun n => 1 - p_n a n) (seq 0 (S N))) <=
  fold_right Rmult 1 (map (fun n => exp (- lambda * phi P (T P (a n)) * Delta_A n)) (seq 0 (S N))).
Proof.
  intros a N lambda Hlambda Hlb.
  induction N as [| N' IH].
  - apply product_of_one_minus_p_n_base; assumption.
  - apply product_of_one_minus_p_n_step; assumption.
Qed.

Lemma exp_product_equals_exp_sum : forall (f : nat -> R) (N : nat),
  fold_right Rmult 1 (map (fun n => exp (f n)) (seq 0 (S N))) = exp (sum_f_R0 f N).
Proof.
  intros f N.
  apply exp_sum_product.
Qed.

Lemma sum_lower_bound_by_scalar : forall (f : nat -> R) (c : R) (N : nat),
  c > 0 ->
  (forall n, (n <= N)%nat -> f n >= c) ->
  sum_f_R0 f N >= INR (S N) * c.
Proof.
  intros f c N Hc Hf.
  induction N.
  - unfold sum_f_R0. simpl.
    replace (1 * c) with c by ring.
    apply Hf. lia.
  - rewrite tech5.
    assert (IH : sum_f_R0 f N >= INR (S N) * c).
    { apply IHN. intros n Hn. apply Hf. lia. }
    assert (HfN : f (S N) >= c) by (apply Hf; lia).
    assert (Heq : INR (S (S N)) * c = INR (S N) * c + c).
    { rewrite S_INR. ring. }
    rewrite Heq. lra.
Qed.

Lemma phi_times_delta_lower_bound : forall (a : nat -> A P) (gamma : R) (n : nat),
  gamma > 0 ->
  phi P (T P (a n)) >= gamma ->
  phi P (T P (a n)) * Delta_A n >= gamma * Delta_A n.
Proof.
  intros a gamma n Hgamma Hphi.
  apply Rle_ge.
  apply Rmult_le_compat_r; [apply Delta_A_nonneg | apply Rge_le; exact Hphi].
Qed.

Lemma sum_phi_delta_lower_bound : forall (a : nat -> A P) (gamma : R) (N : nat),
  gamma > 0 ->
  (forall n, (n <= N)%nat -> phi P (T P (a n)) >= gamma) ->
  sum_f_R0 (fun n => phi P (T P (a n)) * Delta_A n) N >= gamma * sum_f_R0 Delta_A N.
Proof.
  intros a gamma N Hgamma Hphi.
  rewrite mult_sum_distr_R.
  apply Rle_ge.
  apply sum_f_R0_monotone.
  intros k Hk.
  apply Rge_le.
  apply phi_times_delta_lower_bound; [exact Hgamma | apply Hphi; exact Hk].
Qed.

Theorem EOX_discrete_extinction : forall (a : nat -> A P),
  forall N, (N > 0)%nat ->
  S_N a N <= exp (- sum_f_R0 (fun k => p_n a k) (pred N)).
Proof.
  intros a N HN.
  apply EOX_product_upper_bound.
  assumption.
Qed.

(** *** Helper lemmas for discrete extinction *)

Lemma sum_f_R0_nondec_extend : forall (f : nat -> R) (n m : nat),
  (forall k, 0 <= f k) ->
  (n <= m)%nat ->
  sum_f_R0 f n <= sum_f_R0 f m.
Proof.
  intros f n m Hf Hnm.
  revert n Hnm.
  induction m; intros n Hnm.
  - assert (Heq : (n = 0)%nat).
    { lia. }
    subst. lra.
  - destruct (Nat.eq_dec n (S m)) as [Heq | Hneq].
    + subst. lra.
    + assert (Hle : (n <= m)%nat).
      { lia. }
      rewrite tech5.
      specialize (IHm n Hle).
      assert (Hfm : 0 <= f (S m)).
      { apply Hf. }
      lra.
Qed.

Lemma p_n_lower_bound_via_hazard : forall (a : nat -> A P) (n : nat) (lambda gamma : R),
  lambda > 0 ->
  gamma > 0 ->
  phi P (T P (a n)) >= gamma ->
  Delta_A n > 0 ->
  (forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= g P x) ->
  p_n a n >= 1 - exp (- (lambda * gamma * Delta_A n)).
Proof.
  intros a n lambda gamma Hlambda Hgamma Hphi HDelta Hlb.
  unfold p_n.
  assert (Hphi_le : gamma <= phi P (T P (a n))).
  { apply Rge_le. exact Hphi. }
  assert (Hprod : gamma * Delta_A n <= phi P (T P (a n)) * Delta_A n).
  { apply Rmult_le_compat_r; [apply Rlt_le; exact HDelta | exact Hphi_le]. }
  assert (Hmult_assoc : lambda * (gamma * Delta_A n) = lambda * gamma * Delta_A n) by ring.
  assert (Hg_bound : 1 - exp (- (lambda * gamma * Delta_A n)) <=
                     g P (gamma * Delta_A n)).
  { rewrite <- Hmult_assoc.
    apply Hlb. apply Rmult_le_pos; [lra | apply Rlt_le; exact HDelta]. }
  assert (Hg_mono : g P (gamma * Delta_A n) <= g P (phi P (T P (a n)) * Delta_A n)).
  { apply g_nondecreasing. exact Hprod. }
  apply Rle_ge.
  apply Rle_trans with (r2 := g P (gamma * Delta_A n)).
  - exact Hg_bound.
  - exact Hg_mono.
Qed.

(** *** Discrete-Continuous Bridge: Connecting A_N to A_sum *)

Hypothesis A_sum_unit_bounded : A_sum P 1 <= 1.

Theorem A_N_approximates_A_sum :
  forall h, h >= 1 -> exists N, (N > 0)%nat /\
    Rabs (A_N N - A_sum P h) <= 2 * A_sum P 1.
Proof.
  intros h Hh.
  pose (N := Z.to_nat (up h)).
  assert (HN_pos : (N > 0)%nat).
  { unfold N. assert (Hup : IZR (up h) > h) by apply archimed.
    assert (Hh_pos : h > 0) by lra.
    assert (Hup_pos : (0 < up h)%Z).
    { destruct (Z_lt_le_dec 0 (up h)) as [Hlt | Hle]; [assumption |].
      exfalso.
      assert (Hup_val : IZR (up h) <= IZR 0) by (apply IZR_le; assumption).
      simpl in Hup_val. lra. }
    lia. }
  exists N. split; [assumption |].
  unfold A_N, N.
  assert (Hup_bound : IZR (up h) > h) by apply archimed.
  assert (Hup_pos : (0 < up h)%Z).
  { destruct (Z_lt_le_dec 0 (up h)) as [Hlt | Hle]; [assumption |].
    exfalso.
    assert (Hup_val : IZR (up h) <= IZR 0) by (apply IZR_le; assumption).
    simpl in Hup_val. lra. }
  assert (HN_val : INR (Z.to_nat (up h)) = IZR (up h)) by (rewrite INR_IZR_INZ; rewrite Z2Nat.id by lia; reflexivity).
  rewrite HN_val.
  assert (Harch : h < IZR (up h) <= h + 1) by (destruct (archimed h) as [Hub Hlb]; split; lra).
  assert (HA_mono : A_sum P h <= A_sum P (IZR (up h))) by (apply A_sum_nondecreasing; lra).
  rewrite Rabs_right by (apply Rle_ge; lra).
  destruct Harch as [Hlb Hub].
  assert (Hdiff : A_sum P (IZR (up h)) - A_sum P h <= 2 * A_sum P 1).
  { assert (Hle_h1 : A_sum P (IZR (up h)) - A_sum P h <= A_sum P (h + 1) - A_sum P (h - 1)).
    { assert (Hmono_up : A_sum P (IZR (up h)) <= A_sum P (h + 1)) by (apply A_sum_nondecreasing; lra).
      assert (Hmono_down : A_sum P (h - 1) <= A_sum P h) by (apply A_sum_nondecreasing; lra).
      lra. }
    apply Rle_trans with (r2 := A_sum P (h + 1) - A_sum P (h - 1)).
    - assumption.
    - replace (h + 1) with ((h - 1) + 2) by ring.
      assert (HA_2step : A_sum P ((h - 1) + 2) - A_sum P (h - 1) <= 2 * A_sum P 1).
      { replace ((h - 1) + 2) with ((h - 1) + 1 + 1) by ring.
        assert (Hincr1 : A_sum P ((h - 1) + 1) - A_sum P (h - 1) <= A_sum P 1).
        { assert (Hh1_nonneg : 0 <= h - 1) by lra.
          assert (H1_nonneg : 0 <= 1) by lra.
          exact (@A_sum_subadditive (h - 1) 1 Hh1_nonneg H1_nonneg). }
        assert (Hincr2 : A_sum P ((h - 1) + 1 + 1) - A_sum P ((h - 1) + 1) <= A_sum P 1).
        { assert (Hh1p1_nonneg : 0 <= (h - 1) + 1) by lra.
          assert (H1_nonneg : 0 <= 1) by lra.
          exact (@A_sum_subadditive ((h - 1) + 1) 1 Hh1p1_nonneg H1_nonneg). }
        assert (Hsum : A_sum P ((h - 1) + 1 + 1) - A_sum P (h - 1) =
                       (A_sum P ((h - 1) + 1) - A_sum P (h - 1)) +
                       (A_sum P ((h - 1) + 1 + 1) - A_sum P ((h - 1) + 1))) by ring.
        rewrite Hsum.
        assert (H2times : 2 * A_sum P 1 = A_sum P 1 + A_sum P 1) by ring.
        rewrite H2times.
        apply Rplus_le_compat; assumption. }
      assumption. }
  assumption.
Qed.


End Discrete.

(** ** 4. Comparative Statics *)

Section ComparativeStatics.

Context (P : EOX_Params).

Lemma EOX_payoff_order_in_T : forall h a1 a2,
  0 <= h ->
  T P a1 <= T P a2 ->
  C P a1 <= C P a2 ->
  payoff P h a1 >= payoff P h a2.
Proof.
  intros h a1 a2 Hh HT HC.
  unfold payoff.
  assert (H_elim : elim_prob P h a1 <= elim_prob P h a2).
  { apply EOX_elim_prob_monotone_in_T; assumption. }
  assert (H_surv : 1 - elim_prob P h a2 <= 1 - elim_prob P h a1) by lra.
  assert (H_val : (1 - elim_prob P h a2) * V P <= (1 - elim_prob P h a1) * V P).
  { apply Rmult_le_compat_r.
    - apply Rlt_le. apply V_pos.
    - assumption. }
  lra.
Qed.

Lemma dominance_elim_prob_threshold : forall a h,
  0 <= h ->
  C P (proj1_sig (A0 P)) < C P a ->
  elim_prob P h a > (C P a - C P (proj1_sig (A0 P))) / V P ->
  payoff P h (proj1_sig (A0 P)) > payoff P h a.
Proof.
  intros a h Hh HC_strict H_elim.
  assert (Ha0_payoff : payoff P h (proj1_sig (A0 P)) = V P - C P (proj1_sig (A0 P))).
  { apply EOX_payoff_null_exposure_constant. assumption. }
  rewrite Ha0_payoff.
  unfold payoff.
  assert (H_V_pos : V P > 0) by apply V_pos.
  assert (H_threshold : elim_prob P h a > (C P a - C P (proj1_sig (A0 P))) / V P) by exact H_elim.
  assert (H_rearrange : 1 - elim_prob P h a < 1 - (C P a - C P (proj1_sig (A0 P))) / V P).
  { lra. }
  assert (H_simplify : 1 - (C P a - C P (proj1_sig (A0 P))) / V P =
                       (V P - (C P a - C P (proj1_sig (A0 P)))) / V P).
  { field. apply Rgt_not_eq. exact H_V_pos. }
  rewrite H_simplify in H_rearrange.
  assert (H_mult : (1 - elim_prob P h a) * V P <
                   ((V P - (C P a - C P (proj1_sig (A0 P)))) / V P) * V P).
  { apply Rmult_lt_compat_r; [exact H_V_pos | exact H_rearrange]. }
  assert (H_cancel : ((V P - (C P a - C P (proj1_sig (A0 P)))) / V P) * V P =
                     V P - (C P a - C P (proj1_sig (A0 P)))).
  { field. apply Rgt_not_eq. exact H_V_pos. }
  rewrite H_cancel in H_mult.
  lra.
Qed.

Theorem dominance_threshold_bounds : forall a,
  C P (proj1_sig (A0 P)) < C P a ->
  C P a < V P ->
  T P a > 0 ->
  exists H, 0 <= H /\
    forall h, H <= h ->
      elim_prob P h a > (C P a - C P (proj1_sig (A0 P))) / V P /\
      payoff P h (proj1_sig (A0 P)) > payoff P h a.
Proof.
  intros a HC_strict HCa_lt_V HTa.
  assert (H_V_pos : V P > 0) by apply V_pos.
  pose (eps := (V P - (C P a - C P (proj1_sig (A0 P)))) / V P).
  assert (Heps_bound : eps < 1).
  { unfold eps.
    assert (H_margin : V P - C P (proj1_sig (A0 P)) > 0) by apply V_margin.
    assert (H_num : V P - (C P a - C P (proj1_sig (A0 P))) < V P).
    { assert (HC_diff_pos : C P a - C P (proj1_sig (A0 P)) > 0) by lra. lra. }
    apply Rmult_lt_compat_r with (r := / V P) in H_num.
    - assert (Hsimp : V P * / V P = 1).
      { field. apply Rgt_not_eq. exact H_V_pos. }
      rewrite Hsimp in H_num.
      unfold Rdiv in *. exact H_num.
    - apply Rinv_0_lt_compat. exact H_V_pos. }
  assert (Heps_pos : eps > 0).
  { unfold eps.
    assert (H_margin : V P - C P (proj1_sig (A0 P)) > 0) by apply V_margin.
    assert (H_Ca0_nonneg : 0 <= C P (proj1_sig (A0 P))) by apply C_nonneg.
    apply Rdiv_pos.
    - assert (Hexpand : V P - (C P a - C P (proj1_sig (A0 P))) =
                        (V P - C P a) + C P (proj1_sig (A0 P))) by ring.
      rewrite Hexpand.
      assert (H_diff_pos : V P - C P a > 0) by lra.
      lra.
    - exact H_V_pos. }
  destruct (@EOX_elim_prob_tends_to_1_explicit P a eps HTa Heps_pos) as [H [HH_nonneg H_elim]].
  exists H. split; [exact HH_nonneg |].
  intros h Hh.
  specialize (H_elim h Hh).
  destruct H_elim as [H_elim_lower H_elim_upper].
  split.
  - unfold eps in H_elim_lower.
    assert (H_rearrange : 1 - (V P - (C P a - C P (proj1_sig (A0 P)))) / V P =
                          (C P a - C P (proj1_sig (A0 P))) / V P).
    { field. apply Rgt_not_eq. exact H_V_pos. }
    rewrite H_rearrange in H_elim_lower.
    exact H_elim_lower.
  - apply dominance_elim_prob_threshold.
    + apply Rle_trans with (r2 := H); [exact HH_nonneg | exact Hh].
    + exact HC_strict.
    + unfold eps in H_elim_lower.
      assert (H_rearrange : 1 - (V P - (C P a - C P (proj1_sig (A0 P)))) / V P =
                            (C P a - C P (proj1_sig (A0 P))) / V P).
      { field. apply Rgt_not_eq. exact H_V_pos. }
      rewrite H_rearrange in H_elim_lower.
      exact H_elim_lower.
Qed.

Definition payoff_V (V_alt : R) (h : R) (a : A P) : R :=
  (1 - elim_prob P h a) * V_alt - C P a.

Lemma payoff_V_eq_payoff : forall h a,
  payoff_V (V P) h a = payoff P h a.
Proof.
  intros h a.
  unfold payoff_V, payoff.
  reflexivity.
Qed.

Theorem value_increases_exposure_aversion : forall a1 a2 h V1 V2,
  0 <= h ->
  elim_prob P h a1 < elim_prob P h a2 ->
  C P a1 > C P a2 ->
  V1 < V2 ->
  V1 > 0 ->
  V2 > 0 ->
  payoff_V V2 h a1 - payoff_V V2 h a2 >
  payoff_V V1 h a1 - payoff_V V1 h a2.
Proof.
  intros a1 a2 h V1 V2 Hh Helim HC HV12 HV1_pos HV2_pos.
  unfold payoff_V.
  assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Hdiff_expand :
    ((1 - elim_prob P h a1) * V2 - C P a1) - ((1 - elim_prob P h a2) * V2 - C P a2) =
    (elim_prob P h a2 - elim_prob P h a1) * V2 + (C P a2 - C P a1)).
  { ring. }
  assert (Hdiff_expand_V1 :
    ((1 - elim_prob P h a1) * V1 - C P a1) - ((1 - elim_prob P h a2) * V1 - C P a2) =
    (elim_prob P h a2 - elim_prob P h a1) * V1 + (C P a2 - C P a1)).
  { ring. }
  rewrite Hdiff_expand.
  rewrite Hdiff_expand_V1.
  assert (Hpelim_diff_pos : elim_prob P h a2 - elim_prob P h a1 > 0) by lra.
  assert (HC_diff_neg : C P a2 - C P a1 < 0) by lra.
  assert (Hineq : (elim_prob P h a2 - elim_prob P h a1) * V2 >
                  (elim_prob P h a2 - elim_prob P h a1) * V1).
  { apply Rmult_lt_compat_l; assumption. }
  lra.
Qed.

Theorem value_effect_on_dominance : forall a1 a2 h V_low,
  0 <= h ->
  elim_prob P h a1 < elim_prob P h a2 ->
  C P a1 > C P a2 ->
  0 < V_low ->
  payoff_V V_low h a2 >= payoff_V V_low h a1 ->
  exists V_threshold,
    V_low <= V_threshold /\
    (forall V', V_threshold < V' ->
      payoff_V V' h a1 > payoff_V V' h a2).
Proof.
  intros a1 a2 h V_low Hh Helim HC HV_low_pos Hpayoff_low.
  assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  pose (delta_p := elim_prob P h a2 - elim_prob P h a1).
  pose (delta_C := C P a1 - C P a2).
  assert (Hdelta_p_pos : delta_p > 0) by (unfold delta_p; lra).
  assert (Hdelta_C_pos : delta_C > 0) by (unfold delta_C; lra).
  pose (V_threshold := delta_C / delta_p).
  exists V_threshold.
  assert (HV_threshold_pos : V_threshold > 0).
  { unfold V_threshold. apply Rdiv_pos; assumption. }
  split.
  - unfold payoff_V in Hpayoff_low.
    assert (Hexpand : (1 - elim_prob P h a2) * V_low - C P a2 >=
                      (1 - elim_prob P h a1) * V_low - C P a1) by exact Hpayoff_low.
    assert (Hrearrange : delta_p * V_low <= delta_C).
    { unfold delta_p, delta_C. lra. }
    unfold V_threshold.
    apply Rmult_le_compat_r with (r := / delta_p) in Hrearrange.
    + unfold Rdiv.
      assert (Hsimp : delta_p * V_low * / delta_p = V_low).
      { field. apply Rgt_not_eq. exact Hdelta_p_pos. }
      rewrite Hsimp in Hrearrange.
      exact Hrearrange.
    + apply Rlt_le. apply Rinv_0_lt_compat. exact Hdelta_p_pos.
  - intros V' HV'_gt.
    unfold payoff_V.
    assert (Hdiff : (1 - elim_prob P h a1) * V' - C P a1 -
                    ((1 - elim_prob P h a2) * V' - C P a2) =
                    delta_p * V' - delta_C).
    { unfold delta_p, delta_C. ring. }
    assert (HV'_bound : V' > delta_C / delta_p) by exact HV'_gt.
    apply Rmult_lt_compat_l with (r := delta_p) in HV'_bound.
    + unfold Rdiv in HV'_bound.
      assert (Hsimp : delta_p * (delta_C * / delta_p) = delta_C).
      { field. apply Rgt_not_eq. exact Hdelta_p_pos. }
      rewrite Hsimp in HV'_bound.
      lra.
    + exact Hdelta_p_pos.
Qed.

Lemma payoff_indifference_cost_relation : forall a1 a2 h,
  0 <= h ->
  payoff P h a1 = payoff P h a2 ->
  C P a1 - C P a2 = (elim_prob P h a2 - elim_prob P h a1) * V P.
Proof.
  intros a1 a2 h Hh Hpayoff_eq.
  unfold payoff in Hpayoff_eq.
  assert (HV_pos : V P > 0) by apply V_pos.
  assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  lra.
Qed.

Lemma marginal_cost_exposure_tradeoff : forall a1 a2 h,
  0 <= h ->
  A_sum P h > 0 ->
  T P a1 < T P a2 ->
  payoff P h a1 = payoff P h a2 ->
  C P a1 - C P a2 = (g P (phi P (T P a2) * A_sum P h) -
                      g P (phi P (T P a1) * A_sum P h)) * V P.
Proof.
  intros a1 a2 h Hh HA_pos HT Hpayoff_eq.
  assert (Hcost_rel : C P a1 - C P a2 = (elim_prob P h a2 - elim_prob P h a1) * V P).
  { apply payoff_indifference_cost_relation; assumption. }
  unfold elim_prob in Hcost_rel.
  exact Hcost_rel.
Qed.

Theorem cost_exposure_indifference_curve : forall a1 a2 h,
  0 <= h ->
  A_sum P h > 0 ->
  T P a1 < T P a2 ->
  elim_prob P h a1 < elim_prob P h a2 ->
  payoff P h a1 = payoff P h a2 ->
  exists MRS : R,
    MRS > 0 /\
    C P a1 - C P a2 = MRS * V P /\
    MRS = elim_prob P h a2 - elim_prob P h a1 /\
    MRS = g P (phi P (T P a2) * A_sum P h) - g P (phi P (T P a1) * A_sum P h).
Proof.
  intros a1 a2 h Hh HA_pos HT Helim_ineq Hpayoff_eq.
  pose (MRS := elim_prob P h a2 - elim_prob P h a1).
  exists MRS.
  assert (HMRS_pos : MRS > 0) by (unfold MRS; lra).
  split; [exact HMRS_pos |].
  split.
  - assert (Hcost_rel : C P a1 - C P a2 = (elim_prob P h a2 - elim_prob P h a1) * V P).
    { apply payoff_indifference_cost_relation; assumption. }
    unfold MRS. exact Hcost_rel.
  - split.
    + unfold MRS. reflexivity.
    + unfold MRS, elim_prob. reflexivity.
Qed.

Lemma cost_exposure_exchange_rate_bounds : forall a1 a2 h,
  0 <= h ->
  T P a1 < T P a2 ->
  elim_prob P h a1 < elim_prob P h a2 ->
  payoff P h a1 = payoff P h a2 ->
  0 < (C P a1 - C P a2) / V P <= 1.
Proof.
  intros a1 a2 h Hh HT Helim_ineq Hpayoff_eq.
  assert (HV_pos : V P > 0) by apply V_pos.
  assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Helim_a1_lower : 0 <= elim_prob P h a1) by apply Hbounds1.
  assert (Helim_a1_upper : elim_prob P h a1 <= 1) by apply Hbounds1.
  assert (Helim_a2_lower : 0 <= elim_prob P h a2) by apply Hbounds2.
  assert (Helim_a2_upper : elim_prob P h a2 <= 1) by apply Hbounds2.
  assert (Hcost_rel : C P a1 - C P a2 = (elim_prob P h a2 - elim_prob P h a1) * V P).
  { apply payoff_indifference_cost_relation; assumption. }
  assert (Hdelta_elim_pos : elim_prob P h a2 - elim_prob P h a1 > 0).
  { apply Rlt_0_minus. exact Helim_ineq. }
  split.
  - apply Rdiv_pos.
    + rewrite Hcost_rel. apply Rmult_lt_0_compat; assumption.
    + exact HV_pos.
  - assert (Hdelta_elim_bound : elim_prob P h a2 - elim_prob P h a1 <= 1).
    { assert (Hdirect : elim_prob P h a2 <= 1) by exact Helim_a2_upper.
      assert (Hdirect2 : 0 <= elim_prob P h a1) by exact Helim_a1_lower.
      assert (Hrw2 : - elim_prob P h a1 <= - 0).
      { apply Ropp_le_contravar. exact Hdirect2. }
      replace (- 0) with 0 in Hrw2 by ring.
      assert (Hsum : elim_prob P h a2 + (- elim_prob P h a1) <= 1 + 0).
      { apply Rplus_le_compat; [exact Hdirect | exact Hrw2]. }
      replace (1 + 0) with 1 in Hsum by ring.
      replace (elim_prob P h a2 + (- elim_prob P h a1)) with
              (elim_prob P h a2 - elim_prob P h a1) in Hsum by ring.
      exact Hsum. }
    unfold Rdiv.
    rewrite Hcost_rel.
    replace ((elim_prob P h a2 - elim_prob P h a1) * V P * / V P) with
            (elim_prob P h a2 - elim_prob P h a1).
    + exact Hdelta_elim_bound.
    + field. apply Rgt_not_eq. exact HV_pos.
Qed.

Theorem exposure_dominates_via_value_increase : forall a1 a2 h,
  0 <= h ->
  T P a1 < T P a2 ->
  elim_prob P h a1 < elim_prob P h a2 ->
  payoff P h a1 = payoff P h a2 ->
  forall V_new,
    V_new > V P ->
    payoff_V V_new h a1 > payoff_V V_new h a2.
Proof.
  intros a1 a2 h Hh HT Helim_ineq Hpayoff_eq V_new HV_new.
  assert (HV_pos : V P > 0) by apply V_pos.
  assert (HV_new_pos : V_new > 0) by lra.
  assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  unfold payoff_V.
  assert (Hcost_rel : C P a1 - C P a2 = (elim_prob P h a2 - elim_prob P h a1) * V P).
  { apply payoff_indifference_cost_relation; assumption. }
  assert (Hdelta_elim : elim_prob P h a2 - elim_prob P h a1 > 0) by lra.
  assert (Hineq : (elim_prob P h a2 - elim_prob P h a1) * V_new >
                  (elim_prob P h a2 - elim_prob P h a1) * V P).
  { apply Rmult_lt_compat_l; assumption. }
  rewrite <- Hcost_rel in Hineq.
  lra.
Qed.

Theorem cost_dominates_via_value_decrease : forall a1 a2 h,
  0 <= h ->
  T P a1 < T P a2 ->
  elim_prob P h a1 < elim_prob P h a2 ->
  payoff P h a1 = payoff P h a2 ->
  forall V_new,
    0 < V_new ->
    V_new < V P ->
    payoff_V V_new h a2 > payoff_V V_new h a1.
Proof.
  intros a1 a2 h Hh HT Helim_ineq Hpayoff_eq V_new HV_new_pos HV_new.
  assert (HV_pos : V P > 0) by apply V_pos.
  assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  unfold payoff_V.
  assert (Hcost_rel : C P a1 - C P a2 = (elim_prob P h a2 - elim_prob P h a1) * V P).
  { apply payoff_indifference_cost_relation; assumption. }
  assert (Hdelta_elim : elim_prob P h a2 - elim_prob P h a1 > 0) by lra.
  assert (HV_diff_pos : V P - V_new > 0) by lra.
  assert (Hproduct_pos : (elim_prob P h a2 - elim_prob P h a1) * (V P - V_new) > 0).
  { apply Rmult_lt_0_compat; assumption. }
  lra.
Qed.

End ComparativeStatics.

(** ** 5. Example Instantiation *)

Section Example.

Definition example_A_sum (h : R) : R := h.

Lemma example_A_sum_nonneg : forall h, 0 <= h -> 0 <= example_A_sum h.
Proof. intros h Hh. unfold example_A_sum. assumption. Qed.

Lemma example_A_sum_nondecreasing : nondecreasing example_A_sum.
Proof. unfold nondecreasing, example_A_sum. intros x y Hxy. assumption. Qed.

Lemma example_A_sum_unbounded : forall M, exists h, 0 <= h /\ example_A_sum h >= M.
Proof.
  intro M.
  destruct (Rle_dec 0 M) as [HM | HM].
  - exists M. split; [assumption | unfold example_A_sum; lra].
  - exists 0. split; [lra | unfold example_A_sum; lra].
Qed.

Lemma example_A_sum_to_infty :
  filterlim example_A_sum (Rbar_locally p_infty) (Rbar_locally p_infty).
Proof.
  unfold filterlim, filter_le, filtermap, example_A_sum.
  intros P HP.
  destruct HP as [M HM].
  exists M.
  intros x Hx.
  apply HM.
  assumption.
Qed.

Definition example_phi (x : R) : R := x.

Lemma example_phi_domain : forall x, 0 <= x -> 0 <= example_phi x.
Proof. intros x Hx. unfold example_phi. assumption. Qed.

Lemma example_phi_increasing0 : forall x y, 0 <= x -> 0 <= y -> x <= y ->
  example_phi x <= example_phi y.
Proof. intros x y _ _ Hxy. unfold example_phi. assumption. Qed.

Lemma example_phi_zero : example_phi 0 = 0.
Proof. unfold example_phi. reflexivity. Qed.

Lemma example_phi_pos : forall x, x > 0 -> example_phi x > 0.
Proof. intros x Hx. unfold example_phi. assumption. Qed.

Definition example_g (x : R) : R := 1 - exp (- x).

Lemma example_g_bounds : forall x, 0 <= x -> 0 <= example_g x <= 1.
Proof.
  intros x Hx.
  unfold example_g.
  split.
  - assert (H : exp (- x) <= 1).
    { destruct (Req_dec x 0) as [Heq | Hneq].
      - subst. rewrite Ropp_0, exp_0. lra.
      - assert (Hx_pos : x > 0) by lra.
        assert (H_neg : - x < 0) by lra.
        apply Rlt_le.
        apply exp_increasing in H_neg.
        rewrite exp_0 in H_neg.
        assumption. }
    lra.
  - assert (H : 0 < exp (- x)) by apply exp_pos.
    lra.
Qed.

Lemma example_g_zero : example_g 0 = 0.
Proof.
  unfold example_g.
  rewrite Ropp_0, exp_0.
  ring.
Qed.

Lemma example_g_pos : forall x, x > 0 -> example_g x > 0.
Proof.
  intros x Hx.
  unfold example_g.
  assert (H_neg : - x < 0) by lra.
  assert (H_exp : exp (- x) < exp 0).
  { apply exp_increasing. assumption. }
  rewrite exp_0 in H_exp.
  lra.
Qed.

Lemma example_g_nondecreasing : nondecreasing example_g.
Proof.
  unfold nondecreasing, example_g.
  intros x y Hxy.
  destruct (Req_dec x y) as [Heq | Hneq].
  - subst. lra.
  - assert (Hlt : x < y) by lra.
    assert (H : - y < - x) by lra.
    apply exp_increasing in H.
    lra.
Qed.

Lemma example_g_tendsto_1 :
  filterlim example_g (Rbar_locally p_infty) (locally 1).
Proof.
  intros P [eps HP].
  exists (- ln (eps / 2)).
  intros x Hx.
  apply HP.
  unfold ball, AbsRing_ball, example_g.
  unfold abs; simpl; unfold minus, plus, opp; simpl.
  assert (Heps_pos : 0 < eps) by apply (cond_pos eps).
  assert (Heps_half_pos : 0 < eps / 2) by lra.
  assert (Hx_neg : - x < ln (eps / 2)) by lra.
  apply exp_increasing in Hx_neg.
  rewrite exp_ln in Hx_neg by lra.
  assert (Hgoal_form : Rabs (Rplus (Rplus 1 (Ropp (exp (Ropp x)))) (Ropp 1)) < eps).
  { replace (Rplus (Rplus 1 (Ropp (exp (Ropp x)))) (Ropp 1)) with (Ropp (exp (Ropp x))) by ring.
    rewrite Rabs_Ropp, Rabs_right by (apply Rle_ge, Rlt_le, exp_pos).
    lra. }
  exact Hgoal_form.
Qed.

Definition example_T (a : R) : R := Rmax 0 a.

Lemma example_T_nonneg : forall a, 0 <= example_T a.
Proof.
  intro a.
  unfold example_T.
  apply Rmax_l.
Qed.

Lemma example_A0_witness : { a0 : R | example_T a0 = 0 }.
Proof.
  exists 0.
  unfold example_T.
  rewrite Rmax_left; [reflexivity | lra].
Qed.

Definition example_C (a : R) : R := 0.

Lemma example_C_nonneg : forall a, 0 <= example_C a.
Proof. intro a. unfold example_C. lra. Qed.

Lemma example_V_margin_proof : 1 - example_C (proj1_sig example_A0_witness) > 0.
Proof.
  simpl. unfold example_C. lra.
Qed.

Lemma example_g_hazard_lb_proof : { lambda : R | lambda > 0 /\ forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= example_g x }.
Proof.
  exists 1.
  split; [lra |].
  intros x Hx.
  unfold example_g.
  replace (1 * x) with x by ring.
  lra.
Qed.

Definition Example_EOX_Params : EOX_Params := {|
  A := R;
  A_inhabited := exist _ 0 I;
  T := example_T;
  T_nonneg := example_T_nonneg;
  A0 := example_A0_witness;
  phi := example_phi;
  phi_domain := example_phi_domain;
  phi_increasing0 := example_phi_increasing0;
  phi_zero := example_phi_zero;
  phi_pos := example_phi_pos;
  g := example_g;
  g_bounds := example_g_bounds;
  g_zero := example_g_zero;
  g_pos := example_g_pos;
  g_nondecreasing := example_g_nondecreasing;
  g_tendsto_1 := example_g_tendsto_1;
  g_hazard_lb := example_g_hazard_lb_proof;
  A_sum := example_A_sum;
  A_sum_nonneg := example_A_sum_nonneg;
  A_sum_nondecreasing := example_A_sum_nondecreasing;
  A_sum_unbounded := example_A_sum_unbounded;
  A_sum_to_infty := example_A_sum_to_infty;
  V := 1;
  V_pos := Rlt_0_1;
  C := example_C;
  C_nonneg := example_C_nonneg;
  V_margin := example_V_margin_proof
|}.

Theorem example_dominance : forall a,
  C Example_EOX_Params (proj1_sig (A0 Example_EOX_Params)) <= C Example_EOX_Params a ->
  (T Example_EOX_Params a = 0 /\
   C Example_EOX_Params (proj1_sig (A0 Example_EOX_Params)) = C Example_EOX_Params a) \/
  exists H : R, 0 <= H /\
    forall h, H <= h ->
      payoff Example_EOX_Params h (proj1_sig (A0 Example_EOX_Params)) >
      payoff Example_EOX_Params h a.
Proof.
  intros a HC.
  apply EOX_asymptotic_null_dominance_pointwise.
  exact HC.
Qed.

End Example.

(** ** 6. Derived Consequences *)

Section DerivedConsequences.

Context (P : EOX_Params).

Definition exposure_hazard (a : A P) (h : R) : R :=
  phi P (T P a) * A_sum P h.

Theorem exposure_product_universality : forall a1 a2 h1 h2,
  0 <= h1 ->
  0 <= h2 ->
  exposure_hazard a1 h1 = exposure_hazard a2 h2 ->
  elim_prob P h1 a1 = elim_prob P h2 a2.
Proof.
  intros a1 a2 h1 h2 Hh1 Hh2 Heq.
  unfold elim_prob, exposure_hazard in *.
  rewrite Heq.
  reflexivity.
Qed.

Theorem null_exposure_temporal_invariance : forall h1 h2,
  0 <= h1 ->
  0 <= h2 ->
  payoff P h1 (proj1_sig (A0 P)) = payoff P h2 (proj1_sig (A0 P)).
Proof.
  intros h1 h2 Hh1 Hh2.
  rewrite EOX_payoff_null_exposure_constant; [| exact Hh1].
  rewrite EOX_payoff_null_exposure_constant; [| exact Hh2].
  reflexivity.
Qed.

Theorem survival_eventually_arbitrarily_small : forall a eps,
  T P a > 0 ->
  0 < eps < 1 ->
  exists h, 0 <= h /\ 1 - elim_prob P h a < eps.
Proof.
  intros a eps HTa [Heps_pos Heps_bound].
  destruct (@EOX_elim_prob_tends_to_1_explicit P a eps HTa Heps_pos) as [H [HH_nonneg Hforall]].
  exists H.
  split; [exact HH_nonneg |].
  specialize (Hforall H (Rle_refl H)).
  destruct Hforall as [Hlower Hupper].
  apply Ropp_lt_contravar in Hlower.
  apply Rplus_lt_compat_l with (r := 1) in Hlower.
  replace (1 + - elim_prob P H a) with (1 - elim_prob P H a) in Hlower by ring.
  replace (1 + - (1 - eps)) with eps in Hlower by ring.
  exact Hlower.
Qed.

Lemma payoff_nondecreasing_in_h : forall a h1 h2,
  0 <= h1 ->
  h1 <= h2 ->
  payoff P h2 a <= payoff P h1 a.
Proof.
  intros a h1 h2 Hh1 Hh1h2.
  unfold payoff.
  assert (Hh2 : 0 <= h2) by lra.
  assert (H_A_mono : A_sum P h1 <= A_sum P h2).
  { apply A_sum_nondecreasing. assumption. }
  assert (H_phi_nonneg : 0 <= phi P (T P a)).
  { apply phi_domain. apply T_nonneg. }
  assert (H_product_mono : phi P (T P a) * A_sum P h1 <= phi P (T P a) * A_sum P h2).
  { apply Rmult_le_compat_l; assumption. }
  assert (H_elim_mono : elim_prob P h1 a <= elim_prob P h2 a).
  { unfold elim_prob. apply g_nondecreasing. assumption. }
  assert (H_surv_mono : 1 - elim_prob P h2 a <= 1 - elim_prob P h1 a) by lra.
  assert (HV_pos : V P > 0) by apply V_pos.
  assert (H_val_mono : (1 - elim_prob P h2 a) * V P <= (1 - elim_prob P h1 a) * V P).
  { apply Rmult_le_compat_r; [lra | assumption]. }
  lra.
Qed.

Theorem phi_A_sum_scaling_invariance : forall c a h,
  c > 0 ->
  0 <= h ->
  g P (c * phi P (T P a) * (A_sum P h / c)) = g P (phi P (T P a) * A_sum P h).
Proof.
  intros c a h Hc Hh.
  assert (Heq : c * phi P (T P a) * (A_sum P h / c) = phi P (T P a) * A_sum P h).
  { unfold Rdiv. field. apply Rgt_not_eq. assumption. }
  rewrite Heq.
  reflexivity.
Qed.

End DerivedConsequences.

(** ** 7. Nash Equilibrium Analysis *)

Section NashEquilibrium.

Context (P : EOX_Params).

Definition is_best_response (h : R) (a_star a_alt : A P) : Prop :=
  payoff P h a_star >= payoff P h a_alt.

Definition is_strict_best_response (h : R) (a_star a_alt : A P) : Prop :=
  payoff P h a_star > payoff P h a_alt.

Definition is_weakly_dominant (a_star : A P) : Prop :=
  forall a, C P (proj1_sig (A0 P)) <= C P a ->
  forall h, 0 <= h -> is_best_response h a_star a.

Definition is_asymptotically_dominant (a_star : A P) : Prop :=
  forall a, C P (proj1_sig (A0 P)) <= C P a ->
  (T P a = 0 /\ C P (proj1_sig (A0 P)) = C P a) \/
  exists H : R, 0 <= H /\ forall h, H <= h -> is_strict_best_response h a_star a.

Theorem null_exposure_is_asymptotically_dominant :
  is_asymptotically_dominant (proj1_sig (A0 P)).
Proof.
  unfold is_asymptotically_dominant, is_strict_best_response.
  intros a HC.
  exact (EOX_asymptotic_null_dominance_pointwise P a HC).
Qed.

Lemma best_response_transitive : forall h a1 a2 a3,
  is_best_response h a1 a2 ->
  is_best_response h a2 a3 ->
  is_best_response h a1 a3.
Proof.
  unfold is_best_response.
  intros h a1 a2 a3 H12 H23.
  apply Rge_trans with (r2 := payoff P h a2); assumption.
Qed.

Definition nash_equilibrium (h : R) (a_star : A P) : Prop :=
  forall a, is_best_response h a_star a.

Theorem asymptotic_null_exposure_nash :
  (forall a, C P a >= C P (proj1_sig (A0 P))) ->
  exists H, 0 <= H /\ forall h, H <= h -> nash_equilibrium h (proj1_sig (A0 P)).
Proof.
  intro Hcost_assumption.
  pose (a0 := proj1_sig (A0 P)).
  assert (H_exists : forall a, exists H_a, 0 <= H_a /\
    ((T P a = 0 /\ C P a0 = C P a) \/
     forall h, H_a <= h -> payoff P h a0 > payoff P h a)).
  { intro a.
    assert (HC : C P a0 <= C P a) by (apply Rge_le; apply Hcost_assumption).
    pose proof (EOX_asymptotic_null_dominance_pointwise P a HC) as Hdom.
    destruct Hdom as [[HT HC_eq] | [H_a [HH_a Hforall]]].
    - exists 0. split; [lra |]. left. split; assumption.
    - exists H_a. split; [assumption |]. right. assumption. }
  exists 0. split; [lra |].
  intros h Hh.
  unfold nash_equilibrium, is_best_response.
  intro a.
  assert (HC : C P a0 <= C P a) by (apply Rge_le; apply Hcost_assumption).
  pose proof (EOX_asymptotic_null_dominance_pointwise P a HC) as Hdom.
  destruct Hdom as [[HT_eq HC_eq] | [H_a [HH_a Hforall]]].
  - unfold a0 in *.
    rewrite EOX_payoff_null_exposure_constant by assumption.
    unfold payoff, elim_prob.
    rewrite HT_eq, phi_zero, Rmult_0_l, g_zero.
    rewrite HC_eq.
    lra.
  - destruct (Rle_dec H_a h) as [Hle | Hgt].
    + assert (Hstrict := Hforall h Hle).
      apply Rle_ge, Rlt_le, Hstrict.
    + unfold a0 in *.
      rewrite EOX_payoff_null_exposure_constant by assumption.
      unfold payoff.
      assert (Hbounds : 0 <= elim_prob P h a <= 1).
      { apply EOX_elim_prob_bounds. assumption. }
      assert (HV := V_pos P).
      assert (HC_nonneg := C_nonneg P a).
      assert (HC0_nonneg := C_nonneg P (proj1_sig (A0 P))).
      apply Rle_ge.
      assert (H_survival : (1 - elim_prob P h a) * V P <= V P).
      { assert (H_elim_nonneg : 0 <= elim_prob P h a) by apply Hbounds.
        nra. }
      nra.
Qed.

End NashEquilibrium.

(** ** 8. Multi-Agent Extension *)

Section MultiAgent.

Context (P : EOX_Params).

Variable num_agents : nat.
Hypothesis num_agents_pos : (num_agents > 0)%nat.

Definition agent_strategy := nat -> A P.

Definition joint_elim_prob (h : R) (agents : agent_strategy) (i : nat) : R :=
  elim_prob P h (agents i).

Definition independent_survival_prob (h : R) (agents : agent_strategy) : R :=
  fold_right Rmult 1 (map (fun i => 1 - joint_elim_prob h agents i) (seq 0 num_agents)).

Lemma multi_agent_survival_nonneg : forall h agents,
  0 <= h ->
  0 <= independent_survival_prob h agents.
Proof.
  intros h agents Hh.
  unfold independent_survival_prob.
  apply fold_right_Rmult_nonneg.
  intros x Hx.
  apply in_map_iff in Hx.
  destruct Hx as [i [Heq Hin]]. subst.
  unfold joint_elim_prob, elim_prob.
  assert (Hbounds : 0 <= g P (phi P (T P (agents i)) * A_sum P h) <= 1).
  { apply g_bounds.
    apply Rmult_le_pos.
    - apply phi_domain. apply T_nonneg.
    - apply A_sum_nonneg. assumption. }
  lra.
Qed.

Theorem multi_agent_null_exposure_dominance : forall h agents,
  0 <= h ->
  (forall i, (i < num_agents)%nat -> agents i = proj1_sig (A0 P)) ->
  independent_survival_prob h agents = (1 - 0) ^ num_agents.
Proof.
  intros h agents Hh Hall_null.
  unfold independent_survival_prob.
  assert (H_all_zero : forall i, (i < num_agents)%nat -> joint_elim_prob h agents i = 0).
  { intros i Hi.
    unfold joint_elim_prob.
    rewrite Hall_null by assumption.
    apply EOX_elim_prob_null_exposure. assumption. }
  assert (H_map : map (fun i => 1 - joint_elim_prob h agents i) (seq 0 num_agents) =
                  map (fun _ => 1) (seq 0 num_agents)).
  { apply map_ext_in.
    intros i Hi.
    apply in_seq in Hi.
    rewrite H_all_zero by lia.
    ring. }
  rewrite H_map.
  clear H_map H_all_zero.
  assert (H_all_ones : forall n, fold_right Rmult 1 (map (fun _ => 1) (seq 0 n)) = 1).
  { intro n. induction n.
    - simpl. reflexivity.
    - rewrite (seq_last 0 n).
      rewrite map_app.
      rewrite fold_right_Rmult_app.
      simpl fold_right.
      rewrite Rmult_1_r.
      rewrite IHn.
      ring. }
  rewrite H_all_ones.
  replace (1 - 0) with 1 by ring.
  assert (H_pow : forall n, 1 ^ n = 1).
  { intro n. induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. ring. }
  rewrite H_pow.
  reflexivity.
Qed.

(** *** Strict Pareto Dominance *)

Theorem null_exposure_pareto_dominates : forall (agents : agent_strategy),
  (forall i, (i < num_agents)%nat -> C P (proj1_sig (A0 P)) <= C P (agents i)) ->
  (exists i, (i < num_agents)%nat /\ T P (agents i) > 0) ->
  forall h, 0 <= h ->
    forall i, (i < num_agents)%nat ->
      payoff P h (proj1_sig (A0 P)) >= payoff P h (agents i).
Proof.
  intros agents HC_all [i_wit [Hi_wit HT_wit]] h Hh i Hi.
  pose (a0 := proj1_sig (A0 P)).
  assert (HC_i : C P a0 <= C P (agents i)) by (apply HC_all; assumption).
  pose proof (EOX_asymptotic_null_dominance_pointwise P (agents i) HC_i) as Hdom.
  destruct Hdom as [[HT_zero HC_eq] | [H_i [HH_i Hforall]]].
  - unfold a0 in *.
    rewrite EOX_payoff_null_exposure_constant by assumption.
    unfold payoff, elim_prob.
    rewrite HT_zero, phi_zero, Rmult_0_l, g_zero.
    rewrite HC_eq.
    lra.
  - destruct (Rle_dec H_i h) as [Hle | Hgt].
    + assert (Hstrict : payoff P h (proj1_sig (A0 P)) > payoff P h (agents i)).
      { apply Hforall. assumption. }
      lra.
    + unfold a0 in *.
      rewrite EOX_payoff_null_exposure_constant by assumption.
      unfold payoff.
      assert (Hbounds : 0 <= elim_prob P h (agents i) <= 1).
      { apply EOX_elim_prob_bounds. assumption. }
      assert (HV := V_pos P).
      assert (H_survival : (1 - elim_prob P h (agents i)) * V P <= V P).
      { nra. }
      lra.
Qed.

(** *** Stronger Pareto Dominance: Strict for Positive Exposure *)

Theorem null_exposure_pareto_dominates_strict : forall (agents : agent_strategy),
  (forall i, (i < num_agents)%nat -> C P (proj1_sig (A0 P)) <= C P (agents i)) ->
  (exists i, (i < num_agents)%nat /\ T P (agents i) > 0) ->
  forall i, (i < num_agents)%nat ->
    (T P (agents i) = 0 /\ C P (proj1_sig (A0 P)) = C P (agents i)) \/
    (exists H : R, 0 <= H /\ forall h, H <= h -> payoff P h (proj1_sig (A0 P)) > payoff P h (agents i)).
Proof.
  intros agents HC_all Hex_pos i Hi.
  assert (HC_i : C P (proj1_sig (A0 P)) <= C P (agents i)) by (apply HC_all; assumption).
  pose proof (EOX_asymptotic_null_dominance_pointwise P (agents i) HC_i) as Hdom.
  exact Hdom.
Qed.

Corollary pareto_dominance_dichotomy : forall (agents : agent_strategy),
  (forall i, (i < num_agents)%nat -> C P (proj1_sig (A0 P)) <= C P (agents i)) ->
  (exists i, (i < num_agents)%nat /\ T P (agents i) > 0) ->
  forall i, (i < num_agents)%nat ->
    (forall h, 0 <= h -> payoff P h (proj1_sig (A0 P)) = payoff P h (agents i)) \/
    (exists H : R, 0 <= H /\ forall h, H <= h -> payoff P h (proj1_sig (A0 P)) > payoff P h (agents i)).
Proof.
  intros agents HC_all Hex_pos i Hi.
  assert (HC_i : C P (proj1_sig (A0 P)) <= C P (agents i)) by (apply HC_all; assumption).
  pose proof (EOX_asymptotic_null_dominance_pointwise P (agents i) HC_i) as Hdom.
  destruct Hdom as [[HT_zero HC_eq] | [H [HH Hstrict]]].
  - left. intros h Hh.
    rewrite EOX_payoff_null_exposure_constant by assumption.
    unfold payoff, elim_prob.
    rewrite HT_zero, phi_zero, Rmult_0_l, g_zero.
    rewrite HC_eq.
    ring.
  - right. exists H. split; assumption.
Qed.

End MultiAgent.

(** ** 8b. Nash Equilibrium Uniqueness *)

Section NashEquilibriumUniqueness.

Context (P : EOX_Params).

Variable num_agents : nat.
Hypothesis num_agents_pos : (num_agents > 0)%nat.

Definition strategy_profile := nat -> A P.

Definition null_exposure_profile : strategy_profile :=
  fun _ => proj1_sig (A0 P).

Record Nash_Equilibrium (profile : strategy_profile) := {
  equilibrium_horizon : R;
  horizon_nonneg : 0 <= equilibrium_horizon;
  no_profitable_deviation : forall i a_i,
    (i < num_agents)%nat ->
    forall h, equilibrium_horizon <= h ->
      payoff P h (profile i) >= payoff P h a_i
}.

Definition is_nash_equilibrium (profile : strategy_profile) : Prop :=
  exists H, 0 <= H /\
    forall i a_i,
      (i < num_agents)%nat ->
      forall h, H <= h ->
        payoff P h (profile i) >= payoff P h a_i.

Definition behaviorally_equivalent (a1 a2 : A P) : Prop :=
  T P a1 = T P a2 /\ C P a1 = C P a2.

Definition unique_nash_equilibrium (profile : strategy_profile) : Prop :=
  is_nash_equilibrium profile /\
  forall profile',
    is_nash_equilibrium profile' ->
    exists H, 0 <= H /\
      forall i h, (i < num_agents)%nat -> H <= h ->
        behaviorally_equivalent (profile' i) (profile i).

Hypothesis cost_assumption : forall a, C P a >= C P (proj1_sig (A0 P)).

Theorem null_exposure_is_nash : is_nash_equilibrium null_exposure_profile.
Proof.
  unfold is_nash_equilibrium, null_exposure_profile.
  exists 0. split; [lra |].
  intros i a_i Hi h Hh.
  assert (HC : C P (proj1_sig (A0 P)) <= C P a_i).
  { apply Rge_le. apply cost_assumption. }
  pose proof (EOX_asymptotic_null_dominance_pointwise P a_i HC) as Hdom.
  destruct Hdom as [[HT_zero HC_eq] | [H_a [HH_a Hforall]]].
  - rewrite EOX_payoff_null_exposure_constant by assumption.
    unfold payoff, elim_prob.
    rewrite HT_zero, phi_zero, Rmult_0_l, g_zero.
    rewrite HC_eq.
    lra.
  - destruct (Rle_dec H_a h) as [Hle | Hgt].
    + assert (Hstrict : payoff P h (proj1_sig (A0 P)) > payoff P h a_i).
      { apply Hforall. assumption. }
      lra.
    + rewrite EOX_payoff_null_exposure_constant by assumption.
      unfold payoff.
      assert (Hbounds : 0 <= elim_prob P h a_i <= 1).
      { apply EOX_elim_prob_bounds. assumption. }
      assert (HV := V_pos P).
      assert (H_survival : (1 - elim_prob P h a_i) * V P <= V P) by nra.
      lra.
Qed.

Theorem null_exposure_unique_nash : unique_nash_equilibrium null_exposure_profile.
Proof.
  unfold unique_nash_equilibrium.
  split.
  - apply null_exposure_is_nash.
  - intros profile' Hnash'.
    unfold is_nash_equilibrium in Hnash'.
    destruct Hnash' as [H' [HH'_nonneg Hno_dev]].
    exists 0. split; [lra |].
    intros i h Hi Hh.
    unfold null_exposure_profile.
    pose (a_i := profile' i).
    assert (HC : C P (proj1_sig (A0 P)) <= C P a_i).
    { apply Rge_le. apply cost_assumption. }
    pose proof (EOX_asymptotic_null_dominance_pointwise P a_i HC) as Hdom.
    destruct Hdom as [[HT_zero HC_eq] | [H_a [HH_a Hforall]]].
    + assert (H_payoff_eq : forall h', 0 <= h' ->
        payoff P h' (proj1_sig (A0 P)) = payoff P h' a_i).
      { intros h' Hh'.
        rewrite EOX_payoff_null_exposure_constant by assumption.
        unfold payoff, elim_prob.
        rewrite HT_zero, phi_zero, Rmult_0_l, g_zero.
        rewrite HC_eq.
        ring. }
      assert (Helim_zero : forall h', 0 <= h' -> elim_prob P h' a_i = 0).
      { intros h' Hh'.
        unfold elim_prob.
        rewrite HT_zero, phi_zero, Rmult_0_l, g_zero.
        reflexivity. }
      unfold elim_prob in Helim_zero.
      assert (Hg_implies_zero : forall h', 0 <= h' ->
        g P (phi P (T P a_i) * A_sum P h') = 0).
      { intros h' Hh'. apply Helim_zero. assumption. }
      assert (Hphi_zero : phi P (T P a_i) = 0).
      { destruct (Req_dec (phi P (T P a_i)) 0) as [Heq | Hneq].
        - assumption.
        - assert (Hphi_pos : phi P (T P a_i) > 0).
          { assert (HT_nonneg : 0 <= T P a_i) by apply T_nonneg.
            destruct (Req_dec (T P a_i) 0) as [HTeq | HTneq].
            + rewrite HTeq in *. rewrite phi_zero in Hneq. lra.
            + assert (HT_pos : T P a_i > 0) by lra.
              apply phi_pos. assumption. }
          assert (Hex_h : exists h', 0 <= h' /\ A_sum P h' > 0).
          { pose proof (A_sum_unbounded P 1) as [h' [Hh' HA_bound]].
            exists h'. split; [assumption |].
            assert (HA_nonneg : 0 <= A_sum P h') by (apply A_sum_nonneg; assumption).
            lra. }
          destruct Hex_h as [h' [Hh'_nonneg HA_pos]].
          specialize (Hg_implies_zero h' Hh'_nonneg).
          assert (Hprod_pos : phi P (T P a_i) * A_sum P h' > 0).
          { apply Rmult_lt_0_compat; assumption. }
          assert (Hg_pos : g P (phi P (T P a_i) * A_sum P h') > 0).
          { apply g_pos. assumption. }
          lra. }
      assert (HT_a_zero : T P a_i = 0).
      { assert (HT_nonneg : 0 <= T P a_i) by apply T_nonneg.
        destruct (Req_dec (T P a_i) 0) as [Heq | Hneq].
        - assumption.
        - assert (HT_pos : T P a_i > 0) by lra.
          assert (Hphi_pos : phi P (T P a_i) > 0).
          { apply phi_pos. assumption. }
          lra. }
      unfold a_i in HT_a_zero.
      assert (HT_a0 : T P (proj1_sig (A0 P)) = 0).
      { destruct (A0 P) as [a0 Ha0]. simpl. assumption. }
      assert (HC_eq' : C P (profile' i) = C P (proj1_sig (A0 P))).
      { unfold a_i in HC_eq. symmetry. exact HC_eq. }
      unfold behaviorally_equivalent.
      split.
      * rewrite HT_a_zero, HT_a0. reflexivity.
      * exact HC_eq'.
    + exfalso.
      pose (H_max := Rmax H' H_a).
      assert (Hmax_nonneg : 0 <= H_max).
      { unfold H_max. apply Rle_trans with (r2 := H'); [assumption | apply Rmax_l]. }
      assert (Hno_dev_at_max : payoff P H_max (profile' i) >= payoff P H_max (proj1_sig (A0 P))).
      { apply Hno_dev; [assumption |]. unfold H_max. apply Rmax_l. }
      assert (Hdom_at_max : payoff P H_max (proj1_sig (A0 P)) > payoff P H_max a_i).
      { apply Hforall. unfold H_max. apply Rmax_r. }
      unfold a_i in Hdom_at_max.
      lra.
Qed.

Corollary null_exposure_only_equilibrium_behavior :
  forall profile',
    is_nash_equilibrium profile' ->
    forall i, (i < num_agents)%nat ->
      T P (profile' i) = 0 /\ C P (profile' i) = C P (proj1_sig (A0 P)).
Proof.
  intros profile' Hnash i Hi.
  assert (Hunique := null_exposure_unique_nash).
  unfold unique_nash_equilibrium in Hunique.
  destruct Hunique as [_ Hforall].
  specialize (Hforall profile' Hnash).
  destruct Hforall as [H [HH_nonneg Hbehav]].
  specialize (Hbehav i H Hi (Rle_refl H)).
  unfold behaviorally_equivalent, null_exposure_profile in Hbehav.
  destruct Hbehav as [HT_eq HC_eq].
  destruct (A0 P) as [a0 Ha0]. simpl in *.
  split.
  - rewrite HT_eq. exact Ha0.
  - exact HC_eq.
Qed.

End NashEquilibriumUniqueness.

(** ** 8c. Evolutionary Stability: Exposure as a Dead End *)

Section EvolutionaryStability.

Context (P : EOX_Params).

Variable num_agents : nat.
Hypothesis num_agents_pos : (num_agents > 0)%nat.
Hypothesis cost_assumption : forall a, C P a >= C P (proj1_sig (A0 P)).

Definition population_state := A P -> R.

Definition population_valid (pop : population_state) : Prop :=
  (forall a, 0 <= pop a) /\
  exists a, pop a > 0.

Definition expected_payoff (h : R) (a : A P) (pop : population_state) : R :=
  payoff P h a.

Definition fitness_advantage (h : R) (a1 a2 : A P) : R :=
  payoff P h a1 - payoff P h a2.

Definition strictly_dominates_in_population (h : R) (a_dominant a_other : A P) : Prop :=
  fitness_advantage h a_dominant a_other > 0.

Theorem null_exposure_evolutionarily_stable : forall a h,
  0 <= h ->
  C P (proj1_sig (A0 P)) <= C P a ->
  T P a > 0 ->
  exists H, 0 <= H /\ forall h', H <= h' ->
    strictly_dominates_in_population h' (proj1_sig (A0 P)) a.
Proof.
  intros a h Hh HC HTa.
  pose proof (EOX_asymptotic_null_dominance_pointwise P a HC) as Hdom.
  destruct Hdom as [[HT_zero HC_eq] | [H [HH_nonneg Hforall]]].
  - exfalso. lra.
  - exists H. split; [assumption |].
    intros h' Hh'.
    unfold strictly_dominates_in_population, fitness_advantage.
    assert (Hstrict : payoff P h' (proj1_sig (A0 P)) > payoff P h' a).
    { apply Hforall. assumption. }
    lra.
Qed.

Definition evolutionarily_stable_strategy (a : A P) : Prop :=
  forall a', C P (proj1_sig (A0 P)) <= C P a' ->
    (T P a' = 0 /\ C P (proj1_sig (A0 P)) = C P a') \/
    exists H, 0 <= H /\ forall h, H <= h ->
      strictly_dominates_in_population h a a'.

Theorem null_exposure_is_ESS : evolutionarily_stable_strategy (proj1_sig (A0 P)).
Proof.
  unfold evolutionarily_stable_strategy.
  intros a' HC.
  pose proof (EOX_asymptotic_null_dominance_pointwise P a' HC) as Hdom.
  destruct Hdom as [[HT_zero HC_eq] | [H [HH_nonneg Hforall]]].
  - left. split; assumption.
  - right. exists H. split; [assumption |].
    intros h Hh.
    unfold strictly_dominates_in_population, fitness_advantage.
    assert (Hstrict : payoff P h (proj1_sig (A0 P)) > payoff P h a').
    { apply Hforall. assumption. }
    lra.
Qed.

Definition mutant_invasion_fitness (h : R) (a_mutant : A P) : R :=
  payoff P h a_mutant - payoff P h (proj1_sig (A0 P)).

Theorem exposure_mutants_cannot_invade : forall a,
  C P (proj1_sig (A0 P)) <= C P a ->
  T P a > 0 ->
  exists H, 0 <= H /\ forall h, H <= h ->
    mutant_invasion_fitness h a < 0.
Proof.
  intros a HC HTa.
  pose proof (EOX_asymptotic_null_dominance_pointwise P a HC) as Hdom.
  destruct Hdom as [[HT_zero HC_eq] | [H [HH_nonneg Hforall]]].
  - exfalso. lra.
  - exists H. split; [assumption |].
    intros h Hh.
    unfold mutant_invasion_fitness.
    assert (Hstrict : payoff P h (proj1_sig (A0 P)) > payoff P h a).
    { apply Hforall. assumption. }
    lra.
Qed.

Theorem extinction_inevitability : forall a,
  C P (proj1_sig (A0 P)) <= C P a ->
  T P a > 0 ->
  is_lim (fun h => mutant_invasion_fitness h a) p_infty (- (V P - C P (proj1_sig (A0 P)) + C P a)).
Proof.
  intros a HC HTa.
  unfold mutant_invasion_fitness.
  assert (H_null_constant : forall h, 0 <= h ->
    payoff P h (proj1_sig (A0 P)) = V P - C P (proj1_sig (A0 P))).
  { intros h Hh. apply EOX_payoff_null_exposure_constant. assumption. }
  assert (H_a_limit : is_lim (fun h => payoff P h a) p_infty (- C P a)).
  { apply EOX_payoff_limit_pos_exposure. assumption. }
  unfold is_lim, filterlim, filter_le, filtermap in *.
  intros Q HQ.
  destruct HQ as [eps Heps].
  unfold is_lim, filterlim, filter_le, filtermap in H_a_limit.
  assert (H_ball : locally (- C P a) (ball (- C P a) eps)).
  { exists eps. intros y Hy. exact Hy. }
  specialize (H_a_limit (ball (- C P a) eps) H_ball).
  destruct H_a_limit as [M HM].
  exists (Rmax M 0).
  intros h Hh.
  apply Heps.
  unfold ball, AbsRing_ball, abs, minus, plus, opp. simpl.
  assert (Hh_nonneg : 0 <= h).
  { apply Rle_trans with (r2 := Rmax M 0).
    - unfold Rmax. destruct (Rle_dec M 0); lra.
    - apply Rlt_le. assumption. }
  assert (Hh_M : M < h).
  { unfold Rmax in Hh. destruct (Rle_dec M 0) in Hh; lra. }
  rewrite H_null_constant by assumption.
  specialize (HM h Hh_M).
  unfold ball, AbsRing_ball, abs, minus, plus, opp in HM. simpl in HM.
  assert (Hgoal : Rabs (payoff P h a - (V P - C P (proj1_sig (A0 P))) - (- (V P - C P (proj1_sig (A0 P)) + C P a))) < eps).
  { replace (payoff P h a - (V P - C P (proj1_sig (A0 P))) - (- (V P - C P (proj1_sig (A0 P)) + C P a)))
      with (payoff P h a - (- C P a)) by ring.
    exact HM. }
  exact Hgoal.
Qed.

End EvolutionaryStability.

(** ** 9. Concrete Example: Data Backup Strategy *)

Section BackupExample.

Definition backup_interval_days : Type := R.

Definition backup_T (a : backup_interval_days) : R := Rmax 0 a.

Lemma backup_T_nonneg : forall a, 0 <= backup_T a.
Proof.
  intro a. unfold backup_T. apply Rmax_l.
Qed.

Lemma backup_A0_witness : { a0 : backup_interval_days | backup_T a0 = 0 }.
Proof.
  exists 0. unfold backup_T. rewrite Rmax_left; [reflexivity | lra].
Qed.

Definition backup_phi (exposure_days : R) : R := exposure_days.

Lemma backup_phi_domain : forall x, 0 <= x -> 0 <= backup_phi x.
Proof.
  intros x Hx. unfold backup_phi. assumption.
Qed.

Lemma backup_phi_increasing0 : forall x y, 0 <= x -> 0 <= y -> x <= y ->
  backup_phi x <= backup_phi y.
Proof.
  intros x y _ _ Hxy. unfold backup_phi. assumption.
Qed.

Lemma backup_phi_zero : backup_phi 0 = 0.
Proof.
  unfold backup_phi. reflexivity.
Qed.

Lemma backup_phi_pos : forall x, x > 0 -> backup_phi x > 0.
Proof.
  intros x Hx. unfold backup_phi. assumption.
Qed.

Definition backup_g (x : R) : R := 1 - exp (- x).

Lemma backup_g_bounds : forall x, 0 <= x -> 0 <= backup_g x <= 1.
Proof.
  intros x Hx. unfold backup_g.
  split.
  - assert (H : exp (- x) <= 1).
    { destruct (Req_dec x 0) as [Heq | Hneq].
      - subst. rewrite Ropp_0, exp_0. lra.
      - assert (Hx_pos : x > 0) by lra.
        assert (H_neg : - x < 0) by lra.
        apply Rlt_le. apply exp_increasing in H_neg.
        rewrite exp_0 in H_neg. assumption. }
    lra.
  - assert (H : 0 < exp (- x)) by apply exp_pos. lra.
Qed.

Lemma backup_g_zero : backup_g 0 = 0.
Proof.
  unfold backup_g. rewrite Ropp_0, exp_0. ring.
Qed.

Lemma backup_g_pos : forall x, x > 0 -> backup_g x > 0.
Proof.
  intros x Hx. unfold backup_g.
  assert (H_neg : - x < 0) by lra.
  assert (H_exp : exp (- x) < exp 0).
  { apply exp_increasing. assumption. }
  rewrite exp_0 in H_exp. lra.
Qed.

Lemma backup_g_nondecreasing : nondecreasing backup_g.
Proof.
  unfold nondecreasing, backup_g. intros x y Hxy.
  destruct (Req_dec x y) as [Heq | Hneq].
  - subst. lra.
  - assert (Hlt : x < y) by lra.
    assert (H : - y < - x) by lra.
    apply exp_increasing in H. lra.
Qed.

Lemma backup_g_tendsto_1 :
  filterlim backup_g (Rbar_locally p_infty) (locally 1).
Proof.
  intros P [eps HP].
  exists (- ln (eps / 2)).
  intros x Hx. apply HP.
  unfold ball, AbsRing_ball, backup_g.
  unfold abs; simpl; unfold minus, plus, opp; simpl.
  assert (Heps_pos : 0 < eps) by apply (cond_pos eps).
  assert (Heps_half_pos : 0 < eps / 2) by lra.
  assert (Hx_neg : - x < ln (eps / 2)) by lra.
  apply exp_increasing in Hx_neg.
  rewrite exp_ln in Hx_neg by lra.
  assert (Hgoal_form : Rabs (Rplus (Rplus 1 (Ropp (exp (Ropp x)))) (Ropp 1)) < eps).
  { replace (Rplus (Rplus 1 (Ropp (exp (Ropp x)))) (Ropp 1)) with (Ropp (exp (Ropp x))) by ring.
    rewrite Rabs_Ropp, Rabs_right by (apply Rle_ge, Rlt_le, exp_pos).
    lra. }
  exact Hgoal_form.
Qed.

Lemma backup_g_hazard_lb_proof :
  { lambda : R | lambda > 0 /\ forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= backup_g x }.
Proof.
  exists 1. split; [lra |].
  intros x Hx. unfold backup_g.
  replace (1 * x) with x by ring. lra.
Qed.

Definition threat_discovery_rate : R := 1.

Definition backup_A_sum (h : R) : R := threat_discovery_rate * h.

Lemma backup_A_sum_nonneg : forall h, 0 <= h -> 0 <= backup_A_sum h.
Proof.
  intros h Hh. unfold backup_A_sum, threat_discovery_rate. lra.
Qed.

Lemma backup_A_sum_nondecreasing : nondecreasing backup_A_sum.
Proof.
  unfold nondecreasing, backup_A_sum. intros x y Hxy.
  unfold threat_discovery_rate. lra.
Qed.

Lemma backup_A_sum_unbounded : forall M, exists h, 0 <= h /\ backup_A_sum h >= M.
Proof.
  intro M. destruct (Rle_dec 0 M) as [HM | HM].
  - exists M. split; [assumption |].
    unfold backup_A_sum, threat_discovery_rate. lra.
  - exists 0. split; [lra |].
    unfold backup_A_sum, threat_discovery_rate. lra.
Qed.

Lemma backup_A_sum_to_infty :
  filterlim backup_A_sum (Rbar_locally p_infty) (Rbar_locally p_infty).
Proof.
  unfold filterlim, filter_le, filtermap, backup_A_sum.
  intros P HP. destruct HP as [M HM].
  exists M. intros x Hx. apply HM.
  unfold threat_discovery_rate. lra.
Qed.

Definition data_value : R := 10000.

Lemma data_value_pos : data_value > 0.
Proof.
  unfold data_value. lra.
Qed.

Definition backup_cost (a : backup_interval_days) : R := 0.

Lemma backup_cost_nonneg : forall a, 0 <= backup_cost a.
Proof.
  intro a. unfold backup_cost. lra.
Qed.

Lemma backup_V_margin_proof :
  data_value - backup_cost (proj1_sig backup_A0_witness) > 0.
Proof.
  simpl. unfold data_value, backup_cost. lra.
Qed.

Definition Backup_EOX_Params : EOX_Params := {|
  A := backup_interval_days;
  A_inhabited := exist _ 0 I;
  T := backup_T;
  T_nonneg := backup_T_nonneg;
  A0 := backup_A0_witness;
  phi := backup_phi;
  phi_domain := backup_phi_domain;
  phi_increasing0 := backup_phi_increasing0;
  phi_zero := backup_phi_zero;
  phi_pos := backup_phi_pos;
  g := backup_g;
  g_bounds := backup_g_bounds;
  g_zero := backup_g_zero;
  g_pos := backup_g_pos;
  g_nondecreasing := backup_g_nondecreasing;
  g_tendsto_1 := backup_g_tendsto_1;
  g_hazard_lb := backup_g_hazard_lb_proof;
  A_sum := backup_A_sum;
  A_sum_nonneg := backup_A_sum_nonneg;
  A_sum_nondecreasing := backup_A_sum_nondecreasing;
  A_sum_unbounded := backup_A_sum_unbounded;
  A_sum_to_infty := backup_A_sum_to_infty;
  V := data_value;
  V_pos := data_value_pos;
  C := backup_cost;
  C_nonneg := backup_cost_nonneg;
  V_margin := backup_V_margin_proof
|}.

Theorem daily_backups_dominate_weekly : forall weekly_interval,
  weekly_interval >= 7 ->
  exists horizon_days, 0 <= horizon_days /\
    forall h, horizon_days <= h ->
      payoff Backup_EOX_Params h (proj1_sig (A0 Backup_EOX_Params)) >
      payoff Backup_EOX_Params h weekly_interval.
Proof.
  intros weekly_interval Hweekly.
  assert (HT_weekly : T Backup_EOX_Params weekly_interval > 0).
  { simpl. unfold backup_T, Rmax.
    destruct (Rle_dec 0 weekly_interval) as [H0 | H0].
    - assert (Hpos : weekly_interval > 0) by lra. assumption.
    - lra. }
  assert (HC : C Backup_EOX_Params (proj1_sig (A0 Backup_EOX_Params)) <=
               C Backup_EOX_Params weekly_interval).
  { simpl. unfold backup_cost. lra. }
  destruct (EOX_asymptotic_null_dominance_pointwise Backup_EOX_Params weekly_interval HC)
    as [[HT_zero HC_eq] | [H [HH_nonneg Hdom]]].
  - simpl in HT_zero. unfold backup_T, Rmax in HT_zero.
    destruct (Rle_dec 0 weekly_interval) as [H0 | H0]; lra.
  - exists H. split; [assumption |].
    intros h Hh. apply Hdom. assumption.
Qed.

Theorem daily_backups_dominate_monthly : forall monthly_interval,
  monthly_interval >= 30 ->
  exists horizon_days, 0 <= horizon_days /\
    forall h, horizon_days <= h ->
      payoff Backup_EOX_Params h (proj1_sig (A0 Backup_EOX_Params)) >
      payoff Backup_EOX_Params h monthly_interval.
Proof.
  intros monthly_interval Hmonthly.
  assert (HT_monthly : T Backup_EOX_Params monthly_interval > 0).
  { simpl. unfold backup_T, Rmax.
    destruct (Rle_dec 0 monthly_interval) as [H0 | H0].
    - assert (Hpos : monthly_interval > 0) by lra. assumption.
    - lra. }
  assert (HC : C Backup_EOX_Params (proj1_sig (A0 Backup_EOX_Params)) <=
               C Backup_EOX_Params monthly_interval).
  { simpl. unfold backup_cost. lra. }
  destruct (EOX_asymptotic_null_dominance_pointwise Backup_EOX_Params monthly_interval HC)
    as [[HT_zero HC_eq] | [H [HH_nonneg Hdom]]].
  - simpl in HT_zero. unfold backup_T, Rmax in HT_zero.
    destruct (Rle_dec 0 monthly_interval) as [H0 | H0]; lra.
  - exists H. split; [assumption | assumption].
Qed.

Theorem backup_data_loss_probability_grows : forall backup_interval h,
  backup_interval > 0 ->
  h > 0 ->
  elim_prob Backup_EOX_Params h backup_interval > 0.
Proof.
  intros backup_interval h Hinterval Hh.
  unfold elim_prob. simpl.
  unfold backup_g, backup_phi, backup_T, backup_A_sum, threat_discovery_rate.
  unfold Rmax. destruct (Rle_dec 0 backup_interval).
  - assert (Hproduct : backup_interval * (1 * h) > 0).
    { replace (1 * h) with h by ring. apply Rmult_lt_0_compat; assumption. }
    assert (Hexp_bound : exp (- (backup_interval * (1 * h))) < 1).
    { replace (- (backup_interval * (1 * h))) with (- (backup_interval * h)) by ring.
      assert (Hpos_product : backup_interval * h > 0).
      { replace (1 * h) with h in Hproduct by ring. assumption. }
      assert (Hneg : - (backup_interval * h) < 0) by lra.
      apply exp_increasing in Hneg. rewrite exp_0 in Hneg. assumption. }
    lra.
  - lra.
Qed.

End BackupExample.

(** ** 10. Concrete Example: Cybersecurity Patch Management *)

Section PatchingExample.

Definition patch_delay_hours : Type := R.

Definition patch_T (a : patch_delay_hours) : R := Rmax 0 a.

Lemma patch_T_nonneg : forall a, 0 <= patch_T a.
Proof.
  intro a. unfold patch_T. apply Rmax_l.
Qed.

Lemma patch_A0_witness : { a0 : patch_delay_hours | patch_T a0 = 0 }.
Proof.
  exists 0. unfold patch_T. rewrite Rmax_left; [reflexivity | lra].
Defined.

Definition patch_phi (exposure_hours : R) : R := exposure_hours.

Lemma patch_phi_domain : forall x, 0 <= x -> 0 <= patch_phi x.
Proof.
  intros x Hx. unfold patch_phi. assumption.
Qed.

Lemma patch_phi_increasing0 : forall x y, 0 <= x -> 0 <= y -> x <= y ->
  patch_phi x <= patch_phi y.
Proof.
  intros x y _ _ Hxy. unfold patch_phi. assumption.
Qed.

Lemma patch_phi_zero : patch_phi 0 = 0.
Proof.
  unfold patch_phi. reflexivity.
Qed.

Lemma patch_phi_pos : forall x, x > 0 -> patch_phi x > 0.
Proof.
  intros x Hx. unfold patch_phi. assumption.
Qed.

Definition patch_lambda : R := 0.01.

Lemma patch_lambda_pos : patch_lambda > 0.
Proof.
  unfold patch_lambda. lra.
Qed.

Definition patch_g (x : R) : R := 1 - exp (- (patch_lambda * x)).

Lemma patch_g_bounds : forall x, 0 <= x -> 0 <= patch_g x <= 1.
Proof.
  intros x Hx. unfold patch_g.
  split.
  - assert (H : exp (- (patch_lambda * x)) <= 1).
    { destruct (Req_dec x 0) as [Heq | Hneq].
      - subst. replace (patch_lambda * 0) with 0 by ring.
        rewrite Ropp_0, exp_0. lra.
      - assert (Hx_pos : x > 0) by lra.
        assert (Hprod_pos : patch_lambda * x > 0).
        { apply Rmult_lt_0_compat; [apply patch_lambda_pos | assumption]. }
        assert (H_neg : - (patch_lambda * x) < 0) by lra.
        apply Rlt_le. apply exp_increasing in H_neg.
        rewrite exp_0 in H_neg. assumption. }
    lra.
  - assert (H : 0 < exp (- (patch_lambda * x))) by apply exp_pos. lra.
Qed.

Lemma patch_g_zero : patch_g 0 = 0.
Proof.
  unfold patch_g. replace (patch_lambda * 0) with 0 by ring.
  rewrite Ropp_0, exp_0. ring.
Qed.

Lemma patch_g_pos : forall x, x > 0 -> patch_g x > 0.
Proof.
  intros x Hx. unfold patch_g.
  assert (Hprod : patch_lambda * x > 0).
  { apply Rmult_lt_0_compat; [apply patch_lambda_pos | assumption]. }
  assert (H_neg : - (patch_lambda * x) < 0) by lra.
  assert (H_exp : exp (- (patch_lambda * x)) < exp 0).
  { apply exp_increasing. assumption. }
  rewrite exp_0 in H_exp. lra.
Qed.

Lemma patch_g_nondecreasing : nondecreasing patch_g.
Proof.
  unfold nondecreasing, patch_g. intros x y Hxy.
  destruct (Req_dec x y) as [Heq | Hneq].
  - subst. lra.
  - assert (Hlt : x < y) by lra.
    assert (Hprod : patch_lambda * x < patch_lambda * y).
    { apply Rmult_lt_compat_l; [apply patch_lambda_pos | assumption]. }
    assert (H : - (patch_lambda * y) < - (patch_lambda * x)) by lra.
    apply exp_increasing in H. lra.
Qed.

Lemma patch_g_tendsto_1 :
  filterlim patch_g (Rbar_locally p_infty) (locally 1).
Proof.
  intros P [eps HP].
  exists (- ln (eps / 2) / patch_lambda).
  intros x Hx. apply HP.
  unfold ball, AbsRing_ball, patch_g.
  unfold abs; simpl; unfold minus, plus, opp; simpl.
  assert (Heps_pos : 0 < eps) by apply (cond_pos eps).
  assert (Heps_half_pos : 0 < eps / 2) by lra.
  assert (Hx_bound : - ln (eps / 2) / patch_lambda < x) by exact Hx.
  assert (Hprod : - ln (eps / 2) < patch_lambda * x).
  { apply Rmult_lt_reg_r with (r := / patch_lambda).
    - apply Rinv_0_lt_compat. apply patch_lambda_pos.
    - unfold Rdiv in Hx_bound.
      replace (- ln (eps / 2) * / patch_lambda) with (- ln (eps / 2) / patch_lambda).
      + replace (patch_lambda * x * / patch_lambda) with x.
        * assumption.
        * field. apply Rgt_not_eq. apply patch_lambda_pos.
      + unfold Rdiv. reflexivity. }
  assert (Hx_neg : - (patch_lambda * x) < ln (eps / 2)) by lra.
  apply exp_increasing in Hx_neg.
  rewrite exp_ln in Hx_neg by lra.
  assert (Hgoal_form : Rabs (Rplus (Rplus 1 (Ropp (exp (Ropp (patch_lambda * x))))) (Ropp 1)) < eps).
  { replace (Rplus (Rplus 1 (Ropp (exp (Ropp (patch_lambda * x))))) (Ropp 1)) with
            (Ropp (exp (Ropp (patch_lambda * x)))) by ring.
    rewrite Rabs_Ropp, Rabs_right by (apply Rle_ge, Rlt_le, exp_pos).
    lra. }
  exact Hgoal_form.
Qed.

Lemma patch_g_hazard_lb_proof :
  { lambda : R | lambda > 0 /\ forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= patch_g x }.
Proof.
  exists patch_lambda. split; [apply patch_lambda_pos |].
  intros x Hx. unfold patch_g. lra.
Qed.

Definition cve_discovery_rate : R := 2.

Lemma cve_rate_pos : cve_discovery_rate > 0.
Proof.
  unfold cve_discovery_rate. lra.
Qed.

Definition patch_A_sum (h : R) : R := cve_discovery_rate * h.

Lemma patch_A_sum_nonneg : forall h, 0 <= h -> 0 <= patch_A_sum h.
Proof.
  intros h Hh. unfold patch_A_sum.
  apply Rmult_le_pos; [apply Rlt_le; apply cve_rate_pos | assumption].
Qed.

Lemma patch_A_sum_nondecreasing : nondecreasing patch_A_sum.
Proof.
  unfold nondecreasing, patch_A_sum. intros x y Hxy.
  apply Rmult_le_compat_l; [apply Rlt_le; apply cve_rate_pos | assumption].
Qed.

Lemma patch_A_sum_unbounded : forall M, exists h, 0 <= h /\ patch_A_sum h >= M.
Proof.
  intro M. destruct (Rle_dec 0 M) as [HM | HM].
  - exists (M / cve_discovery_rate). split.
    + unfold Rdiv. apply Rmult_le_pos.
      * assumption.
      * apply Rlt_le. apply Rinv_0_lt_compat. apply cve_rate_pos.
    + unfold patch_A_sum, Rdiv.
      replace (cve_discovery_rate * (M * / cve_discovery_rate)) with M.
      * lra.
      * field. apply Rgt_not_eq. apply cve_rate_pos.
  - exists 0. split; [lra |].
    unfold patch_A_sum. replace (cve_discovery_rate * 0) with 0 by ring. lra.
Qed.

Lemma patch_A_sum_to_infty :
  filterlim patch_A_sum (Rbar_locally p_infty) (Rbar_locally p_infty).
Proof.
  unfold filterlim, filter_le, filtermap, patch_A_sum.
  intros P HP. destruct HP as [M HM].
  exists (M / cve_discovery_rate). intros x Hx.
  apply HM. unfold Rdiv in *.
  apply Rmult_lt_compat_l with (r := cve_discovery_rate) in Hx.
  - replace (cve_discovery_rate * (M * / cve_discovery_rate)) with M in Hx.
    + replace (cve_discovery_rate * x) with (x * cve_discovery_rate) by ring.
      lra.
    + field. apply Rgt_not_eq. apply cve_rate_pos.
  - apply cve_rate_pos.
Qed.

Definition business_value : R := 1000000.

Lemma business_value_pos : business_value > 0.
Proof.
  unfold business_value. lra.
Qed.

Definition patch_operational_cost (delay_hours : patch_delay_hours) : R :=
  Rmax 0 (delay_hours * 10).

Lemma patch_cost_nonneg : forall a, 0 <= patch_operational_cost a.
Proof.
  intro a. unfold patch_operational_cost. apply Rmax_l.
Qed.

Lemma patch_V_margin_proof :
  business_value - patch_operational_cost (proj1_sig patch_A0_witness) > 0.
Proof.
  simpl. unfold business_value, patch_operational_cost.
  unfold patch_A0_witness. simpl.
  replace (0 * 10) with 0 by ring.
  unfold Rmax. destruct (Rle_dec 0 0) as [H0 | H0]; unfold business_value; lra.
Qed.

Definition Patching_EOX_Params : EOX_Params := {|
  A := patch_delay_hours;
  A_inhabited := exist _ 0 I;
  T := patch_T;
  T_nonneg := patch_T_nonneg;
  A0 := patch_A0_witness;
  phi := patch_phi;
  phi_domain := patch_phi_domain;
  phi_increasing0 := patch_phi_increasing0;
  phi_zero := patch_phi_zero;
  phi_pos := patch_phi_pos;
  g := patch_g;
  g_bounds := patch_g_bounds;
  g_zero := patch_g_zero;
  g_pos := patch_g_pos;
  g_nondecreasing := patch_g_nondecreasing;
  g_tendsto_1 := patch_g_tendsto_1;
  g_hazard_lb := patch_g_hazard_lb_proof;
  A_sum := patch_A_sum;
  A_sum_nonneg := patch_A_sum_nonneg;
  A_sum_nondecreasing := patch_A_sum_nondecreasing;
  A_sum_unbounded := patch_A_sum_unbounded;
  A_sum_to_infty := patch_A_sum_to_infty;
  V := business_value;
  V_pos := business_value_pos;
  C := patch_operational_cost;
  C_nonneg := patch_cost_nonneg;
  V_margin := patch_V_margin_proof
|}.

Theorem immediate_patching_dominates_24h_delay : forall delay_hours,
  delay_hours >= 24 ->
  exists horizon_hours, 0 <= horizon_hours /\
    forall h, horizon_hours <= h ->
      payoff Patching_EOX_Params h (proj1_sig (A0 Patching_EOX_Params)) >
      payoff Patching_EOX_Params h delay_hours.
Proof.
  intros delay_hours Hdelay.
  assert (HT_delay : T Patching_EOX_Params delay_hours > 0).
  { simpl. unfold patch_T, Rmax.
    destruct (Rle_dec 0 delay_hours) as [H0 | H0].
    - assert (Hpos : delay_hours > 0) by lra. assumption.
    - lra. }
  assert (HC : C Patching_EOX_Params (proj1_sig (A0 Patching_EOX_Params)) <=
               C Patching_EOX_Params delay_hours).
  { simpl. unfold patch_operational_cost.
    replace (0 * 10) with 0 by ring.
    rewrite Rmax_left by lra.
    apply Rmax_l. }
  destruct (EOX_asymptotic_null_dominance_pointwise Patching_EOX_Params delay_hours HC)
    as [[HT_zero HC_eq] | [H [HH_nonneg Hdom]]].
  - simpl in HT_zero. unfold patch_T, Rmax in HT_zero.
    destruct (Rle_dec 0 delay_hours) as [H0 | H0]; lra.
  - exists H. split; [assumption |].
    intros h Hh. apply Hdom. assumption.
Qed.

Theorem immediate_patching_dominates_weekly_delay : forall delay_hours,
  delay_hours >= 168 ->
  exists horizon_hours, 0 <= horizon_hours /\
    forall h, horizon_hours <= h ->
      payoff Patching_EOX_Params h (proj1_sig (A0 Patching_EOX_Params)) >
      payoff Patching_EOX_Params h delay_hours.
Proof.
  intros delay_hours Hdelay.
  assert (HT_delay : T Patching_EOX_Params delay_hours > 0).
  { simpl. unfold patch_T, Rmax.
    destruct (Rle_dec 0 delay_hours) as [H0 | H0].
    - assert (Hpos : delay_hours > 0) by lra. assumption.
    - lra. }
  assert (HC : C Patching_EOX_Params (proj1_sig (A0 Patching_EOX_Params)) <=
               C Patching_EOX_Params delay_hours).
  { simpl. unfold patch_operational_cost.
    replace (0 * 10) with 0 by ring.
    rewrite Rmax_left by lra.
    apply Rmax_l. }
  destruct (EOX_asymptotic_null_dominance_pointwise Patching_EOX_Params delay_hours HC)
    as [[HT_zero HC_eq] | [H [HH_nonneg Hdom]]].
  - simpl in HT_zero. unfold patch_T, Rmax in HT_zero.
    destruct (Rle_dec 0 delay_hours) as [H0 | H0]; lra.
  - exists H. split; [assumption | assumption].
Qed.

Theorem breach_probability_increases_with_delay : forall delay1 delay2 h,
  h > 0 ->
  0 <= delay1 < delay2 ->
  elim_prob Patching_EOX_Params h delay1 < elim_prob Patching_EOX_Params h delay2.
Proof.
  intros delay1 delay2 h Hh [Hd1_nonneg Hd_order].
  unfold elim_prob. simpl.
  unfold patch_g, patch_phi, patch_T, patch_A_sum.
  unfold Rmax.
  destruct (Rle_dec 0 delay1) as [Hr1 | Hr1];
  destruct (Rle_dec 0 delay2) as [Hr2 | Hr2].
  - assert (Hprod1 : patch_lambda * (delay1 * (cve_discovery_rate * h)) =
                     patch_lambda * delay1 * cve_discovery_rate * h) by ring.
    assert (Hprod2 : patch_lambda * (delay2 * (cve_discovery_rate * h)) =
                     patch_lambda * delay2 * cve_discovery_rate * h) by ring.
    rewrite Hprod1, Hprod2.
    assert (Hmono : patch_lambda * delay1 * cve_discovery_rate * h <
                    patch_lambda * delay2 * cve_discovery_rate * h).
    { apply Rmult_lt_compat_r; [exact Hh |].
      apply Rmult_lt_compat_r; [apply cve_rate_pos |].
      apply Rmult_lt_compat_l; [apply patch_lambda_pos | assumption]. }
    assert (Hneg_mono : - (patch_lambda * delay2 * cve_discovery_rate * h) <
                        - (patch_lambda * delay1 * cve_discovery_rate * h)) by lra.
    apply exp_increasing in Hneg_mono.
    lra.
  - lra.
  - lra.
  - lra.
Qed.

Theorem cve_accumulation_makes_patching_urgent : forall delay_hours,
  delay_hours > 0 ->
  forall epsilon, 0 < epsilon < 1 ->
  exists horizon_hours, 0 <= horizon_hours /\
    forall h, horizon_hours <= h ->
      elim_prob Patching_EOX_Params h delay_hours > 1 - epsilon.
Proof.
  intros delay_hours Hdelay epsilon [Heps_pos Heps_bound].
  assert (HT_delay : T Patching_EOX_Params delay_hours > 0).
  { simpl. unfold patch_T, Rmax.
    destruct (Rle_dec 0 delay_hours) as [H0 | H0]; lra. }
  destruct (@EOX_elim_prob_tends_to_1_explicit Patching_EOX_Params delay_hours epsilon HT_delay Heps_pos)
    as [H [HH_nonneg Hforall]].
  exists H. split; [assumption |].
  intros h Hh.
  specialize (Hforall h Hh).
  destruct Hforall as [Hlower Hupper].
  assumption.
Qed.

End PatchingExample.

(** ** 11. Concrete Example: Dark Forest (Interstellar Stealth) *)

Section DarkForest.

Definition detectability_level : Type := R.

Definition dark_forest_T (a : detectability_level) : R := Rmax 0 a.

Lemma dark_forest_T_nonneg : forall a, 0 <= dark_forest_T a.
Proof.
  intro a. unfold dark_forest_T. apply Rmax_l.
Qed.

Lemma dark_forest_A0_witness : { a0 : detectability_level | dark_forest_T a0 = 0 }.
Proof.
  exists 0. unfold dark_forest_T. rewrite Rmax_left; [reflexivity | lra].
Defined.

Definition dark_forest_phi (exposure_signature : R) : R := exposure_signature.

Lemma dark_forest_phi_domain : forall x, 0 <= x -> 0 <= dark_forest_phi x.
Proof.
  intros x Hx. unfold dark_forest_phi. assumption.
Qed.

Lemma dark_forest_phi_increasing0 : forall x y, 0 <= x -> 0 <= y -> x <= y ->
  dark_forest_phi x <= dark_forest_phi y.
Proof.
  intros x y _ _ Hxy. unfold dark_forest_phi. assumption.
Qed.

Lemma dark_forest_phi_zero : dark_forest_phi 0 = 0.
Proof.
  unfold dark_forest_phi. reflexivity.
Qed.

Lemma dark_forest_phi_pos : forall x, x > 0 -> dark_forest_phi x > 0.
Proof.
  intros x Hx. unfold dark_forest_phi. assumption.
Qed.

Definition hostile_observer_density : R := 0.001.

Lemma hostile_observer_density_pos : hostile_observer_density > 0.
Proof.
  unfold hostile_observer_density. lra.
Qed.

Definition dark_forest_g (x : R) : R := 1 - exp (- (hostile_observer_density * x)).

Lemma dark_forest_g_bounds : forall x, 0 <= x -> 0 <= dark_forest_g x <= 1.
Proof.
  intros x Hx. unfold dark_forest_g.
  split.
  - assert (H : exp (- (hostile_observer_density * x)) <= 1).
    { destruct (Req_dec x 0) as [Heq | Hneq].
      - subst. replace (hostile_observer_density * 0) with 0 by ring.
        rewrite Ropp_0, exp_0. lra.
      - assert (Hx_pos : x > 0) by lra.
        assert (Hprod_pos : hostile_observer_density * x > 0).
        { apply Rmult_lt_0_compat; [apply hostile_observer_density_pos | assumption]. }
        assert (H_neg : - (hostile_observer_density * x) < 0) by lra.
        apply Rlt_le. apply exp_increasing in H_neg.
        rewrite exp_0 in H_neg. assumption. }
    lra.
  - assert (H : 0 < exp (- (hostile_observer_density * x))) by apply exp_pos. lra.
Qed.

Lemma dark_forest_g_zero : dark_forest_g 0 = 0.
Proof.
  unfold dark_forest_g. replace (hostile_observer_density * 0) with 0 by ring.
  rewrite Ropp_0, exp_0. ring.
Qed.

Lemma dark_forest_g_pos : forall x, x > 0 -> dark_forest_g x > 0.
Proof.
  intros x Hx. unfold dark_forest_g.
  assert (Hprod : hostile_observer_density * x > 0).
  { apply Rmult_lt_0_compat; [apply hostile_observer_density_pos | assumption]. }
  assert (H_neg : - (hostile_observer_density * x) < 0) by lra.
  assert (H_exp : exp (- (hostile_observer_density * x)) < exp 0).
  { apply exp_increasing. assumption. }
  rewrite exp_0 in H_exp. lra.
Qed.

Lemma dark_forest_g_nondecreasing : nondecreasing dark_forest_g.
Proof.
  unfold nondecreasing, dark_forest_g. intros x y Hxy.
  destruct (Req_dec x y) as [Heq | Hneq].
  - subst. lra.
  - assert (Hlt : x < y) by lra.
    assert (Hprod : hostile_observer_density * x < hostile_observer_density * y).
    { apply Rmult_lt_compat_l; [apply hostile_observer_density_pos | assumption]. }
    assert (H : - (hostile_observer_density * y) < - (hostile_observer_density * x)) by lra.
    apply exp_increasing in H. lra.
Qed.

Lemma dark_forest_g_tendsto_1 :
  filterlim dark_forest_g (Rbar_locally p_infty) (locally 1).
Proof.
  intros P [eps HP].
  exists (- ln (eps / 2) / hostile_observer_density).
  intros x Hx. apply HP.
  unfold ball, AbsRing_ball, dark_forest_g.
  unfold abs; simpl; unfold minus, plus, opp; simpl.
  assert (Heps_pos : 0 < eps) by apply (cond_pos eps).
  assert (Heps_half_pos : 0 < eps / 2) by lra.
  assert (Hx_bound : - ln (eps / 2) / hostile_observer_density < x) by exact Hx.
  assert (Hprod : - ln (eps / 2) < hostile_observer_density * x).
  { apply Rmult_lt_reg_r with (r := / hostile_observer_density).
    - apply Rinv_0_lt_compat. apply hostile_observer_density_pos.
    - unfold Rdiv in Hx_bound.
      replace (- ln (eps / 2) * / hostile_observer_density) with (- ln (eps / 2) / hostile_observer_density).
      + replace (hostile_observer_density * x * / hostile_observer_density) with x.
        * assumption.
        * field. apply Rgt_not_eq. apply hostile_observer_density_pos.
      + unfold Rdiv. reflexivity. }
  assert (Hx_neg : - (hostile_observer_density * x) < ln (eps / 2)) by lra.
  apply exp_increasing in Hx_neg.
  rewrite exp_ln in Hx_neg by lra.
  assert (Hgoal_form : Rabs (Rplus (Rplus 1 (Ropp (exp (Ropp (hostile_observer_density * x))))) (Ropp 1)) < eps).
  { replace (Rplus (Rplus 1 (Ropp (exp (Ropp (hostile_observer_density * x))))) (Ropp 1)) with
            (Ropp (exp (Ropp (hostile_observer_density * x)))) by ring.
    rewrite Rabs_Ropp, Rabs_right by (apply Rle_ge, Rlt_le, exp_pos).
    lra. }
  exact Hgoal_form.
Qed.

Lemma dark_forest_g_hazard_lb_proof :
  { lambda : R | lambda > 0 /\ forall x, 0 <= x -> 1 - exp (- (lambda * x)) <= dark_forest_g x }.
Proof.
  exists hostile_observer_density. split; [apply hostile_observer_density_pos |].
  intros x Hx. unfold dark_forest_g. lra.
Qed.

Definition speed_of_light : R := 1.

Definition light_cone_volume (cosmic_time : R) : R := cosmic_time * cosmic_time * cosmic_time.

Lemma light_cone_volume_nonneg : forall h, 0 <= h -> 0 <= light_cone_volume h.
Proof.
  intros h Hh. unfold light_cone_volume.
  assert (H0 : 0 <= h * h).
  { apply Rmult_le_pos; assumption. }
  apply Rmult_le_pos; assumption.
Qed.

Lemma light_cone_volume_nondecreasing : nondecreasing light_cone_volume.
Proof.
  unfold nondecreasing, light_cone_volume. intros x y Hxy.
  destruct (Req_dec x y) as [Heq | Hneq].
  - subst. lra.
  - assert (Hlt : x < y) by lra.
    destruct (Rle_dec 0 x) as [Hx_nonneg | Hx_neg].
    + assert (Hy_nonneg : 0 <= y) by lra.
      assert (Hx2 : x * x <= y * y).
      { apply Rmult_le_compat; lra. }
      assert (Hy2_pos : 0 <= y * y).
      { apply Rmult_le_pos; assumption. }
      assert (Hx2_pos : 0 <= x * x).
      { apply Rmult_le_pos; assumption. }
      assert (Hx3 : x * x * x <= y * y * y).
      { apply Rmult_le_compat; lra. }
      assumption.
    + destruct (Rle_dec 0 y) as [Hy_nonneg | Hy_neg].
      * replace (x * x * x) with (- ((- x) * (- x) * (- x))) by ring.
        assert (Hmx_pos : 0 < - x) by lra.
        assert (H0 : 0 <= (- x) * (- x) * (- x)).
        { assert (H1 : 0 <= (- x) * (- x)).
          { apply Rmult_le_pos; lra. }
          apply Rmult_le_pos; lra. }
        assert (H_y3 : 0 <= y * y * y).
        { assert (H1 : 0 <= y * y).
          { apply Rmult_le_pos; lra. }
          apply Rmult_le_pos; lra. }
        lra.
      * assert (Hmy_pos : 0 < - y) by lra.
        assert (Hmx_pos : 0 < - x) by lra.
        assert (H_order : - y < - x) by lra.
        assert (Hmy2 : (- y) * (- y) < (- x) * (- x)).
        { nra. }
        assert (Hmy3 : (- y) * (- y) * (- y) < (- x) * (- x) * (- x)).
        { nra. }
        replace (x * x * x) with (- ((- x) * (- x) * (- x))) by ring.
        replace (y * y * y) with (- ((- y) * (- y) * (- y))) by ring.
        lra.
Qed.

Lemma light_cone_volume_unbounded : forall M, exists h, 0 <= h /\ light_cone_volume h >= M.
Proof.
  intro M.
  destruct (Rle_dec 0 M) as [HM | HM].
  - destruct (Rle_dec M 1) as [HM1 | HM1].
    + exists 1. split; [lra |].
      unfold light_cone_volume. replace (1 * 1 * 1) with 1 by ring. lra.
    + assert (HM_pos : M > 0) by lra.
      exists (M + 1). split.
      * lra.
      * unfold light_cone_volume.
        assert (HM1_bound : M + 1 > 1) by lra.
        assert (Hpow2 : (M + 1) * (M + 1) > M + 1).
        { nra. }
        assert (Hpow3 : (M + 1) * (M + 1) * (M + 1) > M).
        { apply Rlt_le_trans with (r2 := (M + 1) * (M + 1)).
          - lra.
          - apply Rmult_le_compat_r; lra. }
        lra.
  - exists 0. split; [lra |].
    unfold light_cone_volume. replace (0 * 0 * 0) with 0 by ring. lra.
Qed.

Lemma light_cone_volume_to_infty :
  filterlim light_cone_volume (Rbar_locally p_infty) (Rbar_locally p_infty).
Proof.
  unfold filterlim, filter_le, filtermap, light_cone_volume.
  intros P HP. destruct HP as [M HM].
  exists (Rmax (M + 1) 1). intros x Hx.
  apply HM.
  assert (Hx_ge_1 : x >= 1).
  { apply Rle_ge. apply Rle_trans with (r2 := Rmax (M + 1) 1).
    - apply Rmax_r.
    - apply Rlt_le. assumption. }
  assert (Hx_ge_M1 : x >= M + 1).
  { apply Rle_ge. apply Rle_trans with (r2 := Rmax (M + 1) 1).
    - apply Rmax_l.
    - apply Rlt_le. assumption. }
  assert (Hx2 : x * x >= x).
  { apply Rge_le in Hx_ge_1. apply Rle_ge.
    replace (x * x) with (x * 1 + x * (x - 1)) by ring.
    assert (Hxm1 : x - 1 >= 0) by lra.
    assert (Hprod : x * (x - 1) >= 0).
    { apply Rge_le in Hxm1. apply Rle_ge. apply Rmult_le_pos; lra. }
    lra. }
  assert (Hx3 : x * x * x >= M + 1).
  { apply Rge_trans with (r2 := x * x).
    - apply Rle_ge. apply Rmult_le_compat_r; [| apply Rge_le; exact Hx2].
      apply Rge_le in Hx_ge_1. lra.
    - apply Rge_trans with (r2 := x); [exact Hx2 | exact Hx_ge_M1]. }
  lra.
Qed.

Definition civilization_value : R := 1000000000000.

Lemma civilization_value_pos : civilization_value > 0.
Proof.
  unfold civilization_value. lra.
Qed.

Definition stealth_cost (detectability : detectability_level) : R :=
  Rmax 0 (detectability * 100).

Lemma stealth_cost_nonneg : forall a, 0 <= stealth_cost a.
Proof.
  intro a. unfold stealth_cost. apply Rmax_l.
Qed.

Lemma dark_forest_V_margin_proof :
  civilization_value - stealth_cost (proj1_sig dark_forest_A0_witness) > 0.
Proof.
  simpl. unfold civilization_value, stealth_cost.
  unfold dark_forest_A0_witness. simpl.
  replace (0 * 100) with 0 by ring.
  unfold Rmax. destruct (Rle_dec 0 0) as [H0 | H0]; unfold civilization_value; lra.
Qed.

Definition DarkForest_EOX_Params : EOX_Params := {|
  A := detectability_level;
  A_inhabited := exist _ 0 I;
  T := dark_forest_T;
  T_nonneg := dark_forest_T_nonneg;
  A0 := dark_forest_A0_witness;
  phi := dark_forest_phi;
  phi_domain := dark_forest_phi_domain;
  phi_increasing0 := dark_forest_phi_increasing0;
  phi_zero := dark_forest_phi_zero;
  phi_pos := dark_forest_phi_pos;
  g := dark_forest_g;
  g_bounds := dark_forest_g_bounds;
  g_zero := dark_forest_g_zero;
  g_pos := dark_forest_g_pos;
  g_nondecreasing := dark_forest_g_nondecreasing;
  g_tendsto_1 := dark_forest_g_tendsto_1;
  g_hazard_lb := dark_forest_g_hazard_lb_proof;
  A_sum := light_cone_volume;
  A_sum_nonneg := light_cone_volume_nonneg;
  A_sum_nondecreasing := light_cone_volume_nondecreasing;
  A_sum_unbounded := light_cone_volume_unbounded;
  A_sum_to_infty := light_cone_volume_to_infty;
  V := civilization_value;
  V_pos := civilization_value_pos;
  C := stealth_cost;
  C_nonneg := stealth_cost_nonneg;
  V_margin := dark_forest_V_margin_proof
|}.

Theorem perfect_stealth_dominates_any_detectability : forall detectability,
  detectability > 0 ->
  exists cosmic_time_horizon, 0 <= cosmic_time_horizon /\
    forall t, cosmic_time_horizon <= t ->
      payoff DarkForest_EOX_Params t (proj1_sig (A0 DarkForest_EOX_Params)) >
      payoff DarkForest_EOX_Params t detectability.
Proof.
  intros detectability Hdetect.
  assert (HT_detect : T DarkForest_EOX_Params detectability > 0).
  { simpl. unfold dark_forest_T, Rmax.
    destruct (Rle_dec 0 detectability) as [H0 | H0].
    - assumption.
    - lra. }
  assert (HC : C DarkForest_EOX_Params (proj1_sig (A0 DarkForest_EOX_Params)) <=
               C DarkForest_EOX_Params detectability).
  { simpl. unfold stealth_cost.
    replace (0 * 100) with 0 by ring.
    unfold Rmax. destruct (Rle_dec 0 0) as [H0_l | H0_r].
    - destruct (Rle_dec 0 (detectability * 100)) as [Hdet_l | Hdet_r].
      + assert (Hdet_nonneg : 0 <= detectability) by lra.
        assert (H_prod : 0 <= detectability * 100).
        { apply Rmult_le_pos; lra. }
        lra.
      + lra.
    - lra. }
  destruct (EOX_asymptotic_null_dominance_pointwise DarkForest_EOX_Params detectability HC)
    as [[HT_zero HC_eq] | [H [HH_nonneg Hdom]]].
  - simpl in HT_zero. unfold dark_forest_T, Rmax in HT_zero.
    destruct (Rle_dec 0 detectability) as [H0 | H0]; lra.
  - exists H. split; [assumption |].
    intros t Ht. apply Hdom. assumption.
Qed.

Theorem detection_probability_cubic_growth : forall detectability t1 t2,
  detectability > 0 ->
  0 <= t1 < t2 ->
  elim_prob DarkForest_EOX_Params t1 detectability <
  elim_prob DarkForest_EOX_Params t2 detectability.
Proof.
  intros detectability t1 t2 Hdetect [Ht1_nonneg Ht_order].
  unfold elim_prob. simpl.
  unfold dark_forest_g, dark_forest_phi, dark_forest_T, light_cone_volume.
  unfold Rmax.
  destruct (Rle_dec 0 detectability) as [Hr | Hr].
  - assert (Hvol1 : t1 * t1 * t1 < t2 * t2 * t2).
    { destruct (Req_dec t1 0) as [Ht1_eq | Ht1_neq].
      - subst. replace (0 * 0 * 0) with 0 by ring.
        assert (Ht2_pos : t2 > 0) by lra.
        assert (Ht2_sq : t2 * t2 > 0).
        { apply Rmult_lt_0_compat; assumption. }
        apply Rmult_lt_0_compat; assumption.
      - assert (Ht1_pos : t1 > 0) by lra.
        assert (Ht2_pos : t2 > 0) by lra.
        assert (Ht1_sq : t1 * t1 < t2 * t2).
        { nra. }
        nra. }
    assert (Hprod1 : hostile_observer_density * (detectability * (t1 * t1 * t1)) <
                     hostile_observer_density * (detectability * (t2 * t2 * t2))).
    { apply Rmult_lt_compat_l; [apply hostile_observer_density_pos |].
      apply Rmult_lt_compat_l; lra. }
    assert (Hneg : - (hostile_observer_density * (detectability * (t2 * t2 * t2))) <
                   - (hostile_observer_density * (detectability * (t1 * t1 * t1)))).
    { lra. }
    apply exp_increasing in Hneg. lra.
  - lra.
Qed.

Theorem light_cone_expansion_ensures_eventual_detection : forall detectability epsilon,
  detectability > 0 ->
  0 < epsilon < 1 ->
  exists cosmic_time, 0 <= cosmic_time /\
    forall t, cosmic_time <= t ->
      elim_prob DarkForest_EOX_Params t detectability > 1 - epsilon.
Proof.
  intros detectability epsilon Hdetect [Heps_pos Heps_bound].
  assert (HT_detect : T DarkForest_EOX_Params detectability > 0).
  { simpl. unfold dark_forest_T, Rmax.
    destruct (Rle_dec 0 detectability) as [H0 | H0]; lra. }
  destruct (@EOX_elim_prob_tends_to_1_explicit DarkForest_EOX_Params detectability epsilon HT_detect Heps_pos)
    as [H [HH_nonneg Hforall]].
  exists H. split; [assumption |].
  intros t Ht.
  specialize (Hforall t Ht).
  destruct Hforall as [Hlower Hupper].
  assumption.
Qed.

Theorem dark_forest_axiom_formalized :
  forall detectability,
    detectability > 0 ->
    is_lim (fun t => 1 - elim_prob DarkForest_EOX_Params t detectability) p_infty 0.
Proof.
  intros detectability Hdetect.
  assert (HT_detect : T DarkForest_EOX_Params detectability > 0).
  { simpl. unfold dark_forest_T, Rmax.
    destruct (Rle_dec 0 detectability) as [H0 | H0]; lra. }
  assert (Hphi_pos : phi DarkForest_EOX_Params (T DarkForest_EOX_Params detectability) > 0).
  { simpl. unfold dark_forest_phi, dark_forest_T, Rmax.
    destruct (Rle_dec 0 detectability) as [H0 | H0]; lra. }
  apply EOX_survival_prob_to_zero with (gamma := phi DarkForest_EOX_Params (T DarkForest_EOX_Params detectability)).
  - exact Hphi_pos.
  - apply Rle_ge. lra.
Qed.

End DarkForest.

(** ** 12. Finite Horizon Optimality *)

Section FiniteHorizon.

Context (P : EOX_Params).

Definition expected_loss (h : R) (a : A P) : R :=
  elim_prob P h a * V P + C P a.

Lemma expected_loss_nonneg : forall h a,
  0 <= h -> 0 <= expected_loss h a.
Proof.
  intros h a Hh.
  unfold expected_loss.
  assert (Hbounds : 0 <= elim_prob P h a <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (HV : V P > 0) by apply V_pos.
  assert (HC : 0 <= C P a) by apply C_nonneg.
  assert (Hprod : 0 <= elim_prob P h a * V P).
  { apply Rmult_le_pos; lra. }
  lra.
Qed.

Theorem finite_horizon_optimality : forall h a1 a2,
  0 <= h ->
  payoff P h a1 > payoff P h a2 <->
  expected_loss h a1 < expected_loss h a2.
Proof.
  intros h a1 a2 Hh.
  unfold payoff, expected_loss.
  assert (HV : V P > 0) by apply V_pos.
  split; intro H.
  - assert (Hexp : (1 - elim_prob P h a1) * V P - C P a1 >
                   (1 - elim_prob P h a2) * V P - C P a2) by exact H.
    assert (Hrw : elim_prob P h a1 * V P + C P a1 <
                  elim_prob P h a2 * V P + C P a2).
    { assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
      { apply EOX_elim_prob_bounds. assumption. }
      assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
      { apply EOX_elim_prob_bounds. assumption. }
      nra. }
    exact Hrw.
  - assert (Hexp : elim_prob P h a1 * V P + C P a1 <
                   elim_prob P h a2 * V P + C P a2) by exact H.
    assert (Hrw : (1 - elim_prob P h a1) * V P - C P a1 >
                  (1 - elim_prob P h a2) * V P - C P a2).
    { assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
      { apply EOX_elim_prob_bounds. assumption. }
      assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
      { apply EOX_elim_prob_bounds. assumption. }
      nra. }
    exact Hrw.
Qed.

Theorem finite_horizon_dominance_condition : forall h a1 a2,
  0 <= h ->
  C P a1 - C P a2 < (elim_prob P h a2 - elim_prob P h a1) * V P ->
  payoff P h a1 > payoff P h a2.
Proof.
  intros h a1 a2 Hh Hcond.
  unfold payoff.
  assert (HV : V P > 0) by apply V_pos.
  assert (Hbounds1 : 0 <= elim_prob P h a1 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (Hbounds2 : 0 <= elim_prob P h a2 <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  nra.
Qed.

Theorem finite_horizon_null_exposure_optimal_when : forall h a,
  0 <= h ->
  C P (proj1_sig (A0 P)) <= C P a ->
  payoff P h (proj1_sig (A0 P)) >= payoff P h a.
Proof.
  intros h a Hh HC.
  unfold payoff.
  rewrite EOX_elim_prob_null_exposure by assumption.
  assert (Hbounds : 0 <= elim_prob P h a <= 1).
  { apply EOX_elim_prob_bounds. assumption. }
  assert (HV : V P > 0) by apply V_pos.
  replace (1 - 0) with 1 by ring.
  assert (H1 : 1 * V P = V P) by ring.
  rewrite H1.
  assert (Hsurv : (1 - elim_prob P h a) * V P <= V P).
  { nra. }
  lra.
Qed.

Definition epsilon_optimal (h : R) (a a_star : A P) (eps : R) : Prop :=
  payoff P h a >= payoff P h a_star - eps.

Lemma epsilon_optimal_reflexive : forall h a eps,
  0 <= h ->
  eps > 0 ->
  epsilon_optimal h a a eps.
Proof.
  intros h a eps Hh Heps.
  unfold epsilon_optimal.
  lra.
Qed.

Theorem epsilon_optimality_from_dominance : forall h a1 a2 eps,
  0 <= h ->
  eps > 0 ->
  payoff P h a1 >= payoff P h a2 ->
  epsilon_optimal h a1 a2 eps.
Proof.
  intros h a1 a2 eps Hh Heps Hdom.
  unfold epsilon_optimal.
  lra.
Qed.

End FiniteHorizon.

Definition EOX_compilation_success : bool := true.

Check EOX_compilation_success.

