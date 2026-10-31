/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.AddInv
-- Proof-only: the pure-power coefficients of a formal group law, lower bounds for the order of
-- substitutions, and the order of `F(X, Y) - X - Y`.
import TauCeti.RingTheory.FormalGroup.LazardRing.Basic
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# The order filtration on the points of a formal group law

Let `G` be a formal group law over a commutative ring `R`. The power-series points `G.Point σ`
vanishing to order `N` form a subgroup, and when `N ≥ 1` the group law of `G` is ordinary addition
on it up to terms of degree above `N`, since `G(X, Y) = X + Y` up to terms of degree two divisible
by `X`. So the degree-`N` part is additive on the points vanishing to order `N`: this is how
identities in the group `G.Point σ` pass to identities between leading terms.

## Main results

* `FormalGroup.le_order_subst_sub_sub`: if `w` vanishes to order `N ≥ 1` and `v` has no constant
  term, then `G(w, v) - w - v` vanishes to order `N + 1`.
* `FormalGroup.le_order_val_add`, `FormalGroup.le_order_val_neg`, `FormalGroup.le_order_val_sub`,
  `FormalGroup.le_order_val_sum`: the points vanishing to order `N` form a subgroup.
* `FormalGroup.homogeneousComponent_val_add`, `FormalGroup.homogeneousComponent_val_sub`,
  `FormalGroup.homogeneousComponent_val_sum`: on points vanishing to order `N ≥ 1`, the group law
  of `G` agrees with ordinary addition in degree `N`.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (G : FormalGroup R) {σ : Type*}

/-- **A formal group law is additive to first order.** If `w` vanishes to order `N ≥ 1` and `v`
has no constant term, then `G(w, v) - w - v` vanishes to order `N + 1`: the monomials of
`G(X, Y) - X - Y` have degree at least two and are divisible by `X`, since `G(0, Y) = Y`. -/
theorem le_order_subst_sub_sub {N : ℕ} (hN : N ≠ 0) {w v : MvPowerSeries σ R}
    (hw : (N : ℕ∞) ≤ w.order) (hv : constantCoeff v = 0) :
    ((N + 1 : ℕ) : ℕ∞) ≤ (G.toPowerSeries.subst ![w, v] - w - v).order := by
  have hw₀ : constantCoeff w = 0 :=
    one_le_order_iff_constCoeff_eq_zero.mp
      (le_trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN) hw)
  have hwv : HasSubst ![w, v] := hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i <;> simp [hw₀, hv]
  have hD : G.toPowerSeries.subst ![w, v] - w - v =
      (G.toPowerSeries - (X 0 + X 1)).subst ![w, v] := by
    rw [subst_sub hwv, subst_add hwv, subst_X hwv, subst_X hwv]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  rw [hD]
  refine le_trans ?_ (le_weightedOrder_subst (fun _ ↦ 1) hwv _)
  simp only [ne_eq, le_iInf_iff]
  intro d hd
  have hG := two_le_order_sub_X_add_X G.zero_constantCoeff G.lin_coeff_X G.lin_coeff_Y
  -- the monomials of `G - X - Y` have degree at least two
  have hdeg : 2 ≤ d.degree := by
    by_contra h
    exact hd (coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast not_le.mp h) hG))
  -- and are not pure powers of `Y`, since `G(0, Y) = Y`
  have hd0 : d 0 ≠ 0 := by
    intro h0
    have hd' : d = Finsupp.single 1 (d 1) := by
      ext i; fin_cases i <;> simp [h0]
    have h1 : d 1 ≠ 1 := by
      intro h1
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, h0, h1] at hdeg
      omega
    apply hd
    rw [hd', map_sub, map_add, coeff_single_one, ite_eq_right_iff.mpr (fun h ↦ (h1 h).elim),
      coeff_X, coeff_X]
    simp [Finsupp.single_eq_single_iff, h1]
  have hv' : (1 : ℕ∞) ≤ v.order := one_le_order_iff_constCoeff_eq_zero.mpr hv
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, nsmul_eq_mul]
  -- `order` is by definition `weightedOrder` for the weight `1`
  change ((N + 1 : ℕ) : ℕ∞) ≤ (d 0 : ℕ∞) * w.order + (d 1 : ℕ∞) * v.order
  have hdeg' : 2 ≤ d 0 + d 1 := by rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
  have key : N + 1 ≤ d 0 * N + d 1 := by
    rcases Nat.lt_or_ge (d 0) 2 with h | h
    · have : d 0 = 1 := by omega
      rw [this]; omega
    · have := Nat.mul_le_mul_right N h
      omega
  calc ((N + 1 : ℕ) : ℕ∞) ≤ ((d 0 * N + d 1 : ℕ) : ℕ∞) := by exact_mod_cast key
    _ = (d 0 : ℕ∞) * N + (d 1 : ℕ∞) * 1 := by push_cast; ring
    _ ≤ _ := by gcongr

/-- Sums of points without constant term have no constant term. -/
theorem constantCoeff_val_add {x y : G.Point σ}
    (hx : constantCoeff x.val = 0) (hy : constantCoeff y.val = 0) :
    constantCoeff (x + y).val = 0 := by
  rw [add_apply, constantCoeff_subst_of_constantCoeff_zero (hasSubst_finTwo x.prop y.prop)
    (fun i ↦ by fin_cases i <;> assumption), G.zero_constantCoeff, map_zero]

/-- The points of `G` vanishing to order `N` are closed under addition. -/
theorem le_order_val_add {N : ℕ∞} {x y : G.Point σ} (hx : N ≤ x.val.order)
    (hy : N ≤ y.val.order) : N ≤ (x + y).val.order := by
  rw [add_apply]
  refine le_trans ?_ (le_order_subst (hasSubst_finTwo x.prop y.prop) _)
  have hG : (1 : ℕ∞) ≤ G.toPowerSeries.order :=
    one_le_order_iff_constCoeff_eq_zero.mpr G.zero_constantCoeff
  calc N = N * 1 := (mul_one N).symm
    _ ≤ _ := mul_le_mul' (le_iInf fun i ↦ by fin_cases i <;> simpa) hG

/-- The points of `G` vanishing to order `N` are closed under negation. -/
theorem le_order_val_neg {N : ℕ∞} {x : G.Point σ} (hx : N ≤ x.val.order) :
    N ≤ (-x).val.order := by
  rw [neg_apply]
  refine le_trans ?_ (PowerSeries.le_order_subst _ x.prop _)
  have hi : (1 : ℕ∞) ≤ G.addInvX.order := by
    rw [PowerSeries.order_eq_order]
    exact one_le_order_iff_constCoeff_eq_zero.mpr G.constantCoeff_addInvX
  calc N = N * 1 := (mul_one N).symm
    _ ≤ _ := mul_le_mul' hx hi

/-- The points of `G` vanishing to order `N` are closed under subtraction. -/
theorem le_order_val_sub {N : ℕ∞} {x y : G.Point σ} (hx : N ≤ x.val.order)
    (hy : N ≤ y.val.order) : N ≤ (x - y).val.order := by
  rw [sub_eq_add_neg]
  exact G.le_order_val_add hx (G.le_order_val_neg hy)

/-- The points of a commutative formal group law vanishing to order `N` are closed under finite
sums. -/
theorem le_order_val_sum [G.IsComm] {N : ℕ∞} {ι : Type*} (s : Finset ι) (t : ι → G.Point σ)
    (ht : ∀ j ∈ s, N ≤ (t j).val.order) : N ≤ (∑ j ∈ s, t j).val.order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact G.le_order_val_add (ht a (Finset.mem_insert_self a s))
      (ih fun j hj ↦ ht j (Finset.mem_insert_of_mem hj))

/-- If `x - y` vanishes to order `N ≥ 1` in the points of `G` and `y` has no constant term, then
subtraction in `G` agrees with ordinary subtraction up to degree `N + 1`. -/
theorem le_order_val_sub_val_sub {N : ℕ} (hN : N ≠ 0) {x y : G.Point σ}
    (hy : constantCoeff y.val = 0) (h : (N : ℕ∞) ≤ (x - y).val.order) :
    ((N + 1 : ℕ) : ℕ∞) ≤ (x.val - y.val - (x - y).val).order := by
  have hx : x.val = G.toPowerSeries.subst ![(x - y).val, y.val] := by
    rw [← add_apply, sub_add_cancel]
  have := G.le_order_subst_sub_sub hN h hy
  rw [hx]
  convert this using 2
  ring

/-- On points whose difference in `G` vanishes to order `N ≥ 1`, the degree-`N` part of the
difference in `G` is the degree-`N` part of the ordinary difference. -/
theorem homogeneousComponent_val_sub {N : ℕ} (hN : N ≠ 0) {x y : G.Point σ}
    (hy : constantCoeff y.val = 0) (h : (N : ℕ∞) ≤ (x - y).val.order) :
    homogeneousComponent N (x - y).val = homogeneousComponent N (x.val - y.val) := by
  have h' := G.le_order_val_sub_val_sub hN hy h
  rw [← sub_eq_zero, ← map_sub]
  ext d
  rw [coeff_homogeneousComponent, map_zero]
  split_ifs with hd
  · have hlt : (d.degree : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by
      rw [hd]; exact_mod_cast Nat.lt_succ_self N
    exact coeff_of_lt_order (hlt.trans_le (by rwa [← neg_sub, order_neg]))
  · rfl

/-- If `x` vanishes to order `N ≥ 1` and `y` has no constant term, the degree-`N` part of the sum
`x + y` in `G` is the sum of the degree-`N` parts. -/
theorem homogeneousComponent_val_add {N : ℕ} (hN : N ≠ 0) {x y : G.Point σ}
    (hx : (N : ℕ∞) ≤ x.val.order) (hy : constantCoeff y.val = 0) :
    homogeneousComponent N (x + y).val =
      homogeneousComponent N x.val + homogeneousComponent N y.val := by
  have h := G.homogeneousComponent_val_sub hN hy (x := x + y) (by rwa [add_sub_cancel_right])
  rw [add_sub_cancel_right, map_sub] at h
  rw [h, sub_add_cancel]

/-- On points of a commutative formal group law vanishing to order `N ≥ 1`, the degree-`N` part
of a finite sum in `G` is the sum of the degree-`N` parts. -/
theorem homogeneousComponent_val_sum [G.IsComm] {N : ℕ} (hN : N ≠ 0) {ι : Type*} (s : Finset ι)
    (t : ι → G.Point σ) (ht : ∀ j ∈ s, (N : ℕ∞) ≤ (t j).val.order) :
    homogeneousComponent N (∑ j ∈ s, t j).val = ∑ j ∈ s, homogeneousComponent N (t j).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_apply]
  | insert a s ha ih =>
    have hs : ∀ j ∈ s, (N : ℕ∞) ≤ (t j).val.order := fun j hj ↦
      ht j (Finset.mem_insert_of_mem hj)
    have hs₀ : constantCoeff (∑ j ∈ s, t j).val = 0 :=
      one_le_order_iff_constCoeff_eq_zero.mp
        (le_trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN) (G.le_order_val_sum s t hs))
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      G.homogeneousComponent_val_add hN (ht a (Finset.mem_insert_self a s)) hs₀, ih hs]

/-- If `x` and `y` have no constant term and `x - y` vanishes to order `N` as power series, then
the difference `x - y` in the points of `G` vanishes to order `N` too. -/
theorem le_order_val_sub_of_le_order_sub {N : ℕ} {x y : G.Point σ}
    (hx : constantCoeff x.val = 0) (hy : constantCoeff y.val = 0)
    (h : (N : ℕ∞) ≤ (x.val - y.val).order) : (N : ℕ∞) ≤ (x - y).val.order := by
  induction N with
  | zero => simp
  | succ m ih =>
    have ih := ih (le_trans (by exact_mod_cast Nat.le_succ m) h)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact G.le_order_val_sub (one_le_order_iff_constCoeff_eq_zero.mpr hx)
        (one_le_order_iff_constCoeff_eq_zero.mpr hy)
    · have h' := G.le_order_val_sub_val_sub hm.ne' hy ih
      have := le_order_sub h h'
      rwa [sub_sub_cancel] at this

end FormalGroup
