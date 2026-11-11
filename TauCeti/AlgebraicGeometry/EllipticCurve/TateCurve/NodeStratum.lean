/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Uniformization
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Strata
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Ring.Ultra
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Surjectivity of the Tate uniformisation onto the node stratum

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`. Modulo the maximal
ideal, the Tate curve `E_q : y² + xy = x³ + a₄(q) x + a₆(q)` is the nodal cubic `y² + xy = x³`,
whose node is the origin. The points of `E_q(K)` reducing to the node are the solutions `(x, y)`
with `‖x‖ < 1` and `‖y‖ < 1`. This file shows that every such point is the image of a parameter
`u` in the strict annulus `‖q‖ < ‖u‖ < 1`. Together with the converse
`norm_tateQuotientCoordinates_fst_lt_one_and_snd_lt_one_iff` from `TateCurve.Strata`, an affine
point of `E_q(K)` is the image of such a parameter exactly when both of its coordinates lie in the
maximal ideal (`exists_tateUniformization_eq_some_iff_norm_lt_one_and_norm_lt_one`). Nothing here
assumes a discrete value group or restricts the characteristic. When `‖q‖` generates the value
group, as for `v(q) = 1` over a discretely valued field, there are no such points and no such
parameters.

On the annulus, the Tate coordinates are dominated by the terms of index `0` and `-1` of their
defining series: with `v = q / u`,

`X(u) + Y(u) = u / (1 - u)³ - v² / (1 - v)³ + O(‖q‖)`.

Since the negative of `(x, y)` is `(x, -x - y)`, we may assume `‖y‖ ≤ ‖x + y‖`. Put `s = x + y`.
The equation `y s = x³ + a₄ x + a₆` and `‖a₆‖ = ‖q‖` force `‖q‖ ≤ ‖s‖²`. The parameter is the
fixed point of

`u ↦ (1 - u)³ (s - (X(u) + Y(u) - u / (1 - u)³))`

on the circle `‖u‖ = ‖s‖`, a contraction with constant `‖s‖`: the error `X(u) + Y(u) - u / (1 - u)³`
has norm at most `‖q‖` there, and it is Lipschitz with constant `‖q‖ / ‖s‖ ≤ ‖s‖` because the
terms of index `-1` of the two coordinates combine into `-v² / (1 - v)³`, which is flat at `v = 0`.
At the fixed point `X(u) + Y(u) = s`. A line `x + y = s` meets the curve in at most one point whose
first coordinate has norm at most `‖s‖`, so `(X(u), Y(u)) = (x, y)`.

## Main results

* `TauCeti.eq_and_eq_of_add_eq_of_add_eq_of_norm_le`: over an ultrametric field, a line
  `x + y = s` with `‖s‖ < 1` meets `y² + xy = x³ + A₄x + A₆`, `‖A₄‖ < ‖s‖`, in at most one point
  whose first coordinate has norm at most `‖s‖`.
* `TauCeti.exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_norm_lt_one`: every solution
  `(x, y)` of the Tate equation with `‖x‖ < 1` and `‖y‖ < 1` is `(X(u), Y(u))` for some `u` with
  `‖q‖ < ‖u‖ < 1`.
* `TauCeti.exists_tateUniformization_eq_some_iff_norm_lt_one_and_norm_lt_one`: an affine point of
  `E_q(K)` is the image of a parameter with `‖q‖ < ‖u‖ < 1` exactly when both of its coordinates
  have norm less than one.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, V.3–V.4.
* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
-/

public section

namespace TauCeti

open WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### Points on a line of slope `-1` -/

/-- **A line `x + y = s` meets the curve in at most one point with `‖x‖ ≤ ‖s‖`.** Over an
ultrametric normed field, let `A₄, A₆` be arbitrary coefficients. If `(x, y)` and `(X, Y)` solve
`y² + xy = x³ + A₄x + A₆` with `‖A₄‖ < ‖s‖ < 1`, both lie on the line `x + y = s` and both first
coordinates have norm at most `‖s‖`, then the two points are equal. -/
theorem eq_and_eq_of_add_eq_of_add_eq_of_norm_le {A₄ A₆ s x y X Y : K} (hA₄ : ‖A₄‖ < ‖s‖)
    (hs : ‖s‖ < 1) (hx : ‖x‖ ≤ ‖s‖) (hX : ‖X‖ ≤ ‖s‖) (h₁ : y ^ 2 + x * y = x ^ 3 + A₄ * x + A₆)
    (h₂ : Y ^ 2 + X * Y = X ^ 3 + A₄ * X + A₆) (hxy : x + y = s) (hXY : X + Y = s) :
    X = x ∧ Y = y := by
  obtain rfl : y = s - x := eq_sub_of_add_eq' hxy
  obtain rfl : Y = s - X := eq_sub_of_add_eq' hXY
  -- on the line, the equation reads `s² - s x = x³ + A₄ x + A₆`
  have key : (x - X) * (x ^ 2 + x * X + X ^ 2 + A₄ + s) = 0 := by
    linear_combination h₂ - h₁
  have hs0 : 0 < ‖s‖ := (norm_nonneg _).trans_lt hA₄
  have hm {a b : K} (ha : ‖a‖ ≤ ‖s‖) (hb : ‖b‖ ≤ ‖s‖) : ‖a * b‖ < ‖s‖ := by
    rw [norm_mul]
    exact (mul_le_mul ha hb (norm_nonneg _) hs0.le).trans_lt (mul_lt_of_lt_one_left hs0 hs)
  have hlt : ‖x ^ 2 + x * X + X ^ 2 + A₄‖ < ‖s‖ := by
    rw [sq, sq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hA₄)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ (hm hX hX))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hm hx hx) (hm hx hX))
  have hne : x ^ 2 + x * X + X ^ 2 + A₄ + s ≠ 0 := fun h0 ↦
    hlt.ne' (by rw [eq_neg_of_add_eq_zero_right h0, norm_neg])
  have hxX : x = X := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)
  exact ⟨hxX.symm, by rw [hxX]⟩

/-! ### The size of a point reducing to the node -/

variable [CompleteSpace K]

/-- **A point reducing to the node is not too close to it.** If `(x, y)` solves the Tate equation,
`‖y‖ ≤ ‖x + y‖` and `‖x + y‖ < 1`, then `‖q‖ ≤ ‖x + y‖²`. The equation reads
`y (x + y) = x³ + a₄ x + a₆`, and `‖a₆‖ = ‖q‖`. -/
private theorem norm_le_norm_add_sq_of_equation (q : Kˣ) (hq : ‖(q : K)‖ < 1) {x y : K}
    (h : (tateCurveAt q hq).toAffine.Equation x y) (hy : ‖y‖ ≤ ‖x + y‖) (hs : ‖x + y‖ < 1) :
    ‖(q : K)‖ ≤ ‖x + y‖ ^ 2 := by
  by_contra! hlt
  have hq0 : 0 < ‖(q : K)‖ := norm_pos_iff.mpr q.ne_zero
  have hx : ‖x‖ ≤ ‖x + y‖ :=
    IsUltrametricDist.norm_le_of_norm_sub_le le_rfl (by rwa [sub_add_cancel_left, norm_neg])
  have hA₆ : tateCurveA₆ (q : K) hq = y * (x + y) - x ^ 3 - tateCurveA₄ (q : K) hq * x := by
    linear_combination -(tateCurveAt_equation_iff q hq).mp h
  have hss : ‖x + y‖ ^ 3 ≤ ‖x + y‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hs.le (by norm_num)
  refine (norm_tateCurveA₆ (q : K) hq).not_lt ?_
  rw [hA₆]
  refine (IsUltrametricDist.norm_sub_le_max _ _).trans_lt (max_lt
    ((IsUltrametricDist.norm_sub_le_max _ _).trans_lt (max_lt ?_ ?_)) ?_)
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hy (norm_nonneg _)).trans_lt (by rwa [← sq])
  · rw [norm_pow]
    exact ((pow_le_pow_left₀ (norm_nonneg _) hx 3).trans hss).trans_lt hlt
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_tateCurveA₄_le (q : K) hq) (norm_nonneg _)).trans_lt
      (mul_lt_of_lt_one_right hq0 (hx.trans_lt hs))

/-! ### The Tate coordinates near the node -/

/-- The difference between `X(u) + Y(u)` and its central term `u / (1 - u)³`. -/
private noncomputable def tateNodeErr (q u : Kˣ) : K :=
  tateUniformizationX q u + tateUniformizationY q u - u / (1 - u) ^ 3

omit [IsUltrametricDist K] in
/-- The one-sided series of the first and second Tate coordinates converge. -/
private theorem summable_tateTerms (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    (Summable fun n : ℕ ↦ (q : K) ^ (n + 1) * u / (1 - (q : K) ^ (n + 1) * u) ^ 2) ∧
    (Summable fun n : ℕ ↦ ((q : K) ^ (n + 1) * u) ^ 2 / (1 - (q : K) ^ (n + 1) * u) ^ 3) ∧
    (Summable fun n : ℕ ↦
      (q : K) ^ (n + 1) * (u : K)⁻¹ / (1 - (q : K) ^ (n + 1) * (u : K)⁻¹) ^ 2) ∧
    (Summable fun n : ℕ ↦
      -((q : K) ^ (n + 1) * (u : K)⁻¹) / (1 - (q : K) ^ (n + 1) * (u : K)⁻¹) ^ 3) := by
  have hi : Function.Injective fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ) := fun a b h ↦ by simpa using h
  have hi' : Function.Injective fun n : ℕ ↦ -((n + 1 : ℕ) : ℤ) := fun a b h ↦ by simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, zpow_natCast] using
      (summable_tateUniformizationX q hq u).comp_injective hi
  · simpa only [Function.comp_def, zpow_natCast] using
      (summable_tateUniformizationY q hq u).comp_injective hi
  · simpa only [Function.comp_def, zpow_natCast, Units.val_inv_eq_inv_val] using
      (summable_tateUniformizationX q hq u⁻¹).comp_injective hi
  · refine ((summable_tateUniformizationY q hq u).comp_injective hi').congr fun n ↦ ?_
    simp only [Function.comp_apply, zpow_neg, zpow_natCast]
    rw [← inv_sq_div_one_sub_inv_cube, mul_inv, inv_inv]

omit [IsUltrametricDist K] in
/-- **The series of the error near the node.** The terms of positive index of `X + Y` combine
into `t / (1 - t)³` at `t = qⁿu`, and those of negative index into `-t² / (1 - t)³` at
`t = qⁿu⁻¹`. -/
private theorem tateNodeErr_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    tateNodeErr q u =
      ∑' n : ℕ, (q : K) ^ (n + 1) * u / (1 - (q : K) ^ (n + 1) * u) ^ 3 +
        ∑' n : ℕ, -(((q : K) ^ (n + 1) * (u : K)⁻¹) ^ 2 /
          (1 - (q : K) ^ (n + 1) * (u : K)⁻¹) ^ 3) - divisorSumAt 1 (q : K) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := summable_tateTerms q hq u
  have hneg (t : K) : -(t ^ 2 / (1 - t) ^ 3) = t / (1 - t) ^ 2 + -t / (1 - t) ^ 3 := by
    linear_combination -div_one_sub_sq_add_sq_div_one_sub_cube t
  rw [tateNodeErr, tateUniformizationX_eq_tsum_nat q hq u, tateUniformizationY_eq_tsum_nat q hq u,
    ← div_one_sub_sq_add_sq_div_one_sub_cube,
    tsum_congr fun n ↦ (div_one_sub_sq_add_sq_div_one_sub_cube ((q : K) ^ (n + 1) * u)).symm,
    tsum_congr fun n ↦ hneg ((q : K) ^ (n + 1) * (u : K)⁻¹),
    h₁.tsum_add h₂, h₃.tsum_add h₄]
  ring

omit [IsUltrametricDist K] in
/-- The series of the error near the node converge. -/
private theorem summable_tateNodeErr (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ) :
    (Summable fun n : ℕ ↦ (q : K) ^ (n + 1) * u / (1 - (q : K) ^ (n + 1) * u) ^ 3) ∧
    (Summable fun n : ℕ ↦ -(((q : K) ^ (n + 1) * (u : K)⁻¹) ^ 2 /
      (1 - (q : K) ^ (n + 1) * (u : K)⁻¹) ^ 3)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := summable_tateTerms q hq u
  exact ⟨(h₁.add h₂).congr fun n ↦ div_one_sub_sq_add_sq_div_one_sub_cube _,
    (h₃.add h₄).congr fun n ↦ by
      linear_combination div_one_sub_sq_add_sq_div_one_sub_cube ((q : K) ^ (n + 1) * (u : K)⁻¹)⟩

/-- **The error near the node is small.** If `‖q‖ ≤ ‖u‖² < 1`, then `X(u) + Y(u)` differs from
`u / (1 - u)³` by at most `‖q‖`. -/
private theorem norm_tateNodeErr_le (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hqu : ‖(q : K)‖ ≤ ‖(u : K)‖ ^ 2) (hu : ‖(u : K)‖ < 1) :
    ‖tateNodeErr q u‖ ≤ ‖(q : K)‖ := by
  have hb : ‖(q : K)‖ / ‖(u : K)‖ ≤ ‖(u : K)‖ :=
    div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) (by rwa [← sq])
  have hqu' : ‖(q : K) * u‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu.le).trans_lt hq
  rw [tateNodeErr_eq q hq u]
  refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) (norm_divisorSumAt_le 1 hq))
  · refine (norm_tsum_le_norm_mul (fun w ↦ w / (1 - w) ^ 3)
      (fun w hw ↦ (norm_div_one_sub_pow w hw 3).le) hq.le hqu').trans ?_
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hu.le
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
    have ht : ‖(q : K) ^ (n + 1) * (u : K)⁻¹‖ ≤ ‖(q : K)‖ / ‖(u : K)‖ := by
      rw [norm_mul, norm_pow, norm_inv, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right
        (pow_le_of_le_one (norm_nonneg _) hq.le n.succ_ne_zero) (norm_nonneg _)
    rw [norm_neg, norm_div_one_sub_pow _ ((ht.trans hb).trans_lt hu), norm_pow]
    calc ‖(q : K) ^ (n + 1) * (u : K)⁻¹‖ ^ 2 ≤ (‖(q : K)‖ / ‖(u : K)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) ht 2
      _ = ‖(q : K)‖ * (‖(q : K)‖ / ‖(u : K)‖ ^ 2) := by ring
      _ ≤ ‖(q : K)‖ := mul_le_of_le_one_right (norm_nonneg _)
          (div_le_one_of_le₀ hqu (sq_nonneg _))

/-- **The error near the node is Lipschitz.** On the circle `‖u‖ = r` with `‖q‖ ≤ r² < 1`, the
difference between `X(u) + Y(u)` and `u / (1 - u)³` is Lipschitz with constant `r`. -/
private theorem norm_tateNodeErr_sub_le (q u u' : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hqu : ‖(q : K)‖ ≤ ‖(u : K)‖ ^ 2) (hu : ‖(u : K)‖ < 1) (hu' : ‖(u' : K)‖ = ‖(u : K)‖) :
    ‖tateNodeErr q u - tateNodeErr q u'‖ ≤ ‖(u : K)‖ * ‖(u : K) - u'‖ := by
  have hu0 : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hb : ‖(q : K)‖ / ‖(u : K)‖ ≤ ‖(u : K)‖ :=
    div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) (by rwa [← sq])
  have hqr : ‖(q : K)‖ ≤ ‖(u : K)‖ :=
    hqu.trans (pow_le_of_le_one (norm_nonneg _) hu.le two_ne_zero)
  obtain ⟨hG, hH⟩ := summable_tateNodeErr q hq u
  obtain ⟨hG', hH'⟩ := summable_tateNodeErr q hq u'
  have e (G H G' H' s : K) : G + H - s - (G' + H' - s) = (G - G') + (H - H') := by ring
  rw [tateNodeErr_eq q hq u, tateNodeErr_eq q hq u', e, ← hG.tsum_sub hG', ← hH.tsum_sub hH']
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n ↦ ?_
  · -- the terms `t / (1 - t)³` at `t = qⁿu` are `1`-Lipschitz in `t`
    have hpow : ‖(q : K) ^ (n + 1)‖ ≤ ‖(q : K)‖ := by
      rw [norm_pow]
      exact pow_le_of_le_one (norm_nonneg _) hq.le n.succ_ne_zero
    have ht (w : Kˣ) (hw : ‖(w : K)‖ = ‖(u : K)‖) : ‖(q : K) ^ (n + 1) * w‖ < 1 := by
      rw [norm_mul, hw]
      exact ((mul_le_mul hpow hu.le (norm_nonneg _) (norm_nonneg _)).trans_eq
        (mul_one _)).trans_lt hq
    refine (norm_div_one_sub_cube_sub_div_one_sub_cube_le (ht u rfl) (ht u' hu')).trans ?_
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right (hpow.trans hqr) (norm_nonneg _)
  · -- the terms `-t² / (1 - t)³` at `t = qⁿu⁻¹` are Lipschitz with constant `‖q‖ / ‖u‖`
    have ht (w : Kˣ) (hw : ‖(w : K)‖ = ‖(u : K)‖) :
        ‖(q : K) ^ (n + 1) * (w : K)⁻¹‖ ≤ ‖(q : K)‖ / ‖(u : K)‖ := by
      rw [norm_mul, norm_pow, norm_inv, hw, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right
        (pow_le_of_le_one (norm_nonneg _) hq.le n.succ_ne_zero) (norm_nonneg _)
    have hd : ‖(q : K) ^ (n + 1) * (u : K)⁻¹ - (q : K) ^ (n + 1) * (u' : K)⁻¹‖ ≤
        ‖(u : K) - u'‖ := by
      rw [← mul_sub, inv_sub_inv u.ne_zero u'.ne_zero, norm_mul, norm_div, norm_mul, hu',
        norm_sub_rev, norm_pow, ← sq]
      calc ‖(q : K)‖ ^ (n + 1) * (‖(u : K) - u'‖ / ‖(u : K)‖ ^ 2)
          ≤ ‖(q : K)‖ * (‖(u : K) - u'‖ / ‖(u : K)‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (pow_le_of_le_one (norm_nonneg _) hq.le n.succ_ne_zero)
              (by positivity)
        _ = ‖(q : K)‖ / ‖(u : K)‖ ^ 2 * ‖(u : K) - u'‖ := by ring
        _ ≤ ‖(u : K) - u'‖ := mul_le_of_le_one_left (norm_nonneg _)
            (div_le_one_of_le₀ hqu (sq_nonneg _))
    have hd' : ‖(q : K) ^ (n + 1) * (u' : K)⁻¹ - (q : K) ^ (n + 1) * (u : K)⁻¹‖ ≤
        ‖(u : K) - u'‖ := by
      rwa [norm_sub_rev]
    rw [neg_sub_neg]
    exact (norm_sq_div_one_sub_cube_sub_sq_div_one_sub_cube_le_max_mul
      (((ht u' hu').trans hb).trans_lt hu) (((ht u rfl).trans hb).trans_lt hu)).trans
      (mul_le_mul ((max_le (ht u' hu') (ht u rfl)).trans hb) hd' (norm_nonneg _) hu0.le)

/-! ### Solving for the parameter by a contraction -/

/-- One step of the contraction, `u ↦ (1 - u)³ (s - (X(u) + Y(u) - u / (1 - u)³))`. -/
private noncomputable def tateNodeStep (q u : Kˣ) (s : K) : K :=
  (1 - (u : K)) ^ 3 * (s - tateNodeErr q u)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- At a fixed point of the contraction, `X(u) + Y(u) = s`. -/
private theorem tateUniformizationX_add_tateUniformizationY_of_tateNodeStep_eq (q u : Kˣ) {s : K}
    (h : 1 - (u : K) ≠ 0) (hu : tateNodeStep q u s = u) :
    tateUniformizationX q u + tateUniformizationY q u = s := by
  rw [tateNodeStep, tateNodeErr] at hu
  have hc : (1 - (u : K)) ^ 3 ≠ 0 := pow_ne_zero _ h
  field_simp at hu
  have h0 : (1 - (u : K)) ^ 3 * (s - (tateUniformizationX q u + tateUniformizationY q u)) = 0 := by
    linear_combination hu
  exact (sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hc)).symm

/-- **Solving for the parameter.** For `‖q‖ ≤ ‖s‖² < 1` there is a parameter `u` with `‖u‖ = ‖s‖`
and `X(u) + Y(u) = s`. It is the fixed point of the contraction `tateNodeStep q · s` of the
complete circle `{u : ‖u‖ = ‖s‖}`, with constant `‖s‖`. -/
private theorem exists_tateUniformizationX_add_tateUniformizationY_eq (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {s : K} (hqs : ‖(q : K)‖ ≤ ‖s‖ ^ 2) (hs : ‖s‖ < 1) :
    ∃ u : Kˣ, ‖(u : K)‖ = ‖s‖ ∧ tateUniformizationX q u + tateUniformizationY q u = s := by
  have hs0 : 0 < ‖s‖ := norm_pos_iff.mpr fun h ↦ by simp [h, q.ne_zero] at hqs
  have hss : ‖s‖ ^ 2 < ‖s‖ := pow_lt_self_of_lt_one₀ hs0 hs one_lt_two
  set S : Set K := {u | ‖u‖ = ‖s‖}
  have : CompleteSpace S := (isClosed_eq continuous_norm continuous_const).completeSpace_coe
  have : Nonempty S := ⟨⟨s, rfl⟩⟩
  have hne (v : S) : (v : K) ≠ 0 := norm_ne_zero_iff.mp (by rw [v.2]; exact hs0.ne')
  let U : S → Kˣ := fun v ↦ Units.mk0 v (hne v)
  have hUv (v : S) : ((U v : Kˣ) : K) = v := Units.val_mk0 _
  have hU (v : S) : ‖((U v : Kˣ) : K)‖ = ‖s‖ := by rw [hUv]; exact v.2
  have hU₁ (v : S) : ‖1 - ((U v : Kˣ) : K)‖ = 1 :=
    norm_one_sub_of_norm_lt_one ((hU v).trans_lt hs)
  have hqU (v : S) : ‖(q : K)‖ ≤ ‖((U v : Kˣ) : K)‖ ^ 2 := by rw [hU v]; exact hqs
  have hErr (v : S) : ‖tateNodeErr q (U v)‖ ≤ ‖s‖ ^ 2 :=
    (norm_tateNodeErr_le q (U v) hq (hqU v) ((hU v).trans_lt hs)).trans hqs
  -- the step moves every point of the circle to within `‖s‖²` of `s`, so it preserves the circle
  have hstep (v : S) : ‖tateNodeStep q (U v) s - s‖ ≤ ‖s‖ ^ 2 := by
    have h := norm_pow_sub_one_le_norm_sub_one (hU₁ v).le 3
    rw [sub_sub_cancel_left, norm_neg, hU v] at h
    have hrw (c E : K) : c * (s - E) - s = (c - 1) * s - c * E := by ring
    rw [tateNodeStep, hrw]
    refine (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, sq]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    · rw [norm_mul, norm_pow, hU₁ v, one_pow, one_mul]
      exact hErr v
  have hmem (v : S) : tateNodeStep q (U v) s ∈ S :=
    (IsUltrametricDist.norm_eq_of_norm_sub_lt_left
      (by rw [norm_sub_rev]; exact (hstep v).trans_lt hss)).symm
  -- the step is Lipschitz with constant `‖s‖`
  have hlip (v w : S) : ‖tateNodeStep q (U v) s - tateNodeStep q (U w) s‖ ≤
      ‖s‖ * ‖((U v : Kˣ) : K) - (U w : Kˣ)‖ := by
    have h := norm_prod_sub_prod_le (s := .univ) (f := fun _ : Fin 3 ↦ 1 - ((U v : Kˣ) : K))
      (g := fun _ ↦ 1 - ((U w : Kˣ) : K)) zero_le_one (norm_nonneg _) (fun _ _ ↦ (hU₁ v).le)
      (fun _ _ ↦ (hU₁ w).le) fun _ _ ↦ by rw [sub_sub_sub_cancel_left, norm_sub_rev]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_one] at h
    have hrw (c d E F : K) :
        c * (s - E) - d * (s - F) = (c - d) * (s - E) + d * (F - E) := by ring
    rw [tateNodeStep, tateNodeStep, hrw]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, mul_comm ‖s‖]
      exact mul_le_mul (h.trans_eq (norm_sub_rev _ _))
        ((IsUltrametricDist.norm_sub_le_max _ _).trans (max_le le_rfl ((hErr v).trans hss.le)))
        (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul, norm_pow, hU₁ w, one_pow, one_mul, norm_sub_rev, ← hU v]
      exact norm_tateNodeErr_sub_le q (U v) (U w) hq (hqU v) ((hU v).trans_lt hs)
        ((hU w).trans (hU v).symm)
  have hF : ContractingWith ‖s‖₊ (fun v : S ↦ (⟨tateNodeStep q (U v) s, hmem v⟩ : S)) := by
    refine ⟨by rwa [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one],
      LipschitzWith.of_dist_le_mul fun v w ↦ ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, coe_nnnorm, ← hUv v, ← hUv w]
    exact hlip v w
  exact ⟨U _, hU _, tateUniformizationX_add_tateUniformizationY_of_tateNodeStep_eq q (U _)
    (norm_ne_zero_iff.mp (by rw [hU₁]; exact one_ne_zero))
    ((congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt hF)).trans (hUv _).symm)⟩

/-! ### Surjectivity onto the node stratum -/

/-- The case `‖y‖ ≤ ‖x + y‖` of
`exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_norm_lt_one`: the parameter lies on
the circle `‖u‖ = ‖x + y‖`. -/
private theorem exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_norm_le (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {x y : K} (h : (tateCurveAt q hq).toAffine.Equation x y)
    (hy : ‖y‖ ≤ ‖x + y‖) (hs : ‖x + y‖ < 1) :
    ∃ u : Kˣ, ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ < 1 ∧
      tateUniformizationX q u = x ∧ tateUniformizationY q u = y := by
  have hqs := norm_le_norm_add_sq_of_equation q hq h hy hs
  obtain ⟨u, hu, hXY⟩ := exists_tateUniformizationX_add_tateUniformizationY_eq q hq hqs hs
  have hs0 : 0 < ‖x + y‖ := norm_pos_iff.mpr fun h0 ↦ by simp [h0, q.ne_zero] at hqs
  have hqs' : ‖(q : K)‖ < ‖x + y‖ := hqs.trans_lt (by rw [sq]; exact mul_lt_of_lt_one_left hs0 hs)
  have hqu : ‖(q : K)‖ < ‖(u : K)‖ := hu ▸ hqs'
  have hu1 : ‖(u : K)‖ < 1 := hu ▸ hs
  have hx : ‖x‖ ≤ ‖x + y‖ :=
    IsUltrametricDist.norm_le_of_norm_sub_le le_rfl (by rwa [sub_add_cancel_left, norm_neg])
  have hX : ‖tateUniformizationX q u‖ ≤ ‖x + y‖ :=
    hu ▸ (norm_tateUniformizationX_le_max q u hqu hu1).trans
      (max_le le_rfl (div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) (by rwa [← sq, hu])))
  obtain ⟨hXe, hYe⟩ := eq_and_eq_of_add_eq_of_add_eq_of_norm_le
    ((norm_tateCurveA₄_le (q : K) hq).trans_lt hqs') hs hx hX ((tateCurveAt_equation_iff q hq).mp h)
    ((tateCurveAt_equation_iff q hq).mp
      (equation_tateUniformizationX_tateUniformizationY_of_notMem_zpowers q u hq
        (notMem_zpowers_of_norm_lt_of_norm_lt_one hqu hu1))) rfl hXY
  exact ⟨u, hqu, hu1, hXe, hYe⟩

/-- **Every solution of the Tate equation reducing to the node comes from the strict annulus.** If
`(x, y)` satisfies `y² + xy = x³ + a₄(q) x + a₆(q)` with `‖x‖ < 1` and `‖y‖ < 1`, then
`(x, y) = (X(u), Y(u))` for a parameter `u` with `‖q‖ < ‖u‖ < 1`. -/
theorem exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_norm_lt_one (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {x y : K} (h : (tateCurveAt q hq).toAffine.Equation x y)
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ∃ u : Kˣ, ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ < 1 ∧
      tateUniformizationX q u = x ∧ tateUniformizationY q u = y := by
  have hs : ‖x + y‖ < 1 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  rcases le_or_gt ‖y‖ ‖x + y‖ with hle | hlt
  · exact exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_norm_le q hq h hle hs
  -- otherwise the negative `(x, -y - x)` falls under the first case, and `q u⁻¹` works for `(x, y)`
  have h' : (tateCurveAt q hq).toAffine.Equation x (-y - x) := by
    simpa [negY] using (equation_neg x y).mpr h
  have e₁ : x + (-y - x) = -y := by ring
  have e₂ : -y - x = -(x + y) := by ring
  obtain ⟨u, hqu, hu1, hX, hY⟩ :=
    exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_norm_le q hq h'
      (by rw [e₁, e₂, norm_neg, norm_neg]; exact hlt.le) (by rwa [e₁, norm_neg])
  have hu0 : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hq0 : 0 < ‖(q : K)‖ := norm_pos_iff.mpr q.ne_zero
  have hn : ‖((q * u⁻¹ : Kˣ) : K)‖ = ‖(q : K)‖ / ‖(u : K)‖ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, div_eq_mul_inv]
  refine ⟨q * u⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [hn, lt_div_iff₀ hu0]
    exact mul_lt_of_lt_one_right hq0 hu1
  · rw [hn]
    exact (div_lt_one hu0).mpr hqu
  · rw [tateUniformizationX_self_mul, tateUniformizationX_inv, hX]
  · rw [tateUniformizationY_self_mul, tateUniformizationY_inv q hq, hX, hY]
    ring

/-- **The Tate uniformisation is onto the node stratum.** An affine point `(x, y)` of `E_q(K)` is
the image of the class of a parameter `u` with `‖q‖ < ‖u‖ < 1` exactly when `‖x‖ < 1` and
`‖y‖ < 1`. -/
theorem exists_tateUniformization_eq_some_iff_norm_lt_one_and_norm_lt_one (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) {x y : K} (h : (tateCurveAt q hq).toAffine.Nonsingular x y) :
    (∃ u : Kˣ, ‖(q : K)‖ < ‖(u : K)‖ ∧ ‖(u : K)‖ < 1 ∧
      tateUniformization q hq (u : Kˣ ⧸ Subgroup.zpowers q) = .some x y h) ↔
      ‖x‖ < 1 ∧ ‖y‖ < 1 := by
  constructor
  · rintro ⟨u, hqu, hu1, hP⟩
    obtain ⟨hne, hX, hY⟩ := (tateUniformization_eq_some_iff q hq _ h).mp hP
    obtain ⟨hX', hY'⟩ :=
      (norm_tateQuotientCoordinates_fst_lt_one_and_snd_lt_one_iff q hq hne).mpr ⟨u, rfl, hqu, hu1⟩
    exact ⟨hX ▸ hX', hY ▸ hY'⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨u, hqu, hu1, hX, hY⟩ :=
      exists_tateUniformizationX_eq_and_tateUniformizationY_eq_of_norm_lt_one q hq h.1 hx hy
    refine ⟨u, hqu, hu1, (tateUniformization_eq_some_iff q hq _ h).mpr ⟨?_, ?_, ?_⟩⟩
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact notMem_zpowers_of_norm_lt_of_norm_lt_one hqu hu1
    · rw [tateQuotientCoordinates_mk, hX]
    · rw [tateQuotientCoordinates_mk, hY]

end TauCeti
