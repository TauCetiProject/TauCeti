/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Complex conjugation: invariant discs, symmetric norms and unit-norm quotients

Complex conjugation is an isometry fixing the real axis (Mathlib's `Complex.dist_conj_conj`), so
it maps every open or closed disc centred on the real axis to itself. Such discs are the natural
domains for reflection across the real axis, for instance the even reflection
`TauCeti.evenReflection`. Conjugation maps the real axis into itself
(`TauCeti.mapsTo_conj_setOf_im_eq_zero`), whereas the rotation `z ↦ I z` does not
(`TauCeti.not_mapsTo_I_mul_setOf_im_eq_zero`).

Conjugation also preserves norms (Mathlib's `Complex.norm_conj`), so the norm of
`1 - conj w * z` is symmetric in `z` and `w` (`Complex.norm_one_sub_conj_mul_comm`). This
expression is the denominator of the Möbius automorphisms of the unit disc and of the
pseudo-hyperbolic expression. For `w` on the unit circle it has the norm of `z - w`
(`Complex.norm_one_sub_conj_mul`), and for `z` in the closed unit disc it lies in the closed right
half-plane (`Complex.re_one_sub_conj_mul_nonneg`; strictly inside it for `z` in the open disc,
`Complex.re_one_sub_conj_mul_pos`), by the bound `re (conj u * e) ≤ ‖u‖ ‖e‖`
(`Complex.re_conj_mul_le`).

Inversion preserves the open right half-plane: `z⁻¹` has positive real part exactly when `z`
does (`Complex.inv_re_pos`).

The map `y ↦ r² / y` (inversion in the circle of radius `r` followed by conjugation) satisfies
`‖conj x - r² / y‖ ≤ 3 ‖x - y‖` for `‖x‖ ≤ r ≤ ‖y‖` (`Complex.norm_conj_sub_sq_div_le`).

The scalar Cayley expression `1 + (z - conj z) / (r - z)` has unit norm for real `r`.
When `z ≠ r`, it is the quotient `(r - conj z) / (r - z)` of a complex number's conjugate
by itself; at `z = r`, Lean's totalized inverse gives value one.

Two integers whose images in `ℂ` are at distance less than `1` are equal.

Dividing by a natural number does not increase the norm, so `‖(a z + b) / M‖ ≤ ‖a‖ C + ‖b‖`
whenever `‖z‖ ≤ C` (`Complex.norm_mul_add_div_natCast_le`).
-/

public section

open scoped ComplexConjugate

/-- A complex number and its inverse lie in the open right half-plane together. -/
theorem Complex.inv_re_pos {z : ℂ} : 0 < z⁻¹.re ↔ 0 < z.re := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [inv_re, div_pos_iff_of_pos_right (normSq_pos.mpr hz)]

/-- The scalar Cayley expression has unit norm at real `r`, including when `z = r`
under the totalized inverse convention. -/
theorem Complex.norm_one_add_sub_conj_mul_inv_ofReal_sub (z : ℂ) (r : ℝ) :
    ‖1 + (z - conj z) * ((r : ℂ) - z)⁻¹‖ = 1 := by
  by_cases hne : (r : ℂ) - z = 0
  · simp [hne]
  have heq : 1 + (z - conj z) * ((r : ℂ) - z)⁻¹ =
      ((r : ℂ) - conj z) / ((r : ℂ) - z) := by
    field_simp
    ring
  have hnorm : ‖(r : ℂ) - conj z‖ = ‖(r : ℂ) - z‖ := by
    simpa using Complex.norm_conj ((r : ℂ) - z)
  rw [heq, norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hne)]

namespace TauCeti

open ComplexConjugate Metric

variable {x₀ z : ℂ} {r : ℝ}

/-- Conjugation maps an open disc centred on the real axis to itself. -/
theorem conj_mem_ball_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ ball x₀ r) :
    conj z ∈ ball x₀ r := by
  rwa [mem_ball, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

/-- Conjugation maps a closed disc centred on the real axis to itself. -/
theorem conj_mem_closedBall_of_im_eq_zero (hx₀ : x₀.im = 0) (hz : z ∈ closedBall x₀ r) :
    conj z ∈ closedBall x₀ r := by
  rwa [mem_closedBall, ← Complex.conj_eq_iff_im.2 hx₀, Complex.dist_conj_conj]

/-- Complex conjugation maps the real axis into itself. -/
theorem mapsTo_conj_setOf_im_eq_zero :
    Set.MapsTo (conj ·) {z : ℂ | z.im = 0} {z : ℂ | z.im = 0} := fun z hz => by
  simpa using hz

/-- The rotation `z ↦ I z` does not preserve the real axis, so it is not admissible on
half-discs. -/
theorem not_mapsTo_I_mul_setOf_im_eq_zero :
    ¬ Set.MapsTo (fun z : ℂ => Complex.I * z) {z | z.im = 0} {z | z.im = 0} := fun h => by
  simpa using h (show (1 : ℂ) ∈ {z : ℂ | z.im = 0} by simp)

variable {E : Type*} [TopologicalSpace E] {τ : E → E} {U : Set E} {ρ : ℝ}

/-- The parameter map `τ` composed with conjugation of the disc coordinate is continuous on the
product of `U` with a disc centred at zero, and maps this product and its punctured version to
themselves. -/
theorem continuousOn_mapsTo_prodMap_conj (hτ : ContinuousOn τ U) (hτU : Set.MapsTo τ U U) :
    ContinuousOn (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 ρ) ∧
      Set.MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 ρ) (U ×ˢ ball 0 ρ) ∧
      Set.MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ (ball 0 ρ \ {0}))
        (U ×ˢ (ball 0 ρ \ {0})) := by
  have hconjBall : Set.MapsTo conj (ball (0 : ℂ) ρ) (ball 0 ρ) := fun _ hz ↦
    conj_mem_ball_of_im_eq_zero (by simp) hz
  exact ⟨hτ.prodMap Complex.continuous_conj.continuousOn, hτU.prodMap hconjBall,
    hτU.prodMap fun z hz ↦ ⟨hconjBall hz.1, by simpa using hz.2⟩⟩

/-- **Two integers whose complex images are closer than `1` are equal.** -/
theorem eq_of_dist_intCast_lt_one {m n : ℤ} (h : dist (m : ℂ) (n : ℂ) < 1) : m = n := by
  by_contra hne
  have : (1 : ℝ) ≤ dist (m : ℂ) (n : ℂ) := by
    rw [Complex.isometry_intCast.dist_eq]; exact Int.pairwise_one_le_dist hne
  linarith

end TauCeti

namespace Complex

open ComplexConjugate

/-- The imaginary part of a conjugate product is bounded by the product of the norms. -/
theorem abs_im_conj_mul_le (u e : ℂ) : |(conj u * e).im| ≤ ‖u‖ * ‖e‖ := by
  simpa [norm_mul] using abs_im_le_norm (conj u * e)

/-- The real part of a conjugate product is bounded by the product of the norms. -/
theorem re_conj_mul_le (u e : ℂ) : (conj u * e).re ≤ ‖u‖ * ‖e‖ := by
  simpa [norm_mul] using re_le_norm (conj u * e)

/-- The norm of `1 - conj w * z` is symmetric in `z` and `w`: conjugation swaps the two
expressions and preserves norms. -/
theorem norm_one_sub_conj_mul_comm (z w : ℂ) : ‖1 - conj w * z‖ = ‖1 - conj z * w‖ := by
  rw [← norm_conj]
  simp [mul_comm]

/-- For `‖w‖ = 1`, `1 - conj w * z` has the norm of `z - w`. -/
theorem norm_one_sub_conj_mul {w z : ℂ} (hw : ‖w‖ = 1) : ‖1 - conj w * z‖ = ‖z - w‖ := by
  have h : w * (1 - conj w * z) = w - z := by
    rw [mul_sub, mul_one, ← mul_assoc, mul_conj, normSq_eq_norm_sq, hw]
    simp
  rw [norm_sub_rev z w, ← h, norm_mul, hw, one_mul]

/-- For `‖w‖ = 1` and `‖z‖ ≤ 1`, `1 - conj w * z` has nonnegative real part. -/
theorem re_one_sub_conj_mul_nonneg {w z : ℂ} (hw : ‖w‖ = 1) (hz : ‖z‖ ≤ 1) :
    0 ≤ (1 - conj w * z).re := by
  simpa [hw] using (re_conj_mul_le w z).trans (by simpa [hw] using hz)

/-- For `‖w‖ = 1` and `‖z‖ < 1`, `1 - conj w * z` has positive real part. -/
theorem re_one_sub_conj_mul_pos {w z : ℂ} (hw : ‖w‖ = 1) (hz : ‖z‖ < 1) :
    0 < (1 - conj w * z).re := by
  simpa [hw] using (re_conj_mul_le w z).trans_lt (by simpa [hw] using hz)

/-- For a point `x` of the closed disc of radius `r` and a point `y` outside the open disc, the
conjugate `conj x` is within `3 ‖x - y‖` of the point `r² / y`, the inversion of `y` in the circle
of radius `r` followed by conjugation. -/
theorem norm_conj_sub_sq_div_le {r : ℝ} (x y : ℂ)
    (hx : ‖x‖ ≤ r) (hy : r ≤ ‖y‖) :
    ‖conj x - (r : ℂ)^2/y‖ ≤ 3*‖x - y‖ := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  rcases eq_or_ne y 0 with rfl | hyne
  · have hr0 : r = 0 := le_antisymm (by simpa using hy) hr
    have hx0 : x = 0 := norm_le_zero_iff.mp (hr0 ▸ hx)
    simp [hr0, hx0]
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hyne
  have heq : conj y - (r : ℂ)^2/y = (((‖y‖^2 - r^2 : ℝ) : ℂ))/y := by
    apply (eq_div_iff hyne).mpr
    rw [sub_mul, div_mul_cancel₀ _ hyne, conj_mul', ofReal_sub, ofReal_pow, ofReal_pow]
  have hgap : ‖y‖-r ≤ ‖x - y‖ := by
    have h := norm_le_norm_add_norm_sub x y
    linarith
  have htail : ‖conj y - (r : ℂ)^2/y‖ ≤ 2 * (‖y‖-r) := by
    rw [heq, norm_div, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith : 0 ≤ ‖y‖^2 - r^2)]
    apply (div_le_iff₀ hy0).mpr
    nlinarith
  calc
    _ ≤ ‖conj x - conj y‖ + ‖conj y - (r : ℂ)^2/y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (conj x) (conj y) ((r : ℂ)^2/y)
    _ ≤ ‖x - y‖ + 2 * (‖y‖-r) := by
      rw [← map_sub, norm_conj]
      exact add_le_add le_rfl htail
    _ ≤ _ := by linarith

/-- Dividing by a natural number does not increase the norm, so the point `(a z + b) / M` has
norm at most `‖a‖ C + ‖b‖` when `‖z‖ ≤ C`. For `M = 0` the quotient is `0` by Lean's convention
`x / 0 = 0`. -/
theorem norm_mul_add_div_natCast_le (M : ℕ) (a b : ℂ) {z : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C) :
    ‖(a * z + b) / M‖ ≤ ‖a‖ * C + ‖b‖ := by
  rw [norm_div, Complex.norm_natCast]
  exact (div_nat_le_self_of_nonneg (norm_nonneg _) M).trans
    (norm_add_le_of_le (norm_mul_le_of_le le_rfl hz) le_rfl)

end Complex
