/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
public import TauCeti.AlgebraicGeometry.EllipticCurve.NodePolynomial

import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic

/-!
# Points reducing to the singular point

Let `v` be a valuation on a field `F`, with valuation ring `O`, maximal ideal `𝔪` and residue
field `k`, and let `W` be a Weierstrass curve over `F` with an integral model `W_O` over `O`. When
the reduced curve `W_k` is singular, the points of `W(F)` with nonsingular reduction form the
subgroup `E₀(F)` (`WeierstrassCurve.Affine.nonsingularReduction`). When `F` is complete for a
discrete valuation with perfect residue field and the equation is minimal, the index
`[E(F) : E₀(F)]` is the local index `c_v` that Tate's algorithm computes. This file gives
conditions on the equation under which no point of `W(F)` reduces to the singular point, so that
`E₀(F) = W(F)` and the index is one.

The input is a computation at an integral solution `(x₀, y₀)` of `W_O`. Translating it to the
origin by `x ↦ x + x₀`, `y ↦ y + y₀` gives an equation with `a₆ = 0`, whose `a₃` and `-a₄` are
the values at `(x₀, y₀)` of the two partial derivatives of the Weierstrass polynomial, and whose
discriminant is that of `W`. For such an equation

`Δ = b₂² (a₄² + a₁ a₃ a₄ − a₂ a₃²) − 8 (2 a₄ + a₁ a₃)³ − 27 a₃⁴ + 9 b₂ (2 a₄ + a₁ a₃) a₃²`,

so `Δ` lies in the square of any ideal containing both partial values
(`WeierstrassCurve.Affine.Δ_mem_sq_of_equation`). If `(x₀, y₀)` reduces to
the singular point of `W_k`, both partial values lie in `𝔪`, hence `Δ ∈ 𝔪²`. If moreover the
singular point is a nonsplit node, the tangent form `a₄² + a₁ a₃ a₄ − a₂ a₃²` is anisotropic
modulo `𝔪`, so its value is a unit times the square of `a₃` or of `a₄`; the remaining terms are of
higher order, so `Δ` is a unit times a square. This gives three criteria for `E₀(F) = W(F)`:

* `Δ ∉ 𝔪²`; for a discrete valuation with normalized additive valuation `ord` this is
  `ord(Δ) ≤ 1`, the reduction symbols `I₀` and `I₁`;
* the reduction is a nonsplit node and `v(Δ)` is not the valuation of a square; for a discrete
  valuation this is nonsplit multiplicative reduction of type `Iₙ` with `n = ord(Δ)` odd;
* the reduction is singular at the origin and `a₆ ∉ 𝔪²`; on such an equation with `b₂ ∈ 𝔪` this
  is Tate's test for the reduction symbol `II`.

In each case Tate's algorithm reports the local index `1` (Silverman, *Advanced Topics*, IV.9,
Table 4.1), and the theorems here show that `E₀(F) = W(F)` there, for an arbitrary valuation and
without completeness.

When the reduction is singular at the origin, that is `a₃, a₄, a₆ ∈ 𝔪`, the points outside `E₀(F)`
are the affine points `(x, y)` with `x, y ∈ 𝔪`, since the singular point of `W_k` is unique.

## Main results

* `WeierstrassCurve.Δ_mem_maximalIdeal_sq_of_isSingular`: over a local ring, a solution
  reducing to a singular point forces `Δ ∈ 𝔪²`.
* `WeierstrassCurve.exists_associated_sq_Δ_of_isSingular`: over a valuation ring, a solution
  reducing to a nonsplit node forces `Δ` to be a unit times a square.
* `WeierstrassCurve.mem_maximalIdeal_of_isSingular`: over a local ring, if the reduction is
  singular at the origin, a point reducing to a singular point has coordinates in `𝔪`.
* `WeierstrassCurve.a₆_mem_maximalIdeal_sq_of_isSingular`: over a local ring, if the
  reduction is singular at the origin, a solution reducing to it forces `a₆ ∈ 𝔪²`.
* `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_forall_not_isSingular`: if no integral
  solution reduces to a singular point, then `E₀(F) = W(F)`.
* `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_forall_mem_maximalIdeal_not_equation`:
  if the reduction is singular at the origin and no integral solution has both coordinates in
  `𝔪`, then `E₀(F) = W(F)`.
* `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_Δ_notMem`,
  `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_not_splits` and
  `WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_a₆_notMem`: the three criteria above.
* `WeierstrassCurve.Affine.some_notMem_nonsingularReduction_iff`: when the reduction is singular
  at the origin, an affine point has singular reduction exactly when both of its coordinates lie in
  the maximal ideal, and `WeierstrassCurve.Affine.exists_eq_some_of_notMem_nonsingularReduction`
  writes such a point with integral coordinates.
* `WeierstrassCurve.Affine.some_coe_notMem_nonsingularReduction_iff`: the same criterion for
  points with coordinates in the valuation ring.
* `WeierstrassCurve.Affine.exists_chord_of_add_notMem_nonsingularReduction`: the identities
  satisfied by the chord through two points whose sum has singular reduction.
* `WeierstrassCurve.Affine.two_nsmul_notMem_of_slope_mem`: twice a point with singular reduction
  whose tangent slope lies in the maximal ideal has singular reduction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2 and VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **A solution reducing to a singular point forces `Δ ∈ 𝔪²`.** Over a local ring, if an integral
solution `(x, y)` of the Weierstrass equation reduces to a singular point of the reduced curve,
then the discriminant lies in the square of the maximal ideal. -/
theorem Δ_mem_maximalIdeal_sq_of_isSingular (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y)
    (hs : (W.map (residue R)).toAffine.IsSingular (residue R x) (residue R y)) :
    W.Δ ∈ maximalIdeal R ^ 2 :=
  W.toAffine.Δ_mem_sq_of_equation h hs.evalEval_polynomialX_mem_maximalIdeal
    hs.evalEval_polynomialY_mem_maximalIdeal

/-- **A point reducing to the singular point at the origin has coordinates in the maximal
ideal.** Over a local ring, suppose that `a₃`, `a₄` and `a₆` lie in the maximal ideal, so that the
reduced curve is singular at the origin. If `(x, y)` reduces to a singular point of the reduced
curve, that point is the origin, since the reduced curve has only one singular point, so `x` and `y`
lie in the maximal ideal. -/
theorem mem_maximalIdeal_of_isSingular (W : WeierstrassCurve R)
    (h₃ : W.a₃ ∈ maximalIdeal R) (h₄ : W.a₄ ∈ maximalIdeal R) (h₆ : W.a₆ ∈ maximalIdeal R)
    {x y : R} (hs : (W.map (residue R)).toAffine.IsSingular (residue R x) (residue R y)) :
    x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R := by
  have h0 : (W.map (residue R)).toAffine.IsSingular 0 0 := by
    simp [(residue_eq_zero_iff _).mpr h₃, (residue_eq_zero_iff _).mpr h₄,
      (residue_eq_zero_iff _).mpr h₆]
  obtain ⟨hx, hy⟩ := Affine.eq_of_isSingular_of_isSingular hs h0
  exact ⟨(residue_eq_zero_iff x).mp hx, (residue_eq_zero_iff y).mp hy⟩

/-- **A solution reducing to the singular point at the origin forces `a₆ ∈ 𝔪²`.** Over a local
ring, suppose that `a₃`, `a₄` and `a₆` lie in the maximal ideal, so that the reduced curve is
singular at the origin. If an integral solution `(x, y)` reduces to a singular point, that point is
the origin, so `x` and `y` lie in the maximal ideal, and then `a₆` lies in its square. -/
theorem a₆_mem_maximalIdeal_sq_of_isSingular (W : WeierstrassCurve R)
    (h₃ : W.a₃ ∈ maximalIdeal R) (h₄ : W.a₄ ∈ maximalIdeal R) (h₆ : W.a₆ ∈ maximalIdeal R)
    {x y : R} (h : W.toAffine.Equation x y)
    (hs : (W.map (residue R)).toAffine.IsSingular (residue R x) (residue R y)) :
    W.a₆ ∈ maximalIdeal R ^ 2 := by
  obtain ⟨hx, hy⟩ := W.mem_maximalIdeal_of_isSingular h₃ h₄ h₆ hs
  rw [Affine.equation_iff'] at h
  have ha₆ : W.a₆ = y * y + W.a₁ * (x * y) + W.a₃ * y -
      ((x * x) * x + (W.a₂ * x) * x + W.a₄ * x) := by
    linear_combination -h
  rw [ha₆, pow_two]
  refine sub_mem (add_mem (add_mem ?_ ?_) ?_) (add_mem (add_mem ?_ ?_) ?_)
  · exact Ideal.mul_mem_mul hy hy
  · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hx hy)
  · exact Ideal.mul_mem_mul h₃ hy
  · exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hx) hx
  · exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hx) hx
  · exact Ideal.mul_mem_mul h₄ hx

/-! ### Solutions reducing to a nonsplit node -/

section ValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-- On an equation through the origin whose reduction is a node at the origin with no rational
tangent direction, the discriminant is a unit times the square of `a₃` or of `a₄`. -/
private theorem exists_associated_sq_Δ_of_a₆_eq_zero (W : WeierstrassCurve R) (h₆ : W.a₆ = 0)
    (h₃ : W.a₃ ∈ maximalIdeal R) (h₄ : W.a₄ ∈ maximalIdeal R) (hb₂ : IsUnit W.b₂)
    (hroot : ∀ t : ResidueField R, t ^ 2 + residue R W.a₁ * t - residue R W.a₂ ≠ 0) :
    ∃ m : R, Associated (m ^ 2) W.Δ := by
  have hb : residue R W.b₂ ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr hb₂
  -- in a valuation ring one of `a₃` and `a₄` divides the other
  obtain ⟨c, hc | hc⟩ := PreValuationRing.cond W.a₄ W.a₃
  · refine ⟨W.a₄, ?_⟩
    have hΔ : W.Δ = W.a₄ ^ 2 * (W.b₂ ^ 2 * (1 + W.a₁ * c - W.a₂ * c ^ 2) + W.a₄ *
        (-8 * (2 + W.a₁ * c) ^ 3 - 27 * c ^ 4 * W.a₄ + 9 * W.b₂ * (2 + W.a₁ * c) * c ^ 2)) := by
      simp only [Δ, b₄, b₆, b₈, h₆, ← hc]
      ring
    -- the value of the tangent form at `(1, c)` is a unit, since the form is anisotropic
    have hq : 1 + residue R W.a₁ * residue R c - residue R W.a₂ * residue R c ^ 2 ≠ 0 := by
      intro h0
      by_cases hc0 : residue R c = 0
      · simp [hc0] at h0
      · refine hroot (residue R c)⁻¹ ?_
        rw [show (residue R c)⁻¹ ^ 2 + residue R W.a₁ * (residue R c)⁻¹ - residue R W.a₂ =
          (residue R c)⁻¹ ^ 2 * (1 + residue R W.a₁ * residue R c -
            residue R W.a₂ * residue R c ^ 2) by field_simp, h0, mul_zero]
    have hu : IsUnit (W.b₂ ^ 2 * (1 + W.a₁ * c - W.a₂ * c ^ 2) + W.a₄ *
        (-8 * (2 + W.a₁ * c) ^ 3 - 27 * c ^ 4 * W.a₄ + 9 * W.b₂ * (2 + W.a₁ * c) * c ^ 2)) := by
      rw [← residue_ne_zero_iff_isUnit]
      simpa [(residue_eq_zero_iff _).mpr h₄] using mul_ne_zero (pow_ne_zero 2 hb) hq
    exact ⟨hu.unit, by rw [IsUnit.unit_spec, hΔ]⟩
  · refine ⟨W.a₃, ?_⟩
    have hΔ : W.Δ = W.a₃ ^ 2 * (W.b₂ ^ 2 * (c ^ 2 + W.a₁ * c - W.a₂) +
        W.a₃ * (-8 * (2 * c + W.a₁) ^ 3 - 27 * W.a₃ + 9 * W.b₂ * (2 * c + W.a₁))) := by
      simp only [Δ, b₄, b₆, b₈, h₆, ← hc]
      ring
    have hu : IsUnit (W.b₂ ^ 2 * (c ^ 2 + W.a₁ * c - W.a₂) +
        W.a₃ * (-8 * (2 * c + W.a₁) ^ 3 - 27 * W.a₃ + 9 * W.b₂ * (2 * c + W.a₁))) := by
      rw [← residue_ne_zero_iff_isUnit]
      simpa [(residue_eq_zero_iff _).mpr h₃] using
        mul_ne_zero (pow_ne_zero 2 hb) (hroot (residue R c))
    exact ⟨hu.unit, by rw [IsUnit.unit_spec, hΔ]⟩

/-- **A solution reducing to a nonsplit node forces `Δ` to be a unit times a square.** Over a
valuation ring, suppose that `c₄` is a unit and that the node polynomial
(`WeierstrassCurve.nodePolynomial`) does not split over the residue field, so that a singular point
of the reduced curve is a node whose tangent directions are not rational. If an integral solution
`(x, y)` reduces to a singular point, then `Δ` is associated to the square of an element; for a
discrete valuation with normalized additive valuation `ord`, `ord(Δ)` is even. -/
theorem exists_associated_sq_Δ_of_isSingular (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y)
    (hs : (W.map (residue R)).toAffine.IsSingular (residue R x) (residue R y))
    (hc₄ : residue R W.c₄ ≠ 0) (hn : ¬ (W.nodePolynomial.map (residue R)).Splits) :
    ∃ m : R, Associated (m ^ 2) W.Δ := by
  set W' := VariableChange.mk 1 x 0 y • W
  have hX := hs.evalEval_polynomialX_mem_maximalIdeal
  have hY := hs.evalEval_polynomialY_mem_maximalIdeal
  have h₆ : W'.a₆ = 0 := variableChange_translate_a₆_of_equation W h
  have h₃ : W'.a₃ ∈ maximalIdeal R := variableChange_translate_a₃ W x y ▸ hY
  have h₄ : W'.a₄ ∈ maximalIdeal R :=
    variableChange_translate_a₄ W x y ▸ (maximalIdeal R).neg_mem hX
  -- the translated reduction is singular at the origin
  have h0 : (W'.map (residue R)).toAffine.IsSingular 0 0 := by
    simp [h₆, (residue_eq_zero_iff _).mpr h₃, (residue_eq_zero_iff _).mpr h₄]
  -- there `c₄ = b₂²`, so `b₂` is a unit
  have hb₂ : IsUnit W'.b₂ := by
    have hc := Affine.c₄_eq_b₂_sq_of_isSingular_zero h0
    rw [map_c₄, map_b₂, variableChange_translate_c₄] at hc
    rw [← residue_ne_zero_iff_isUnit]
    exact fun hb ↦ hc₄ (by rw [hc, hb, zero_pow two_ne_zero])
  -- a rational root of the tangent quadratic would split the node polynomial
  have hroot : ∀ t : ResidueField R, t ^ 2 + residue R W'.a₁ * t - residue R W'.a₂ ≠ 0 := by
    intro t ht
    refine hn ?_
    rw [← W.splits_variableChange_nodePolynomial_map_iff (residue R) (VariableChange.mk 1 x 0 y),
      ← map_nodePolynomial, nodePolynomial_eq_of_isSingular_zero _ h0, map_a₁, map_a₂]
    have hfac : C 1 * X ^ 2 + C (residue R W'.a₁) * X + C (-residue R W'.a₂) =
        (X - C t) * (X - C (-residue R W'.a₁ - t)) := by
      rw [show -residue R W'.a₂ = t * (-residue R W'.a₁ - t) by linear_combination ht, C_mul,
        map_sub, map_neg, C_1]
      ring
    rw [hfac]
    exact (Splits.C _).mul ((Splits.X_sub_C _).mul (Splits.X_sub_C _))
  obtain ⟨m, hm⟩ := W'.exists_associated_sq_Δ_of_a₆_eq_zero h₆ h₃ h₄ hb₂ hroot
  exact ⟨m, variableChange_translate_Δ W x y ▸ hm⟩

end ValuationRing

/-! ### Criteria for every point to have nonsingular reduction -/

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

/-- **If no integral solution reduces to a singular point, every point has nonsingular
reduction**: `E₀(F) = W(F)`. Points whose `x`-coordinate has a pole reduce to the point at
infinity, and every other affine point is an integral solution of the integral model. -/
theorem nonsingularReduction_eq_top_of_forall_not_isSingular
    (h : ∀ x y : v.valuationSubring, (integralModel v.valuationSubring W).toAffine.Equation x y →
      ¬ ((integralModel v.valuationSubring W).map (residue v.valuationSubring)).toAffine.IsSingular
        (residue _ x) (residue _ y)) :
    W.nonsingularReduction v = ⊤ := by
  refine eq_top_iff.mpr fun P _ ↦ ?_
  rcases P with _ | ⟨x, y, hxy⟩
  · exact zero_mem _
  rcases le_or_gt (v x) 1 with hx | hx
  · rw [some_mem_nonsingularReduction_iff v hxy hx]
    set x₀ : v.valuationSubring := ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩
    set y₀ : v.valuationSubring := ⟨y, (v.mem_valuationSubring_iff y).mpr
      (valuation_y_le_one_of_valuation_x_le_one v hxy.left hx)⟩
    have hE : (integralModel v.valuationSubring W).toAffine.Equation x₀ y₀ :=
      (equation_integralModel_iff v).2 hxy.left
    by_contra hn
    exact h x₀ y₀ hE (isSingular_iff_equation_and_not_nonsingular.mpr ⟨hE.map _, hn⟩)
  · exact mem_nonsingularReduction_of_one_lt v (by rwa [Point.xCoord_some])

/-- **If `Δ ∉ 𝔪²`, every point has nonsingular reduction**: `E₀(F) = W(F)`. For a discrete
valuation with normalized additive valuation `ord` the hypothesis is `ord(Δ) ≤ 1`, which on a
minimal equation is the reduction symbol `I₀` or `I₁`. -/
theorem nonsingularReduction_eq_top_of_Δ_notMem
    (h : (integralModel v.valuationSubring W).Δ ∉ maximalIdeal v.valuationSubring ^ 2) :
    W.nonsingularReduction v = ⊤ :=
  nonsingularReduction_eq_top_of_forall_not_isSingular v fun _ _ hE hs ↦
    h (Δ_mem_maximalIdeal_sq_of_isSingular _ hE hs)

/-- **If the reduction is singular at the origin and no integral solution lies in `𝔪 × 𝔪`, every
point has nonsingular reduction**: `E₀(F) = W(F)`. Here `a₃`, `a₄` and `a₆` of the integral model
lie in the maximal ideal, so that the singular point of the reduced curve is the origin, and the
points reducing to it are the integral solutions with both coordinates in the maximal ideal. -/
theorem nonsingularReduction_eq_top_of_forall_mem_maximalIdeal_not_equation
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    (h : ∀ x y : v.valuationSubring, x ∈ maximalIdeal v.valuationSubring →
      y ∈ maximalIdeal v.valuationSubring →
        ¬ (integralModel v.valuationSubring W).toAffine.Equation x y) :
    W.nonsingularReduction v = ⊤ :=
  nonsingularReduction_eq_top_of_forall_not_isSingular v fun x y hE hs ↦
    have hxy := mem_maximalIdeal_of_isSingular _ h₃ h₄ h₆ hs
    h x y hxy.1 hxy.2 hE

/-- **At a nonsplit node with `v(Δ)` not a square, every point has nonsingular reduction**:
`E₀(F) = W(F)`. Here `c₄` of the integral model is a unit and its node polynomial
(`WeierstrassCurve.nodePolynomial`) does not split over the residue field, so the singular point
of the reduced curve, if any, is a node without rational tangent directions. For a discrete
valuation, on a minimal equation, this is nonsplit multiplicative reduction of type `Iₙ` with `n`
odd. -/
theorem nonsingularReduction_eq_top_of_not_splits
    (hc₄ : residue _ (integralModel v.valuationSubring W).c₄ ≠ 0)
    (hn : ¬ ((integralModel v.valuationSubring W).nodePolynomial.map (residue _)).Splits)
    (hΔ : ∀ z : F, v W.Δ ≠ v z ^ 2) :
    W.nonsingularReduction v = ⊤ :=
  nonsingularReduction_eq_top_of_forall_not_isSingular v fun _ _ hE hs ↦ by
    obtain ⟨m, u, hu⟩ := exists_associated_sq_Δ_of_isSingular _ hE hs hc₄ hn
    refine hΔ m ?_
    rw [← integralModel_Δ_eq v.valuationSubring W, ← hu, map_mul, map_pow, map_mul, map_pow,
      (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one.mp u.isUnit, mul_one,
      ValuationSubring.algebraMap_apply]

/-- **If the reduction is singular at the origin and `a₆ ∉ 𝔪²`, every point has nonsingular
reduction**: `E₀(F) = W(F)`. Here `a₃`, `a₄` and `a₆` of the integral model lie in the maximal
ideal, so that the reduced curve is singular at the origin. For a discrete valuation, on an
equation with `b₂ ∈ 𝔪` as well, these are the conditions at which Tate's algorithm stops with
the symbol `II`. -/
theorem nonsingularReduction_eq_top_of_a₆_notMem
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    (h : (integralModel v.valuationSubring W).a₆ ∉ maximalIdeal v.valuationSubring ^ 2) :
    W.nonsingularReduction v = ⊤ :=
  nonsingularReduction_eq_top_of_forall_not_isSingular v fun _ _ hE hs ↦
    h (a₆_mem_maximalIdeal_sq_of_isSingular _ h₃ h₄ h₆ hE hs)

/-! ### Points with singular reduction -/

-- `↓`: tried before `simp` rewrites the membership inside `∉` with
-- `mem_nonsingularReduction_iff`, after which this left-hand side no longer matches.
/-- **When the reduction is singular at the origin, the points with singular reduction are the
affine points with both coordinates in the maximal ideal.** Here `a₃`, `a₄` and `a₆` of the
integral model lie in the maximal ideal, and `(x, y)` lies outside `E₀(F)` exactly when `v x < 1`
and `v y < 1`. -/
@[simp↓]
theorem some_notMem_nonsingularReduction_iff
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {x y : F} (h : W.Nonsingular x y) :
    Point.some x y h ∉ W.nonsingularReduction v ↔ v x < 1 ∧ v y < 1 := by
  have h0 : ((integralModel v.valuationSubring W).map (residue _)).toAffine.IsSingular 0 0 :=
    (isSingular_zero _).2 <| by simp [(residue_eq_zero_iff _).2, h₃, h₄, h₆]
  constructor
  · intro hn
    have hx : v x ≤ 1 := not_lt.1 fun hx ↦
      hn (mem_nonsingularReduction_of_one_lt v (by rwa [Point.xCoord_some]))
    rw [some_mem_nonsingularReduction_iff v h hx] at hn
    have hy := valuation_y_le_one_of_valuation_x_le_one v h.left hx
    have hE := ((equation_integralModel_iff v (x := ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
      (y := ⟨y, (v.mem_valuationSubring_iff y).mpr hy⟩)).2 h.left).map (residue _)
    obtain ⟨hx0, hy0⟩ := eq_of_isSingular_of_isSingular
      (isSingular_iff_equation_and_not_nonsingular.2 ⟨hE, hn⟩) h0
    exact ⟨(Valuation.mem_maximalIdeal_iff (v := v)).1 ((residue_eq_zero_iff _).1 hx0),
      (Valuation.mem_maximalIdeal_iff (v := v)).1 ((residue_eq_zero_iff _).1 hy0)⟩
  · rintro ⟨hx, hy⟩ hm
    rw [some_mem_nonsingularReduction_iff v h hx.le,
      (residue_eq_zero_iff _).2 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hx),
      (residue_eq_zero_iff _).2 ((Valuation.mem_maximalIdeal_iff (v := v)).2 hy)] at hm
    exact (isSingular_iff_equation_and_not_nonsingular.1 h0).2 hm

/-- **When the reduction is singular at the origin, a point with integral coordinates has singular
reduction exactly when both coordinates lie in the maximal ideal.** This is
`WeierstrassCurve.Affine.some_notMem_nonsingularReduction_iff` for coordinates in the valuation
ring. -/
theorem some_coe_notMem_nonsingularReduction_iff
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {x y : v.valuationSubring} (h : W.Nonsingular (x : F) (y : F)) :
    Point.some _ _ h ∉ W.nonsingularReduction v ↔
      x ∈ maximalIdeal v.valuationSubring ∧ y ∈ maximalIdeal v.valuationSubring := by
  rw [some_notMem_nonsingularReduction_iff v h₃ h₄ h₆, Valuation.mem_maximalIdeal_iff,
    Valuation.mem_maximalIdeal_iff]

/-- **When the reduction is singular at the origin, a point with singular reduction is an affine
point whose coordinates lie in the maximal ideal of the valuation ring.** Here `a₃`, `a₄` and `a₆`
of the integral model lie in the maximal ideal. -/
theorem exists_eq_some_of_notMem_nonsingularReduction
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {P : W.Point} (hP : P ∉ W.nonsingularReduction v) :
    ∃ (x y : v.valuationSubring) (h : W.Nonsingular x y), P = .some _ _ h ∧
      x ∈ maximalIdeal v.valuationSubring ∧ y ∈ maximalIdeal v.valuationSubring := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd (zero_mem _) hP
  obtain ⟨hx, hy⟩ := (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ h).1 hP
  exact ⟨⟨x, (v.mem_valuationSubring_iff x).2 hx.le⟩, ⟨y, (v.mem_valuationSubring_iff y).2 hy.le⟩,
    h, rfl, (Valuation.mem_maximalIdeal_iff (v := v)).2 hx,
    (Valuation.mem_maximalIdeal_iff (v := v)).2 hy⟩

/-- **The chord through two points whose sum has singular reduction.** Let `(x₁, y₁)` and
`(x₂, y₂)` be points of `W(F)` with integral coordinates, at a reduction singular at the origin, and
suppose that their sum has singular reduction. Then the sum is an affine point `(x₃, y₃)` with
`x₃, y₃ ∈ 𝔪`, and the slope `ℓ = W.slope x₁ x₂ y₁ y₂` of the line through the two points is
integral, with

* `ℓ² + a₁ ℓ − a₂ = x₁ + x₂ + x₃`,
* `y₁ − y₂ = ℓ (x₁ − x₂)`,
* `a₄ − a₃ ℓ − (2 ℓ + a₁) (y₁ − ℓ x₁) = x₁ x₂ + x₁ x₃ + x₂ x₃`, and
* `x₁ x₂ x₃ = (y₁ − ℓ x₁)² + a₃ (y₁ − ℓ x₁) − a₆`.

All but the second identity compare coefficients in the Weierstrass cubic restricted to the line
`y = ℓ (x − x₁) + y₁`, whose roots are `x₁`, `x₂` and `x₃`. The coefficients are those of the
integral model. -/
theorem exists_chord_of_add_notMem_nonsingularReduction
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {x₁ y₁ x₂ y₂ : v.valuationSubring} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hPQ : Point.some _ _ h₁ + Point.some _ _ h₂ ∉ W.nonsingularReduction v) :
    ∃ (x₃ y₃ ℓ : v.valuationSubring) (h : W.Nonsingular x₃ y₃),
      Point.some _ _ h₁ + Point.some _ _ h₂ = .some _ _ h ∧ (ℓ : F) = W.slope x₁ x₂ y₁ y₂ ∧
      x₃ ∈ maximalIdeal v.valuationSubring ∧ y₃ ∈ maximalIdeal v.valuationSubring ∧
      ℓ ^ 2 + (integralModel v.valuationSubring W).a₁ * ℓ -
        (integralModel v.valuationSubring W).a₂ = x₁ + x₂ + x₃ ∧
      y₁ - y₂ = ℓ * (x₁ - x₂) ∧
      (integralModel v.valuationSubring W).a₄ - (integralModel v.valuationSubring W).a₃ * ℓ -
        (2 * ℓ + (integralModel v.valuationSubring W).a₁) * (y₁ - ℓ * x₁) =
          x₁ * x₂ + x₁ * x₃ + x₂ * x₃ ∧
      x₁ * x₂ * x₃ = (y₁ - ℓ * x₁) ^ 2 + (integralModel v.valuationSubring W).a₃ * (y₁ - ℓ * x₁) -
        (integralModel v.valuationSubring W).a₆ := by
  have hxy : ¬((x₁ : F) = x₂ ∧ (y₁ : F) = W.negY x₂ y₂) := by
    rintro ⟨hx, hy⟩
    exact hPQ (by rw [Point.add_of_Y_eq hx hy]; exact zero_mem _)
  rw [Point.add_some hxy] at hPQ ⊢
  obtain ⟨hx₃, hy₃⟩ := (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ _).1 hPQ
  set ℓ := W.slope (x₁ : F) x₂ y₁ y₂
  have hO {z : F} (hz : v z < 1) : z ∈ v.valuationSubring :=
    (v.mem_valuationSubring_iff z).2 hz.le
  have hint (z : v.valuationSubring) : v (z : F) ≤ 1 := (v.mem_valuationSubring_iff _).1 z.2
  have hℓ : ℓ ∈ v.valuationSubring := (v.mem_valuationSubring_iff ℓ).2
    (valuation_le_one_of_valuation_addX_le_one v (hint x₁) (hint x₂) hx₃.le)
  -- the coefficients of `X` and `1` in `W(X, ℓ (X − x₁) + y₁) = −(X − x₁) (X − x₂) (X − x₃)`
  have key := W.addPolynomial_slope h₁.left h₂.left hxy
  rw [addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_inj] at key
  have hc : 2 * (x₁ : F) * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ + (-W.a₁ * y₁ + W.a₄) =
      x₁ * x₂ + x₁ * W.addX x₁ x₂ ℓ + x₂ * W.addX x₁ x₂ ℓ :=
    congrArg Cubic.c ((Cubic.toPoly_injective _ _).1 key)
  have hd := congrArg Cubic.d ((Cubic.toPoly_injective _ _).1 key)
  -- the line passes through both points; when `x₁ = x₂` the two points are equal
  have hL : (y₁ : F) - y₂ = ℓ * (x₁ - x₂) := by
    by_cases hx : (x₁ : F) = x₂
    · rw [Y_eq_of_Y_ne h₁.left h₂.left hx fun hy ↦ hxy ⟨hx, hy⟩, hx]
      ring
    · have hℓ' : ℓ = (y₁ - y₂) / (x₁ - x₂) := slope_of_X_ne hx
      rw [hℓ', div_mul_cancel₀ _ (sub_ne_zero.2 hx)]
  have h2 : ((2 : v.valuationSubring) : F) = 2 := by
    simpa using map_ofNat (algebraMap v.valuationSubring F) 2
  refine ⟨⟨_, hO hx₃⟩, ⟨_, hO hy₃⟩, ⟨ℓ, hℓ⟩, nonsingular_add h₁ h₂ hxy, rfl, rfl,
    (Valuation.mem_maximalIdeal_iff (v := v)).2 hx₃,
    (Valuation.mem_maximalIdeal_iff (v := v)).2 hy₃, ?_, ?_, ?_, ?_⟩ <;> apply Subtype.ext <;>
    push_cast
  · simp only [addX, ← integralModel_a₁_eq v.valuationSubring W,
      ← integralModel_a₂_eq v.valuationSubring W, ValuationSubring.algebraMap_apply]
    ring
  · exact hL
  · simp only [← integralModel_a₁_eq v.valuationSubring W,
      ← integralModel_a₃_eq v.valuationSubring W, ← integralModel_a₄_eq v.valuationSubring W,
      ValuationSubring.algebraMap_apply] at hc
    rw [h2]
    linear_combination hc
  · simp only [← integralModel_a₃_eq v.valuationSubring W,
      ← integralModel_a₆_eq v.valuationSubring W, ValuationSubring.algebraMap_apply] at hd
    linear_combination hd

/-- **Twice a point whose tangent slope lies in `𝔪` has singular reduction.** Here the reduction is
singular at the origin and `a₂ ∈ 𝔪` as well. If `(x, y)` has integral coordinates in `𝔪` and the
tangent there has slope `ℓ ∈ 𝔪`, that is `ℓ (2 y + a₁ x + a₃) = 3 x² + 2 a₂ x + a₄ − a₁ y` with
`2 y + a₁ x + a₃ ≠ 0`, then both coordinates of twice the point lie in `𝔪`. -/
theorem two_nsmul_notMem_of_slope_mem
    (h₂ : (integralModel v.valuationSubring W).a₂ ∈ maximalIdeal v.valuationSubring)
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    {x y ℓ : v.valuationSubring} {hxy : W.Nonsingular x y}
    (hx : x ∈ maximalIdeal v.valuationSubring) (hy : y ∈ maximalIdeal v.valuationSubring)
    (hℓ : ℓ ∈ maximalIdeal v.valuationSubring)
    (hne : 2 * y + (integralModel v.valuationSubring W).a₁ * x +
      (integralModel v.valuationSubring W).a₃ ≠ 0)
    (hslope : ℓ * (2 * y + (integralModel v.valuationSubring W).a₁ * x +
      (integralModel v.valuationSubring W).a₃) = 3 * x ^ 2 +
        2 * (integralModel v.valuationSubring W).a₂ * x + (integralModel v.valuationSubring W).a₄ -
          (integralModel v.valuationSubring W).a₁ * y) :
    2 • Point.some _ _ hxy ∉ W.nonsingularReduction v := by
  set Wo := integralModel v.valuationSubring W
  have hy' : (y : F) ≠ W.negY x y := by
    rw [← coe_negY_integralModel, Ne, Subtype.coe_inj]
    intro h
    exact hne (by rw [negY] at h; linear_combination h)
  have h2 : ((2 : v.valuationSubring) : F) = 2 := by
    simpa using map_ofNat (algebraMap v.valuationSubring F) 2
  have h3 : ((3 : v.valuationSubring) : F) = 3 := by
    simpa using map_ofNat (algebraMap v.valuationSubring F) 3
  have hslopeF : W.slope (x : F) x y y = ℓ := by
    rw [slope_of_Y_ne rfl hy', div_eq_iff (sub_ne_zero.2 hy')]
    have := congrArg ((↑) : v.valuationSubring → F) hslope
    push_cast at this
    rw [h2, h3] at this
    simp only [negY, ← integralModel_a₁_eq v.valuationSubring W,
      ← integralModel_a₂_eq v.valuationSubring W, ← integralModel_a₃_eq v.valuationSubring W,
      ← integralModel_a₄_eq v.valuationSubring W, ValuationSubring.algebraMap_apply]
    linear_combination -this
  have hx₃ : Wo.toAffine.addX x x ℓ ∈ maximalIdeal v.valuationSubring :=
    sub_mem (sub_mem (sub_mem (add_mem (Ideal.pow_mem_of_mem _ hℓ 2 two_pos)
      (Ideal.mul_mem_left _ _ hℓ)) h₂) hx) hx
  have hy₃ : Wo.toAffine.addY x x y ℓ ∈ maximalIdeal v.valuationSubring :=
    sub_mem (sub_mem (neg_mem (add_mem (Ideal.mul_mem_right _ _ hℓ) hy))
      (Ideal.mul_mem_left _ _ hx₃)) h₃
  -- the coordinates of `2 P` are the images of those computed in the integral model
  rw [two_nsmul, Point.add_self_of_Y_ne hy', some_notMem_nonsingularReduction_iff v h₃ h₄ h₆,
    hslopeF, ← coe_addX_integralModel, ← coe_addY_integralModel]
  exact ⟨(Valuation.mem_maximalIdeal_iff (v := v)).1 hx₃,
    (Valuation.mem_maximalIdeal_iff (v := v)).1 hy₃⟩

end Affine

end WeierstrassCurve

end
