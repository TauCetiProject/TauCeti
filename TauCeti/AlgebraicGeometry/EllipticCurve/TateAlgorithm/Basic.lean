/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic

/-!
# Tate's algorithm: the singular point at the origin

Tate's algorithm reads the reduction type of a minimal Weierstrass equation over a discrete
valuation ring `R`, with uniformiser `π` and perfect residue field `k`, off a sequence of changes of
variables defined over `R` and divisibility tests on the coefficients. This file contains its first
two steps, from whose normal form every later step starts.

Step 1 tests whether `π ∣ Δ`: the reduction is good exactly when it does not
(`WeierstrassCurve.reduction_Δ_eq_zero_iff`). Otherwise the reduced curve is singular, and its
singular point is `k`-rational because `k` is perfect
(`WeierstrassCurve.Affine.exists_isSingular_of_Δ_eq_zero`). Step 2 lifts that point to `R` and
translates it to the origin by `x ↦ x + r`, `y ↦ y + t`. Afterwards `π` divides `a₃`, `a₄` and
`a₆`, so the reduced equation reads `y² + a₁ x y = x³ + a₂ x²` and has `c₄ = b₂²`. On such an
equation:

* the reduction is multiplicative exactly when `π ∤ b₂`, and additive exactly when `π ∣ b₂`;
* a multiplicative reduction is split exactly when the tangent quadratic `T² + a₁ T − a₂` splits
  over `k`, its roots being the slopes of the two tangent lines at the node.

Every reduction type is invariant under changes of variables defined over `R`
(`WeierstrassCurve.hasMultiplicativeReduction_baseChange_smul_iff` and its companions), so these
tests decide the reduction type of the equation one started from.

Perfectness of `k` is used only to find the singular point. Over the imperfect field `𝔽₃(s)` the
cubic `y² = x³ − s` is singular only at `(s^{1/3}, 0)`, which is not rational.

## Main results

* `WeierstrassCurve.map_residue_isSingular_zero_iff`: the reduction of an integral equation over a
  local ring is singular at the origin exactly when `a₆`, `a₄` and `a₃` lie in the maximal ideal.
* `WeierstrassCurve.exists_map_residue_variableChange_isSingular_zero`: over a local ring with
  perfect residue field, an integral equation whose discriminant lies in the maximal ideal is
  translated over `R` to one whose reduction is singular at the origin.
* `WeierstrassCurve.exists_reduction_baseChange_smul_isSingular_zero`: a minimal equation with bad
  reduction is translated over `R` to a minimal equation whose reduction is singular at the
  origin.
* `WeierstrassCurve.hasMultiplicativeReduction_iff_reduction_b₂_ne_zero` and
  `WeierstrassCurve.hasAdditiveReduction_iff_reduction_b₂_eq_zero`: on a minimal equation whose
  reduction is singular at the origin, the reduction is multiplicative when `π ∤ b₂` and additive
  when `π ∣ b₂`.
* `WeierstrassCurve.hasSplitMultiplicativeReduction_iff_reduction_b₂_ne_zero_and_splits`: on such
  an equation, the reduction is split multiplicative exactly when `π ∤ b₂` and `T² + a₁ T − a₂`
  splits over the residue field.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9,
  Steps 1 and 2 of Tate's algorithm.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing Polynomial

section LocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **The reduction of an integral equation is singular at the origin exactly when `a₆`, `a₄` and
`a₃` lie in the maximal ideal**, which is the normal form Step 2 of Tate's algorithm produces. -/
theorem map_residue_isSingular_zero_iff (W : WeierstrassCurve R) :
    (W.map (residue R)).toAffine.IsSingular 0 0 ↔
      W.a₆ ∈ maximalIdeal R ∧ W.a₄ ∈ maximalIdeal R ∧ W.a₃ ∈ maximalIdeal R := by
  simp [residue_eq_zero_iff]

/-- **Tate's algorithm, Step 2.** Over a local ring with perfect residue field, an integral
Weierstrass equation whose discriminant lies in the maximal ideal is carried by a translation
`x ↦ x + r`, `y ↦ y + t` with `r, t ∈ R` to an equation whose reduction is singular at the origin,
that is, whose `a₃`, `a₄` and `a₆` lie in the maximal ideal (`map_residue_isSingular_zero_iff`).
The translation lifts the singular point of the reduction, which is rational over the residue field
because that field is perfect. -/
theorem exists_map_residue_variableChange_isSingular_zero [PerfectField (ResidueField R)]
    (W : WeierstrassCurve R) (hΔ : W.Δ ∈ maximalIdeal R) :
    ∃ r t : R, ((VariableChange.mk 1 r 0 t • W).map (residue R)).toAffine.IsSingular 0 0 := by
  obtain ⟨x, y, h⟩ := Affine.exists_isSingular_of_Δ_eq_zero (W.map (residue R)).toAffine
    (by rwa [toAffine, map_Δ, residue_eq_zero_iff])
  obtain ⟨r, rfl⟩ := residue_surjective x
  obtain ⟨t, rfl⟩ := residue_surjective y
  refine ⟨r, t, ?_⟩
  have hC : (VariableChange.mk 1 r 0 t).map (residue R) =
      VariableChange.mk 1 (residue R r) 0 (residue R t) := by
    ext <;> simp [VariableChange.map]
  rw [← map_variableChange, hC]
  exact (Affine.isSingular_iff_variableChange _ _ _).1 h

end LocalRing

section DiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve K}

/-- **Tate's algorithm, Step 2, for a minimal equation.** Over a discrete valuation ring with
perfect residue field, a minimal Weierstrass equation with bad reduction is carried by a translation
`x ↦ x + r`, `y ↦ y + t` with `r, t ∈ R` to a minimal equation whose reduction is singular at the
origin. The translated equation has the same reduction type
(`hasMultiplicativeReduction_baseChange_smul_iff` and its companions). -/
theorem exists_reduction_baseChange_smul_isSingular_zero [PerfectField (ResidueField R)]
    [IsMinimal R W] (h : ¬ W.HasGoodReduction R) :
    ∃ r t : R,
      (((VariableChange.mk 1 r 0 t).baseChange K • W).reduction R).toAffine.IsSingular 0 0 := by
  have hΔ : (W.integralModel R).Δ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, ← map_Δ]
    exact (reduction_Δ_eq_zero_iff R).2 h
  obtain ⟨r, t, hrt⟩ := exists_map_residue_variableChange_isSingular_zero _ hΔ
  refine ⟨r, t, ?_⟩
  rwa [reduction_baseChange_smul, reduction, map_variableChange]

variable [IsMinimal R W]

/-- **Tate's test for multiplicative reduction.** On a minimal equation whose reduction is singular
at the origin, the reduction is multiplicative exactly when `π ∤ b₂`: there `c₄ ≡ b₂² (mod π)`, and
multiplicative reduction is the case of a singular reduction with `π ∤ c₄`. -/
theorem hasMultiplicativeReduction_iff_reduction_b₂_ne_zero
    (hW : (W.reduction R).toAffine.IsSingular 0 0) :
    W.HasMultiplicativeReduction R ↔ (W.reduction R).b₂ ≠ 0 := by
  rw [← pow_ne_zero_iff two_ne_zero, ← Affine.c₄_eq_b₂_sq_of_isSingular_zero hW]
  refine ⟨fun h ↦ h.reduction_c₄_ne_zero R, fun hc₄ ↦ ?_⟩
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R (W := W) with
    hg | hm | ha
  · exact absurd hg ((reduction_Δ_eq_zero_iff R).1 hW.Δ_eq_zero)
  · exact hm
  · exact absurd (ha.reduction_c₄_eq_zero R) hc₄

/-- **Tate's test for additive reduction.** On a minimal equation whose reduction is singular at the
origin, the reduction is additive exactly when `π ∣ b₂`. -/
theorem hasAdditiveReduction_iff_reduction_b₂_eq_zero
    (hW : (W.reduction R).toAffine.IsSingular 0 0) :
    W.HasAdditiveReduction R ↔ (W.reduction R).b₂ = 0 := by
  rw [← not_ne_iff, ← hasMultiplicativeReduction_iff_reduction_b₂_ne_zero R hW]
  refine ⟨fun h ↦ h.not_hasMultiplicativeReduction R, fun hm ↦ ?_⟩
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R (W := W) with
    hg | hm' | ha
  · exact absurd hg ((reduction_Δ_eq_zero_iff R).1 hW.Δ_eq_zero)
  · exact absurd hm' hm
  · exact ha

/-- **Tate's test for split multiplicative reduction.** On a minimal equation whose reduction is
singular at the origin, the reduction is split multiplicative exactly when `π ∤ b₂` and the tangent
quadratic `T² + a₁ T − a₂` of the reduced equation splits over the residue field. Its roots are the
slopes of the two tangent lines at the node, and the node polynomial of
`HasSplitMultiplicativeReduction` is `c₄` times it. -/
theorem hasSplitMultiplicativeReduction_iff_reduction_b₂_ne_zero_and_splits
    (hW : (W.reduction R).toAffine.IsSingular 0 0) :
    W.HasSplitMultiplicativeReduction R ↔ (W.reduction R).b₂ ≠ 0 ∧
      (X ^ 2 + C (W.reduction R).a₁ * X - C (W.reduction R).a₂).Splits := by
  rw [← hasMultiplicativeReduction_iff_reduction_b₂_ne_zero R hW]
  have key (hm : W.HasMultiplicativeReduction R) : (W.reduction R).nodePolynomial.Splits ↔
      (X ^ 2 + C (W.reduction R).a₁ * X - C (W.reduction R).a₂).Splits := by
    rw [nodePolynomial_eq_of_isSingular_zero _ hW,
      splits_mul_iff_right (C_ne_zero.2 (hm.reduction_c₄_ne_zero R)) (Splits.C _), C_1, one_mul,
      C_neg, ← sub_eq_add_neg]
  exact ⟨fun h ↦ ⟨h.toHasMultiplicativeReduction,
      (key h.toHasMultiplicativeReduction).1 ((h.splits_nodePolynomial_reduction_iff R).2 h)⟩,
    fun ⟨hm, hs⟩ ↦ (hm.splits_nodePolynomial_reduction_iff R).1 ((key hm).2 hs)⟩

end DiscreteValuationRing

end WeierstrassCurve

end
