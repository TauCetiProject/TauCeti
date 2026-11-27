/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Outward
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic

/-!
# The gradient points out of regular sublevels and bands

Let `f : M → ℝ` be a `C¹` function on a boundaryless manifold modelled on a real space of dimension
`n + 1`, and let `a < b` be regular values of `f`. The sublevel `{f ≤ a}` and the band
`f⁻¹([a, b])` are manifolds with boundary, and their outward vectors are read off from the sign of
`df` alone, with no metric: on the level `f⁻¹(a)` bounding the sublevel and on the upper level
`f⁻¹(b)` of the band the outward vectors are those with `df > 0`, and on the lower level `f⁻¹(a)`
of the band those with `df < 0` (`TauCeti.isOutwardPointing_scalarRegularSublevel_iff` and its
band forms).

Once the tangent spaces of `M` carry a Riemannian metric, `±grad f` represent these
co-orientations, for every metric. The inclusion `ι` of the sublevel or the band into `M` has
invertible differential at every point
(`TauCeti.isInvertible_mfderiv_subtypeVal_scalarRegularSublevel` and its band form), so at a
boundary point there is exactly one tangent vector `u` of the sublevel or the band with
`dι u = grad f`, and one with `dι u = -grad f`. The first points out of the sublevel and out of the
band at its upper level, and the second points out of the band at its lower level. Indeed
`df(grad f) = ⟪grad f, grad f⟫` is positive wherever `df` does not vanish
(`TauCeti.Manifold.mvfderiv_apply_mgradient_pos_iff`), in particular at a point of a regular level,
so `f ∘ ι` increases along a vector over `grad f` and decreases along one over `-grad f`
(`TauCeti.Manifold.mvfderiv_comp_apply_pos_of_mfderiv_eq_mgradient` and its negative form).

## Main results

* `TauCeti.isOutwardPointing_scalarRegularSublevel_of_mfderiv_subtypeVal_eq_mgradient`: the
  gradient points out of `{f ≤ a}`.
* `TauCeti.isOutwardPointing_scalarRegularBand_of_mfderiv_subtypeVal_eq_neg_mgradient_of_eq_left`:
  minus the gradient points out of `f⁻¹([a, b])` at its lower level.
* `TauCeti.isOutwardPointing_scalarRegularBand_of_mfderiv_subtypeVal_eq_mgradient_of_eq_right`:
  the gradient points out of `f⁻¹([a, b])` at its upper level.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 5 (regular sublevel sets as regular domains) and Chapter 13 (the
  gradient of a function on a Riemannian manifold).
-/

public section

open Bundle Module Set TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a b : ℝ}
  [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hn : finrank ℝ E = n + 1)

/-- **The gradient points out of a regular sublevel.** At a point `x` of the level `f⁻¹(a)`, for
any Riemannian metric on `M`, the tangent vector of the sublevel `{f ≤ a}` lying over the gradient
of `f` points outward. -/
theorem isOutwardPointing_scalarRegularSublevel_of_mfderiv_subtypeVal_eq_mgradient
    (hreg : IsRegularValue I 𝓘(ℝ) f a) {x : {x | f x ≤ a}} (hx : f x = a)
    {u : letI := scalarRegularSublevelChartedSpace hf hreg hn; TangentSpace (𝓡∂ (n + 1)) x}
    (hu : letI := scalarRegularSublevelChartedSpace hf hreg hn
      mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → M) x u = mgradient I f x) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    IsOutwardPointing x u := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  rw [isOutwardPointing_scalarRegularSublevel_iff hf hn hreg hx]
  -- The restriction of `f` to the sublevel is `f ∘ Subtype.val` by definition.
  exact mvfderiv_comp_apply_pos_of_mfderiv_eq_mgradient ((hf _).mdifferentiableAt one_ne_zero)
    ((contMDiff_subtypeVal_scalarRegularSublevel hreg hn le_rfl hf x).mdifferentiableAt
      one_ne_zero) hu (isRegularPoint_iff_mvfderiv_ne_zero.1 (isRegularValue_iff.1 hreg _ hx))

section Band

variable (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (hab : a < b)

/-- **Minus the gradient points out of a band at its lower level.** At a point `x` of the lower
level `f⁻¹(a)` of a band `f⁻¹([a, b])` between regular values, for any Riemannian metric on `M`, the
tangent vector of the band lying over minus the gradient of `f` points outward. -/
theorem isOutwardPointing_scalarRegularBand_of_mfderiv_subtypeVal_eq_neg_mgradient_of_eq_left
    {x : f ⁻¹' Icc a b} (hx : f x = a)
    {u : letI := scalarRegularBandChartedSpace hf hn ha hb hab; TangentSpace (𝓡∂ (n + 1)) x}
    (hu : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      mfderiv (𝓡∂ (n + 1)) I (Subtype.val : f ⁻¹' Icc a b → M) x u = -mgradient I f x) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    IsOutwardPointing x u := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  rw [isOutwardPointing_scalarRegularBand_iff_of_eq_left hf hn ha hb hab hx]
  -- The restriction of `f` to the band is `f ∘ Subtype.val` by definition.
  exact mvfderiv_comp_apply_neg_of_mfderiv_eq_neg_mgradient ((hf _).mdifferentiableAt one_ne_zero)
    ((contMDiff_subtypeVal_scalarRegularBand hn ha hb le_rfl hf hab x).mdifferentiableAt
      one_ne_zero) hu (isRegularPoint_iff_mvfderiv_ne_zero.1 (isRegularValue_iff.1 ha _ hx))

/-- **The gradient points out of a band at its upper level.** At a point `x` of the upper level
`f⁻¹(b)` of a band `f⁻¹([a, b])` between regular values, for any Riemannian metric on `M`, the
tangent vector of the band lying over the gradient of `f` points outward. -/
theorem isOutwardPointing_scalarRegularBand_of_mfderiv_subtypeVal_eq_mgradient_of_eq_right
    {x : f ⁻¹' Icc a b} (hx : f x = b)
    {u : letI := scalarRegularBandChartedSpace hf hn ha hb hab; TangentSpace (𝓡∂ (n + 1)) x}
    (hu : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      mfderiv (𝓡∂ (n + 1)) I (Subtype.val : f ⁻¹' Icc a b → M) x u = mgradient I f x) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    IsOutwardPointing x u := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  rw [isOutwardPointing_scalarRegularBand_iff_of_eq_right hf hn ha hb hab hx]
  -- The restriction of `f` to the band is `f ∘ Subtype.val` by definition.
  exact mvfderiv_comp_apply_pos_of_mfderiv_eq_mgradient ((hf _).mdifferentiableAt one_ne_zero)
    ((contMDiff_subtypeVal_scalarRegularBand hn ha hb le_rfl hf hab x).mdifferentiableAt
      one_ne_zero) hu (isRegularPoint_iff_mvfderiv_ne_zero.1 (isRegularValue_iff.1 hb _ hx))

end Band

end TauCeti
