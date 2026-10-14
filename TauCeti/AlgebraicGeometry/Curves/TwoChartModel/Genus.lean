/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Proper
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.GenusOne
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# The genus of the two-chart model

Let `F / k` be an algebraic function field with exact constant field `k`, and let
`X_F = TauCeti.AlgebraicGeometry.twoChartModel hF hx` be its regular proper model, glued from the
normalizations of `k[x]` and `k[x⁻¹]` in `F` for some `x ∈ F` transcendental over `k`. This file
compares the cohomology of `X_F` with the Riemann–Roch theory of `F`.

The cohomological genus `dim_k H¹(X_F, 𝒪_{X_F})` is the genus of `F`, defined through Riemann's
theorem. This is `SchemeWeilDivisor.genus_eq_genus_functionField` for the curve `X_F`, transported
along the identification `k(X_F) ≃ₐ[k] F` of
`TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv`.

When `F` has genus one, the ladder `ℓ(n P) = n deg P` of Riemann–Roch spaces
(`TauCeti.Divisor.dim_natCast_zsmul_ofPoint_of_genus_eq_one`) becomes the ladder
`dim_k H⁰(X_F, 𝒪_{X_F}(n P)) = n deg P` for `n ≥ 1`, where the place `P` is regarded as a point of
`X_F` through `TauCeti.AlgebraicGeometry.twoChartModel.equivPlace`. At a rational place this is
`h⁰(X_F, 𝒪_{X_F}(n P)) = n`.

## Main results

All in the namespace `TauCeti.AlgebraicGeometry`:

* `twoChartModel.finrank_cohomology_one_trivial_eq_genus`: `dim_k H¹(X_F, 𝒪_{X_F}) = g(F)`.
* `twoChartModel.finrank_cohomology_zero_sheaf_natCast_zsmul_ofPoint_of_genus_eq_one`: in genus
  one, `dim_k H⁰(X_F, 𝒪_{X_F}(n P)) = n deg P` for every place `P` of `F` and `n ≥ 1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.5.17 and Appendix B.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section IV.1.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F] {hF : IsFunctionField k F} {x : F}
  {hx : x ≠ 0}

/-- **The cohomological genus of the two-chart model is the genus of the function field.** For
`x` transcendental over `k` and `k` the exact constant field of `F`,
`dim_k H¹(X_F, 𝒪_{X_F}) = g(F)`. -/
theorem finrank_cohomology_one_trivial_eq_genus (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    Module.finrank k
        (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (twoChartModel hF hx)).obj 1) =
      genus k F := by
  have := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  have := isNoetherian (hF := hF) (hx := hx) hxt
  have := locallyOfFiniteType (hF := hF) (hx := hx) hxt
  have hF' : IsFunctionField k (twoChartModel hF hx).functionField :=
    (isFunctionField_functionField_iff k).mpr (topologicalKrullDim_eq_one hxt)
  have h := SchemeWeilDivisor.genus_eq_genus_functionField (valuativeCriterion_existence hF hx)
    (coheight_le_one hxt) hF' ((functionFieldEquiv hxt).isIntegrallyClosedIn.mpr hk)
  rw [Scheme.genus_def] at h
  rw [h]
  exact (genus_eq_of_ringEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
    (functionFieldEquiv hxt).commutes).symm

/-- **The section-dimension ladder on the two-chart model of a genus-one function field.** For `x`
transcendental over `k`, `k` the exact constant field of `F`, and `F` of genus one, every place
`P` of `F` and every `n ≥ 1` satisfy `dim_k H⁰(X_F, 𝒪_{X_F}(n P)) = n deg P`, where `P` is regarded
as a point of `X_F`. At a rational place this reads `dim_k H⁰(X_F, 𝒪_{X_F}(n P)) = n`. -/
theorem finrank_cohomology_zero_sheaf_natCast_zsmul_ofPoint_of_genus_eq_one
    (hxt : Transcendental k x) (hk : IsIntegrallyClosedIn k F) (hg : genus k F = 1)
    (P : Place k F) {n : ℕ} (hn : 1 ≤ n) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Module.finrank k (Scheme.Modules.Cohomology
      (SchemeWeilDivisor.sheaf ((n : ℤ) • WeilDivisor.ofPoint ((equivPlace hxt).symm P))) 0) =
      n * P.degree := by
  have := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  have := isNoetherian (hF := hF) (hx := hx) hxt
  have := isProper (hF := hF) (hx := hx) hxt
  have : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
  have := finiteDimensional_cohomology_one_trivial_of_isProper k (X := twoChartModel hF hx)
    (topologicalKrullDim_eq_one hxt)
  rw [SchemeWeilDivisor.finrank_cohomology_zero_sheaf_natCast_zsmul_ofPoint_of_genus_eq_one k
      ((functionFieldEquiv hxt).isIntegrallyClosedIn.mpr hk)
      (by rw [Scheme.genus_def, finrank_cohomology_one_trivial_eq_genus hxt hk, hg]) _ hn,
    ← degree_equivPlace hxt, Equiv.apply_symm_apply]

end TauCeti.AlgebraicGeometry.twoChartModel
