/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Chains
public import TauCeti.Analysis.Calculus.DifferentialForm.Simplex
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import Mathlib.Analysis.Convex.Topology

/-!
# Stokes' theorem for smooth singular chains

For a smooth singular `(p + 1)`-simplex `σ` of a manifold `M` and a `C¹` `p`-form `φ` with values
in a complete space,

`∫_σ dφ = ∑ᵢ (-1)ⁱ ∫_{∂ᵢσ} φ`,

where `∂ᵢσ` is the `i`-th face of `σ` in the simplicial set of smooth singular simplices
(`TauCeti.SmoothSimplex.integral_mextDeriv`). Since the boundary of the simplicial chain complex
is the alternating sum of the faces, this says that the integration cochain of `dφ` is the
integration cochain of `φ` composed with the boundary
(`TauCeti.d_comp_integrationCochain`): integration of forms over smooth chains is a cochain map from
forms to the dual of the smooth singular chain complex. In particular closed forms integrate to zero
over boundaries, and exact forms integrate to zero over cycles.

The proof transports Stokes' theorem on the standard simplex
(`ContDiffOn.integral_extDerivWithin_fullSimplex`) along `σ`. The integral over `σ` is the integral
over `Δᵖ⁺¹` of the pullback of the form within `Δᵖ⁺¹`, and pullback within `Δᵖ⁺¹` commutes with the
exterior derivative (`TauCeti.extDerivWithin_mpullbackWithin`). The face `∂ᵢσ` is `σ` composed with
the affine face inclusion `Fᵢ = simplexMapAmbient i.succAbove`
(`TauCeti.SmoothSimplex.toContinuousMap_δ`), so by the chain rule its integral is the `i`-th
boundary term of Stokes' theorem on the standard simplex (`TauCeti.SmoothSimplex.integral_δ`).
No compactness, orientation or finite-dimensionality of `M` is needed.

## Main results

* `TauCeti.SmoothSimplex.integral_mextDeriv`: Stokes' theorem for a smooth simplex.
* `TauCeti.SmoothSimplex.integral_mextDeriv_ofFunction`: its case `p = 0`, the fundamental theorem
  of calculus `∫_σ df = f(σ(1)) - f(σ(0))`, which fixes the signs of the faces.
* `TauCeti.d_comp_integrationCochain`: Stokes' theorem for smooth chains, as a cochain identity.
* `TauCeti.d_comp_integrationCochain_eq_zero`: a closed form integrates to zero over boundaries.
* `TauCeti.integrationCochain_mextDeriv_apply_eq_zero`: an exact form integrates to zero over
  cycles.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.12 (Stokes's
  theorem for chains).
-/

public section

noncomputable section

open CategoryTheory MeasureTheory Set Simplicial Opposite
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

namespace SmoothSimplex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I 2 M] [CompleteSpace F]

/-- **Stokes' theorem for a smooth singular simplex.** The integral of the exterior derivative of
a `C¹` `p`-form over a smooth `(p + 1)`-simplex `σ` is the alternating sum of the integrals of the
form over the faces of `σ`. -/
theorem integral_mextDeriv (σ : SmoothSimplex I M (p + 1)) {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) :
    σ.integral (mextDeriv φ) = ∑ i : Fin (p + 2),
      (-1 : ℝ) ^ (i : ℕ) • integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ := by
  set Δ := fullSimplex (p + 1)
  set ψ := mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I σ.extension Δ φ
  have hΔ : UniqueDiffOn ℝ Δ := uniqueDiffOn_fullSimplex _
  have hψ : ContDiffOn ℝ 1 ψ Δ := fun x hx ↦
    RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      ((((isSmoothForm_def _ _).mp hφ (σ.extension x)).contMDiffWithinAt
        (s := univ)).mpullbackWithin_form (σ.contMDiffOn_extension x hx) (by simp)
          (mapsTo_univ _ _) hx hΔ.uniqueMDiffOn)
  simp_rw [integral_δ]
  refine Eq.trans ?_ hψ.integral_extDerivWithin_fullSimplex
  rw [integral_eq_setIntegral_mpullbackWithin σ _ σ.extension_coe]
  refine setIntegral_congr_fun (isClosed_fullSimplex _).measurableSet fun x hx ↦ ?_
  have hc : x ∈ closure (interior Δ) := by
    rw [(convex_fullSimplex _).closure_interior_eq_closure_of_nonempty_interior
      (nonempty_interior_fullSimplex _)]
    exact subset_closure hx
  rw [extDerivWithin_mpullbackWithin ((σ.contMDiffOn_extension x hx).of_le (by simp)) hΔ hc hx
    (((isSmoothForm_def _ _).mp hφ).mdifferentiableAt one_ne_zero)]
  -- The standard basis vectors are typed as tangent vectors of the model space on one side and as
  -- its points on the other; these types agree by definition.
  rfl

/-- **The fundamental theorem of calculus for a smooth `1`-simplex.** The integral of the
differential of a `C¹` function over a smooth `1`-simplex `σ` is the difference of its values at
the endpoints `σ(1)` and `σ(0)`. This fixes the sign convention of
`TauCeti.SmoothSimplex.integral_mextDeriv`: the face `∂₀σ` is the endpoint and `∂₁σ` the initial
point. -/
theorem integral_mextDeriv_ofFunction (σ : SmoothSimplex I M 1) {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) :
    σ.integral (mextDeriv (RoughForm.ofFunction I f)) =
      f (σ.toContinuousMap ⟨EuclideanSpace.single 0 1, by simp⟩) -
        f (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 1⟩) := by
  rw [integral_mextDeriv σ (isSmoothForm_ofFunction_iff.mpr hf), Fin.sum_univ_two,
    integral_ofFunction, integral_ofFunction, toContinuousMap_δ, toContinuousMap_δ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, ← sub_eq_add_neg]
  congr 3 <;> ext j <;> fin_cases j <;>
    simp [← simplexMapAmbient_succAbove_coe, simplexMapAmbient_apply, Finset.filter_singleton]

end SmoothSimplex

section Cochain

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Stokes' theorem for smooth singular chains.** Integrating the exterior derivative of a `C¹`
`p`-form over smooth `(p + 1)`-chains is integrating the form over their boundaries: the integration
cochain of `dφ` is the integration cochain of `φ` composed with the boundary of the smooth singular
chain complex. -/
theorem d_comp_integrationCochain {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
      integrationCochain φ = integrationCochain (mextDeriv φ) := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  simp only [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
    ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [integrationCochain_ιChainComplex (I := I)]
  rw [SmoothSimplex.integral_mextDeriv σ hφ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℝ, smul_comm]
  simp

/-- A closed `C¹` form integrates to zero over every boundary of smooth singular chains. -/
theorem d_comp_integrationCochain_eq_zero {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hclosed : mextDeriv φ = 0) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
      integrationCochain φ = 0 := by
  rw [d_comp_integrationCochain hφ, hclosed, integrationCochain_zero]

/-- The exterior derivative of a `C¹` form integrates to zero over every cycle of smooth singular
chains. -/
theorem integrationCochain_mextDeriv_apply_eq_zero {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ)
    {c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).X (p + 1)}
    (hc : (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d
      (p + 1) p).hom c = 0) :
    (integrationCochain (mextDeriv φ)).hom c = 0 := by
  rw [← d_comp_integrationCochain hφ, ModuleCat.hom_comp, LinearMap.comp_apply, hc, map_zero]

end Cochain

end TauCeti
