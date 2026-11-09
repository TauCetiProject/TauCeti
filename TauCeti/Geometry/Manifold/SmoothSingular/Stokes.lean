/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Chains
public import TauCeti.Analysis.Calculus.DifferentialForm.Simplex
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Stokes' theorem for smooth singular chains

Let `σ` be a smooth singular `(p + 1)`-simplex of a manifold `M` and `φ` a `C¹` `p`-form on `M`
with values in a complete space. Then

`∫_σ dφ = ∑ᵢ (-1)ⁱ ∫_{∂ᵢσ} φ`,

where `∂ᵢσ` is the `i`-th face of `σ` in the simplicial set of smooth singular simplices
(`TauCeti.SmoothSimplex.integral_mextDeriv`). Summing over the simplices of a chain, integration
of forms turns the boundary of smooth singular chains into the exterior derivative: the
integration cochain of `φ`, precomposed with the differential of the smooth singular chain
complex, is the integration cochain of `dφ` (`TauCeti.d_comp_integrationCochain`). So the
integration cochain of a closed form is a cocycle, and an exact form integrates to zero over every
smooth singular cycle.

The proof pulls `φ` back to the standard simplex `Δᵖ⁺¹ ⊆ ℝᵖ⁺¹` along `σ`, with derivatives taken
within `Δᵖ⁺¹`. Pullback within `Δᵖ⁺¹` commutes with the exterior derivative
(`TauCeti.extDerivWithin_mpullbackWithin`), which reduces the statement to Stokes' theorem on the
standard simplex (`ContDiffOn.integral_extDerivWithin_fullSimplex`). Its boundary terms are the
pullbacks along the affine face maps `simplexMapAmbient i.succAbove : ℝᵖ → ℝᵖ⁺¹`. These restrict to
the face inclusions (`TauCeti.SmoothSimplex.toContinuousMap_δ_apply`), so by the chain rule within
the simplices (`TauCeti.mpullbackWithin_comp_simplexMapAmbient`) the boundary terms are the
integrals over the faces of `σ`.

## Main results

* `TauCeti.SmoothSimplex.integral_mextDeriv`: Stokes' theorem for a smooth singular simplex.
* `TauCeti.d_comp_integrationCochain`: Stokes' theorem for smooth singular chains, as an identity
  of cochains.
* `TauCeti.d_comp_integrationCochain_eq_zero`: the integration cochain of a closed form is a
  cocycle.
* `TauCeti.integrationCochain_mextDeriv_apply_eq_zero`: an exact form integrates to zero over
  every smooth singular cycle.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.12 (Stokes's
  theorem for chains).
-/

public section

noncomputable section

open CategoryTheory MeasureTheory Set Simplicial Opposite Bundle
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- Pulling back within `Δᵐ` along `g` composed with the affine map `simplexMapAmbient f` induced
by a vertex map `f` is the flat pullback, along `simplexMapAmbient f`, of the pullback along `g`
within `Δⁿ`. -/
theorem mpullbackWithin_comp_simplexMapAmbient {m n k : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    {g : EuclideanSpace ℝ (Fin n) → M} {y : EuclideanSpace ℝ (Fin m)} (hy : y ∈ fullSimplex m)
    (hg : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I g (fullSimplex n)
      (simplexMapAmbient f y))
    (φ : RoughForm I M F k) :
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I (g ∘ simplexMapAmbient f) (fullSimplex m)
        φ y =
      (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I g (fullSimplex n) φ
        (simplexMapAmbient f y)).compContinuousLinearMap (simplexMapAmbient f).contLinear := by
  rw [mpullbackWithin_comp_at (t := fullSimplex n)
    (simplexMapAmbient f).differentiableWithinAt.mdifferentiableWithinAt hg
    (mapsTo_simplexMapAmbient f)
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex m y hy)),
    mpullbackWithin_eq_flat]
  -- The form's type mentions the tangent spaces, so `rw` cannot reach the derivative.
  exact congrArg
    (mpullbackWithin _ I g (fullSimplex n) φ (simplexMapAmbient f y)).compContinuousLinearMap
    ((simplexMapAmbient f).fderivWithin (uniqueDiffOn_fullSimplex m y hy))

namespace SmoothSimplex

variable [IsManifold I 2 M]

/-- **Stokes' theorem for a smooth singular simplex.** The integral of the exterior derivative of
a `C¹` form over a smooth singular `(p + 1)`-simplex is the alternating sum of the integrals of the
form over the faces of the simplex. -/
theorem integral_mextDeriv [CompleteSpace F] (σ : SmoothSimplex I M (p + 1))
    {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ) :
    σ.integral (mextDeriv φ) = ∑ i : Fin (p + 2),
      (-1 : ℝ) ^ (i : ℕ) • integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ := by
  set Δ := fullSimplex (p + 1)
  set g := σ.extension
  -- The pullback of `φ` to `Δᵖ⁺¹` along the simplex, a flat `C¹` form on `Δᵖ⁺¹`.
  set ψ : RoughForm 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) (EuclideanSpace ℝ (Fin (p + 1))) F p :=
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I g Δ φ
  have hu : UniqueMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) Δ :=
    (uniqueDiffOn_fullSimplex (p + 1)).uniqueMDiffOn
  have hψ : ContDiffOn ℝ 1 ψ Δ := fun x hx ↦
    RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      ((hφ.contMDiff (g x)).contMDiffWithinAt.mpullbackWithin_form
        (σ.contMDiffOn_extension x hx) (by simp) (mapsTo_univ _ _) hx hu)
  -- Pullback within `Δᵖ⁺¹` commutes with the exterior derivative.
  have hd : ∀ x ∈ Δ, mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I g Δ (mextDeriv φ) x =
      extDerivWithin ψ Δ x := fun x hx ↦
    (extDerivWithin_mpullbackWithin ((σ.contMDiffOn_extension x hx).of_le (by simp))
      (uniqueDiffOn_fullSimplex (p + 1)) ((closure_interior_fullSimplex (p + 1)).symm ▸ hx)
      hx ((hφ.contMDiff (g x)).mdifferentiableAt (by simp))).symm
  rw [integral_eq_setIntegral_mpullbackWithin σ _ (g := g) σ.extension_coe,
    setIntegral_congr_fun (isClosed_fullSimplex (p + 1)).measurableSet
    (g := fun x ↦ extDerivWithin ψ Δ x fun i ↦ EuclideanSpace.single i 1)
    fun x hx ↦ DFunLike.congr_fun (hd x hx) _,
    hψ.integral_extDerivWithin_fullSimplex]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ ?_
  -- Each boundary term is the integral over the corresponding face of the simplex.
  set A := simplexMapAmbient (m := p) (n := p + 1) i.succAbove
  rw [integral_eq_setIntegral_mpullbackWithin _ φ (g := g ∘ A) fun x ↦ by
    rw [toContinuousMap_δ_apply, Function.comp_apply, simplexMapAmbient_succAbove_coe]
    exact σ.extension_coe _]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun y hy ↦ ?_
  rw [mpullbackWithin_comp_simplexMapAmbient _ hy ((σ.contMDiffOn_extension _
    (mapsTo_simplexMapAmbient _ hy)).mdifferentiableWithinAt (by simp))]
  exact (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).symm

end SmoothSimplex

section Cochain

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Stokes' theorem for smooth singular chains.** Integrating a `C¹` form over the boundary of a
smooth singular chain is integrating its exterior derivative over the chain: the integration
cochain of `φ`, precomposed with the differential of the smooth singular chain complex, is the
integration cochain of `dφ`. -/
@[reassoc]
theorem d_comp_integrationCochain {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
      integrationCochain φ = integrationCochain (mextDeriv φ) := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp only [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_smul]
  rw [integrationCochain_ιChainComplex, one_smul, SmoothSimplex.integral_mextDeriv σ hφ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.smul_apply, map_zsmul, integrationCochain_ιChainComplex, one_smul,
    ← Int.cast_smul_eq_zsmul ℝ]
  simp

/-- The integration cochain of a closed `C¹` form is a cocycle. -/
theorem d_comp_integrationCochain_eq_zero {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
      integrationCochain φ = 0 := by
  rw [d_comp_integrationCochain hφ, hdφ, integrationCochain_zero]

/-- An exact form integrates to zero over every smooth singular cycle: if the boundary of the
smooth singular `(p + 1)`-chain `c` vanishes, then `∫_c dφ = 0` for every `C¹` `p`-form `φ`. -/
theorem integrationCochain_mextDeriv_apply_eq_zero {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ)
    {c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).X (p + 1)}
    (hc : (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d
      (p + 1) p).hom c = 0) :
    (integrationCochain (mextDeriv φ)).hom c = 0 := by
  rw [← d_comp_integrationCochain hφ, ModuleCat.hom_comp, LinearMap.comp_apply, hc, map_zero]

end Cochain

end TauCeti
