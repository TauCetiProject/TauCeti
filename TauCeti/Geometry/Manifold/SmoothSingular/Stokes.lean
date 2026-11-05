/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.SmoothSingular.Chains
import Mathlib.Analysis.Calculus.FDeriv.Affine
import TauCeti.Analysis.Calculus.DifferentialForm.Simplex
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Stokes' theorem for smooth singular chains

For a smooth singular `(p + 1)`-simplex `σ` of a manifold `M` and a `C¹` `p`-form `φ` with values
in a complete space,

`∫_σ dφ = ∑ᵢ (-1)ⁱ ∫_{∂ᵢσ} φ`,

where `∂ᵢσ` is the `i`-th face of `σ` in the simplicial set of smooth singular simplices
(`TauCeti.SmoothSimplex.integral_mextDeriv`). Since the boundary of the simplicial chain complex
is the alternating sum of the faces, integration therefore intertwines the exterior derivative of
forms with the boundary of smooth singular chains: integrating `φ` over the boundary of a chain is
integrating `dφ` over the chain (`TauCeti.d_comp_integrationCochain`). In particular a closed
form integrates to zero over every boundary
(`TauCeti.d_comp_integrationCochain_of_mextDeriv_eq_zero`), so it defines a cocycle on smooth
singular chains; this is the chain-level input to the de Rham homomorphism from de Rham cohomology
to singular cohomology.

The simplex theorem is pulled back from Stokes' theorem on the standard simplex
(`ContDiffOn.integral_extDerivWithin_fullSimplex`). Reading `σ` on `Δᵖ⁺¹`, the exterior derivative
within `Δᵖ⁺¹` of the pullback of `φ` is the pullback of `dφ`
(`TauCeti.extDerivWithin_mpullbackWithin`), which applies because `Δᵖ⁺¹` is the closure of its
interior; and the face `∂ᵢσ` is `σ` composed with the affine face map
`simplexMapAmbient i.succAbove : ℝᵖ → ℝᵖ⁺¹`, whose derivative is its linear part. No smoothness of
`σ` beyond `Δᵖ⁺¹` is used, and the manifold may have boundary or corners.

## Main results

* `TauCeti.SmoothSimplex.integral_mextDeriv`: Stokes' theorem for a smooth singular simplex.
* `TauCeti.d_comp_integrationCochain`: Stokes' theorem for smooth singular chains.
* `TauCeti.d_comp_integrationCochain_of_mextDeriv_eq_zero`: a closed form integrates to zero over
  boundaries.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.12 (Stokes's
  theorem for chains).
-/

public section

open CategoryTheory MeasureTheory Set
open scoped Manifold Simplicial ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

namespace SmoothSimplex

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ℕ}

/-- **Stokes' theorem for a smooth singular simplex.** The integral of the exterior derivative of a
`C¹` `p`-form over a smooth singular `(p + 1)`-simplex `σ` is the alternating sum of the integrals
of the form over the faces of `σ`. -/
theorem integral_mextDeriv (σ : SmoothSimplex I M (p + 1)) {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) :
    σ.integral (mextDeriv φ) = ∑ i : Fin (p + 2),
      (-1 : ℝ) ^ (i : ℕ) • integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ := by
  set Δ := fullSimplex (p + 1)
  set η : EuclideanSpace ℝ (Fin (p + 1)) → EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F :=
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I σ.extension Δ φ
  have hg := σ.contMDiffOn_extension
  have hu : UniqueDiffOn ℝ Δ := uniqueDiffOn_fullSimplex _
  have hφ' := (isSmoothForm_def _ _).mp hφ
  have hη : ContDiffOn ℝ 1 η Δ := fun x hx ↦
    RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      ((hφ'.contMDiffOn (s := univ)).mpullbackWithin_form hg (by simp) (mapsTo_univ _ _)
        hu.uniqueMDiffOn x hx)
  have hcl : closure (interior Δ) = Δ := by
    rw [(convex_fullSimplex _).closure_interior_eq_closure_of_nonempty_interior
      (nonempty_interior_fullSimplex _), (isClosed_fullSimplex _).closure_eq]
  -- The integrand of `∫_σ dφ` is the flat exterior derivative within `Δᵖ⁺¹` of `η`.
  have hL : σ.integral (mextDeriv φ) = ∫ x in Δ, extDerivWithin η Δ x
      fun i ↦ EuclideanSpace.single i 1 := by
    rw [integral_eq_setIntegral_mpullbackWithin σ _ σ.extension_coe]
    refine setIntegral_congr_fun (isClosed_fullSimplex _).measurableSet fun x hx ↦ ?_
    rw [extDerivWithin_mpullbackWithin ((hg x hx).of_le (by simp)) hu (hcl.symm ▸ hx) hx
      ((hφ' _).mdifferentiableAt one_ne_zero)]
    -- The two sides differ only in whether the basis vectors are typed as tangent vectors or as
    -- vectors of `ℝᵖ⁺¹`, which Mathlib identifies definitionally.
    rfl
  rw [hL, hη.integral_extDerivWithin_fullSimplex]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ ?_
  -- The `i`-th face is `σ` composed with the affine face map `A`, whose derivative is its linear
  -- part.
  set A := simplexMapAmbient i.succAbove
  rw [integral_eq_setIntegral_mpullbackWithin _ φ (g := σ.extension ∘ A) fun y ↦ by
    rw [toContinuousMap_δ, Function.comp_apply, simplexMapAmbient_succAbove_coe, extension_coe]]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun y hy ↦ ?_
  have hyu : UniqueDiffWithinAt ℝ (fullSimplex p) y := uniqueDiffOn_fullSimplex p y hy
  rw [mpullbackWithin_comp_at (A.differentiable.mdifferentiable y).mdifferentiableWithinAt
    ((hg _ (mapsTo_simplexMapAmbient _ hy)).mdifferentiableWithinAt (by simp))
    (mapsTo_simplexMapAmbient _) (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 hyu)]
  refine Eq.trans ?_ (mpullbackWithin_apply _ _ _ _ _).symm
  congr 1
  funext k
  rw [mfderivWithin_eq_fderivWithin, A.fderivWithin hyu]
  -- `NormedSpace.fromTangentSpace` is Mathlib's definitional identification of the tangent spaces
  -- of a normed space with the space; the vector `EuclideanSpace.single k 1` is typed in the model
  -- on the left and in the tangent space on the right, so the rewrite lemmas for it do not apply.
  rfl

end SmoothSimplex

section Cochain

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ℕ}

/-- **Stokes' theorem for smooth singular chains.** Integrating a `C¹` `p`-form over the boundary
of a smooth singular `(p + 1)`-chain is integrating its exterior derivative over the chain. -/
@[reassoc]
theorem d_comp_integrationCochain {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
      integrationCochain φ = integrationCochain (mextDeriv φ) := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
    ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [integrationCochain_ιChainComplex, SmoothSimplex.integral_mextDeriv σ hφ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integrationCochain_ιChainComplex, smul_comm, ← Int.cast_smul_eq_zsmul ℝ]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- A closed `C¹` form integrates to zero over the boundary of every smooth singular chain: its
integration cochain is a cocycle. -/
theorem d_comp_integrationCochain_of_mextDeriv_eq_zero {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
      integrationCochain φ = 0 := by
  rw [d_comp_integrationCochain hφ, hdφ, integrationCochain_zero]

end Cochain

end TauCeti
