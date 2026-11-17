/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.FullSimplex
public import TauCeti.Geometry.Manifold.SmoothSingular.Chains
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.AlgebraicTopology.Singular.Subdivision.FullSimplex
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Reparametrization and barycentric subdivision invariance of smooth singular integration

This file defines smooth, affine, and vertex-permutation reparametrizations of smooth singular
simplices and proves the resulting change-of-variables and barycentric subdivision formulas for
integrating differential forms over smooth singular simplices and chains.

## Main definitions and results

* `TauCeti.SmoothSimplex.compContDiffOn`: reparametrize a smooth `p`-simplex by a map `ℝ^q → ℝ^p`
  that is smooth on a neighbourhood of `Δ^q` and sends `Δ^q` into `Δ^p`.
* `TauCeti.SmoothSimplex.compAffineMapMk`: precompose a smooth `p`-simplex with the affine map
  `Δ^q → Δ^p` determined by a tuple of barycentric vertices.
* `TauCeti.SmoothSimplex.compPerm`: reorder the vertices of a smooth `p`-simplex by a permutation
  of `Fin (p + 1)`.
* `TauCeti.SmoothSimplex.integral_compContDiffOn_of_det_nonneg`,
  `TauCeti.SmoothSimplex.integral_compContDiffOn_of_det_nonpos`: orientation-preserving and
  orientation-reversing change-of-variables formulas for smooth bijective reparametrizations of
  `Δᵖ`.
* `TauCeti.SmoothSimplex.integral_compPerm`: permuting the vertices scales the integral of any
  `p`-form by the sign of the permutation.
* `TauCeti.SmoothSimplex.sum_sign_integral_compAffineMapMk_vertex`,
  `TauCeti.chainsLinearEquivFinsupp_subcomplexSubdivisionX_ιChainComplex`,
  `TauCeti.subcomplexSubdivisionX_comp_integrationCochain`: barycentric subdivision preserves
  integration of continuous differential forms on smooth singular chains.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18.
* A. Hatcher, *Algebraic Topology*, Section 2.1.
-/

public section

noncomputable section

open CategoryTheory Convexity MeasureTheory Set Simplicial Opposite Topology
open scoped BigOperators ContDiff Manifold

universe u

namespace TauCeti

namespace SmoothSimplex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- Reparametrize a smooth `p`-simplex by a map `Ψ : ℝ^q → ℝ^p` that is smooth on a neighbourhood
of `Δ^q` and sends `Δ^q` into `Δ^p`. -/
def compContDiffOn {q : ℕ} (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin p)}
    {U : Set (EuclideanSpace ℝ (Fin q))}
    (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex q))
    (hmaps : MapsTo Ψ (fullSimplex q) (fullSimplex p)) : SmoothSimplex I M q :=
  mk (σ.toContinuousMap.comp
      ⟨hmaps.restrict Ψ (fullSimplex q) (fullSimplex p),
        (hΨ.continuousOn.mono (subset_of_mem_nhdsSet hU)).domRestrict.codRestrict
          fun x ↦ hmaps x.2⟩)
    (σ.contMDiffOnSubset_toContinuousMap.comp_contDiffOn hΨ hU hmaps)

/-- Read on `Δ^q`, `compContDiffOn` evaluates `σ` along `Ψ`. -/
@[simp]
theorem toContinuousMap_compContDiffOn_apply {q : ℕ} (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin p)}
    {U : Set (EuclideanSpace ℝ (Fin q))}
    (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex q))
    (hmaps : MapsTo Ψ (fullSimplex q) (fullSimplex p)) (x : fullSimplex q) :
    (σ.compContDiffOn hΨ hU hmaps).toContinuousMap x = σ.toContinuousMap ⟨Ψ x, hmaps x.2⟩ := by
  rw [compContDiffOn, toContinuousMap_mk]
  rfl

/-- Precompose a smooth `p`-simplex with the affine map `Δ^q → Δ^p` determined by a tuple of
barycentric vertices `v`. This is definitionally the simplex pushed forward by
`AffineChain.subcomplexChain`. -/
def compAffineMapMk {q : ℕ} (σ : SmoothSimplex I M p)
    (v : Fin (q + 1) → StdSimplex ℝ (Fin (p + 1))) : SmoothSimplex I M q :=
  ⟨((TopCat.of M).toSSetObjEquiv _).symm
      (((TopCat.of M).toSSetObjEquiv _ σ.val).comp (StdSimplex.continuousAffineMapMk v)),
    SSet.Subcomplex.IsAffineStable.comp_affineMapMk_mem σ.property v⟩

/-- Read on `Δ^q`, `compAffineMapMk σ v` precomposes `σ` with `affineMapAmbient v`. -/
@[simp]
theorem toContinuousMap_compAffineMapMk_apply {q : ℕ} (σ : SmoothSimplex I M p)
    (v : Fin (q + 1) → StdSimplex ℝ (Fin (p + 1))) (x : fullSimplex q) :
    (σ.compAffineMapMk v).toContinuousMap x =
      σ.toContinuousMap ⟨affineMapAmbient v x, mapsTo_affineMapAmbient v x.2⟩ := by
  have hx : (⟨affineMapAmbient v x, mapsTo_affineMapAmbient v x.2⟩ : fullSimplex p) =
      (fullSimplexEquivStdSimplex p).symm
        (StdSimplex.affineMapMk v (fullSimplexEquivStdSimplex q x)) :=
    Subtype.ext (affineMapAmbient_coe v x)
  rw [toContinuousMap_apply, compAffineMapMk, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
    hx, toContinuousMap_apply, Homeomorph.apply_symm_apply,
    StdSimplex.continuousAffineMapMk_apply]

/-- Reorder the vertices of a smooth `p`-simplex by a permutation `π` of `Fin (p + 1)`. -/
def compPerm (σ : SmoothSimplex I M p) (π : Equiv.Perm (Fin (p + 1))) : SmoothSimplex I M p :=
  σ.compAffineMapMk (StdSimplex.single ∘ π)

/-- Read on `Δ^p`, `compPerm σ π` precomposes `σ` with `simplexMapAmbient π`. -/
@[simp]
theorem toContinuousMap_compPerm_apply (σ : SmoothSimplex I M p) (π : Equiv.Perm (Fin (p + 1)))
    (x : fullSimplex p) :
    (σ.compPerm π).toContinuousMap x =
      σ.toContinuousMap ⟨simplexMapAmbient π x, mapsTo_simplexMapAmbient π x.2⟩ := by
  rw [compPerm, toContinuousMap_compAffineMapMk_apply]
  congr 1
  exact Subtype.ext (congrFun (congrArg DFunLike.coe (affineMapAmbient_single π)) x.val)

private theorem mpullbackWithin_comp_eval_basis (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p))
    {x : EuclideanSpace ℝ (Fin p)} (hx : x ∈ fullSimplex p)
    {L : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hΨ : HasFDerivWithinAt Ψ L (fullSimplex p) x) (φ : RoughForm I M F p) :
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I (σ.extension ∘ Ψ) (fullSimplex p) φ x
      (fun i ↦ EuclideanSpace.single i 1) =
    L.det •
      mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ (Ψ x)
        (fun i ↦ EuclideanSpace.single i 1) := by
  have hσx : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
      (fullSimplex p) (Ψ x) :=
    (σ.contMDiffOn_extension (Ψ x) (hmaps hx)).mdifferentiableWithinAt (by simp)
  have hmp := mpullbackWithin_comp_apply_of_hasFDerivWithinAt hΨ hσx hmaps
    (uniqueDiffOn_fullSimplex p x hx) φ
  refine (congrArg (fun η ↦ η (fun i ↦ EuclideanSpace.single i 1)) hmp).trans ?_
  let η : EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] F :=
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ (Ψ x)
  exact congrFun (congrArg DFunLike.coe
    (AlternatingMap.compLinearMap_eq_det_smul (EuclideanSpace.basisFun (Fin p) ℝ).toBasis
      η.toAlternatingMap L.toLinearMap))
    (fun i ↦ EuclideanSpace.single i 1)

/-- **Orientation-preserving reparametrization of simplex integrals.** If `Ψ` is a smooth bijective
self-reparametrization of `Δᵖ` with nonnegative Jacobian determinant everywhere on `Δᵖ`, then
integrating any `p`-form over `σ ∘ Ψ` gives the same value as over `σ`. -/
theorem integral_compContDiffOn_of_det_nonneg (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {U : Set (EuclideanSpace ℝ (Fin p))}
    (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex p))
    (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p))
    (hinj : InjOn Ψ (fullSimplex p)) (himage : Ψ '' fullSimplex p = fullSimplex p)
    (hdet : ∀ x ∈ fullSimplex p, 0 ≤ (fderiv ℝ Ψ x).det) (φ : RoughForm I M F p) :
    (σ.compContDiffOn hΨ hU hmaps).integral φ = σ.integral φ := by
  rw [(σ.compContDiffOn hΨ hU hmaps).integral_eq_setIntegral_mpullbackWithin φ
    (g := σ.extension ∘ Ψ) fun x ↦ by
      rw [Function.comp_apply, toContinuousMap_compContDiffOn_apply,
        σ.extension_coe ⟨Ψ x, hmaps x.2⟩]]
  have hΨfderiv : ∀ x ∈ fullSimplex p,
      HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) (fullSimplex p) x := fun x hx ↦
    ((hΨ.contDiffAt (mem_nhdsSet_iff_forall.mp hU x hx)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hpt : ∀ x ∈ fullSimplex p,
      mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I (σ.extension ∘ Ψ) (fullSimplex p) φ x
        (fun i ↦ EuclideanSpace.single i 1) =
      |(fderiv ℝ Ψ x).det| •
        mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ (Ψ x)
          (fun i ↦ EuclideanSpace.single i 1) := fun x hx ↦ by
    rw [abs_of_nonneg (hdet x hx)]
    exact σ.mpullbackWithin_comp_eval_basis hmaps hx (hΨfderiv x hx) φ
  rw [setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet hpt, integral_def]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_fullSimplex p).measurableSet hΨfderiv hinj
    (fun y ↦ mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ y
      (fun i ↦ EuclideanSpace.single i 1))
  rw [himage] at hcov
  exact hcov.symm

/-- **Orientation-reversing reparametrization of simplex integrals.** If `Ψ` is a smooth bijective
self-reparametrization of `Δᵖ` with nonpositive Jacobian determinant everywhere on `Δᵖ`, then
integrating any `p`-form over `σ ∘ Ψ` negates the integral over `σ`. -/
theorem integral_compContDiffOn_of_det_nonpos (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {U : Set (EuclideanSpace ℝ (Fin p))}
    (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex p))
    (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p))
    (hinj : InjOn Ψ (fullSimplex p)) (himage : Ψ '' fullSimplex p = fullSimplex p)
    (hdet : ∀ x ∈ fullSimplex p, (fderiv ℝ Ψ x).det ≤ 0) (φ : RoughForm I M F p) :
    (σ.compContDiffOn hΨ hU hmaps).integral φ = -σ.integral φ := by
  rw [(σ.compContDiffOn hΨ hU hmaps).integral_eq_setIntegral_mpullbackWithin φ
    (g := σ.extension ∘ Ψ) fun x ↦ by
      rw [Function.comp_apply, toContinuousMap_compContDiffOn_apply,
        σ.extension_coe ⟨Ψ x, hmaps x.2⟩]]
  have hΨfderiv : ∀ x ∈ fullSimplex p,
      HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) (fullSimplex p) x := fun x hx ↦
    ((hΨ.contDiffAt (mem_nhdsSet_iff_forall.mp hU x hx)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hpt : ∀ x ∈ fullSimplex p,
      mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I (σ.extension ∘ Ψ) (fullSimplex p) φ x
        (fun i ↦ EuclideanSpace.single i 1) =
      -(|(fderiv ℝ Ψ x).det| •
        mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ (Ψ x)
          (fun i ↦ EuclideanSpace.single i 1)) := fun x hx ↦ by
    rw [abs_of_nonpos (hdet x hx), neg_smul, neg_neg]
    exact σ.mpullbackWithin_comp_eval_basis hmaps hx (hΨfderiv x hx) φ
  rw [setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet hpt,
    MeasureTheory.integral_neg, integral_def]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_fullSimplex p).measurableSet hΨfderiv hinj
    (fun y ↦ mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ y
      (fun i ↦ EuclideanSpace.single i 1))
  rw [himage] at hcov
  exact congrArg Neg.neg hcov.symm

/-- Permuting the vertices of a smooth simplex scales the integral of any `p`-form by the sign of
the permutation. -/
theorem integral_compPerm (σ : SmoothSimplex I M p) (π : Equiv.Perm (Fin (p + 1)))
    (φ : RoughForm I M F p) :
    (σ.compPerm π).integral φ = (π.sign : ℝ) • σ.integral φ := by
  have heq : σ.compPerm π = σ.compContDiffOn (simplexMapAmbient π).contDiff.contDiffOn
      Filter.univ_mem (mapsTo_simplexMapAmbient π) := by
    ext x
    simp
  have hdet (x : EuclideanSpace ℝ (Fin p)) :
      (fderiv ℝ (simplexMapAmbient π) x).det = (π.sign : ℝ) := by
    rw [(simplexMapAmbient π).hasFDerivAt.fderiv, ContinuousLinearMap.det,
      det_contLinear_simplexMapAmbient_perm]
  rw [heq]
  rcases Int.units_eq_one_or π.sign with hsign | hsign
  · rw [σ.integral_compContDiffOn_of_det_nonneg _ Filter.univ_mem (mapsTo_simplexMapAmbient π)
      (simplexMapAmbient_perm_injective π).injOn (image_simplexMapAmbient_perm π)
      (fun x _ ↦ by rw [hdet, hsign]; norm_num)]
    simp [hsign]
  · rw [σ.integral_compContDiffOn_of_det_nonpos _ Filter.univ_mem (mapsTo_simplexMapAmbient π)
      (simplexMapAmbient_perm_injective π).injOn (image_simplexMapAmbient_perm π)
      (fun x _ ↦ by rw [hdet, hsign]; norm_num)]
    simp [hsign]

/-- **Barycentric subdivision preserves simplex integration.** The signed sum of the integrals of a
continuous `p`-form over the barycentric subdivision simplices of `σ` equals the integral of the
form over `σ`. -/
theorem sum_sign_integral_compAffineMapMk_vertex [IsManifold I 1 M]
    (σ : SmoothSimplex I M p) {φ : RoughForm I M F p} (hφ : IsSmoothForm I 0 φ) :
    ∑ π : Equiv.Perm (Fin (p + 1)),
      π.sign • (σ.compAffineMapMk (BarycentricSubdivision.vertex π)).integral φ =
    σ.integral φ := by
  have hterm (π : Equiv.Perm (Fin (p + 1))) :
      (σ.compAffineMapMk (BarycentricSubdivision.vertex π)).integral φ =
        ∫ x in fullSimplex p,
          LinearMap.det
            (affineMapAmbient (BarycentricSubdivision.vertex π)).contLinear.toLinearMap •
            mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ
              (affineMapAmbient (BarycentricSubdivision.vertex π) x)
              (fun i ↦ EuclideanSpace.single i 1) := by
    let A := affineMapAmbient (BarycentricSubdivision.vertex π)
    let τ := σ.compAffineMapMk (BarycentricSubdivision.vertex π)
    rw [τ.integral_eq_setIntegral_mpullbackWithin φ (g := σ.extension ∘ A) fun x ↦ by
      rw [Function.comp_apply, toContinuousMap_compAffineMapMk_apply,
        σ.extension_coe ⟨A x, mapsTo_affineMapAmbient _ x.2⟩]]
    refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
    exact σ.mpullbackWithin_comp_eval_basis (mapsTo_affineMapAmbient _) hx
      A.hasFDerivAt.hasFDerivWithinAt φ
  simp_rw [hterm]
  rw [integral_def]
  exact BarycentricSubdivision.sum_sign_setIntegral_affineMapAmbient_vertex
    (σ.integrableOn_mpullbackWithin hφ σ.extension_coe)

end SmoothSimplex

section SubdivisionChains

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

/-- Reading the barycentric subdivision of a single smooth `p`-simplex in the finitely supported
chain representation gives the signed sum of its `(p + 1)!` subdivision subsimplices. -/
theorem chainsLinearEquivFinsupp_subcomplexSubdivisionX_ιChainComplex {R : Type} [Ring R]
    (σ : SmoothSimplex I M p) (a : R) :
    (smoothSingularSubcomplex I M : SSet).chainsLinearEquivFinsupp R p
      ((subcomplexSubdivisionX (ModuleCat.of R R) (smoothSingularSubcomplex I M) p).hom
        (((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of R R) σ).hom a)) =
    ∑ π : Equiv.Perm (Fin (p + 1)),
      Finsupp.single (σ.compAffineMapMk (BarycentricSubdivision.vertex π)) (π.sign • a) := by
  have hfac := congrArg (fun f ↦ f.hom a)
    (ιChainComplex_subcomplexSubdivisionX (ModuleCat.of R R) (smoothSingularSubcomplex I M) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hfac
  rw [hfac, AffineChain.simplex_def, AffineChain.subdivision_single, map_sum,
    ModuleCat.hom_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  have hvertex :
      ⇑(StdSimplex.affineMapMk (R := ℝ) (StdSimplex.single : Fin (p + 1) → _)) ∘
        BarycentricSubdivision.vertex π = BarycentricSubdivision.vertex π := by
    funext k
    simp [StdSimplex.affineMapMk_apply]
  rw [hvertex, one_mul, AffineChain.subcomplexChain_single, ModuleCat.hom_smul,
    LinearMap.smul_apply, map_zsmul,
    _root_.SSet.chainsLinearEquivFinsupp_ιChainComplex (smoothSingularSubcomplex I M : SSet),
    Finsupp.smul_single, Units.smul_def]
  rfl

/-- **Barycentric subdivision preserves integration of continuous forms on real smooth chains.** -/
@[reassoc]
theorem subcomplexSubdivisionX_comp_integrationCochain [IsManifold I 1 M]
    {φ : RoughForm I M F p} (hφ : IsSmoothForm I 0 φ) :
    subcomplexSubdivisionX (ModuleCat.of ℝ ℝ) (smoothSingularSubcomplex I M) p ≫
      integrationCochain φ = integrationCochain φ := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, integrationCochain_ιChainComplex (I := I),
    one_smul]
  rw [integrationCochain_apply (I := I),
    chainsLinearEquivFinsupp_subcomplexSubdivisionX_ιChainComplex]
  let Iφ : (SmoothSimplex I M p →₀ ℝ) →+ F :=
    AddMonoidHom.mk' (fun c ↦ chainIntegral c φ) (fun c d ↦ chainIntegral_add c d φ)
  -- Express `chainIntegral` as an `AddMonoidHom` to pull the finite sum out.
  change Iφ _ = _
  rw [map_sum]
  refine (Finset.sum_congr rfl fun π _ ↦ ?_).trans
    (SmoothSimplex.sum_sign_integral_compAffineMapMk_vertex σ hφ)
  -- Unfold `Iφ` back to `chainIntegral` on each single-simplex term.
  change chainIntegral _ φ = _
  rw [chainIntegral_single]
  rcases Int.units_eq_one_or π.sign with h | h <;> simp [h]

end SubdivisionChains

end TauCeti
