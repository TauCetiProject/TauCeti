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

Defines smooth, affine, and vertex-permutation reparametrizations of smooth singular simplices
(`compContDiffOn`, `compAffineMapMk`, `compPerm`), their identity, composition, comparison, and
injectivity laws (`compAffineMapMk_vertex_injective`), and change-of-variables and barycentric
subdivision invariance (`integral_compContDiffOn_of_det_nonneg`,
`integral_compContDiffOn_of_det_nonpos`, `integral_compPerm`,
`sum_sign_integral_compAffineMapMk_vertex`,
`chainsLinearEquivFinsupp_subcomplexSubdivisionX_ιChainComplex`,
`subcomplexSubdivisionX_comp_integrationCochain`).

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
    {U : Set (EuclideanSpace ℝ (Fin q))} (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex q))
    (hmaps : MapsTo Ψ (fullSimplex q) (fullSimplex p)) : SmoothSimplex I M q :=
  mk (σ.toContinuousMap.comp
      ⟨hmaps.restrict Ψ (fullSimplex q) (fullSimplex p),
        (hΨ.continuousOn.mono (subset_of_mem_nhdsSet hU)).domRestrict.codRestrict
          fun x ↦ hmaps x.property⟩)
    (σ.contMDiffOnSubset_toContinuousMap.comp_contDiffOn hΨ hU hmaps)

/-- Read on `Δ^q`, `compContDiffOn` evaluates `σ` along `Ψ`. -/
@[simp]
theorem toContinuousMap_compContDiffOn_apply {q : ℕ} (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin p)}
    {U : Set (EuclideanSpace ℝ (Fin q))} (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex q))
    (hmaps : MapsTo Ψ (fullSimplex q) (fullSimplex p)) (x : fullSimplex q) :
    (σ.compContDiffOn hΨ hU hmaps).toContinuousMap x =
      σ.toContinuousMap ⟨Ψ x, hmaps x.property⟩ := by
  simp [compContDiffOn, MapsTo.restrict, Subtype.map]

/-- Reparametrizing a smooth simplex by `id` leaves it unchanged. -/
@[simp]
theorem compContDiffOn_id (σ : SmoothSimplex I M p)
    {U : Set (EuclideanSpace ℝ (Fin p))} (hid : ContDiffOn ℝ ∞ id U)
    (hU : U ∈ 𝓝ˢ (fullSimplex p)) (hmaps : MapsTo id (fullSimplex p) (fullSimplex p)) :
    σ.compContDiffOn hid hU hmaps = σ := by
  ext x; simp

/-- Iterated smooth reparametrization of a smooth simplex agrees with reparametrization by the
composite map. -/
theorem compContDiffOn_compContDiffOn {q r : ℕ} (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin p)}
    {U : Set (EuclideanSpace ℝ (Fin q))} (hΨ : ContDiffOn ℝ ∞ Ψ U)
    (hU : U ∈ 𝓝ˢ (fullSimplex q)) (hmapsΨ : MapsTo Ψ (fullSimplex q) (fullSimplex p))
    {Φ : EuclideanSpace ℝ (Fin r) → EuclideanSpace ℝ (Fin q)}
    {V : Set (EuclideanSpace ℝ (Fin r))} (hΦ : ContDiffOn ℝ ∞ Φ V)
    (hV : V ∈ 𝓝ˢ (fullSimplex r)) (hmapsΦ : MapsTo Φ (fullSimplex r) (fullSimplex q))
    {W : Set (EuclideanSpace ℝ (Fin r))} (hΨΦ : ContDiffOn ℝ ∞ (Ψ ∘ Φ) W)
    (hW : W ∈ 𝓝ˢ (fullSimplex r)) :
    (σ.compContDiffOn hΨ hU hmapsΨ).compContDiffOn hΦ hV hmapsΦ =
      σ.compContDiffOn hΨΦ hW (hmapsΨ.comp hmapsΦ) := by
  ext x; simp

/-- Precompose a smooth `p`-simplex with the affine map `Δ^q → Δ^p` determined by a tuple of
barycentric vertices `v`, specializing `SSet.Subcomplex.compAffineMapMk` to
`smoothSingularSubcomplex I M`. -/
def compAffineMapMk {q : ℕ} (σ : SmoothSimplex I M p)
    (v : Fin (q + 1) → StdSimplex ℝ (Fin (p + 1))) : SmoothSimplex I M q :=
  (smoothSingularSubcomplex I M).compAffineMapMk σ v

/-- `SmoothSimplex.compAffineMapMk` is `SSet.Subcomplex.compAffineMapMk` on
`smoothSingularSubcomplex I M`. -/
theorem compAffineMapMk_def {q : ℕ} (σ : SmoothSimplex I M p)
    (v : Fin (q + 1) → StdSimplex ℝ (Fin (p + 1))) :
    σ.compAffineMapMk v = (smoothSingularSubcomplex I M).compAffineMapMk σ v :=
  (rfl)

/-- Read on `Δ^q`, `compAffineMapMk σ v` precomposes `σ` with `affineMapAmbient v`. -/
@[simp]
theorem toContinuousMap_compAffineMapMk_apply {q : ℕ} (σ : SmoothSimplex I M p)
    (v : Fin (q + 1) → StdSimplex ℝ (Fin (p + 1))) (x : fullSimplex q) :
    (σ.compAffineMapMk v).toContinuousMap x =
      σ.toContinuousMap ⟨affineMapAmbient v x, mapsTo_affineMapAmbient v x.property⟩ := by
  have hx : (⟨affineMapAmbient v x, mapsTo_affineMapAmbient v x.property⟩ : fullSimplex p) =
      (fullSimplexEquivStdSimplex p).symm
        (StdSimplex.affineMapMk v (fullSimplexEquivStdSimplex q x)) :=
    Subtype.ext (affineMapAmbient_coe v x)
  rw [toContinuousMap_apply, compAffineMapMk_def, SSet.Subcomplex.coe_compAffineMapMk,
    Equiv.apply_symm_apply, ContinuousMap.comp_apply, hx, toContinuousMap_apply,
    Homeomorph.apply_symm_apply, StdSimplex.continuousAffineMapMk_apply]

/-- Precomposing a smooth simplex with the standard vertex tuple `StdSimplex.single` leaves it
unchanged. -/
@[simp]
theorem compAffineMapMk_single (σ : SmoothSimplex I M p) :
    σ.compAffineMapMk StdSimplex.single = σ :=
  (smoothSingularSubcomplex I M).compAffineMapMk_single σ

/-- Iterated affine reparametrization of a smooth simplex composes the affine maps of standard
simplices. -/
theorem compAffineMapMk_compAffineMapMk {q r : ℕ} (σ : SmoothSimplex I M p)
    (v : Fin (q + 1) → StdSimplex ℝ (Fin (p + 1)))
    (w : Fin (r + 1) → StdSimplex ℝ (Fin (q + 1))) :
    (σ.compAffineMapMk v).compAffineMapMk w =
      σ.compAffineMapMk (StdSimplex.affineMapMk v ∘ w) :=
  (smoothSingularSubcomplex I M).compAffineMapMk_compAffineMapMk σ v w

/-- Affine reparametrization of a smooth simplex agrees with smooth reparametrization along the
ambient affine extension `affineMapAmbient v`. -/
theorem compAffineMapMk_eq_compContDiffOn {q : ℕ} (σ : SmoothSimplex I M p)
    (v : Fin (q + 1) → StdSimplex ℝ (Fin (p + 1))) :
    σ.compAffineMapMk v =
      σ.compContDiffOn (affineMapAmbient v).contDiff.contDiffOn Filter.univ_mem
        (mapsTo_affineMapAmbient v) := by
  ext x; simp

/-- For a smooth simplex whose underlying map on `Δ^p` is injective, distinct vertex tuples yield
distinct affine reparametrizations. -/
theorem compAffineMapMk_injective {q : ℕ} {σ : SmoothSimplex I M p}
    (hσ : Function.Injective σ.toContinuousMap) :
    Function.Injective (σ.compAffineMapMk (q := q)) := fun v₁ v₂ h ↦
  funext fun k ↦ by
    let x : fullSimplex q := (fullSimplexEquivStdSimplex q).symm (StdSimplex.single k)
    have hx := congrArg (fun τ : SmoothSimplex I M q ↦ τ.toContinuousMap x) h
    simp only [toContinuousMap_compAffineMapMk_apply] at hx
    have hval := congrArg Subtype.val (hσ hx)
    dsimp only at hval
    rw [affineMapAmbient_coe, affineMapAmbient_coe] at hval
    simpa only [x, Homeomorph.apply_symm_apply, StdSimplex.affineMapMk_single] using
      (fullSimplexEquivStdSimplex p).symm.injective (Subtype.ext hval)

/-- For a smooth simplex whose underlying map on `Δ^p` is injective, its `(p + 1)!` barycentric
subdivision simplices are pairwise distinct. -/
theorem compAffineMapMk_vertex_injective {σ : SmoothSimplex I M p}
    (hσ : Function.Injective σ.toContinuousMap) :
    Function.Injective fun π : Equiv.Perm (Fin (p + 1)) ↦
      σ.compAffineMapMk (BarycentricSubdivision.vertex π) :=
  (σ.compAffineMapMk_injective hσ).comp BarycentricSubdivision.vertex_injective

/-- Reorder the vertices of a smooth `p`-simplex by a permutation `π` of `Fin (p + 1)`. -/
def compPerm (σ : SmoothSimplex I M p) (π : Equiv.Perm (Fin (p + 1))) : SmoothSimplex I M p :=
  σ.compAffineMapMk (StdSimplex.single ∘ π)

/-- Read on `Δ^p`, `compPerm σ π` precomposes `σ` with `simplexMapAmbient π`. -/
@[simp]
theorem toContinuousMap_compPerm_apply (σ : SmoothSimplex I M p) (π : Equiv.Perm (Fin (p + 1)))
    (x : fullSimplex p) :
    (σ.compPerm π).toContinuousMap x =
      σ.toContinuousMap ⟨simplexMapAmbient π x, mapsTo_simplexMapAmbient π x.property⟩ := by
  rw [compPerm, toContinuousMap_compAffineMapMk_apply]
  exact congrArg σ.toContinuousMap
    (Subtype.ext (DFunLike.congr_fun (affineMapAmbient_single π) x.val))

/-- Permuting the vertices of a smooth simplex by `1` leaves it unchanged. -/
@[simp]
theorem compPerm_one (σ : SmoothSimplex I M p) :
    σ.compPerm 1 = σ := by
  rw [compPerm, Equiv.Perm.coe_one, Function.comp_id, compAffineMapMk_single]

/-- Iterated vertex permutation of a smooth simplex multiplies the permutations. -/
theorem compPerm_compPerm (σ : SmoothSimplex I M p) (π₁ π₂ : Equiv.Perm (Fin (p + 1))) :
    (σ.compPerm π₁).compPerm π₂ = σ.compPerm (π₁ * π₂) := by
  ext x
  simp only [toContinuousMap_compPerm_apply, Equiv.Perm.coe_mul]
  exact congrArg σ.toContinuousMap
    (Subtype.ext (DFunLike.congr_fun (simplexMapAmbient_comp π₁ π₂).symm x.val))

/-- Vertex permutation of a smooth simplex agrees with smooth reparametrization along
`simplexMapAmbient π`. -/
theorem compPerm_eq_compContDiffOn (σ : SmoothSimplex I M p) (π : Equiv.Perm (Fin (p + 1))) :
    σ.compPerm π =
      σ.compContDiffOn (simplexMapAmbient π).contDiff.contDiffOn Filter.univ_mem
        (mapsTo_simplexMapAmbient π) := by
  ext x; simp

private theorem mpullbackWithin_comp_eval_basis (σ : SmoothSimplex I M p)
    {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p)) {x : EuclideanSpace ℝ (Fin p)}
    (hx : x ∈ fullSimplex p) {L : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hΨ : HasFDerivWithinAt Ψ L (fullSimplex p) x) (φ : RoughForm I M F p) :
    mpullbackWithin (𝓡 p) I (σ.extension ∘ Ψ) (fullSimplex p) φ x
        (fun i ↦ EuclideanSpace.single i 1) =
      L.det • mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p) φ (Ψ x)
        (fun i ↦ EuclideanSpace.single i 1) := by
  have hmp := mpullbackWithin_comp_apply_of_hasFDerivWithinAt hΨ
    ((σ.contMDiffOn_extension (Ψ x) (hmaps hx)).mdifferentiableWithinAt (by simp))
    hmaps (uniqueDiffOn_fullSimplex p x hx) φ
  refine (congrArg (fun η ↦ η (fun i ↦ EuclideanSpace.single i 1)) hmp).trans ?_
  let η := mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p) φ (Ψ x)
  exact congrFun (congrArg DFunLike.coe
    (AlternatingMap.compLinearMap_eq_det_smul (EuclideanSpace.basisFun (Fin p) ℝ).toBasis
      η.toAlternatingMap L.toLinearMap)) (fun i ↦ EuclideanSpace.single i 1)

section Reparam

variable (σ : SmoothSimplex I M p) {Ψ : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
  {U : Set (EuclideanSpace ℝ (Fin p))} (hΨ : ContDiffOn ℝ ∞ Ψ U) (hU : U ∈ 𝓝ˢ (fullSimplex p))
  (hmaps : MapsTo Ψ (fullSimplex p) (fullSimplex p)) (hinj : InjOn Ψ (fullSimplex p))
  (himage : Ψ '' fullSimplex p = fullSimplex p)

include hinj himage

private theorem integral_compContDiffOn_of_det_eq {s : ℝ}
    (hdet : ∀ x ∈ fullSimplex p, (fderiv ℝ Ψ x).det = s * |(fderiv ℝ Ψ x).det|)
    (φ : RoughForm I M F p) :
    (σ.compContDiffOn hΨ hU hmaps).integral φ = s • σ.integral φ := by
  rw [(σ.compContDiffOn hΨ hU hmaps).integral_eq_setIntegral_mpullbackWithin φ
    (g := σ.extension ∘ Ψ) fun x ↦ by
      rw [Function.comp_apply, toContinuousMap_compContDiffOn_apply,
        σ.extension_coe ⟨Ψ x, hmaps x.property⟩]]
  have hΨfderiv : ∀ x ∈ fullSimplex p,
      HasFDerivWithinAt Ψ (fderiv ℝ Ψ x) (fullSimplex p) x := fun x hx ↦
    ((hΨ.contDiffAt (mem_nhdsSet_iff_forall.mp hU x hx)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hpt (x : EuclideanSpace ℝ (Fin p)) (hx : x ∈ fullSimplex p) :
      mpullbackWithin (𝓡 p) I (σ.extension ∘ Ψ) (fullSimplex p) φ x
          (fun i ↦ EuclideanSpace.single i 1) =
        s • |(fderiv ℝ Ψ x).det| • mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p) φ (Ψ x)
          (fun i ↦ EuclideanSpace.single i 1) := by
    rw [smul_smul, ← hdet x hx]; exact σ.mpullbackWithin_comp_eval_basis hmaps hx (hΨfderiv x hx) φ
  rw [setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet hpt, MeasureTheory.integral_smul,
    integral_def]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_fullSimplex p).measurableSet hΨfderiv hinj
    (fun y ↦ mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p) φ y
      (fun i ↦ EuclideanSpace.single i 1))
  rw [himage] at hcov; exact congrArg (s • ·) hcov.symm

/-- **Orientation-preserving reparametrization of simplex integrals.** If `Ψ` is a smooth bijective
self-reparametrization of `Δᵖ` with nonnegative Jacobian determinant everywhere on `Δᵖ`, then
integrating any `p`-form over `σ ∘ Ψ` gives the same value as over `σ`. -/
theorem integral_compContDiffOn_of_det_nonneg
    (hdet : ∀ x ∈ fullSimplex p, 0 ≤ (fderiv ℝ Ψ x).det) (φ : RoughForm I M F p) :
    (σ.compContDiffOn hΨ hU hmaps).integral φ = σ.integral φ := by
  simpa using σ.integral_compContDiffOn_of_det_eq hΨ hU hmaps hinj himage (s := 1)
    (fun x hx ↦ by rw [abs_of_nonneg (hdet x hx), one_mul]) φ

/-- **Orientation-reversing reparametrization of simplex integrals.** If `Ψ` is a smooth bijective
self-reparametrization of `Δᵖ` with nonpositive Jacobian determinant everywhere on `Δᵖ`, then
integrating any `p`-form over `σ ∘ Ψ` negates the integral over `σ`. -/
theorem integral_compContDiffOn_of_det_nonpos
    (hdet : ∀ x ∈ fullSimplex p, (fderiv ℝ Ψ x).det ≤ 0) (φ : RoughForm I M F p) :
    (σ.compContDiffOn hΨ hU hmaps).integral φ = -σ.integral φ := by
  simpa using σ.integral_compContDiffOn_of_det_eq hΨ hU hmaps hinj himage (s := -1)
    (fun x hx ↦ by rw [abs_of_nonpos (hdet x hx), neg_one_mul, neg_neg]) φ

end Reparam

/-- Permuting the vertices of a smooth simplex scales the integral of any `p`-form by the sign of
the permutation. -/
@[simp]
theorem integral_compPerm (σ : SmoothSimplex I M p) (π : Equiv.Perm (Fin (p + 1)))
    (φ : RoughForm I M F p) :
    (σ.compPerm π).integral φ = (π.sign : ℝ) • σ.integral φ := by
  rw [σ.compPerm_eq_compContDiffOn π]
  exact σ.integral_compContDiffOn_of_det_eq _ Filter.univ_mem (mapsTo_simplexMapAmbient π)
    (simplexMapAmbient_perm_injective π).injOn (image_simplexMapAmbient_perm π)
    (fun x _ ↦ by
      rw [(simplexMapAmbient π).hasFDerivAt.fderiv, ContinuousLinearMap.det,
        det_contLinear_simplexMapAmbient_perm]
      rcases Int.units_eq_one_or π.sign with h | h <;> simp [h]) φ

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
          (affineMapAmbient (BarycentricSubdivision.vertex π)).contLinear.det •
            mpullbackWithin (𝓡 p) I σ.extension (fullSimplex p) φ
              (affineMapAmbient (BarycentricSubdivision.vertex π) x)
              (fun i ↦ EuclideanSpace.single i 1) := by
    let A := affineMapAmbient (BarycentricSubdivision.vertex π)
    let τ := σ.compAffineMapMk (BarycentricSubdivision.vertex π)
    rw [τ.integral_eq_setIntegral_mpullbackWithin φ (g := σ.extension ∘ A) fun x ↦ by
      rw [Function.comp_apply, toContinuousMap_compAffineMapMk_apply,
        σ.extension_coe ⟨A x, mapsTo_affineMapAmbient _ x.property⟩]]
    exact setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦
      σ.mpullbackWithin_comp_eval_basis (mapsTo_affineMapAmbient _) hx
        A.hasFDerivAt.hasFDerivWithinAt φ
  simp_rw [hterm]; rw [integral_def]
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
  have hvertex : ⇑(StdSimplex.affineMapMk (R := ℝ) (StdSimplex.single : Fin (p + 1) → _)) ∘
      BarycentricSubdivision.vertex π = BarycentricSubdivision.vertex π :=
    funext fun k ↦ by simp [StdSimplex.affineMapMk_apply]
  rw [hvertex, one_mul, AffineChain.subcomplexChain_single, ← SmoothSimplex.compAffineMapMk_def,
    ModuleCat.hom_smul, LinearMap.smul_apply, map_zsmul,
    _root_.SSet.chainsLinearEquivFinsupp_ιChainComplex (smoothSingularSubcomplex I M : SSet),
    Finsupp.smul_single, ← Units.smul_def]

/-- **Barycentric subdivision preserves integration of continuous forms on smooth chains** with
coefficients in any ring `R` acting on `F` (including both `ℝ` and `ℤ`). -/
@[reassoc]
theorem subcomplexSubdivisionX_comp_integrationCochain [IsManifold I 1 M]
    {R : Type} [Ring R] [Module R F] {φ : RoughForm I M F p} (hφ : IsSmoothForm I 0 φ) :
    subcomplexSubdivisionX (ModuleCat.of R R) (smoothSingularSubcomplex I M) p ≫
      integrationCochain φ = integrationCochain φ := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, integrationCochain_ιChainComplex (I := I),
    one_smul]
  rw [integrationCochain_apply (I := I),
    chainsLinearEquivFinsupp_subcomplexSubdivisionX_ιChainComplex]
  let Iφ : (SmoothSimplex I M p →₀ R) →+ F :=
    AddMonoidHom.mk' (fun c ↦ chainIntegral c φ) (fun c d ↦ chainIntegral_add c d φ)
  refine (map_sum Iφ _ _).trans <| (Finset.sum_congr rfl fun π _ ↦ ?_).trans
    (SmoothSimplex.sum_sign_integral_compAffineMapMk_vertex σ hφ)
  have h := chainIntegral_single (SmoothSimplex.compAffineMapMk σ
    (BarycentricSubdivision.vertex π)) (π.sign • (1 : R)) φ
  rcases Int.units_eq_one_or π.sign with hs | hs <;> simpa [Iφ, hs] using h

/-- Element form of `TauCeti.subcomplexSubdivisionX_comp_integrationCochain`: integrating a
continuous form over the barycentric subdivision of a smooth chain equals integrating it over the
chain. -/
theorem integrationCochain_subcomplexSubdivisionX_apply [IsManifold I 1 M]
    {R : Type} [Ring R] [Module R F] {φ : RoughForm I M F p} (hφ : IsSmoothForm I 0 φ)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of R R)).X p) :
    (integrationCochain φ).hom
        ((subcomplexSubdivisionX (ModuleCat.of R R) (smoothSingularSubcomplex I M) p).hom c) =
      (integrationCochain φ).hom c :=
  ConcreteCategory.congr_hom (subcomplexSubdivisionX_comp_integrationCochain hφ) c

end SubdivisionChains

end TauCeti
