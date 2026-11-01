/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integration of differential forms over smooth singular simplices

A smooth singular `p`-simplex `σ` of a manifold `M` (`TauCeti.SmoothSimplex I M p`) is read on the
full-dimensional standard simplex `Δᵖ = {x ∈ ℝᵖ | 0 ≤ xᵢ, ∑ xᵢ ≤ 1}`. The integral of a
`p`-form `φ` over `σ` is

`∫_σ φ = ∫_{Δᵖ} (σ^*φ)(e₁, …, eₚ) dx`,

the Lebesgue integral over `Δᵖ` of the pullback of `φ`, evaluated on the standard basis of `ℝᵖ`.
The derivative of `σ` is taken within `Δᵖ`, where it is unique at every point, faces and corners
included (`TauCeti.uniqueDiffOn_fullSimplex`), and it only depends on the values of `σ` on `Δᵖ`.
Hence the integral may be computed from any map `g : ℝᵖ → M` that agrees with `σ` on `Δᵖ`
(`TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullbackWithin`), and with the ordinary pullback
along such a `g` when it is differentiable on a neighbourhood of `Δᵖ`
(`TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullback`). No single smooth extension of `σ` to a
neighbourhood of `Δᵖ` need exist, which is why the derivative within `Δᵖ` defines the integral.

The integrand of a continuous form is continuous on the compact simplex, hence integrable
(`TauCeti.SmoothSimplex.integrableOn_mpullbackWithin`), so the integral is linear in the form. It
is natural under smooth maps, `∫_{f ∘ σ} ψ = ∫_σ f^*ψ`
(`TauCeti.SmoothSimplex.integral_smoothSingularSubcomplexMap_app`), and over a `0`-simplex it
evaluates a function at the image point (`TauCeti.SmoothSimplex.integral_ofFunction`).

These integrals, summed over smooth chains, are the pairing between differential forms and smooth
singular chains that underlies the de Rham homomorphism to singular cohomology.

## Main definitions and results

* `TauCeti.SmoothSimplex`: the smooth singular `p`-simplices, the `p`-simplices of
  `TauCeti.smoothSingularSubcomplex`.
* `TauCeti.SmoothSimplex.toContinuousMap`: a smooth simplex as a map on `Δᵖ`.
* `TauCeti.SmoothSimplex.integral`: the integral of a `p`-form over a smooth `p`-simplex.
* `TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullbackWithin`,
  `TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullback`: computation from any extension.
* `TauCeti.SmoothSimplex.integral_add`, `TauCeti.SmoothSimplex.integral_smul`: linearity.
* `TauCeti.SmoothSimplex.integral_smoothSingularSubcomplexMap_app`: naturality.
* `TauCeti.SmoothSimplex.integral_ofFunction`: integration over a `0`-simplex is evaluation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, *Integration over smooth
  chains*.
-/

public section

noncomputable section

open CategoryTheory MeasureTheory Set Simplicial Opposite
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

variable (I M) in
/-- The smooth singular `p`-simplices of `M`: the `p`-simplices of the subcomplex
`TauCeti.smoothSingularSubcomplex I M` of the singular simplicial set. They generate the smooth
singular chains. -/
abbrev SmoothSimplex (p : ℕ) : Type u :=
  (smoothSingularSubcomplex I M : SSet.{u}) _⦋p⦌

namespace SmoothSimplex

/-- A smooth singular simplex as a continuous map on the full-dimensional simplex `Δᵖ`. -/
def toContinuousMap (σ : SmoothSimplex I M p) : C(fullSimplex p, M) :=
  ((TopCat.of M).toSSetObjEquiv _ σ.1).comp
    ⟨fullSimplexEquivStdSimplex p, (fullSimplexEquivStdSimplex p).continuous⟩

/-- A smooth singular simplex read on `Δᵖ` is the underlying singular simplex read through the
identification of `Δᵖ` with the barycentric standard simplex. -/
theorem toContinuousMap_apply (σ : SmoothSimplex I M p) (x : fullSimplex p) :
    σ.toContinuousMap x = (TopCat.of M).toSSetObjEquiv _ σ.1 (fullSimplexEquivStdSimplex p x) :=
  (rfl)

/-- A smooth singular simplex is smooth on `Δᵖ` in the sense of maps on arbitrary subsets. -/
theorem contMDiffOnSubset_toContinuousMap (σ : SmoothSimplex I M p) :
    ContMDiffOnSubset I ∞ σ.toContinuousMap :=
  (mem_smoothSingularSubcomplex_iff σ.1).mp σ.2

/-- The integral of a `p`-form `φ` over a smooth singular `p`-simplex `σ`: the integral over the
full-dimensional simplex `Δᵖ ⊆ ℝᵖ` of the pullback `σ^*φ` evaluated on the standard basis, with the
derivative of `σ` taken within `Δᵖ`. To form that derivative, `σ` is extended to `ℝᵖ` by its value
at the origin; only its values on `Δᵖ` matter
(`TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullbackWithin`). -/
def integral (σ : SmoothSimplex I M p) (φ : RoughForm I M F p) : F :=
  ∫ x in fullSimplex p, mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I
    (Function.extend Subtype.val σ.toContinuousMap
      fun _ ↦ σ.toContinuousMap ⟨0, zero_mem_fullSimplex p⟩)
    (fullSimplex p) φ x fun i ↦ EuclideanSpace.single i 1

/-- The extension of a smooth simplex used to define its integrals agrees with it on `Δᵖ`. -/
private theorem extend_coe (σ : SmoothSimplex I M p) (x : fullSimplex p) :
    Function.extend Subtype.val σ.toContinuousMap
      (fun _ ↦ σ.toContinuousMap ⟨0, zero_mem_fullSimplex p⟩) x = σ.toContinuousMap x :=
  Subtype.val_injective.extend_apply _ _ x

/-- The integral over a smooth simplex may be computed from any map `g : ℝᵖ → M` that agrees with
the simplex on `Δᵖ`, differentiating within `Δᵖ`. -/
theorem integral_eq_setIntegral_mpullbackWithin (σ : SmoothSimplex I M p)
    (φ : RoughForm I M F p) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    σ.integral φ = ∫ x in fullSimplex p,
      mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) φ x
        fun i ↦ EuclideanSpace.single i 1 := by
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [mpullbackWithin_congr (fun y hy ↦ ?_) hx]
  rw [σ.extend_coe ⟨y, hy⟩, hg ⟨y, hy⟩]

/-- The integral over a smooth simplex may be computed by the ordinary pullback along any map
`g : ℝᵖ → M` that agrees with the simplex on `Δᵖ` and is differentiable at each point of `Δᵖ`, for
instance the restriction of a smooth map on a neighbourhood of `Δᵖ`. -/
theorem integral_eq_setIntegral_mpullback (σ : SmoothSimplex I M p)
    (φ : RoughForm I M F p) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x)
    (hgd : ∀ x ∈ fullSimplex p, MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g x) :
    σ.integral φ = ∫ x in fullSimplex p,
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g φ x fun i ↦ EuclideanSpace.single i 1 := by
  rw [σ.integral_eq_setIntegral_mpullbackWithin φ hg]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [mpullbackWithin_eq_mpullback
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx)) (hgd x hx)]

section Linearity

/-- The integral of the zero form vanishes. -/
@[simp]
theorem integral_zero (σ : SmoothSimplex I M p) : σ.integral (0 : RoughForm I M F p) = 0 := by
  rw [integral, mpullbackWithin_zero]
  exact MeasureTheory.integral_zero _ _

/-- The integral over a smooth simplex is homogeneous in the form. -/
@[simp]
theorem integral_smul (σ : SmoothSimplex I M p) (c : ℝ) (φ : RoughForm I M F p) :
    σ.integral (c • φ) = c • σ.integral φ := by
  rw [integral, integral, mpullbackWithin_smul]
  exact MeasureTheory.integral_smul c _

variable [IsManifold I 1 M]

/-- Along a map that agrees with a smooth simplex on `Δᵖ`, a continuous `p`-form pulls back within
`Δᵖ` to a form that is integrable on `Δᵖ` once evaluated on the standard basis. -/
theorem integrableOn_mpullbackWithin (σ : SmoothSimplex I M p) {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    IntegrableOn (fun x ↦ mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) φ x
      fun i ↦ EuclideanSpace.single i 1) (fullSimplex p) := by
  have hgs := σ.contMDiffOnSubset_toContinuousMap.contMDiffOn hg
  have hu : UniqueMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fullSimplex p) :=
    (uniqueDiffOn_fullSimplex p).uniqueMDiffOn
  have hc : ContinuousOn (Y := EuclideanSpace ℝ (Fin p) [⋀^Fin p]→L[ℝ] F)
      (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) φ) (fullSimplex p) :=
    fun x hx ↦ (RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      (((isSmoothForm_def _ _).mp hφ (g x)).contMDiffWithinAt.mpullbackWithin_form (hgs x hx)
        (by simp) (mapsTo_univ _ _) hx hu)).continuousWithinAt
  exact ((ContinuousAlternatingMap.apply ℝ _ F _).continuous.comp_continuousOn hc
    ).integrableOn_compact (isCompact_fullSimplex p)

/-- The integral over a smooth simplex is additive on continuous forms. -/
theorem integral_add (σ : SmoothSimplex I M p) {φ ψ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    σ.integral (φ + ψ) = σ.integral φ + σ.integral ψ := by
  simp only [integral, mpullbackWithin_add, Pi.add_apply]
  exact MeasureTheory.integral_add (σ.integrableOn_mpullbackWithin hφ σ.extend_coe)
    (σ.integrableOn_mpullbackWithin hψ σ.extend_coe)

end Linearity

section Naturality

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]

/-- The image of a smooth simplex under a smooth map, read on `Δᵖ`, is the composite. -/
theorem toContinuousMap_smoothSingularSubcomplexMap_app {f : M → N} (hf : ContMDiff I J ∞ f)
    (σ : SmoothSimplex I M p) :
    toContinuousMap ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ) =
      (ContinuousMap.mk f hf.continuous).comp σ.toContinuousMap := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (smoothSingularSubcomplexMap_ι hf) (op ⦋p⦌)) σ
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app,
    TypeCat.ofHom_apply] at h
  ext x
  rw [toContinuousMap_apply, h, TopCat.toSSetObjEquiv_toSSet_map_app]
  simp [toContinuousMap_apply]

/-- **Naturality of integration over smooth simplices.** Integrating over the image of a smooth
simplex under a smooth map is integrating the pulled-back form over the simplex. -/
theorem integral_smoothSingularSubcomplexMap_app {f : M → N} (hf : ContMDiff I J ∞ f)
    (σ : SmoothSimplex I M p) (ψ : RoughForm J N F p) :
    integral ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ) ψ =
      σ.integral (mpullback I J f ψ) := by
  set g := Function.extend Subtype.val σ.toContinuousMap
    fun _ ↦ σ.toContinuousMap ⟨0, zero_mem_fullSimplex p⟩
  have hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x := σ.extend_coe
  have hgs := σ.contMDiffOnSubset_toContinuousMap.contMDiffOn hg
  rw [integral_eq_setIntegral_mpullbackWithin _ ψ (g := f ∘ g) fun x ↦ by
    rw [toContinuousMap_smoothSingularSubcomplexMap_app]
    simp [hg x]]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [mpullbackWithin_comp_at (t := univ) ((hgs x hx).mdifferentiableWithinAt (by simp))
    (hf.mdifferentiable (by simp) (g x)).mdifferentiableWithinAt (mapsTo_univ _ _)
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx)),
    mpullbackWithin_univ]

end Naturality

/-- Integrating the `0`-form of a function over a smooth `0`-simplex evaluates the function at the
image point of the simplex. The coefficient space is complete, as Bochner integration requires. -/
@[simp]
theorem integral_ofFunction [CompleteSpace F] (σ : SmoothSimplex I M 0) (a : M → F) :
    σ.integral (RoughForm.ofFunction I a) = a (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 0⟩) := by
  have hs : fullSimplex 0 = univ := eq_univ_of_forall fun x ↦ by simp
  have hx : ∀ x : EuclideanSpace ℝ (Fin 0), x = 0 := fun x ↦ Subsingleton.elim x 0
  rw [integral_eq_setIntegral_mpullbackWithin σ _ (g := fun _ ↦ σ.toContinuousMap
    ⟨0, zero_mem_fullSimplex 0⟩) fun x ↦ congrArg σ.toContinuousMap (Subtype.ext (hx x.1).symm)]
  rw [mpullbackWithin_ofFunction]
  refine (setIntegral_congr_fun (isClosed_fullSimplex 0).measurableSet
    (g := fun _ ↦ a (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 0⟩))
    fun x _ ↦ RoughForm.ofFunction_apply (M := EuclideanSpace ℝ (Fin 0)) _ _ _).trans ?_
  have hvol : volume.real (fullSimplex 0) = 1 := by
    rw [hs, volume_euclideanSpace_eq_dirac]
    simp
  rw [setIntegral_const, hvol, one_smul]

end SmoothSimplex

end TauCeti
