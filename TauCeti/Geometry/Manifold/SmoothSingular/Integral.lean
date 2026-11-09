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
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integration of differential forms over smooth singular simplices

A smooth singular `p`-simplex `σ` of a manifold `M` (`TauCeti.SmoothSimplex I M p`) is read on the
full-dimensional standard simplex `Δᵖ = {x ∈ ℝᵖ | 0 ≤ xᵢ, ∑ xᵢ ≤ 1}`. The integral of a
`p`-form `φ` over `σ` is

`∫_σ φ = ∫_{Δᵖ} (σ^*φ)(e₁, …, eₚ) dx`,

the Bochner integral over `Δᵖ` of the pullback of `φ`, evaluated on the standard basis of `ℝᵖ`.
It is meaningful for a complete coefficient space `F` and an integrable integrand, such as that of a
continuous form; otherwise Bochner's convention makes it `0`.
The derivative of `σ` is taken within `Δᵖ`, where it is unique at every point, faces and corners
included (`TauCeti.uniqueDiffOn_fullSimplex`), and it only depends on the values of `σ` on `Δᵖ`.
Hence the integral may be computed from any map `g : ℝᵖ → M` that agrees with `σ` on `Δᵖ`
(`TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullbackWithin`), and with the ordinary pullback
along such a `g` when it is differentiable at each point of `Δᵖ`
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

* `TauCeti.SmoothSimplex.integral`: the integral of a `p`-form over a smooth `p`-simplex.
* `TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullbackWithin`: computation from any extension.
* `TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullback`: computation by the ordinary pullback
  along an extension differentiable at the points of `Δᵖ`.
* `TauCeti.SmoothSimplex.integral_δ`: the integral over a face as a boundary term of Stokes' theorem
  on the standard simplex.
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

namespace SmoothSimplex

/-- The integral of a `p`-form `φ` over a smooth singular `p`-simplex `σ`: the integral over the
full-dimensional simplex `Δᵖ ⊆ ℝᵖ` of the pullback `σ^*φ` evaluated on the standard basis, with the
derivative of `σ` taken within `Δᵖ`. To form that derivative, `σ` is extended to `ℝᵖ`
(`TauCeti.SmoothSimplex.extension`); only its values on `Δᵖ` matter
(`TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullbackWithin`).

This is a Bochner integral: it is meaningful when `F` is complete and the integrand is integrable,
as for continuous forms (`TauCeti.SmoothSimplex.integrableOn_mpullbackWithin`), and it is `0`
otherwise. -/
def integral (σ : SmoothSimplex I M p) (φ : RoughForm I M F p) : F :=
  ∫ x in fullSimplex p, mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
    (fullSimplex p) φ x fun i ↦ EuclideanSpace.single i 1

/-- The integral over a smooth simplex may be computed from any map `g : ℝᵖ → M` that agrees with
the simplex on `Δᵖ`, differentiating within `Δᵖ`. -/
theorem integral_eq_setIntegral_mpullbackWithin (σ : SmoothSimplex I M p)
    (φ : RoughForm I M F p) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    σ.integral φ = ∫ x in fullSimplex p,
      mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) φ x
        fun i ↦ EuclideanSpace.single i 1 := by
  rw [integral]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [mpullbackWithin_congr (g := g) (fun y hy ↦ ?_) hx]
  rw [σ.extension_coe ⟨y, hy⟩, hg ⟨y, hy⟩]

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

/-- The integral over the `i`-th face of a smooth simplex `σ` is the integral over `Δᵖ` of the
pullback of the form along `σ`, within `Δᵖ⁺¹`, evaluated at the points and on the edge vectors of
the `i`-th face of `Δᵖ⁺¹`. These are the boundary terms of Stokes' theorem on the standard
simplex. -/
theorem integral_δ (σ : SmoothSimplex I M (p + 1)) (i : Fin (p + 2)) (φ : RoughForm I M F p) :
    integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ =
      ∫ y in fullSimplex p, mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I σ.extension
        (fullSimplex (p + 1)) φ (simplexMapAmbient i.succAbove y)
          (fun k ↦ (simplexMapAmbient i.succAbove).contLinear (EuclideanSpace.single k 1)) := by
  set A := simplexMapAmbient (m := p) i.succAbove
  rw [integral_eq_setIntegral_mpullbackWithin _ φ (g := σ.extension ∘ A) fun x ↦ by
    rw [Function.comp_apply, simplexMapAmbient_succAbove_coe, extension_coe, toContinuousMap_δ]]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun y hy ↦ ?_
  have hu : UniqueDiffWithinAt ℝ (fullSimplex p) y := uniqueDiffOn_fullSimplex p y hy
  have hA : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) A (fullSimplex p) y :=
    A.differentiableAt.differentiableWithinAt.mdifferentiableWithinAt
  have hσ : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I σ.extension
      (fullSimplex (p + 1)) (A y) :=
    (σ.contMDiffOn_extension (A y) (mapsTo_simplexMapAmbient _ hy)).mdifferentiableWithinAt
      (by simp)
  rw [mpullbackWithin_comp_at hA hσ (mapsTo_simplexMapAmbient _)
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 hu)]
  refine (mpullbackWithin_apply (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1)))) A (fullSimplex p) _ y _).trans ?_
  rw [mfderivWithin_eq_fderivWithin, A.fderivWithin hu]
  -- Both sides evaluate the same form on the same vectors, typed once as tangent vectors of the
  -- model space and once as its points; these types agree by definition.
  rfl

section Linearity

/-- The integral of the zero form vanishes. -/
@[simp]
theorem integral_zero (σ : SmoothSimplex I M p) : σ.integral (0 : RoughForm I M F p) = 0 := by
  simp only [integral, mpullbackWithin_zero, Pi.zero_apply]
  -- `(0 : _ [⋀^Fin p]→L[ℝ] F) v` is `0` by definition of the zero alternating map, which `simp`
  -- does not normalise when the domain is a tangent space.
  exact MeasureTheory.integral_zero _ _

/-- The integral over a smooth simplex is homogeneous in the form, for any scalars acting on the
coefficients compatibly with the real structure, such as complex scalars on complex-valued forms. -/
@[simp]
theorem integral_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (σ : SmoothSimplex I M p) (c : 𝕜) (φ : RoughForm I M F p) :
    σ.integral (c • φ) = c • σ.integral φ := by
  simp only [integral, mpullbackWithin_smul, Pi.smul_apply]
  -- `(c • ω x) v` is `c • ω x v` by definition of the scalar action on alternating maps; the
  -- rewrite `ContinuousAlternatingMap.smul_apply` does not fire syntactically on tangent spaces.
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
  -- `(ω x + η x) v` is `ω x v + η x v` by definition of addition of alternating maps; the rewrite
  -- `ContinuousAlternatingMap.add_apply` does not fire syntactically on tangent spaces.
  exact MeasureTheory.integral_add (σ.integrableOn_mpullbackWithin hφ σ.extension_coe)
    (σ.integrableOn_mpullbackWithin hψ σ.extension_coe)

end Linearity

section Naturality

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]

/-- **Naturality of integration over smooth simplices.** Integrating over the image of a smooth
simplex under a smooth map is integrating the pulled-back form over the simplex. -/
theorem integral_smoothSingularSubcomplexMap_app {f : M → N} (hf : ContMDiff I J ∞ f)
    (σ : SmoothSimplex I M p) (ψ : RoughForm J N F p) :
    integral ((smoothSingularSubcomplexMap f hf).app (op ⦋p⦌) σ) ψ =
      σ.integral (mpullback I J f ψ) := by
  rw [integral_eq_setIntegral_mpullbackWithin _ ψ (g := f ∘ σ.extension) fun x ↦ by
    rw [toContinuousMap_smoothSingularSubcomplexMap_app]
    simp, integral]
  refine setIntegral_congr_fun (isClosed_fullSimplex p).measurableSet fun x hx ↦ ?_
  rw [mpullbackWithin_comp_at (t := univ)
    ((σ.contMDiffOn_extension x hx).mdifferentiableWithinAt (by simp))
    (hf.mdifferentiable (by simp) (σ.extension x)).mdifferentiableWithinAt (mapsTo_univ _ _)
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
