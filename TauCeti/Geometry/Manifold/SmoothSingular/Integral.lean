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
import TauCeti.MeasureTheory.Integral.FullSimplex

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

On a `C¹` manifold, a `C^n` form pulls back within `Δᵖ` to a `C^n` map into alternating maps
(`TauCeti.SmoothSimplex.contDiffOn_mpullbackWithin`); in particular, the integrand of a continuous
form is continuous on the compact simplex, hence integrable
(`TauCeti.SmoothSimplex.integrableOn_mpullbackWithin`), so the integral is linear in the form. It
is natural under smooth maps, `∫_{f ∘ σ} ψ = ∫_σ f^*ψ`
(`TauCeti.SmoothSimplex.integral_smoothSingularSubcomplexMap_app`), transforms under simplicial
operators by precomposition with `simplexMapAmbient` (`TauCeti.SmoothSimplex.integral_map`,
`TauCeti.SmoothSimplex.integral_δ`), vanishes on degeneracies (`TauCeti.SmoothSimplex.integral_σ`),
and over a `0`-simplex evaluates a function at the image point
(`TauCeti.SmoothSimplex.integral_ofFunction`).

These integrals, summed over smooth chains, are the pairing between differential forms and smooth
singular chains that underlies the de Rham homomorphism to singular cohomology.

## Main definitions and results

* `TauCeti.SmoothSimplex.integral`, `TauCeti.SmoothSimplex.integral_def`: the integral of a
  `p`-form over a smooth `p`-simplex.
* `TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullbackWithin`: computation from any extension.
* `TauCeti.SmoothSimplex.integral_eq_setIntegral_mpullback`: computation by the ordinary pullback
  along an extension differentiable at the points of `Δᵖ`.
* `TauCeti.SmoothSimplex.contDiffOn_mpullbackWithin_of_contMDiffAt`,
  `TauCeti.SmoothSimplex.contDiffOn_mpullbackWithin`: `C^n` regularity of the within-set pullback.
* `TauCeti.SmoothSimplex.integral_add`, `TauCeti.SmoothSimplex.integral_neg`,
  `TauCeti.SmoothSimplex.integral_sub`, `TauCeti.SmoothSimplex.integral_smul`,
  `TauCeti.SmoothSimplex.integral_sum`: linearity.
* `TauCeti.SmoothSimplex.integral_map`, `TauCeti.SmoothSimplex.integral_δ`,
  `TauCeti.SmoothSimplex.integral_map_eq_zero_of_lt`, `TauCeti.SmoothSimplex.integral_σ`:
  simplicial operators and degeneracy vanishing.
* `TauCeti.SmoothSimplex.integral_smoothSingularSubcomplexMap_app`: naturality.
* `TauCeti.SmoothSimplex.integral_ofFunction`,
  `TauCeti.SmoothSimplex.integral_equiv₀_symm_ofFunction`: integration over a `0`-simplex is
  evaluation.
* `TauCeti.SmoothSimplex.integral_ofContMDiffOn`,
  `TauCeti.SmoothSimplex.integral_ofContMDiff`: integration over a smooth map on a neighbourhood of
  `Δᵖ` or on `ℝᵖ`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, *Integration over smooth
  chains*.
-/

public section

noncomputable section

open Bundle CategoryTheory MeasureTheory Set Simplicial Opposite Topology
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

/-- The integral over a smooth simplex is the Bochner integral over `Δᵖ` of the within-set pullback
along `σ.extension` evaluated on the standard basis. -/
theorem integral_def (σ : SmoothSimplex I M p) (φ : RoughForm I M F p) :
    σ.integral φ = ∫ x in fullSimplex p, mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I
      σ.extension (fullSimplex p) φ x fun i ↦ EuclideanSpace.single i 1 :=
  (rfl)

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

/-- The integral over a smooth simplex respects negation of forms. -/
@[simp]
theorem integral_neg (σ : SmoothSimplex I M p) (φ : RoughForm I M F p) :
    σ.integral (-φ) = -σ.integral φ := by
  simpa only [neg_one_smul] using σ.integral_smul (-1 : ℝ) φ

variable [IsManifold I 1 M]

/-- Along a map that agrees with a smooth simplex on `Δᵖ`, a `k`-form that is `C^n` at each point
of the image of `σ` pulls back within `Δᵖ` to a `C^n` map into the space of alternating maps on
`ℝᵖ`. -/
theorem contDiffOn_mpullbackWithin_of_contMDiffAt {k : ℕ} {n : ℕ∞}
    (σ : SmoothSimplex I M p) {φ : RoughForm I M F k}
    (hφ : ∀ x : fullSimplex p, ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) (σ.toContinuousMap x))
    {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    ContDiffOn ℝ (F := EuclideanSpace ℝ (Fin p) [⋀^Fin k]→L[ℝ] F) n
      (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) φ) (fullSimplex p) := by
  have hgs := σ.contMDiffOnSubset_toContinuousMap.contMDiffOn hg
  have hu : UniqueMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fullSimplex p) :=
    (uniqueDiffOn_fullSimplex p).uniqueMDiffOn
  intro x hx
  have hgx : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) (g x) := by
    rw [hg ⟨x, hx⟩]
    exact hφ ⟨x, hx⟩
  exact RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
    (hgx.contMDiffWithinAt.mpullbackWithin_form (hgs x hx)
      (by simp) (mapsTo_univ _ _) hx hu)

/-- Along a map that agrees with a smooth simplex on `Δᵖ`, a `C^n` `k`-form pulls back within `Δᵖ`
to a `C^n` map into the space of alternating maps on `ℝᵖ`. -/
theorem contDiffOn_mpullbackWithin {k : ℕ} {n : ℕ∞} (σ : SmoothSimplex I M p)
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    ContDiffOn ℝ (F := EuclideanSpace ℝ (Fin p) [⋀^Fin k]→L[ℝ] F) n
      (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) φ) (fullSimplex p) :=
  σ.contDiffOn_mpullbackWithin_of_contMDiffAt
    (fun x ↦ (isSmoothForm_def _ _).mp hφ (σ.toContinuousMap x)) hg

/-- Along a map that agrees with a smooth simplex on `Δᵖ`, a continuous `p`-form pulls back within
`Δᵖ` to a form that is integrable on `Δᵖ` once evaluated on the standard basis. -/
theorem integrableOn_mpullbackWithin (σ : SmoothSimplex I M p) {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ∀ x : fullSimplex p, g x = σ.toContinuousMap x) :
    IntegrableOn (fun x ↦ mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g (fullSimplex p) φ x
      fun i ↦ EuclideanSpace.single i 1) (fullSimplex p) :=
  ((ContinuousAlternatingMap.apply ℝ _ F _).continuous.comp_continuousOn
    (σ.contDiffOn_mpullbackWithin (n := 0) hφ hg).continuousOn).integrableOn_compact
      (isCompact_fullSimplex p)

/-- The integral over a smooth simplex is additive on continuous forms. -/
theorem integral_add (σ : SmoothSimplex I M p) {φ ψ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    σ.integral (φ + ψ) = σ.integral φ + σ.integral ψ := by
  simp only [integral, mpullbackWithin_add, Pi.add_apply]
  -- `(ω x + η x) v` is `ω x v + η x v` by definition of addition of alternating maps; the rewrite
  -- `ContinuousAlternatingMap.add_apply` does not fire syntactically on tangent spaces.
  exact MeasureTheory.integral_add (σ.integrableOn_mpullbackWithin hφ σ.extension_coe)
    (σ.integrableOn_mpullbackWithin hψ σ.extension_coe)

/-- The integral over a smooth simplex respects subtraction of continuous forms. -/
theorem integral_sub (σ : SmoothSimplex I M p) {φ ψ : RoughForm I M F p}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    σ.integral (φ - ψ) = σ.integral φ - σ.integral ψ := by
  rw [sub_eq_add_neg, σ.integral_add hφ hψ.neg, σ.integral_neg, sub_eq_add_neg]

/-- The integral over a smooth simplex commutes with finite sums of continuous forms. -/
theorem integral_sum {ι : Type*} (σ : SmoothSimplex I M p) (s : Finset ι)
    (φ : ι → RoughForm I M F p) (hφ : ∀ i ∈ s, IsSmoothForm I 0 (φ i)) :
    σ.integral (∑ i ∈ s, φ i) = ∑ i ∈ s, σ.integral (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      σ.integral_add (hφ a (Finset.mem_insert_self a s))
        (IsSmoothForm.sum φ s fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi)]

end Linearity

section Simplicial

/-- Integrating a `q`-form over the image of a smooth `p`-simplex under a simplicial operator
`f : ⦋q⦌ ⟶ ⦋p⦌` integrates over `Δ^q` the pullback of `φ` along `σ`, precomposed with the ambient
affine map `simplexMapAmbient f.toOrderHom`. -/
theorem integral_map {q : ℕ} (f : ⦋q⦌ ⟶ ⦋p⦌) (σ : SmoothSimplex I M p) (φ : RoughForm I M F q) :
    integral ((smoothSingularSubcomplex I M : SSet).map f.op σ) φ =
      ∫ x in fullSimplex q,
        mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ
          (simplexMapAmbient f.toOrderHom x)
          fun i ↦ (simplexMapAmbient f.toOrderHom).contLinear (EuclideanSpace.single i 1) := by
  let L := simplexMapAmbient f.toOrderHom
  rw [integral_eq_setIntegral_mpullbackWithin _ φ (g := σ.extension ∘ L) fun x ↦ by
    rw [Function.comp_apply, toContinuousMap_map_apply,
      ← σ.extension_coe ⟨L x, mapsTo_simplexMapAmbient _ x.2⟩]]
  refine setIntegral_congr_fun (isClosed_fullSimplex q).measurableSet fun x hx ↦ ?_
  rw [mpullbackWithin_comp_apply_of_hasFDerivWithinAt L.hasFDerivWithinAt
    ((σ.contMDiffOn_extension (L x) (mapsTo_simplexMapAmbient _ hx)).mdifferentiableWithinAt
      (by simp))
    (mapsTo_simplexMapAmbient _) (uniqueDiffOn_fullSimplex q x hx) φ]
  -- `compContinuousLinearMap` evaluates by precomposing the vector arguments.
  rfl

/-- Integrating a `p`-form over the `i`-th face of a smooth `(p + 1)`-simplex integrates over `Δᵖ`
the pullback of `φ` along the simplex, restricted along the ambient face map
`simplexMapAmbient i.succAbove`. -/
theorem integral_δ (i : Fin (p + 2)) (σ : SmoothSimplex I M (p + 1)) (φ : RoughForm I M F p) :
    integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ =
      ∫ x in fullSimplex p,
        mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I σ.extension (fullSimplex (p + 1)) φ
          (simplexMapAmbient i.succAbove x)
          fun k ↦ (simplexMapAmbient i.succAbove).contLinear (EuclideanSpace.single k 1) :=
  integral_map (SimplexCategory.δ i) σ φ

/-- If `p < q`, the integral of any `q`-form over the image of a smooth `p`-simplex under a
simplicial operator `f : ⦋q⦌ ⟶ ⦋p⦌` vanishes, since any `q` vectors in `ℝᵖ` are linearly
dependent. -/
theorem integral_map_eq_zero_of_lt {q : ℕ} (hpq : p < q) (f : ⦋q⦌ ⟶ ⦋p⦌)
    (σ : SmoothSimplex I M p) (φ : RoughForm I M F q) :
    integral ((smoothSingularSubcomplex I M : SSet).map f.op σ) φ = 0 := by
  rw [integral_map]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x _ ↦ ?_
  let η : EuclideanSpace ℝ (Fin p) [⋀^Fin q]→L[ℝ] F :=
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p) φ
      (simplexMapAmbient f.toOrderHom x)
  have hdep : ¬ LinearIndependent ℝ (fun i : Fin q ↦
      (simplexMapAmbient f.toOrderHom).contLinear (EuclideanSpace.single i 1)) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace_fin, SimplexCategory.len_mk] at hcard
    exact hpq.not_ge hcard
  exact η.toAlternatingMap.map_linearDependent _ hdep

-- `simp` reduces `SmoothSimplex` in implicit type arguments via `Subfunctor.toFunctor_obj` before
-- looking up `integral_σ`, so the left-hand side is normalized with `dsimp% only`.
/-- **Degeneracy vanishing.** The integral of any `(p + 1)`-form over a degenerate smooth
`(p + 1)`-simplex vanishes. -/
@[simp]
theorem integral_σ (i : Fin (p + 1)) (σ : SmoothSimplex I M p) (φ : RoughForm I M F (p + 1)) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (integral ((smoothSingularSubcomplex I M : SSet).σ i σ) φ)) = 0 :=
  integral_map_eq_zero_of_lt (Nat.lt_succ_self p) (SimplexCategory.σ i) σ φ

end Simplicial

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
  have hx : ∀ x : EuclideanSpace ℝ (Fin 0), x = 0 := fun x ↦ Subsingleton.elim x 0
  rw [integral_eq_setIntegral_mpullbackWithin σ _ (g := fun _ ↦ σ.toContinuousMap
    ⟨0, zero_mem_fullSimplex 0⟩) fun x ↦ congrArg σ.toContinuousMap (Subtype.ext (hx x.1).symm)]
  rw [mpullbackWithin_ofFunction]
  refine (setIntegral_congr_fun (isClosed_fullSimplex 0).measurableSet
    (g := fun _ ↦ a (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 0⟩))
    fun x _ ↦ RoughForm.ofFunction_apply (M := EuclideanSpace ℝ (Fin 0)) _ _ _).trans ?_
  rw [setIntegral_const, volume_real_fullSimplex_zero, one_smul]

/-- Integrating the `0`-form of a function over the smooth `0`-simplex of `x₀` evaluates the
function at `x₀`. -/
theorem integral_equiv₀_symm_ofFunction [CompleteSpace F] (x₀ : M) (a : M → F) :
    ((equiv₀ I M).symm x₀).integral (RoughForm.ofFunction I a) = a x₀ := by
  rw [integral_ofFunction, toContinuousMap_equiv₀_symm_apply]

/-- Integrating over `SmoothSimplex.ofContMDiffOn hg hU` integrates the ordinary pullback along `g`
over `Δᵖ`. -/
theorem integral_ofContMDiffOn {U : Set (EuclideanSpace ℝ (Fin p))}
    {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g U) (hU : U ∈ 𝓝ˢ (fullSimplex p))
    (φ : RoughForm I M F p) :
    (ofContMDiffOn hg hU).integral φ = ∫ x in fullSimplex p,
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g φ x fun i ↦ EuclideanSpace.single i 1 :=
  (ofContMDiffOn hg hU).integral_eq_setIntegral_mpullback φ
    (fun x ↦ (toContinuousMap_ofContMDiffOn_apply hg hU x).symm)
    fun x hx ↦ ((hg.contMDiffAt (Filter.mem_of_superset (mem_nhdsSet_iff_forall.mp hU x hx)
      Subset.rfl)).mdifferentiableAt (by simp))

/-- Integrating over `SmoothSimplex.ofContMDiff hg` integrates the ordinary pullback along `g` over
`Δᵖ`. -/
theorem integral_ofContMDiff {g : EuclideanSpace ℝ (Fin p) → M}
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I ∞ g) (φ : RoughForm I M F p) :
    (ofContMDiff hg).integral φ = ∫ x in fullSimplex p,
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I g φ x fun i ↦ EuclideanSpace.single i 1 :=
  (ofContMDiff hg).integral_eq_setIntegral_mpullback φ
    (fun x ↦ (toContinuousMap_ofContMDiff_apply hg x).symm)
    fun x _ ↦ (hg.mdifferentiable (by simp)) x

end SmoothSimplex

end TauCeti
