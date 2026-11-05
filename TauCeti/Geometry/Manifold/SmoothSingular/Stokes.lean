/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.SmoothSingular.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Simplex
import TauCeti.MeasureTheory.Integral.FullSimplex
import TauCeti.MeasureTheory.Measure.Haar.EuclideanSpace

/-!
# Stokes' theorem for smooth singular simplices

For a smooth singular `(p + 1)`-simplex `σ` of a `C²` manifold `M` (possibly with boundary or
corners) and a `C¹` `p`-form `φ` with values in a complete normed space `F`, Stokes' theorem on
`σ` states that the integral of the exterior derivative `dφ` over `σ` equals the alternating sum of
the integrals of `φ` over the faces of `σ`:

`∫_σ dφ = ∑_{i = 0}^{p + 1} (-1)ⁱ ∫_{δᵢ σ} φ`

(`TauCeti.SmoothSimplex.integral_mextDeriv`). The proof is independent of manifold-level Stokes'
theorem on oriented manifolds with boundary: `σ.extension` is `C^∞` within the closed simplex
`Δᵖ⁺¹`, `Δᵖ⁺¹` has unique derivatives (`TauCeti.uniqueDiffOn_fullSimplex`) and is the closure of
its interior (`TauCeti.closure_interior_fullSimplex`), so within-set pullback commutes with exterior
differentiation on `Δᵖ⁺¹` (`TauCeti.extDerivWithin_mpullbackWithin`). Applying Euclidean simplex
Stokes (`ContDiffOn.integral_extDerivWithin_fullSimplex`) to the `C¹` pulled-back form
(`TauCeti.SmoothSimplex.contDiffOn_mpullbackWithin_of_contMDiffAt`) and identifying the face
integrals via `TauCeti.SmoothSimplex.integral_δ` yields the formula.

In degree `0`, the fundamental theorem of calculus for smooth `1`-simplices holds on any charted
space without manifold smoothness hypotheses
(`TauCeti.SmoothSimplex.integral_mextDeriv_ofFunction`), and for general `C¹` `0`-forms on any `C¹`
manifold (`TauCeti.SmoothSimplex.integral_mextDeriv_eq_sub`). Integrating a `1`-form over the smooth
`1`-simplex `SmoothSimplex.ofCurve hγ` of a smooth curve `γ : ℝ → M` agrees with the line integral
`pathIntegral φ γ 0 1` (`TauCeti.SmoothSimplex.integral_ofCurve`), and integrating the standard
coordinate `1`-form `dt` on `ℝ` over the identity `1`-simplex yields `+1`
(`TauCeti.SmoothSimplex.integral_ofCurve_id_realLineCoordForm`).

Through `TauCeti.cochainValuesEquiv`, simplex Stokes expresses the simplicial coboundary of the
cochain `σ ↦ ∫_σ φ` as the cochain `σ ↦ ∫_σ dφ`
(`TauCeti.d_comp_cochainValuesEquiv_symm_integral`), so closed forms define cocycles on the
smooth singular chain complex.

## Main results

* `TauCeti.SmoothSimplex.integral_mextDeriv_of_contMDiffAt`,
  `TauCeti.SmoothSimplex.integral_mextDeriv`,
  `TauCeti.SmoothSimplex.integral_mextDerivₗ`: Stokes' theorem for smooth singular simplices.
* `TauCeti.SmoothSimplex.sum_integral_δ_eq_zero_of_mextDeriv_eq_zero_on`,
  `TauCeti.SmoothSimplex.sum_integral_δ_eq_zero_of_mextDeriv_eq_zero`,
  `TauCeti.SmoothSimplex.sum_integral_δ_eq_zero_of_mem_closedForms`: closed forms integrate to zero
  over the boundary of a smooth `(p + 1)`-simplex.
* `TauCeti.SmoothSimplex.integral_mextDeriv_ofFunction_of_contMDiffAt`,
  `TauCeti.SmoothSimplex.integral_mextDeriv_ofFunction`,
  `TauCeti.SmoothSimplex.integral_mextDeriv_eq_sub`,
  `TauCeti.SmoothSimplex.integral_eq_zero_of_mem_exactForms_of_eq`: degree-`0` fundamental theorem
  of calculus on smooth `1`-simplices.
* `TauCeti.SmoothSimplex.integral_ofCurve`,
  `TauCeti.SmoothSimplex.integral_ofCurve_id_realLineCoordForm`: compatibility with `pathIntegral`
  and concrete orientation check.
* `TauCeti.d_comp_cochainValuesEquiv_symm_integral`,
  `TauCeti.d_comp_cochainValuesEquiv_symm_integral_eq_zero`,
  `TauCeti.d_comp_cochainValuesEquiv_symm_integral_eq_zero_of_mem_closedForms`: simplicial
  coboundary of simplex integration.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.12 (Stokes's
  theorem for chains).
-/

public section

noncomputable section

open Bundle CategoryTheory MeasureTheory Set Simplicial Opposite
open scoped Manifold ContDiff

universe u

namespace TauCeti

namespace SmoothSimplex

section Stokes

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℕ}

/-- **Stokes' theorem for smooth singular simplices** (pointwise `C¹` hypothesis). For a smooth
singular `(p + 1)`-simplex `σ` of a `C²` manifold `M` and a `p`-form `φ` with values in a complete
space `F` that is `C¹` at each point of the image of `σ`, the integral of `dφ` over `σ` is the
alternating sum of the integrals of `φ` over the faces of `σ`. -/
theorem integral_mextDeriv_of_contMDiffAt (σ : SmoothSimplex I M (p + 1))
    {φ : RoughForm I M F p}
    (hφ : ∀ x : fullSimplex (p + 1), ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin p]→L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin p]→L[ℝ] F) y (φ y)) (σ.toContinuousMap x)) :
    σ.integral (mextDeriv φ) =
      ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ := by
  have hpull : ContDiffOn ℝ
      (F := EuclideanSpace ℝ (Fin (p + 1)) [⋀^Fin p]→L[ℝ] F) 1
      (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I σ.extension (fullSimplex (p + 1)) φ)
      (fullSimplex (p + 1)) :=
    σ.contDiffOn_mpullbackWithin_of_contMDiffAt (n := 1) hφ σ.extension_coe
  have hext : ∀ x ∈ fullSimplex (p + 1),
      mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I σ.extension
        (fullSimplex (p + 1)) (mextDeriv φ) x =
      extDerivWithin
        (mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) I σ.extension
          (fullSimplex (p + 1)) φ)
        (fullSimplex (p + 1)) x := by
    intro x hx
    have hφx : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin p]→L[ℝ] F))
        (fun y ↦ TotalSpace.mk' (E [⋀^Fin p]→L[ℝ] F) y (φ y)) (σ.extension x) := by
      rw [σ.extension_coe ⟨x, hx⟩]
      exact (hφ ⟨x, hx⟩).mdifferentiableAt one_ne_zero
    exact (extDerivWithin_mpullbackWithin
      ((σ.contMDiffOn_extension x hx).of_le (by simp))
      (uniqueDiffOn_fullSimplex (p + 1))
      (by rw [closure_interior_fullSimplex]; exact hx) hx hφx).symm
  refine (integral_def σ (mextDeriv φ)).trans ?_
  refine (setIntegral_congr_fun (isClosed_fullSimplex (p + 1)).measurableSet
    fun x hx ↦ congrArg (fun η ↦ η fun i ↦ EuclideanSpace.single i 1) (hext x hx)).trans ?_
  refine hpull.integral_extDerivWithin_fullSimplex.trans
    (Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℝ) ^ (i : ℕ) • ·) (integral_δ i σ φ).symm)

/-- **Stokes' theorem for smooth singular simplices.** For a smooth singular `(p + 1)`-simplex `σ`
of a `C²` manifold `M` and a `C¹` `p`-form `φ` with values in a complete space `F`, the integral of
`dφ` over `σ` is the alternating sum of the integrals of `φ` over the faces of `σ`. -/
theorem integral_mextDeriv (σ : SmoothSimplex I M (p + 1)) {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) :
    σ.integral (mextDeriv φ) =
      ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ :=
  σ.integral_mextDeriv_of_contMDiffAt
    fun x ↦ (isSmoothForm_def _ _).mp hφ (σ.toContinuousMap x)

/-- **Stokes' theorem for bundled smooth forms** over a smooth singular `(p + 1)`-simplex. -/
theorem integral_mextDerivₗ (σ : SmoothSimplex I M (p + 1)) (φ : SmoothForm I M F p) :
    σ.integral (mextDerivₗ I p φ).1 =
      ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ.1 := by
  rw [mextDerivₗ_apply]
  exact σ.integral_mextDeriv (φ.isSmoothForm.of_le (by exact_mod_cast le_top))

/-- If `dφ` vanishes along the image of a smooth `(p + 1)`-simplex `σ`, the alternating sum of the
integrals of a `C¹` `p`-form `φ` over the faces of `σ` vanishes. -/
theorem sum_integral_δ_eq_zero_of_mextDeriv_eq_zero_on (σ : SmoothSimplex I M (p + 1))
    {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ)
    (hd : ∀ x : fullSimplex (p + 1), mextDeriv φ (σ.toContinuousMap x) = 0) :
    ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ = 0 := by
  rw [← σ.integral_mextDeriv hφ, integral_def]
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
  refine (mpullbackWithin_apply σ.extension (fullSimplex (p + 1)) (mextDeriv φ) x _).trans ?_
  rw [σ.extension_coe ⟨x, hx⟩, hd ⟨x, hx⟩]
  -- Evaluating the zero alternating map gives `0`.
  rfl

/-- If `φ` is a `C¹` `p`-form with `dφ = 0`, the alternating sum of the integrals of `φ` over the
faces of any smooth `(p + 1)`-simplex vanishes. -/
theorem sum_integral_δ_eq_zero_of_mextDeriv_eq_zero (σ : SmoothSimplex I M (p + 1))
    {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ) (hd : mextDeriv φ = 0) :
    ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ = 0 :=
  σ.sum_integral_δ_eq_zero_of_mextDeriv_eq_zero_on hφ fun x ↦ by simp [hd]

/-- Closed smooth real `p`-forms integrate to zero over the boundary of any smooth
`(p + 1)`-simplex. -/
theorem sum_integral_δ_eq_zero_of_mem_closedForms (σ : SmoothSimplex I M (p + 1))
    {φ : SmoothForm I M ℝ p} (hφ : φ ∈ closedForms I M p) :
    ∑ i : Fin (p + 2), (-1 : ℝ) ^ (i : ℕ) •
        integral ((smoothSingularSubcomplex I M : SSet).δ i σ) φ.1 = 0 :=
  σ.sum_integral_δ_eq_zero_of_mextDeriv_eq_zero
    (φ.isSmoothForm.of_le (by exact_mod_cast le_top)) ((mem_closedForms I φ).mp hφ)

end Stokes

section DegreeZero

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Inserting `t` as the unique coordinate over `Fin 0` gives `single 0 t` in `ℝ¹`. -/
private theorem toLp_insertNth_zero_fin_one (t : ℝ) (y : Fin 0 → ℝ) :
    WithLp.toLp 2 ((0 : Fin 1).insertNth t y) = EuclideanSpace.single (0 : Fin 1) t := by
  ext i
  fin_cases i
  simp

/-- At a point of `Δᵖ` where `a : M → F` is differentiable along `σ`, the within-set pullback of
`da` along `σ.extension` agrees with the Euclidean within-set derivative of `a ∘ σ.extension`. -/
private theorem mpullbackWithin_mextDeriv_ofFunction_apply {p : ℕ} (σ : SmoothSimplex I M p)
    {a : M → F} {x : EuclideanSpace ℝ (Fin p)} (hx : x ∈ fullSimplex p)
    (ha : MDifferentiableAt I 𝓘(ℝ, F) a (σ.toContinuousMap ⟨x, hx⟩))
    (v : Fin 1 → EuclideanSpace ℝ (Fin p)) :
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p)
      (mextDeriv (RoughForm.ofFunction I a)) x v =
      fderivWithin ℝ (a ∘ σ.extension) (fullSimplex p) x (v 0) := by
  have hax : MDifferentiableAt I 𝓘(ℝ, F) a (σ.extension x) := by
    rwa [σ.extension_coe ⟨x, hx⟩]
  have hσx : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
      (fullSimplex p) x :=
    (σ.contMDiffOn_extension x hx).mdifferentiableWithinAt (by simp)
  have hux : UniqueMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fullSimplex p) x :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx)
  refine (mpullbackWithin_apply σ.extension (fullSimplex p)
    (mextDeriv (RoughForm.ofFunction I a)) x v).trans ?_
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_apply_eq_mfderiv_apply]
  -- `ContinuousLinearMap.comp_apply` is definitional; `DFunLike.congr_fun` avoids `rw`'s
  -- `implicit`-transparency check on `TangentSpace (𝓡 p) x`.
  exact DFunLike.congr_fun
    ((mfderiv_comp_mfderivWithin x hax hσx hux).symm.trans mfderivWithin_eq_fderivWithin) (v 0)

variable [CompleteSpace F]

/-- **Fundamental theorem of calculus for smooth `1`-simplices** (pointwise `C¹` function). Over a
smooth `1`-simplex `σ` of any charted space `M`, the integral of `da` for a function `a : M → F`
that is `C¹` at each point of the image of `σ` equals the difference of the values of `a` at the
endpoints `σ(e₀)` and `σ(0)`. -/
theorem integral_mextDeriv_ofFunction_of_contMDiffAt (σ : SmoothSimplex I M 1) {a : M → F}
    (ha : ∀ x : fullSimplex 1, ContMDiffAt I 𝓘(ℝ, F) 1 a (σ.toContinuousMap x)) :
    σ.integral (mextDeriv (RoughForm.ofFunction I a)) =
      a (σ.toContinuousMap ⟨EuclideanSpace.single 0 1, single_one_mem_fullSimplex 0⟩) -
        a (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 1⟩) := by
  -- `g = a ∘ σ.extension` is `C¹` within `Δ¹`, and the pulled-back integrand is its directional
  -- derivative along `e₀`.
  let g : EuclideanSpace ℝ (Fin 1) → F := a ∘ σ.extension
  have hg : ContDiffOn ℝ 1 g (fullSimplex 1) := fun x hx ↦ by
    have hax : ContMDiffAt I 𝓘(ℝ, F) 1 a (σ.extension x) := by
      simpa only [σ.extension_coe ⟨x, hx⟩] using ha ⟨x, hx⟩
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp
      (hax.contMDiffWithinAt.comp x ((σ.contMDiffOn_extension x hx).of_le (by simp))
        (mapsTo_univ _ _))
  -- Apply the Euclidean simplex FTC along the unique coordinate of `Δ¹`, then evaluate the two
  -- resulting constant integrals over the single-point `0`-simplex `Δ⁰`.
  rw [integral_def, setIntegral_congr_fun (isClosed_fullSimplex 1).measurableSet
      fun x hx ↦ σ.mpullbackWithin_mextDeriv_ofFunction_apply hx
        ((ha ⟨x, hx⟩).mdifferentiableAt one_ne_zero) _,
    hg.integral_fderivWithin_fullSimplex 0]
  simp only [toLp_insertNth_zero_fin_one, Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
    (PiLp.single_eq_zero_iff 2 (0 : Fin 1)).mpr rfl, g, Function.comp_apply,
    σ.extension_coe ⟨EuclideanSpace.single 0 1, single_one_mem_fullSimplex 0⟩,
    σ.extension_coe ⟨0, zero_mem_fullSimplex 1⟩, setIntegral_const, volume_real_fullSimplex_zero,
    one_smul]

/-- **Fundamental theorem of calculus for smooth `1`-simplices.** Over a smooth `1`-simplex `σ` of
any charted space `M`, the integral of `da` for a `C¹` function `a : M → F` equals the difference
of the values of `a` at the endpoints `σ(e₀)` and `σ(0)`. -/
theorem integral_mextDeriv_ofFunction (σ : SmoothSimplex I M 1) {a : M → F}
    (ha : ContMDiff I 𝓘(ℝ, F) 1 a) :
    σ.integral (mextDeriv (RoughForm.ofFunction I a)) =
      a (σ.toContinuousMap ⟨EuclideanSpace.single 0 1, single_one_mem_fullSimplex 0⟩) -
        a (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 1⟩) :=
  σ.integral_mextDeriv_ofFunction_of_contMDiffAt fun x ↦ ha (σ.toContinuousMap x)

/-- On a `C¹` manifold, the integral of the exterior derivative of a `C¹` `0`-form `ψ` over a
smooth `1`-simplex `σ` is the difference of `ψ` evaluated at the endpoints `σ(e₀)` and `σ(0)`. -/
theorem integral_mextDeriv_eq_sub [IsManifold I 1 M] (σ : SmoothSimplex I M 1)
    {ψ : RoughForm I M F 0} (hψ : IsSmoothForm I 1 ψ) :
    σ.integral (mextDeriv ψ) =
      ψ (σ.toContinuousMap ⟨EuclideanSpace.single 0 1, single_one_mem_fullSimplex 0⟩) 0 -
        ψ (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 1⟩) 0 := by
  rw [RoughForm.eq_ofFunction ψ, isSmoothForm_ofFunction_iff] at hψ
  have h := σ.integral_mextDeriv_ofFunction hψ
  rwa [← RoughForm.eq_ofFunction] at h

/-- Exact smooth `1`-forms integrate to zero over closed smooth `1`-simplices (those whose two face
vertices agree). -/
theorem integral_eq_zero_of_mem_exactForms_of_eq [IsManifold I 2 M] (σ : SmoothSimplex I M 1)
    {φ : SmoothForm I M ℝ 1} (hφ : φ ∈ exactForms I M 1)
    (hclosed : σ.toContinuousMap ⟨0, zero_mem_fullSimplex 1⟩ =
      σ.toContinuousMap ⟨EuclideanSpace.single 0 1, single_one_mem_fullSimplex 0⟩) :
    σ.integral φ.1 = 0 := by
  rw [exactForms_succ, LinearMap.mem_range] at hφ
  obtain ⟨g, rfl⟩ := hφ
  have hg : IsSmoothForm I 1 g.1 := g.isSmoothForm.of_le (by exact_mod_cast le_top)
  rw [mextDerivₗ_apply, σ.integral_mextDeriv_eq_sub hg, hclosed, sub_self]

end DegreeZero

section Curve

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrating a `1`-form over the smooth `1`-simplex `SmoothSimplex.ofCurve hγ` of a smooth curve
`γ : ℝ → M` agrees with the line integral `pathIntegral φ γ 0 1`. Neither manifold smoothness nor
completeness of `F` is required. -/
theorem integral_ofCurve {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (φ : RoughForm I M F 1) :
    (ofCurve hγ).integral φ = pathIntegral φ γ 0 1 := by
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0
  have hγP : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) I ∞ (γ ∘ P) :=
    hγ.comp P.contDiff.contMDiff
  rw [(ofCurve hγ).integral_eq_setIntegral_mpullback φ
    (fun x ↦ (toContinuousMap_ofCurve_apply hγ x).symm)
    fun x _ ↦ (hγP.mdifferentiable (by simp)) x]
  have hpull : ∀ x : EuclideanSpace ℝ (Fin 1),
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) I (γ ∘ P) φ x (fun i ↦ EuclideanSpace.single i 1) =
        mpullback 𝓘(ℝ, ℝ) I γ φ (P x) (fun _ ↦ 1) := by
    intro x
    rw [mpullback_comp_apply_of_hasFDerivAt P.hasFDerivAt ((hγ.mdifferentiable (by simp)) (P x)) φ]
    -- `compContinuousLinearMap` acts by precomposing the tangent-vector arguments with `P`, and
    -- `TangentSpace 𝓘(ℝ, ℝ) (P x)` is definitionally `ℝ`.
    refine congrArg (mpullback 𝓘(ℝ, ℝ) I γ φ (P x)) (funext fun i ↦ ?_)
    change P (EuclideanSpace.single i 1) = (1 : ℝ)
    rw [Subsingleton.elim i 0]
    simp [P]
  simp_rw [hpull]
  dsimp only [P]
  rw [fullSimplex_one_eq_preimage_proj_zero_Icc,
    (volume_preserving_euclideanSpace_proj (ι := Fin 1) 0).setIntegral_preimage_emb
      (measurableEmbedding_euclideanSpace_proj (ι := Fin 1) 0)
      (fun t ↦ mpullback 𝓘(ℝ, ℝ) I γ φ t fun _ ↦ 1) (Icc 0 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    pathIntegral_eq_integral_mpullback]

/-- Integrating the coordinate `1`-form `dt` of `ℝ` over the identity `1`-simplex yields `+1`,
pinning the orientation convention of `SmoothSimplex.ofCurve` and `SmoothSimplex.integral`. -/
@[simp]
theorem integral_ofCurve_id_realLineCoordForm :
    (ofCurve (I := 𝓘(ℝ)) (γ := id) contMDiff_id).integral SmoothForm.realLineCoordForm.1 = 1 := by
  have hd : SmoothForm.realLineCoordForm.1 = mextDeriv (RoughForm.ofFunction 𝓘(ℝ) id) := by
    simpa only [mpullback_id] using SmoothForm.mpullback_realLineCoordForm (I := 𝓘(ℝ)) id
  rw [integral_ofCurve, hd, pathIntegral_mextDeriv_ofFunction contMDiff_id contMDiff_id 0 1]
  norm_num

end Curve

end SmoothSimplex

section Cochain

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℕ}

/-- **Simplicial coboundary of simplex integration.** Under `TauCeti.cochainValuesEquiv`, the
simplicial coboundary of the cochain `σ ↦ ∫_σ φ` on the smooth singular chain complex of `M` is
the cochain `σ ↦ ∫_σ dφ`. -/
theorem d_comp_cochainValuesEquiv_symm_integral {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
        (cochainValuesEquiv ℝ (ModuleCat.of ℝ F) (smoothSingularSubcomplex I M : SSet) p).symm
          (fun σ ↦ SmoothSimplex.integral σ φ) =
      (cochainValuesEquiv ℝ (ModuleCat.of ℝ F) (smoothSingularSubcomplex I M : SSet) (p + 1)).symm
        (fun σ ↦ SmoothSimplex.integral σ (mextDeriv φ)) := by
  apply (cochainValuesEquiv ℝ (ModuleCat.of ℝ F)
    (smoothSingularSubcomplex I M : SSet) (p + 1)).injective
  funext σ
  rw [cochainValuesEquiv_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    SmoothSimplex.integral_mextDeriv σ hφ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- If `φ` is a `C¹` `p`-form with `dφ = 0`, the cochain `σ ↦ ∫_σ φ` is a cocycle on the smooth
singular chain complex of `M`. -/
theorem d_comp_cochainValuesEquiv_symm_integral_eq_zero {φ : RoughForm I M F p}
    (hφ : IsSmoothForm I 1 φ) (hd : mextDeriv φ = 0) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
        (cochainValuesEquiv ℝ (ModuleCat.of ℝ F) (smoothSingularSubcomplex I M : SSet) p).symm
          (fun σ ↦ SmoothSimplex.integral σ φ) = 0 := by
  rw [d_comp_cochainValuesEquiv_symm_integral hφ, hd]
  simp only [SmoothSimplex.integral_zero]
  exact map_zero _

/-- Every closed smooth real `p`-form defines a cocycle on the smooth singular chain complex of
`M`. -/
theorem d_comp_cochainValuesEquiv_symm_integral_eq_zero_of_mem_closedForms
    {φ : SmoothForm I M ℝ p} (hφ : φ ∈ closedForms I M p) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℝ ℝ)).d (p + 1) p ≫
        (cochainValuesEquiv ℝ (ModuleCat.of ℝ ℝ) (smoothSingularSubcomplex I M : SSet) p).symm
          (fun σ ↦ SmoothSimplex.integral σ φ.1) = 0 :=
  d_comp_cochainValuesEquiv_symm_integral_eq_zero
    (φ.isSmoothForm.of_le (by exact_mod_cast le_top)) ((mem_closedForms I φ).mp hφ)

end Cochain

end TauCeti
