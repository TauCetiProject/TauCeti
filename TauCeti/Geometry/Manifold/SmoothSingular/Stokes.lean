/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Chains
public import TauCeti.Analysis.Calculus.DifferentialForm.Simplex
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.MeasureTheory.Integral.FullSimplex

/-!
# Stokes' theorem for smooth singular simplices and chains

Let `σ` be a smooth singular `(p + 1)`-simplex of a `C²` manifold `M` (possibly with boundary or
corners) and `φ` a `C¹` `p`-form on `M` with values in a real normed space `F`. Then

`∫_σ dφ = ∑_{i = 0}^{p + 1} (-1)ⁱ ∫_{δᵢ σ} φ`,

where `δᵢ σ` is the `i`-th face of `σ` in the simplicial set of smooth singular simplices
(`TauCeti.SmoothSimplex.integral_mextDeriv`, and
`TauCeti.SmoothSimplex.integral_mextDeriv_of_contMDiffAt` when `φ` is only `C¹` along the image of
`σ`). Summing over the simplices of a chain, integration of
forms turns the boundary of smooth singular chains into the exterior derivative: the integration
cochain of `φ`, precomposed with the differential of the smooth singular chain complex, is the
integration cochain of `dφ` (`TauCeti.d_comp_integrationCochain`). Consequently, the integration
cochain of a closed form is a cocycle (`TauCeti.d_comp_integrationCochain_eq_zero`), and an exact
form integrates to zero over every smooth singular cycle
(`TauCeti.integrationCochain_mextDeriv_apply_eq_zero`).

The proof pulls `φ` back to the standard simplex `Δᵖ⁺¹ ⊆ ℝᵖ⁺¹` along `σ.extension`, with
derivatives taken within `Δᵖ⁺¹`. Since `Δᵖ⁺¹` has unique derivatives
(`TauCeti.uniqueDiffOn_fullSimplex`) and is the closure of its interior
(`TauCeti.closure_interior_fullSimplex`), pullback within `Δᵖ⁺¹` commutes with exterior
differentiation (`TauCeti.extDerivWithin_mpullbackWithin`), reducing the identity to Euclidean
simplex Stokes (`ContDiffOn.integral_extDerivWithin_fullSimplex`) and the face-pullback formula
`TauCeti.SmoothSimplex.integral_δ`.

In degree `0`, the fundamental theorem of calculus for smooth `1`-simplices holds on any charted
space without manifold smoothness hypotheses (`TauCeti.SmoothSimplex.integral_mextDeriv_ofFunction`,
fixing the face sign convention `δ₀ σ` = endpoint, `δ₁ σ` = initial point), and for general `C¹`
`0`-forms on any `C¹` manifold (`TauCeti.SmoothSimplex.integral_mextDeriv_eq_sub`).

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

open Bundle CategoryTheory MeasureTheory Set Simplicial Opposite
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}

namespace SmoothSimplex

section Stokes

variable [IsManifold I 2 M]

/-- **Stokes' theorem for smooth singular simplices** (pointwise `C¹` hypothesis). For a smooth
singular `(p + 1)`-simplex `σ` of a `C²` manifold `M` and a `p`-form `φ` with values in a real
normed space `F` that is `C¹` at each point of the image of `σ`, the integral of `dφ` over `σ` is
the alternating sum of the integrals of `φ` over the faces of `σ`. -/
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
    (Finset.sum_congr rfl fun i _ ↦ congrArg ((-1 : ℝ) ^ (i : ℕ) • ·) (σ.integral_δ i φ).symm)

/-- **Stokes' theorem for a smooth singular simplex.** The integral of the exterior derivative of
a `C¹` form over a smooth singular `(p + 1)`-simplex is the alternating sum of the integrals of the
form over the faces of the simplex. -/
theorem integral_mextDeriv (σ : SmoothSimplex I M (p + 1))
    {φ : RoughForm I M F p} (hφ : IsSmoothForm I 1 φ) :
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

/-- At a point of `Δᵖ` where `f : M → F` is differentiable along `σ`, the within-set pullback of
`df` along `σ.extension` agrees with the Euclidean within-set derivative of `f ∘ σ.extension`. -/
private theorem mpullbackWithin_mextDeriv_ofFunction_apply (σ : SmoothSimplex I M p)
    {f : M → F} {x : EuclideanSpace ℝ (Fin p)} (hx : x ∈ fullSimplex p)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f (σ.toContinuousMap ⟨x, hx⟩))
    (v : Fin 1 → EuclideanSpace ℝ (Fin p)) :
    mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension (fullSimplex p)
      (mextDeriv (RoughForm.ofFunction I f)) x v =
      fderivWithin ℝ (f ∘ σ.extension) (fullSimplex p) x (v 0) := by
  have hfx : MDifferentiableAt I 𝓘(ℝ, F) f (σ.extension x) := by
    rwa [σ.extension_coe ⟨x, hx⟩]
  have hσx : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) I σ.extension
      (fullSimplex p) x :=
    (σ.contMDiffOn_extension x hx).mdifferentiableWithinAt (by simp)
  have hux : UniqueMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fullSimplex p) x :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_fullSimplex p x hx)
  refine (mpullbackWithin_apply σ.extension (fullSimplex p)
    (mextDeriv (RoughForm.ofFunction I f)) x v).trans ?_
  rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_apply_eq_mfderiv_apply]
  -- `ContinuousLinearMap.comp_apply` is definitional; `DFunLike.congr_fun` avoids `rw`'s
  -- `implicit`-transparency check on `TangentSpace (𝓡 p) x`.
  exact DFunLike.congr_fun
    ((mfderiv_comp_mfderivWithin x hfx hσx hux).symm.trans mfderivWithin_eq_fderivWithin) (v 0)

variable [CompleteSpace F]

/-- **Fundamental theorem of calculus for smooth `1`-simplices** (pointwise `C¹` function). Over a
smooth `1`-simplex `σ` of any charted space `M`, the integral of `df` for a function `f : M → F`
that is `C¹` at each point of the image of `σ` equals the difference of the values of `f` at the
endpoints `σ(e₀)` and `σ(0)`. -/
theorem integral_mextDeriv_ofFunction_of_contMDiffAt (σ : SmoothSimplex I M 1) {f : M → F}
    (hf : ∀ x : fullSimplex 1, ContMDiffAt I 𝓘(ℝ, F) 1 f (σ.toContinuousMap x)) :
    σ.integral (mextDeriv (RoughForm.ofFunction I f)) =
      f (σ.toContinuousMap ⟨EuclideanSpace.single 0 1, single_one_mem_fullSimplex 0⟩) -
        f (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 1⟩) := by
  -- `g = f ∘ σ.extension` is `C¹` within `Δ¹`, and the pulled-back integrand is its directional
  -- derivative along `e₀`.
  let g : EuclideanSpace ℝ (Fin 1) → F := f ∘ σ.extension
  have hg : ContDiffOn ℝ 1 g (fullSimplex 1) := fun x hx ↦ by
    have hfx : ContMDiffAt I 𝓘(ℝ, F) 1 f (σ.extension x) := by
      simpa only [σ.extension_coe ⟨x, hx⟩] using hf ⟨x, hx⟩
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp
      (hfx.contMDiffWithinAt.comp x ((σ.contMDiffOn_extension x hx).of_le (by simp))
        (mapsTo_univ _ _))
  -- Apply the Euclidean simplex FTC along the unique coordinate of `Δ¹`, then identify the two
  -- boundary evaluations with `simplexFace 0 0` and `simplexFace 0 1` over the single-point `Δ⁰`.
  rw [integral_def, setIntegral_congr_fun (isClosed_fullSimplex 1).measurableSet
      fun x hx ↦ σ.mpullbackWithin_mextDeriv_ofFunction_apply hx
        ((hf ⟨x, hx⟩).mdifferentiableAt one_ne_zero) _,
    hg.integral_fderivWithin_fullSimplex 0]
  have hface : ∀ y ∈ fullSimplex 0,
      g (WithLp.toLp 2 ((0 : Fin 1).insertNth (1 - ∑ k, y k) y.ofLp)) -
        g (WithLp.toLp 2 ((0 : Fin 1).insertNth 0 y.ofLp)) =
      f (σ.toContinuousMap ⟨EuclideanSpace.single 0 1, single_one_mem_fullSimplex 0⟩) -
        f (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 1⟩) := by
    intro y hy
    let y₀ : fullSimplex 0 :=
      ⟨simplexMapAmbient (0 : Fin 1).cycleRange.symm y, mapsTo_simplexMapAmbient _ hy⟩
    have h0 : WithLp.toLp 2 ((0 : Fin 1).insertNth (1 - ∑ k, y k) y.ofLp) =
        (simplexFace 0 0 y₀).1 :=
      (toLp_insertNth_eq_simplexMapAmbient 0 y).trans (simplexMapAmbient_succAbove_coe 0 y₀)
    have h1 : WithLp.toLp 2 ((0 : Fin 1).insertNth 0 y.ofLp) = (simplexFace 0 1 ⟨y, hy⟩).1 :=
      (simplexMapAmbient_succAbove_succ 0 y).symm.trans (simplexMapAmbient_succAbove_coe 1 ⟨y, hy⟩)
    rw [h0, h1]
    simp only [g, Function.comp_apply, σ.extension_coe]
    simp
  rw [setIntegral_congr_fun (isClosed_fullSimplex 0).measurableSet hface,
    setIntegral_const, volume_real_fullSimplex_zero, one_smul]

/-- **The fundamental theorem of calculus for a smooth `1`-simplex.** Over a smooth `1`-simplex `σ`
of any charted space `M`, the integral of the differential of a `C¹` function `f : M → F` is the
difference of its values at the endpoints `σ(e₀)` and `σ(0)`. This fixes the sign convention of
`TauCeti.SmoothSimplex.integral_mextDeriv`: the face `δ₀ σ` is the endpoint and `δ₁ σ` the initial
point. -/
theorem integral_mextDeriv_ofFunction (σ : SmoothSimplex I M 1) {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) :
    σ.integral (mextDeriv (RoughForm.ofFunction I f)) =
      f (σ.toContinuousMap ⟨EuclideanSpace.single 0 1, single_one_mem_fullSimplex 0⟩) -
        f (σ.toContinuousMap ⟨0, zero_mem_fullSimplex 1⟩) :=
  σ.integral_mextDeriv_ofFunction_of_contMDiffAt fun x ↦ hf (σ.toContinuousMap x)

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

end SmoothSimplex

section Cochain

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

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
