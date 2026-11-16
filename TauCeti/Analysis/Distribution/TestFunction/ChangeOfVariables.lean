/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import TauCeti.Analysis.Distribution.TestFunction.Pullback
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Calculus.Deriv.Abs
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Pushforward of test densities along a change of variables

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real normed space `E` whose
inverse is smooth as well, so `e` is a diffeomorphism from its source onto its target. Let `U` be an
open subset of the source and `Ω` an open set containing `e '' U`. A test function `φ` on `U`,
read as a density, pushes forward along `e` to the test function on `Ω`

`(e_* φ) y = |det D e⁻¹ (y)| φ (e⁻¹ y)` for `y` in the target of `e`, and `0` elsewhere.

The factor `|det D e⁻¹|` is the Jacobian of the change of variables `x = e⁻¹ y`, so integrating
against `e_* φ` is integrating against `φ` after composing with `e`:
`∫ (e_* φ) f = ∫ φ (f ∘ e)` for every additive Haar measure
(`TestFunction.integral_pushforwardCLM_smul`). The pushforward is continuous for the LF topology of
test functions. Its transpose pulls distributions back along `e`, see
`TauCeti.Analysis.Distribution.ChangeOfVariables`.

The pushforward is the nonlinear analogue of `ContinuousLinearEquiv.transportTestFunction`, which
carries no Jacobian factor, and the compactly supported analogue of `SchwartzMap.pushforwardCLM`.
Continuity is proved by reducing to `TestFunction.cutoffCompCLM`: on test functions supported in
a fixed compact set `K ⊆ U`, the Jacobian may be replaced by a test function on the target that
agrees with it on `e '' K`.

## Main declarations

* `TestFunction.pushforwardCLM`: the pushforward `φ ↦ e_* φ`, as a continuous linear map
  `𝓓(U, F) →L[ℝ] 𝓓(Ω, F)`.
* `TestFunction.pushforwardCLM_apply_of_mem`, `TestFunction.pushforwardCLM_apply_of_notMem`: its
  values on and off the target of `e`; `TestFunction.pushforwardCLM_apply_of_mem_source`: its value
  `|det D e (x)|⁻¹ φ x` at `e x`.
* `TestFunction.tsupport_pushforwardCLM_subset`: `supp e_* φ ⊆ e '' supp φ`.
* `TestFunction.integral_pushforwardCLM_smul`: the change of variables `∫ (e_* φ) f = ∫ φ (f ∘ e)`.
* `TestFunction.pushforwardCLM_refl`: pushing forward along the identity is extension by zero.
* `TestFunction.pushforwardCLM_trans`: pushing forward along `e₁.trans e₂` is pushing forward along
  `e₁` and then along `e₂`.
* `TestFunction.pushforwardCLM_pushforwardCLM_symm`,
  `TestFunction.pushforwardCLM_symm_pushforwardCLM`: pushing forward along `e` and `e⁻¹` are
  inverse to each other.
* `TestFunction.postcompCLM_pushforwardCLM`, `TestFunction.monoCLM_pushforwardCLM`: the pushforward
  commutes with postcomposition by a continuous linear map, for instance with real and imaginary
  parts, and with extension by zero to larger open sets.
* `TestFunction.pushforwardCLM_eq_smul_transportTestFunction`: along a continuous linear
  automorphism `L`, the pushforward is `|det L|⁻¹` times
  `ContinuousLinearEquiv.transportTestFunction`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1.
-/

public section

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology Distributions

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {e : OpenPartialHomeomorph E E} {U V Ω : Opens E}

section Jacobian

variable (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
include he he'

/-- On a compact set `K` mapped by `e` into `Ω`, the Jacobian agrees with a test function on the
part of `Ω` inside the target of `e`. -/
private theorem exists_eqOn_abs_det_fderiv_symm [FiniteDimensional ℝ E] {K : Set E}
    (hK : IsCompact K) (hKs : K ⊆ e.source) (hKΩ : MapsTo e K Ω) :
    ∃ ρ : 𝓓(⟨e.target, e.open_target⟩ ⊓ Ω, ℝ),
      EqOn ρ (fun y ↦ |(fderiv ℝ e.symm y).det|) (e '' K) := by
  have hL : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have hLW : e '' K ⊆ ((⟨e.target, e.open_target⟩ ⊓ Ω : Opens E) : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨e.map_source (hKs hx), hKΩ hx⟩
  obtain ⟨χ, hχ, -⟩ := exists_eventually_eq_one (n := (⊤ : ℕ∞)) hL hLW
  -- On the target the Jacobian is smooth, since its determinant does not vanish there.
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun y ↦ |(fderiv ℝ e.symm y).det|)
      (⟨e.target, e.open_target⟩ ⊓ Ω : Opens E) := fun y hy ↦
    (ContDiffAt.comp (g := fun t : ℝ ↦ |t|) y
      (contDiffAt_abs (e.symm.det_fderiv_ne_zero_of_contDiffOn he' he (by simp) hy.1))
      (ContinuousLinearMap.contDiff_det.contDiffAt.comp y
        ((he'.fderiv_of_isOpen e.open_target (by simp)).contDiffAt
          (e.open_target.mem_nhds hy.1)))).contDiffWithinAt
  obtain ⟨ρ, hρ⟩ := exists_coe_eq_smul_of_contDiffOn hg χ
  exact ⟨ρ, fun y hy ↦ by simp [hρ, hχ.self_of_nhdsSet y hy]⟩

end Jacobian

variable [FiniteDimensional ℝ E]

/-- The pointwise pushforward of a density `φ` along `e`. -/
private def pushforwardFun (e : OpenPartialHomeomorph E E) (φ : E → F) : E → F :=
  e.target.indicator fun y ↦ |(fderiv ℝ e.symm y).det| • φ (e.symm y)

/-- The pushforward of test functions supported in a compact set `K`, through a test function `ρ`
agreeing with the Jacobian on `e '' K`. -/
private def pushforwardOfCompact (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (ρ : 𝓓(⟨e.target, e.open_target⟩ ⊓ Ω, ℝ)) : 𝓓(U, F) →L[ℝ] 𝓓(Ω, F) :=
  monoCLM ℝ ∘L cutoffCompCLM ρ e.symm (he'.mono fun _ hy ↦ hy.1)

omit [FiniteDimensional ℝ E] in
private theorem coe_pushforwardOfCompact (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {K : Set E} {ρ : 𝓓(⟨e.target, e.open_target⟩ ⊓ Ω, ℝ)}
    (hρ : EqOn ρ (fun y ↦ |(fderiv ℝ e.symm y).det|) (e '' K)) {φ : 𝓓(U, F)}
    (hφ : tsupport φ ⊆ K) : ⇑(pushforwardOfCompact he' ρ φ) = pushforwardFun e φ := by
  ext y
  have hle : (⟨e.target, e.open_target⟩ ⊓ Ω : Opens E) ≤ Ω := inf_le_right
  simp only [pushforwardOfCompact, ContinuousLinearMap.comp_apply, monoCLM_apply, le_refl,
    hle, and_self, ↓reduceIte, cutoffCompCLM_apply, pushforwardFun]
  by_cases hy : y ∈ e.target
  · rw [indicator_of_mem hy]
    by_cases h0 : φ (e.symm y) = 0
    · simp [h0]
    · -- Then `e⁻¹ y ∈ K`, so `y ∈ e '' K`, where `ρ` is the Jacobian.
      have hK : e.symm y ∈ K := hφ (subset_tsupport _ h0)
      rw [hρ ⟨e.symm y, hK, e.right_inv hy⟩]
  · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport fun h ↦ hy
      ((ρ.tsupport_subset h).1), zero_smul]

/-- A test function on the target agreeing with the Jacobian on `e '' K`. -/
private def jacobianCutoff (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) (hU : (U : Set E) ⊆ e.source)
    (hUΩ : MapsTo e U Ω) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    𝓓(⟨e.target, e.open_target⟩ ⊓ Ω, ℝ) :=
  (exists_eqOn_abs_det_fderiv_symm he he' hK (hKU.trans hU) (hUΩ.mono_left hKU)).choose

private theorem coe_pushforwardOfCompact_jacobianCutoff
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source) (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    (hU : (U : Set E) ⊆ e.source) (hUΩ : MapsTo e U Ω) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) {φ : 𝓓(U, F)} (hφ : tsupport φ ⊆ K) :
    ⇑(pushforwardOfCompact he' (jacobianCutoff he he' hU hUΩ hK hKU) φ) = pushforwardFun e φ :=
  coe_pushforwardOfCompact he' (exists_eqOn_abs_det_fderiv_symm he he' hK (hKU.trans hU)
    (hUΩ.mono_left hKU)).choose_spec hφ

/-- The **pushforward of test densities along a change of variables** `e`, a smooth open partial
homeomorphism with smooth inverse, from an open subset `U` of its source to an open set `Ω`
containing `e '' U`: `(e_* φ) y = |det D e⁻¹ (y)| φ (e⁻¹ y)` on the target of `e` and `0` off it
(`TestFunction.pushforwardCLM_apply_of_mem`, `TestFunction.pushforwardCLM_apply_of_notMem`).
Integrating against `e_* φ` is integrating against `φ` after composing with `e`
(`TestFunction.integral_pushforwardCLM_smul`). -/
def pushforwardCLM (e : OpenPartialHomeomorph E E) (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) (hU : (U : Set E) ⊆ e.source)
    (hUΩ : MapsTo e U Ω) : 𝓓(U, F) →L[ℝ] 𝓓(Ω, F) :=
  -- The pushforward of `φ` is computed through the Jacobian cutoff for its own support.
  have hcoe (φ : 𝓓(U, F)) := coe_pushforwardOfCompact_jacobianCutoff he he' hU hUΩ
    φ.hasCompactSupport φ.tsupport_subset subset_rfl
  TestFunction.mkCLM ℝ
    (fun φ ↦ pushforwardOfCompact he'
      (jacobianCutoff he he' hU hUΩ φ.hasCompactSupport φ.tsupport_subset) φ)
    (fun φ ψ ↦ by
      ext y
      simp only [add_apply, hcoe, pushforwardFun]
      by_cases hy : y ∈ e.target <;> simp [hy])
    (fun c φ ↦ by
      ext y
      simp only [smul_apply, hcoe, pushforwardFun]
      by_cases hy : y ∈ e.target <;> simp [hy, smul_comm c])
    (fun K hK ↦ by
      -- On tests supported in `K`, the pushforward is computed through the cutoff for `K`.
      have h : (fun φ : 𝓓(U, F) ↦ pushforwardOfCompact he'
            (jacobianCutoff he he' hU hUΩ φ.hasCompactSupport φ.tsupport_subset) φ) ∘
          ofSupportedIn hK = pushforwardOfCompact (U := U) (Ω := Ω) (F := F) he'
            (jacobianCutoff he he' hU hUΩ K.isCompact hK) ∘L ofSupportedInCLM ℝ hK := by
        ext φ y
        simp only [Function.comp_apply, hcoe, ContinuousLinearMap.comp_apply,
          coe_ofSupportedInCLM, coe_pushforwardOfCompact_jacobianCutoff he he' hU hUΩ
            K.isCompact hK (φ := ofSupportedIn hK φ) (ContDiffMapSupportedIn.tsupport_subset φ)]
      rw [h]
      exact ContinuousLinearMap.continuous _)

variable {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- The pushforward is `y ↦ |det D e⁻¹ (y)| φ (e⁻¹ y)` on the target of `e`, extended by zero. -/
theorem coe_pushforwardCLM (φ : 𝓓(U, F)) :
    ⇑(pushforwardCLM e he he' hU hUΩ φ) =
      e.target.indicator fun y ↦ |(fderiv ℝ e.symm y).det| • φ (e.symm y) :=
  coe_pushforwardOfCompact_jacobianCutoff he he' hU hUΩ _ _ subset_rfl

/-- On the target of `e`, the pushforward is `|det D e⁻¹ (y)| φ (e⁻¹ y)`. -/
@[simp]
theorem pushforwardCLM_apply_of_mem (φ : 𝓓(U, F)) {y : E} (hy : y ∈ e.target) :
    pushforwardCLM e he he' hU hUΩ φ y = |(fderiv ℝ e.symm y).det| • φ (e.symm y) := by
  rw [coe_pushforwardCLM, indicator_of_mem hy]

/-- Off the target of `e`, the pushforward vanishes. -/
@[simp]
theorem pushforwardCLM_apply_of_notMem (φ : 𝓓(U, F)) {y : E} (hy : y ∉ e.target) :
    pushforwardCLM e he he' hU hUΩ φ y = 0 := by
  rw [coe_pushforwardCLM, indicator_of_notMem hy]

/-- At the image of a point `x` of the source, the pushforward is `|det D e (x)|⁻¹ φ x`. -/
theorem pushforwardCLM_apply_of_mem_source (φ : 𝓓(U, F)) {x : E} (hx : x ∈ e.source) :
    pushforwardCLM e he he' hU hUΩ φ (e x) = |(fderiv ℝ e x).det|⁻¹ • φ x := by
  rw [pushforwardCLM_apply_of_mem φ (e.map_source hx), e.left_inv hx,
    e.det_fderiv_symm_apply_of_contDiffOn he he' (by simp) hx, abs_inv]

/-- The support of the pushforward of `φ` lies in the image of the support of `φ`. -/
theorem tsupport_pushforwardCLM_subset (φ : 𝓓(U, F)) :
    tsupport (pushforwardCLM e he he' hU hUΩ φ) ⊆ e '' tsupport φ := by
  have hK : IsCompact (e '' tsupport φ) :=
    φ.hasCompactSupport.isCompact.image_of_continuousOn
      (e.continuousOn.mono (φ.tsupport_subset.trans hU))
  refine closure_minimal (fun y hy ↦ ?_) hK.isClosed
  by_cases hyt : y ∈ e.target
  · rw [Function.mem_support, pushforwardCLM_apply_of_mem φ hyt] at hy
    exact ⟨e.symm y, subset_tsupport _ (right_ne_zero_of_smul hy), e.right_inv hyt⟩
  · exact absurd (pushforwardCLM_apply_of_notMem φ hyt) hy

/-- The pushforward commutes with postcomposition by a continuous linear map. -/
theorem postcompCLM_pushforwardCLM {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (φ : 𝓓(U, F)) :
    postcompCLM L (pushforwardCLM e he he' hU hUΩ φ) =
      pushforwardCLM e he he' hU hUΩ (postcompCLM L φ) := by
  ext y
  by_cases hy : y ∈ e.target <;> simp [hy]

/-- **Change of variables against a pushed forward density**: for every additive Haar measure,
`∫ (e_* φ) f = ∫ φ (f ∘ e)`. No integrability of `f` is needed. -/
theorem integral_pushforwardCLM_smul [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : 𝓓(U, ℝ)) (f : E → G) :
    ∫ y, pushforwardCLM e he he' hU hUΩ φ y • f y ∂μ = ∫ x, φ x • f (e x) ∂μ := by
  have hφ (x : E) (hx : x ∉ e.source) : φ x • f (e x) = 0 := by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hU (φ.tsupport_subset h)), zero_smul]
  have hd (y : E) (hy : y ∈ e.target) :
      HasFDerivWithinAt e.symm (fderiv ℝ e.symm y) e.target y :=
    ((he'.differentiableOn (by simp)).differentiableAt
      (e.open_target.mem_nhds hy)).hasFDerivAt.hasFDerivWithinAt
  -- Both integrands vanish off the target, respectively the source; then change variables
  -- `x = e⁻¹ y` on the target.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hφ,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target) fun y hy ↦ by
      rw [pushforwardCLM_apply_of_notMem φ hy, zero_smul],
    ← e.symm_image_target_eq_source,
    integral_image_eq_integral_abs_det_fderiv_smul μ e.open_target.measurableSet hd e.symm.injOn]
  refine setIntegral_congr_fun e.open_target.measurableSet fun y hy ↦ ?_
  rw [pushforwardCLM_apply_of_mem φ hy, e.right_inv hy, smul_assoc]

/-- Pushing forward along `e⁻¹` and then along `e` gives back the original test function. -/
@[simp]
theorem pushforwardCLM_pushforwardCLM_symm {he₁ : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.symm.source}
    {he₁' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm.symm e.symm.target} {hV : (V : Set E) ⊆ e.symm.source}
    {hVU : MapsTo e.symm V U} {hUV : MapsTo e U V} (φ : 𝓓(V, F)) :
    pushforwardCLM e he he' hU hUV (pushforwardCLM e.symm he₁ he₁' hV hVU φ) = φ := by
  ext y
  by_cases hy : y ∈ e.target
  · obtain ⟨x, hx, rfl⟩ : ∃ x ∈ e.source, e x = y := ⟨e.symm y, e.map_target hy, e.right_inv hy⟩
    rw [pushforwardCLM_apply_of_mem_source _ hx, pushforwardCLM_apply_of_mem _ (by simpa using hx),
      OpenPartialHomeomorph.symm_symm, smul_smul, inv_mul_cancel₀
        (abs_ne_zero.2 (e.det_fderiv_ne_zero_of_contDiffOn he he' (by simp) hx)), one_smul]
  · rw [pushforwardCLM_apply_of_notMem _ hy,
      image_eq_zero_of_notMem_tsupport fun h : y ∈ tsupport φ ↦
        hy (by simpa using hV (φ.tsupport_subset h))]

/-- Pushing forward along `e` and then along `e⁻¹` gives back the original test function. -/
@[simp]
theorem pushforwardCLM_symm_pushforwardCLM {he₁ : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.symm.source}
    {he₁' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm.symm e.symm.target} {hV : (V : Set E) ⊆ e.symm.source}
    {hVU : MapsTo e.symm V U} {hUV : MapsTo e U V} (φ : 𝓓(U, F)) :
    pushforwardCLM e.symm he₁ he₁' hV hVU (pushforwardCLM e he he' hU hUV φ) = φ := by
  ext x
  by_cases hx : x ∈ e.source
  · rw [pushforwardCLM_apply_of_mem _ (by simpa using hx), OpenPartialHomeomorph.symm_symm,
      pushforwardCLM_apply_of_mem_source _ hx, smul_smul, mul_inv_cancel₀
        (abs_ne_zero.2 (e.det_fderiv_ne_zero_of_contDiffOn he he' (by simp) hx)), one_smul]
  · rw [pushforwardCLM_apply_of_notMem _ (by simpa using hx),
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hU (φ.tsupport_subset h))]

/-- Pushing forward along the identity is extension by zero. -/
@[simp]
theorem pushforwardCLM_refl
    {he : ContDiffOn ℝ (⊤ : ℕ∞) (OpenPartialHomeomorph.refl E)
      (OpenPartialHomeomorph.refl E).source}
    {he' : ContDiffOn ℝ (⊤ : ℕ∞) (OpenPartialHomeomorph.refl E).symm
      (OpenPartialHomeomorph.refl E).target}
    {hU : (U : Set E) ⊆ (OpenPartialHomeomorph.refl E).source}
    {hUΩ : MapsTo (OpenPartialHomeomorph.refl E) U Ω} (φ : 𝓓(U, F)) :
    pushforwardCLM (OpenPartialHomeomorph.refl E) he he' hU hUΩ φ = monoCLM ℝ φ := by
  have hUΩ' : U ≤ Ω := SetLike.coe_subset_coe.1 fun x hx ↦ by simpa using hUΩ hx
  ext y
  rw [pushforwardCLM_apply_of_mem φ (mem_univ y)]
  simp [hUΩ']

/-- **Functoriality**: pushing forward along the composite `e₁.trans e₂`, whose Jacobian is the
product of the Jacobians by the chain rule, is pushing forward along `e₁` and then along `e₂`. -/
theorem pushforwardCLM_trans {e₁ e₂ : OpenPartialHomeomorph E E}
    {he₁ : ContDiffOn ℝ (⊤ : ℕ∞) e₁ e₁.source} {he₁' : ContDiffOn ℝ (⊤ : ℕ∞) e₁.symm e₁.target}
    {he₂ : ContDiffOn ℝ (⊤ : ℕ∞) e₂ e₂.source} {he₂' : ContDiffOn ℝ (⊤ : ℕ∞) e₂.symm e₂.target}
    {he : ContDiffOn ℝ (⊤ : ℕ∞) (e₁.trans e₂) (e₁.trans e₂).source}
    {he' : ContDiffOn ℝ (⊤ : ℕ∞) (e₁.trans e₂).symm (e₁.trans e₂).target}
    {hU : (U : Set E) ⊆ e₁.source} {hUV : MapsTo e₁ U V} {hV : (V : Set E) ⊆ e₂.source}
    {hVΩ : MapsTo e₂ V Ω} {hU' : (U : Set E) ⊆ (e₁.trans e₂).source}
    {hUΩ : MapsTo (e₁.trans e₂) U Ω} (φ : 𝓓(U, F)) :
    pushforwardCLM (e₁.trans e₂) he he' hU' hUΩ φ =
      pushforwardCLM e₂ he₂ he₂' hV hVΩ (pushforwardCLM e₁ he₁ he₁' hU hUV φ) := by
  ext z
  by_cases hz₂ : z ∈ e₂.target
  · by_cases hz₁ : e₂.symm z ∈ e₁.target
    · have hz : z ∈ (e₁.trans e₂).target := by
        rw [OpenPartialHomeomorph.trans_target]
        exact ⟨hz₂, hz₁⟩
      -- The chain rule for `(e₁.trans e₂)⁻¹ = e₁⁻¹ ∘ e₂⁻¹` at `z`.
      have hd : fderiv ℝ (e₁.trans e₂).symm z =
          (fderiv ℝ e₁.symm (e₂.symm z)).comp (fderiv ℝ e₂.symm z) := by
        rw [OpenPartialHomeomorph.coe_trans_symm]
        exact fderiv_comp z
          ((he₁'.differentiableOn (by simp)).differentiableAt (e₁.open_target.mem_nhds hz₁))
          ((he₂'.differentiableOn (by simp)).differentiableAt (e₂.open_target.mem_nhds hz₂))
      rw [pushforwardCLM_apply_of_mem _ hz₂, pushforwardCLM_apply_of_mem _ hz₁,
        pushforwardCLM_apply_of_mem _ hz, hd, ContinuousLinearMap.det_comp, abs_mul, smul_smul,
        mul_comm, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    · have hz : z ∉ (e₁.trans e₂).target := by
        rw [OpenPartialHomeomorph.trans_target]
        exact fun h ↦ hz₁ h.2
      rw [pushforwardCLM_apply_of_mem _ hz₂, pushforwardCLM_apply_of_notMem _ hz₁,
        pushforwardCLM_apply_of_notMem _ hz, smul_zero]
  · have hz : z ∉ (e₁.trans e₂).target := by
      rw [OpenPartialHomeomorph.trans_target]
      exact fun h ↦ hz₂ h.1
    rw [pushforwardCLM_apply_of_notMem _ hz₂, pushforwardCLM_apply_of_notMem _ hz]

/-- The pushforward commutes with extending test functions by zero to larger open sets. -/
theorem monoCLM_pushforwardCLM {U' Ω' : Opens E} (hU' : U' ≤ U) (hΩ' : Ω' ≤ Ω)
    {hU'' : (U' : Set E) ⊆ e.source} {hUΩ' : MapsTo e U' Ω'} (φ : 𝓓(U', F)) :
    (monoCLM ℝ (pushforwardCLM e he he' hU'' hUΩ' φ) : 𝓓(Ω, F)) =
      pushforwardCLM e he he' hU hUΩ (monoCLM ℝ φ) := by
  ext y
  simp only [monoCLM_apply, le_refl, hU', hΩ', and_self, ↓reduceIte, coe_pushforwardCLM]

/-- Along a continuous linear automorphism `L`, the pushforward is `|det L|⁻¹` times the transport
`φ ↦ φ ∘ L⁻¹`. -/
theorem pushforwardCLM_eq_smul_transportTestFunction (L : E ≃L[ℝ] E)
    {hL : ContDiffOn ℝ (⊤ : ℕ∞) L.toHomeomorph.toOpenPartialHomeomorph
      L.toHomeomorph.toOpenPartialHomeomorph.source}
    {hL' : ContDiffOn ℝ (⊤ : ℕ∞) L.toHomeomorph.toOpenPartialHomeomorph.symm
      L.toHomeomorph.toOpenPartialHomeomorph.target}
    {hU : (U : Set E) ⊆ L.toHomeomorph.toOpenPartialHomeomorph.source} (hUΩ : MapsTo L U Ω)
    (φ : 𝓓(U, F)) :
    pushforwardCLM L.toHomeomorph.toOpenPartialHomeomorph hL hL' hU hUΩ φ =
      |(L : E →L[ℝ] E).det|⁻¹ • L.transportTestFunction hUΩ φ := by
  ext y
  -- `hUΩ` is stated for `L` rather than for its coercion to a partial homeomorphism, so the value
  -- is unfolded by unification rather than by rewriting.
  refine (pushforwardCLM_apply_of_mem φ (by simp)).trans ?_
  simp [ContinuousLinearEquiv.fderiv]

end TestFunction
