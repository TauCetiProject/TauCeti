/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fourier integrals of compactly supported functions of two variables

Let `g : E × P → F` vanish for first variables outside a compact set `K`, where `E` is a
finite-dimensional real inner-product space and `P` is a normed space. Its Fourier integral in the
first variable, `(η, ξ) ↦ ∫ exp(-2πi ⟪y, η⟫) g(y, ξ) dy`, is jointly continuous in the dual
variable `η` and the second variable `ξ` when `g` is continuous, and, when `g` is `C¹`, may be
differentiated in `ξ` under the integral sign. Both facts reduce to Mathlib's results on parametric
integrals of compactly supported functions. They are local in `ξ`: it suffices that `g` vanish
outside `K` for second variables in a set `s` (for continuity on `s`) or near the point `ξ₀` (for
differentiability at `ξ₀`), so a compact set depending on the second variable is allowed.

These are the regularity properties of the Fourier transform `b̂(η, ξ)` of the position slices of a
symbol with compact spatial support, and of the Fourier transform of the input slices of an
amplitude, used in the composition calculus and the reduction of amplitudes to symbols of
pseudodifferential operators.

## Main declarations

* `TauCeti.hasFDerivAt_integral_fourierChar_smul`: differentiation in `ξ` under the Fourier
  integral, with `TauCeti.integral_fourierChar_smul_fderiv_apply` evaluating the derivative in a
  direction.
* `TauCeti.continuousOn_integral_fourierChar_smul`, `TauCeti.continuous_integral_fourierChar_smul`:
  joint continuity of the Fourier integral.
-/

public section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace Topology

namespace TauCeti

variable {E P F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup P] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {g : E × P → F} {K : Set E}

/-- The integrand `y ↦ exp(-2πi ⟪y, η⟫) ∂_ξ g(y, ξ)` of the derivative of the Fourier integral is
integrable. -/
theorem integrable_fourierChar_smul_fderiv [NormedSpace ℝ P] (hg : ContDiff ℝ 1 g)
    (hK : IsCompact K) {ξ : P} (hKg : ∀ᶠ ξ' in 𝓝 ξ, ∀ y ∉ K, g (y, ξ') = 0) (η : E) :
    Integrable fun y ↦ (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy ↦ ?_)
  · exact (by fun_prop : Continuous fun y : E ↦ (𝐞 (-⟪y, η⟫) : ℂ)).smul
      (ContDiff.fderiv (f := fun (y : E) ξ ↦ g (y, ξ)) hg contDiff_const (n := 0)
        (by simp)).continuous
  · have h : (fun ξ' ↦ g (y, ξ')) =ᶠ[𝓝 ξ] fun _ ↦ 0 := hKg.mono fun ξ' h ↦ h y hy
    simp [h.fderiv_eq]

/-- **Differentiation under the Fourier integral.** For a `C¹` function `g` vanishing for first
variables outside a compact set and second variables near `ξ₀`, the Fourier integral in the first
variable is differentiable in the second variable at `ξ₀`, with the Fourier integral of the
derivative as derivative. -/
theorem hasFDerivAt_integral_fourierChar_smul [NormedSpace ℝ P] (hg : ContDiff ℝ 1 g)
    (hK : IsCompact K) {ξ₀ : P} (hKg : ∀ᶠ ξ in 𝓝 ξ₀, ∀ y ∉ K, g (y, ξ) = 0) (η : E) :
    HasFDerivAt (fun ξ ↦ ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ))
      (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀) ξ₀ := by
  have he : ContDiff ℝ 1 fun y : E ↦ (𝐞 (-⟪y, η⟫) : ℂ) := by
    simp only [Real.fourierChar_apply]
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (ContDiff.inner ℝ contDiff_id contDiff_const).neg)).mul contDiff_const)
  have h := hasFDerivAt_integral_of_contDiffOn (μ := volume) (x₀ := ξ₀)
    (f := fun ξ y ↦ (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ)) Filter.univ_mem hK hK.measure_lt_top.ne
    subset_rfl ((he.comp contDiff_snd).smul (hg.comp (contDiff_snd.prodMk contDiff_fst))).contDiffOn
  have hI : (fun ξ ↦ ∫ y in K, (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ)) =ᶠ[𝓝 ξ₀]
      fun ξ ↦ ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ) :=
    hKg.mono fun ξ hξ ↦ setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      simp [hξ y hy]
  have hD (y : E) : fderiv ℝ (fun ξ ↦ (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ)) ξ₀ =
      (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀ :=
    fderiv_const_smul ((hg.comp (contDiff_prodMk_right y)).differentiable one_ne_zero ξ₀) _
  have hI' : ∫ y in K, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀ =
      ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
    have h : (fun ξ ↦ g (y, ξ)) =ᶠ[𝓝 ξ₀] fun _ ↦ 0 := hKg.mono fun ξ h ↦ h y hy
    simp [h.fderiv_eq]
  simp only [hD, hI'] at h
  exact h.congr_of_eventuallyEq hI.symm

/-- The derivative of the Fourier integral in a direction `v` is the Fourier integral of the
derivative of `g` in the direction `v`. -/
theorem integral_fourierChar_smul_fderiv_apply [NormedSpace ℝ P] (hg : ContDiff ℝ 1 g)
    (hK : IsCompact K) {ξ : P} (hKg : ∀ᶠ ξ' in 𝓝 ξ, ∀ y ∉ K, g (y, ξ') = 0) (η : E) (v : P) :
    (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ) v =
      ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ v := by
  rw [ContinuousLinearMap.integral_apply (integrable_fourierChar_smul_fderiv hg hK hKg η)]
  simp only [smul_apply]

/-- The Fourier integral in the first variable of a continuous `g`, vanishing for first variables
outside a compact set and second variables in a set `s`, is jointly continuous in the dual
variable and the second variable on `s`. -/
theorem continuousOn_integral_fourierChar_smul (hg : Continuous g) (hK : IsCompact K) {s : Set P}
    (hKg : ∀ ξ ∈ s, ∀ y ∉ K, g (y, ξ) = 0) :
    ContinuousOn (fun q : E × P ↦ ∫ y, (𝐞 (-⟪y, q.1⟫) : ℂ) • g (y, q.2)) (Set.univ ×ˢ s) :=
  continuousOn_integral_of_compact_support hK (Continuous.continuousOn (by fun_prop))
    fun q y hq hy ↦ by simp [hKg q.2 hq.2 y hy]

/-- The Fourier integral in the first variable of a continuous `g` vanishing for first variables
outside a compact set is jointly continuous in the dual variable and the second variable. -/
theorem continuous_integral_fourierChar_smul (hg : Continuous g) (hK : IsCompact K)
    (hKg : ∀ y ∉ K, ∀ ξ, g (y, ξ) = 0) :
    Continuous fun q : E × P ↦ ∫ y, (𝐞 (-⟪y, q.1⟫) : ℂ) • g (y, q.2) := by
  rw [← continuousOn_univ, ← Set.univ_prod_univ]
  exact continuousOn_integral_fourierChar_smul hg hK fun ξ _ y hy ↦ hKg y hy ξ

end TauCeti
