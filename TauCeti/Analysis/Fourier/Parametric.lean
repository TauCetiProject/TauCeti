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
import TauCeti.Analysis.Fourier.FourierCharDeriv

/-!
# Fourier integrals of compactly supported functions of two variables

Let `g : E × P → F` vanish for first variables outside a compact set `K`, where `E` is a
finite-dimensional real inner-product space and `P` is a normed space. Its Fourier integral in the
first variable, `(η, ξ) ↦ ∫ exp(-2πi ⟪y, η⟫) g(y, ξ) dy`, is jointly continuous in the dual
variable `η` and the second variable `ξ` when `g` is continuous, and, when `g` is `C¹`, may be
differentiated in `ξ` under the integral sign. Both facts reduce to Mathlib's results on parametric
integrals of compactly supported functions. For the continuity and the differentiation at `ξ₀`, `g`
need only vanish outside `K` for second variables near `ξ₀`.

These are the regularity properties of the Fourier transform `b̂(η, ξ)` of the position slices of a
symbol with compact spatial support, used in the composition calculus of pseudodifferential
operators.

## Main declarations

* `TauCeti.hasFDerivAt_integral_fourierChar_smul`: differentiation in `ξ` under the Fourier
  integral, with `TauCeti.integral_fourierChar_smul_fderiv_apply` evaluating the derivative in a
  direction.
* `TauCeti.continuousAt_integral_fourierChar_smul`: joint continuity of the Fourier integral, with
  `TauCeti.continuous_integral_fourierChar_smul` its global form.
-/

public section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace Topology

namespace TauCeti

variable {E P F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup P] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {g : E × P → F} {K : Set E}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- If `g` vanishes for first variables outside `K` and second variables near `ξ`, then so does its
derivative in the second variable at `ξ`. -/
private theorem fderiv_eq_zero_of_eventually [NormedSpace ℝ P] {ξ : P}
    (hKg : ∀ᶠ ξ' in 𝓝 ξ, ∀ y ∉ K, g (y, ξ') = 0) {y : E} (hy : y ∉ K) :
    fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ = 0 := by
  have h : (fun ξ' ↦ g (y, ξ')) =ᶠ[𝓝 ξ] fun _ ↦ (0 : F) := hKg.mono fun ξ' h ↦ h y hy
  rw [h.fderiv_eq, fderiv_const_apply]

/-- The integrand `y ↦ exp(-2πi ⟪y, η⟫) ∂_ξ g(y, ξ)` of the derivative of the Fourier integral is
integrable. -/
theorem integrable_fourierChar_smul_fderiv [NormedSpace ℝ P] (hg : ContDiff ℝ 1 g)
    {ξ : P} (hK : IsCompact K) (hKg : ∀ᶠ ξ' in 𝓝 ξ, ∀ y ∉ K, g (y, ξ') = 0) (η : E) :
    Integrable fun y ↦ (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ := by
  refine Continuous.integrable_of_hasCompactSupport ?_
    (HasCompactSupport.intro hK fun y hy ↦ by rw [fderiv_eq_zero_of_eventually hKg hy, smul_zero])
  exact (by fun_prop : Continuous fun y : E ↦ (𝐞 (-⟪y, η⟫) : ℂ)).smul
    (ContDiff.fderiv (f := fun (y : E) ξ ↦ g (y, ξ)) hg contDiff_const (n := 0)
      (by simp)).continuous

/-- **Differentiation under the Fourier integral.** For a `C¹` function `g` vanishing for first
variables outside a compact set, as long as the second variable is near `ξ₀`, the Fourier integral
in the first variable is differentiable in the second variable at `ξ₀`, with the Fourier integral of
the derivative as derivative. -/
theorem hasFDerivAt_integral_fourierChar_smul [NormedSpace ℝ P] (hg : ContDiff ℝ 1 g)
    {ξ₀ : P} (hK : IsCompact K) (hKg : ∀ᶠ ξ in 𝓝 ξ₀, ∀ y ∉ K, g (y, ξ) = 0) (η : E) :
    HasFDerivAt (fun ξ ↦ ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ))
      (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀) ξ₀ := by
  have he : ContDiff ℝ 1 fun y : E ↦ (𝐞 (-⟪y, η⟫) : ℂ) :=
    (ContDiff.inner ℝ contDiff_id contDiff_const).neg.fourierChar
  have h := hasFDerivAt_integral_of_contDiffOn (μ := volume) (x₀ := ξ₀)
    (f := fun ξ y ↦ (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ)) Filter.univ_mem hK hK.measure_lt_top.ne
    subset_rfl ((he.comp contDiff_snd).smul (hg.comp (contDiff_snd.prodMk contDiff_fst))).contDiffOn
  -- Near `ξ₀` the integrand vanishes outside `K`, so the integral over `K` is the full integral.
  have hI : (fun ξ ↦ ∫ y in K, (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ)) =ᶠ[𝓝 ξ₀]
      fun ξ ↦ ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ) :=
    hKg.mono fun ξ hξ ↦
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by simp [hξ y hy]
  have hD (y : E) : fderiv ℝ (fun ξ ↦ (𝐞 (-⟪y, η⟫) : ℂ) • g (y, ξ)) ξ₀ =
      (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀ :=
    fderiv_const_smul ((hg.comp (contDiff_prodMk_right y)).differentiable one_ne_zero ξ₀) _
  have hI' : ∫ y in K, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀ =
      ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ₀ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [fderiv_eq_zero_of_eventually hKg hy, smul_zero]
  simp only [hD, hI'] at h
  exact h.congr_of_eventuallyEq hI.symm

/-- The derivative of the Fourier integral in a direction `v` is the Fourier integral of the
derivative of `g` in the direction `v`. -/
theorem integral_fourierChar_smul_fderiv_apply [NormedSpace ℝ P] (hg : ContDiff ℝ 1 g)
    {ξ : P} (hK : IsCompact K) (hKg : ∀ᶠ ξ' in 𝓝 ξ, ∀ y ∉ K, g (y, ξ') = 0) (η : E) (v : P) :
    (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ) v =
      ∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ g (y, ξ)) ξ v := by
  rw [ContinuousLinearMap.integral_apply (integrable_fourierChar_smul_fderiv hg hK hKg η)]
  simp only [smul_apply]

/-- The Fourier integral in the first variable of a continuous `g` vanishing for first variables
outside a compact set, as long as the second variable is near `q₀.2`, is jointly continuous in the
dual variable and the second variable at `q₀`. -/
theorem continuousAt_integral_fourierChar_smul (hg : Continuous g) (hK : IsCompact K)
    {q₀ : E × P} (hKg : ∀ᶠ ξ in 𝓝 q₀.2, ∀ y ∉ K, g (y, ξ) = 0) :
    ContinuousAt (fun q : E × P ↦ ∫ y, (𝐞 (-⟪y, q.1⟫) : ℂ) • g (y, q.2)) q₀ := by
  obtain ⟨t, ht, htopen, hq₀⟩ := eventually_nhds_iff.1 hKg
  have h := continuousOn_integral_of_compact_support (μ := volume) (s := Prod.snd ⁻¹' t) hK
    (f := fun (q : E × P) (y : E) ↦ (𝐞 (-⟪y, q.1⟫) : ℂ) • g (y, q.2))
    (Continuous.continuousOn (by fun_prop)) fun q y hq hy ↦ by simp [ht q.2 hq y hy]
  exact h.continuousAt ((htopen.preimage continuous_snd).mem_nhds hq₀)

/-- The Fourier integral in the first variable of a continuous `g` vanishing for first variables
outside a compact set is jointly continuous in the dual variable and the second variable. -/
theorem continuous_integral_fourierChar_smul (hg : Continuous g) (hK : IsCompact K)
    (hKg : ∀ y ∉ K, ∀ ξ, g (y, ξ) = 0) :
    Continuous fun q : E × P ↦ ∫ y, (𝐞 (-⟪y, q.1⟫) : ℂ) • g (y, q.2) :=
  continuous_iff_continuousAt.2 fun _ ↦
    continuousAt_integral_fourierChar_smul hg hK (.of_forall fun ξ y hy ↦ hKg y hy ξ)

end TauCeti
