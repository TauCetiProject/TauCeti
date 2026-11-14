/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Test functions valued in a real inner product space

Let `Ω` be an open set of a real normed space `E` and `V` a real inner product space. A test
function `φ ∈ 𝓓(Ω, V)` pairs with a field `w : E → V` through the inner product, and the integrals
`∫ ⟪φ, w⟫` are the natural way to test a vector-valued equation. This file records that these
pairings, and those with the coordinate derivatives of `φ`, are integrable for locally integrable
`w`, and proves the fundamental lemma of the calculus of variations in this form: a locally
integrable field is determined almost everywhere on `Ω` by its pairings with `𝓓(Ω, V)`.

## Main results

* `TestFunction.integrable_inner`: `x ↦ ⟪φ x, w x⟫` is integrable for `w` locally integrable
  on `Ω`.
* `TestFunction.integrable_inner_fderiv`: `x ↦ ⟪∂_v φ x, w x⟫` is integrable for `w` locally
  integrable on `Ω`.
* `TauCeti.ae_eq_of_forall_integral_inner_eq`: two locally integrable fields with the same
  pairings against every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on `Ω`. The target `V` need only
  be complete; the proof tests against `ψ • c` for scalar test functions `ψ` and a constant
  vector `c`.
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace TestFunction

/-- A test function paired with a locally integrable field is integrable. -/
theorem integrable_inner {w : E → V} (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, V)) :
    Integrable (fun x => ⟪(φ : E → V) x, w x⟫_ℝ) μ :=
  φ.integrable_bilin (innerSL ℝ) hw

/-- A directional derivative of a test function, paired with a locally integrable field, is
integrable. -/
theorem integrable_inner_fderiv {w : E → V} (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, V))
    (v : E) : Integrable (fun x => ⟪fderiv ℝ (φ : E → V) x v, w x⟫_ℝ) μ := by
  have h := (lineDerivCLM ℝ v φ : 𝓓(Ω, V)).integrable_inner hw
  simp only [coe_lineDerivCLM, lineDeriv_eq_fderiv] at h
  exact h

end TestFunction

namespace TauCeti

variable [CompleteSpace V] [FiniteDimensional ℝ E] [BorelSpace E]

/-- The **fundamental lemma** for vector-valued test functions: locally integrable `g, h` on the
open set `Ω` with `∫ ⟪φ, g⟫ = ∫ ⟪φ, h⟫` for every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on
`Ω`. -/
theorem ae_eq_of_forall_integral_inner_eq {g h : E → V} (hg : LocallyIntegrableOn g Ω μ)
    (hh : LocallyIntegrableOn h Ω μ)
    (H : ∀ φ : 𝓓(Ω, V), ∫ x, ⟪(φ : E → V) x, g x⟫_ℝ ∂μ = ∫ x, ⟪(φ : E → V) x, h x⟫_ℝ ∂μ) :
    g =ᵐ[μ.restrict Ω] h := by
  have hgh : LocallyIntegrableOn (g - h) Ω μ := hg.sub hh
  have key := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero Ω.isOpen hgh
    fun ψ hψ hψc hψΩ => by
      set w := ∫ x, ψ x • (g - h) x ∂μ
      let ψ' : 𝓓(Ω, ℝ) := ⟨ψ, hψ, hψc, hψΩ⟩
      let Φ : 𝓓(Ω, V) := ⟨fun x => ψ x • w, hψ.smul contDiff_const, hψc.smul_right,
        (tsupport_smul_subset_left _ _).trans hψΩ⟩
      have hΦ := H Φ
      have hint : Integrable (fun x => ψ x • (g - h) x) μ :=
        ψ'.integrable_smul hgh
      have : ⟪w, w⟫_ℝ = 0 := by
        calc ⟪w, w⟫_ℝ = ∫ x, ⟪w, ψ x • (g - h) x⟫_ℝ ∂μ := (integral_inner hint w).symm
          _ = ∫ x, ⟪(Φ : E → V) x, g x⟫_ℝ ∂μ - ∫ x, ⟪(Φ : E → V) x, h x⟫_ℝ ∂μ := by
            rw [← integral_sub (Φ.integrable_inner hg) (Φ.integrable_inner hh)]
            refine integral_congr_ae (.of_forall fun x => ?_)
            simp [Φ, inner_smul_left, inner_smul_right, inner_sub_right, mul_sub]
          _ = 0 := sub_eq_zero.2 hΦ
      exact inner_self_eq_zero.1 this
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [key] with x hx hxΩ
  exact sub_eq_zero.1 (hx hxΩ)

end TauCeti
