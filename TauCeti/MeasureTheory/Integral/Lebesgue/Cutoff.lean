/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Lebesgue integrals of cut-off functions

Multiplying a real function `u` by a cutoff `χ` with `|χ| ≤ 1` and support in a set `s` does not
increase the Lebesgue integral of its extended norm beyond that of `u` over `s`.

## Main statements

* `TauCeti.lintegral_enorm_mul_le_setLIntegral_of_support_subset`: `∫ |χ u| ≤ ∫_s |u|`.
* `TauCeti.tendsto_lintegral_enorm_mul_sub_of_eventually_eq_one`: cutoffs with values in `[0, 1]`
  that are eventually `1` at almost every point recover an integrable function in `L¹`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Function Set
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {χ : α → ℝ}

/-- Multiplying by a cutoff `χ` with `|χ| ≤ 1` and `support χ ⊆ s` does not increase the `L¹`
norm on `s`: `∫ |χ u| ≤ ∫_s |u|`. Neither `s` nor the functions need be measurable. -/
theorem lintegral_enorm_mul_le_setLIntegral_of_support_subset (hχ1 : ∀ x, |χ x| ≤ 1)
    (hχs : support χ ⊆ s) (u : α → ℝ) :
    ∫⁻ x, ‖(χ * u) x‖ₑ ∂μ ≤ ∫⁻ x in s, ‖u x‖ₑ ∂μ := by
  refine (lintegral_mono fun x => ?_).trans (lintegral_indicator_le _ s)
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, Pi.mul_apply, enorm_mul]
    exact mul_le_of_le_one_left' (by simpa [← ofReal_norm] using hχ1 x)
  · simp [notMem_support.mp fun hmem => hx (hχs hmem)]

/-- **Cutoffs recover an integrable function in `L¹`.** If the cutoffs `χ n` take values in
`[0, 1]` almost everywhere and almost every point is eventually fixed by them, then
`‖χ n u - u‖₁ → 0` for integrable `u`, by dominated convergence. -/
theorem tendsto_lintegral_enorm_mul_sub_of_eventually_eq_one {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {χ : ι → α → ℝ} {u : α → ℝ} (hu : Integrable u μ)
    (hχ : ∀ n, ∀ᵐ x ∂μ, χ n x ∈ Icc 0 1) (hχm : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hlim : ∀ᵐ x ∂μ, ∀ᶠ n in l, χ n x = 1) :
    Tendsto (fun n => ∫⁻ x, ‖χ n x * u x - u x‖ₑ ∂μ) l (𝓝 0) := by
  have hdom (n : ι) : ∀ᵐ x ∂μ, ‖χ n x * u x - u x‖ₑ ≤ ‖u x‖ₑ := (hχ n).mono fun x hx => by
    rw [← sub_one_mul, enorm_mul]
    have hle : ‖χ n x - 1‖ₑ ≤ 1 := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.1, hx.2])]
      exact ENNReal.ofReal_le_one.2 (by linarith [hx.1])
    simpa using mul_le_mul_left hle ‖u x‖ₑ
  simpa only [Pi.mul_apply, Pi.sub_apply, lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence' (f := fun _ => 0) (fun x => ‖u x‖ₑ)
      (.of_forall fun n => (((hχm n).mul hu.aestronglyMeasurable).sub
        hu.aestronglyMeasurable).enorm)
      (.of_forall hdom) hu.hasFiniteIntegral.ne
      (hlim.mono fun x hx => tendsto_const_nhds.congr' (hx.mono fun n hn => by
        simp only [Pi.sub_apply, Pi.mul_apply, hn, one_mul, sub_self, enorm_zero]))

end TauCeti
