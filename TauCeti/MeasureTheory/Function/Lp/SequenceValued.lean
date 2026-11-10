/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Finite families of operators into sequence-valued `Lᵖ`

For a finite set `s` of indices and continuous linear maps `Tⱼ : E → Lᵖ(μ, F)`,
`MeasureTheory.Lp.lpPi q s T` is the operator `f ↦ (Tⱼ f)_{j ∈ s}` into `Lᵖ(μ, ℓ^q(F))`, placing
`Tⱼ f` in coordinate `j` and `0` in the coordinates outside `s`
(`MeasureTheory.Lp.lpPi_apply`). Pointwise it is
`x ↦ ∑_{j ∈ s} lp.single q j (Tⱼ f x)` (`MeasureTheory.Lp.coeFn_lpPi`), and evaluating coordinate
`j` recovers `Tⱼ f` for `j ∈ s` (`MeasureTheory.Lp.evalCLM_compLpL_lpPi`) and `0` otherwise
(`MeasureTheory.Lp.evalCLM_compLpL_lpPi_of_notMem`).

A typical use is a vector-valued square function: with `q = 2` and blocks `Tⱼ`, the norm of
`lpPi 2 s T f` at `x` is `(∑_{j ∈ s} ‖Tⱼ f x‖²)^{1/2}`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 ι E F : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fact (1 ≤ p)] [DecidableEq ι]

variable (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- The operator `f ↦ (Tⱼ f)_{j ∈ s}` from `E` to `Lᵖ(μ, ℓ^q(F))` built from operators
`Tⱼ : E → Lᵖ(μ, F)`; the coordinates outside `s` vanish. -/
noncomputable def lpPi (s : Finset ι) (T : ι → E →L[𝕜] Lp F p μ) :
    E →L[𝕜] Lp (lp (fun _ : ι ↦ F) q) p μ :=
  ∑ j ∈ s, (lp.singleContinuousLinearMap 𝕜 (fun _ : ι ↦ F) q j).compLpL p μ ∘L T j

/-- `lpPi q s T f` is the sum over `j ∈ s` of `Tⱼ f` placed in coordinate `j`. -/
theorem lpPi_apply (s : Finset ι) (T : ι → E →L[𝕜] Lp F p μ) (f : E) :
    lpPi q s T f =
      ∑ j ∈ s, (lp.singleContinuousLinearMap 𝕜 (fun _ : ι ↦ F) q j).compLpL p μ (T j f) := by
  simp [lpPi]

/-- Pointwise, `lpPi q s T f` is `x ↦ ∑_{j ∈ s} lp.single q j (Tⱼ f x)`. -/
theorem coeFn_lpPi (s : Finset ι) (T : ι → E →L[𝕜] Lp F p μ) (f : E) :
    lpPi q s T f =ᵐ[μ] fun x ↦ ∑ j ∈ s, lp.single q j (T j f x) := by
  have hj : ∀ j ∈ s, ∀ᵐ x ∂μ,
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ι ↦ F) q j).compLpL p μ (T j f) x =
        lp.single q j (T j f x) := fun j _ ↦
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ι ↦ F) q j).coeFn_compLpL (T j f)
  filter_upwards [Lp.coeFn_fun_finsetSum s fun j ↦
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ι ↦ F) q j).compLpL p μ (T j f),
    (Filter.eventually_all_finset s).2 hj] with x hx hjx
  rw [lpPi_apply, hx]
  exact Finset.sum_congr rfl hjx

/-- Coordinate `j ∈ s` of `lpPi q s T f` is `Tⱼ f`. -/
theorem evalCLM_compLpL_lpPi {s : Finset ι} (T : ι → E →L[𝕜] Lp F p μ) {j : ι} (hj : j ∈ s)
    (f : E) :
    (lp.evalCLM 𝕜 (fun _ : ι ↦ F) q j).compLpL p μ (lpPi q s T f) = T j f := by
  apply Lp.ext
  filter_upwards [(lp.evalCLM 𝕜 (fun _ : ι ↦ F) q j).coeFn_compLpL (lpPi q s T f),
    coeFn_lpPi q s T f] with x h₁ h₂
  rw [h₁, h₂, lp.evalCLM_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [hj]

/-- Coordinate `j ∉ s` of `lpPi q s T f` is zero. -/
theorem evalCLM_compLpL_lpPi_of_notMem {s : Finset ι} (T : ι → E →L[𝕜] Lp F p μ) {j : ι}
    (hj : j ∉ s) (f : E) :
    (lp.evalCLM 𝕜 (fun _ : ι ↦ F) q j).compLpL p μ (lpPi q s T f) = 0 := by
  apply Lp.ext
  filter_upwards [(lp.evalCLM 𝕜 (fun _ : ι ↦ F) q j).coeFn_compLpL (lpPi q s T f),
    coeFn_lpPi q s T f, Lp.coeFn_zero F p μ] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, lp.evalCLM_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [Pi.zero_apply]
  exact Finset.sum_eq_zero fun i hi ↦ by
    rw [lp.single_apply_ne]
    rintro rfl
    exact hj hi

end MeasureTheory.Lp
