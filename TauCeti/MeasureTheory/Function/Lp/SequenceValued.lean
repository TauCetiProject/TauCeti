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

For a finite set `s` of indices and continuous linear maps `Tⱼ : E → Lᵖ(μ, Fⱼ)`,
`MeasureTheory.Lp.lpPi q s T` is the operator `f ↦ (Tⱼ f)_{j ∈ s}` into `Lᵖ(μ, ℓ^q(F))`, placing
`Tⱼ f` in coordinate `j` and `0` in the coordinates outside `s`
(`MeasureTheory.Lp.lpPi_apply`). Almost everywhere it is
`x ↦ ∑_{j ∈ s} lp.single q j (Tⱼ f x)` (`MeasureTheory.Lp.coeFn_lpPi`). Evaluating coordinate
`j` gives `Tⱼ` for `j ∈ s` and `0` otherwise (`MeasureTheory.Lp.evalCLM_compLpL_comp_lpPi`);
applied to `f`, this is `MeasureTheory.Lp.evalCLM_compLpL_lpPi` and
`MeasureTheory.Lp.evalCLM_compLpL_lpPi_of_notMem`.

A typical use is a vector-valued square function: with `q = 2` and blocks `Tⱼ`, the norm of
`lpPi 2 s T f` at `x` is `(∑_{j ∈ s} ‖Tⱼ f x‖²)^{1/2}` for `μ`-almost every `x`.
-/
public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 ι E : Type*} {F : ι → Type*} {m : MeasurableSpace α} {μ : Measure α}
  {p : ℝ≥0∞} [NontriviallyNormedField 𝕜] [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)] [Fact (1 ≤ p)] [DecidableEq ι]

variable (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- The operator `f ↦ (Tⱼ f)_{j ∈ s}` from `E` to `Lᵖ(μ, ℓ^q(F))` built from operators
`Tⱼ : E → Lᵖ(μ, Fⱼ)`; the coordinates outside `s` vanish. -/
noncomputable def lpPi (s : Finset ι) (T : ∀ j, E →L[𝕜] Lp (F j) p μ) :
    E →L[𝕜] Lp (lp F q) p μ :=
  ∑ j ∈ s, (lp.singleContinuousLinearMap 𝕜 F q j).compLpL p μ ∘L T j

/-- `lpPi q s T f` is the sum over `j ∈ s` of `Tⱼ f` placed in coordinate `j`. -/
theorem lpPi_apply (s : Finset ι) (T : ∀ j, E →L[𝕜] Lp (F j) p μ) (f : E) :
    lpPi q s T f = ∑ j ∈ s, (lp.singleContinuousLinearMap 𝕜 F q j).compLpL p μ (T j f) := by
  simp [lpPi]

/-- Almost everywhere, `lpPi q s T f` is `x ↦ ∑_{j ∈ s} lp.single q j (Tⱼ f x)`. -/
theorem coeFn_lpPi (s : Finset ι) (T : ∀ j, E →L[𝕜] Lp (F j) p μ) (f : E) :
    lpPi q s T f =ᵐ[μ] fun x ↦ ∑ j ∈ s, lp.single q j (T j f x) := by
  have hj : ∀ j ∈ s, ∀ᵐ x ∂μ,
      (lp.singleContinuousLinearMap 𝕜 F q j).compLpL p μ (T j f) x =
        lp.single q j (T j f x) := fun j _ ↦
    (lp.singleContinuousLinearMap 𝕜 F q j).coeFn_compLpL (T j f)
  filter_upwards [Lp.coeFn_fun_finsetSum s fun j ↦
    (lp.singleContinuousLinearMap 𝕜 F q j).compLpL p μ (T j f),
    (Filter.eventually_all_finset s).2 hj] with x hx hjx
  rw [lpPi_apply, hx]
  exact Finset.sum_congr rfl hjx

/-- Coordinate `j` of `lpPi q s T` is `Tⱼ` if `j ∈ s` and zero otherwise. -/
@[simp]
theorem evalCLM_compLpL_comp_lpPi (s : Finset ι) (T : ∀ j, E →L[𝕜] Lp (F j) p μ) (j : ι) :
    (lp.evalCLM 𝕜 F q j).compLpL p μ ∘L lpPi q s T = if j ∈ s then T j else 0 := by
  ext f : 1
  apply Lp.ext
  filter_upwards [(lp.evalCLM 𝕜 F q j).coeFn_compLpL (lpPi q s T f), coeFn_lpPi q s T f,
    Lp.coeFn_zero (F j) p μ] with x h₁ h₂ h₃
  rw [ContinuousLinearMap.comp_apply, h₁, h₂, lp.evalCLM_apply, lp.coeFn_sum, Finset.sum_apply]
  split_ifs with hj
  · simp [hj]
  · rw [_root_.zero_apply, h₃, Pi.zero_apply]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [lp.single_apply_ne]
      rintro rfl
      exact hj hi

/-- Coordinate `j ∈ s` of `lpPi q s T f` is `Tⱼ f`. -/
@[simp]
theorem evalCLM_compLpL_lpPi {s : Finset ι} (T : ∀ j, E →L[𝕜] Lp (F j) p μ) {j : ι}
    (hj : j ∈ s) (f : E) :
    (lp.evalCLM 𝕜 F q j).compLpL p μ (lpPi q s T f) = T j f := by
  rw [← ContinuousLinearMap.comp_apply, evalCLM_compLpL_comp_lpPi]
  simp [hj]

/-- Coordinate `j ∉ s` of `lpPi q s T f` is zero. -/
@[simp]
theorem evalCLM_compLpL_lpPi_of_notMem {s : Finset ι} (T : ∀ j, E →L[𝕜] Lp (F j) p μ) {j : ι}
    (hj : j ∉ s) (f : E) :
    (lp.evalCLM 𝕜 F q j).compLpL p μ (lpPi q s T f) = 0 := by
  rw [← ContinuousLinearMap.comp_apply, evalCLM_compLpL_comp_lpPi]
  simp [hj]

end MeasureTheory.Lp
