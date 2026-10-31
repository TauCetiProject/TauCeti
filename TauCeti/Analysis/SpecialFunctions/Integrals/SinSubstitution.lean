/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The substitution `t = sin θ` for arbitrary integrands

On `[-π/2, π/2]` the sine is increasing with derivative `cos θ ≥ 0`, so for every function
`g : ℝ → E` and all `a, b ∈ [-π/2, π/2]`,

`∫ θ in a..b, cos θ • g (sin θ) = ∫ t in sin a..sin b, g t`,

and the two integrands are integrable together. No continuity or integrability of `g` is assumed:
these are the one-dimensional change of variables formulas of
`Mathlib/MeasureTheory/Function/JacobianOneDim.lean` for monotone maps, written as interval
integrals. In particular they turn an integral in `t` that is improper at `t = ±1`, such as
`∫₀¹ (1 - t²)^(-1/2) g(t) dt`, into an integral in `θ` whose integrand is often continuous.

## Main statements

* `TauCeti.integral_cos_smul_comp_sin`: the substitution formula.
* `TauCeti.intervalIntegrable_cos_smul_comp_sin_iff`: the two integrands are integrable together.
-/

public section

namespace TauCeti

open MeasureTheory Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cosine is nonnegative between two points of `[-π/2, π/2]`. -/
private lemma cos_nonneg_of_mem_Ioo_of_mem_Icc {a b : ℝ} (ha : a ∈ Icc (-(π / 2)) (π / 2))
    (hb : b ∈ Icc (-(π / 2)) (π / 2)) {θ : ℝ} (hθ : θ ∈ Ioo a b) : 0 ≤ cos θ :=
  cos_nonneg_of_mem_Icc ⟨by linarith [ha.1, hθ.1], by linarith [hb.2, hθ.2]⟩

/-- The substitution formula for `a ≤ b`. -/
private lemma integral_cos_smul_comp_sin_of_le {a b : ℝ} (ha : a ∈ Icc (-(π / 2)) (π / 2))
    (hb : b ∈ Icc (-(π / 2)) (π / 2)) (hab : a ≤ b) (g : ℝ → E) :
    ∫ θ in a..b, cos θ • g (sin θ) = ∫ t in sin a..sin b, g t := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    integral_Icc_deriv_smul_of_deriv_nonneg continuous_sin.continuousOn
      (fun θ _ ↦ hasDerivAt_sin θ) (fun _ ↦ cos_nonneg_of_mem_Ioo_of_mem_Icc ha hb) hab,
    intervalIntegral.integral_of_le (sin_le_sin_of_le_of_le_pi_div_two ha.1 hb.2 hab),
    integral_Icc_eq_integral_Ioc]

/-- **The substitution `t = sin θ`**: for every `g : ℝ → E` and all `a, b ∈ [-π/2, π/2]`,
`∫ θ in a..b, cos θ • g (sin θ) = ∫ t in sin a..sin b, g t`. -/
theorem integral_cos_smul_comp_sin {a b : ℝ} (ha : a ∈ Icc (-(π / 2)) (π / 2))
    (hb : b ∈ Icc (-(π / 2)) (π / 2)) (g : ℝ → E) :
    ∫ θ in a..b, cos θ • g (sin θ) = ∫ t in sin a..sin b, g t := by
  rcases le_total a b with hab | hba
  · exact integral_cos_smul_comp_sin_of_le ha hb hab g
  · rw [intervalIntegral.integral_symm, integral_cos_smul_comp_sin_of_le hb ha hba g,
      ← intervalIntegral.integral_symm]

/-- Integrability in the substitution formula for `a ≤ b`. -/
private lemma intervalIntegrable_cos_smul_comp_sin_iff_of_le {a b : ℝ}
    (ha : a ∈ Icc (-(π / 2)) (π / 2)) (hb : b ∈ Icc (-(π / 2)) (π / 2)) (hab : a ≤ b)
    (g : ℝ → E) :
    IntervalIntegrable (fun θ ↦ cos θ • g (sin θ)) volume a b ↔
      IntervalIntegrable g volume (sin a) (sin b) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab,
    intervalIntegrable_iff_integrableOn_Icc_of_le
      (sin_le_sin_of_le_of_le_pi_div_two ha.1 hb.2 hab)]
  exact integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg continuous_sin.continuousOn
    (fun θ _ ↦ hasDerivAt_sin θ) (fun _ ↦ cos_nonneg_of_mem_Ioo_of_mem_Icc ha hb) hab

/-- In the substitution `t = sin θ` on `[-π/2, π/2]`, the integrand `cos θ • g (sin θ)` is
interval integrable between `a` and `b` if and only if `g` is interval integrable between
`sin a` and `sin b`. -/
theorem intervalIntegrable_cos_smul_comp_sin_iff {a b : ℝ} (ha : a ∈ Icc (-(π / 2)) (π / 2))
    (hb : b ∈ Icc (-(π / 2)) (π / 2)) (g : ℝ → E) :
    IntervalIntegrable (fun θ ↦ cos θ • g (sin θ)) volume a b ↔
      IntervalIntegrable g volume (sin a) (sin b) := by
  rcases le_total a b with hab | hba
  · exact intervalIntegrable_cos_smul_comp_sin_iff_of_le ha hb hab g
  · have h := intervalIntegrable_cos_smul_comp_sin_iff_of_le hb ha hba g
    exact ⟨fun h' ↦ (h.1 h'.symm).symm, fun h' ↦ (h.2 h'.symm).symm⟩

end TauCeti
