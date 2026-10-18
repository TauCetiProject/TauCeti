/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of the real Gamma function and continuity of its reciprocal

`Real.Gamma` is smooth away from the nonpositive integers and has a pole at each of them, so it is
neither continuous nor locally bounded on all of `ℝ`. It is nevertheless Borel measurable, because
the set of its singularities is countable.

Mathlib records the analytic side of this (`Real.differentiableAt_Gamma`,
`Real.not_continuousAt_Gamma_neg_nat`) but never draws the measurability conclusion. It is needed
as soon as a formula containing `Real.Gamma s` is integrated or measured *in the variable `s`* —
for instance for the normalizing constants of the Gamma and Beta densities, which is why their
family-specific measurability modules use this result.

The reciprocal `(Real.Gamma s)⁻¹`, on the other hand, is continuous on all of `ℝ`: Mathlib's
convention `Real.Gamma (-n) = 0` makes it vanish at the poles, matching the zeros of the entire
function `1 / Γ`. It is bounded on every half-line `[a, ∞)`, which is what uniform estimates for
series with coefficients `1 / Γ(b + n)`, such as hypergeometric and Bessel series, need.

## Main results

* `Real.measurable_Gamma` — `Real.Gamma` is measurable.
* `Real.continuous_inv_Gamma` — `s ↦ (Real.Gamma s)⁻¹` is continuous.
* `Real.exists_abs_inv_Gamma_le` — `(Real.Gamma s)⁻¹` is bounded on `[a, ∞)`.
-/

public section

namespace TauCeti

/-- The real Gamma function is Borel measurable on all of `ℝ`, including at its poles. -/
@[fun_prop]
theorem _root_.Real.measurable_Gamma : Measurable Real.Gamma := by
  refine measurable_of_countable_not_continuousAt (Set.Countable.mono ?_
    (Set.countable_range fun m : ℕ => -(m : ℝ)))
  intro s hs
  by_contra hrange
  exact hs (Real.differentiableAt_Gamma fun m hm => hrange ⟨m, hm.symm⟩).continuousAt

/-- The reciprocal of the real Gamma function is continuous on all of `ℝ`, including at the poles
of `Real.Gamma`, where both it and the entire function `1 / Γ` vanish. -/
@[fun_prop]
theorem _root_.Real.continuous_inv_Gamma : Continuous fun s : ℝ => (Real.Gamma s)⁻¹ := by
  have h : (fun s : ℝ => (Real.Gamma s)⁻¹) = fun s : ℝ => ((Complex.Gamma s)⁻¹).re := by
    ext s
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp
    (Complex.differentiable_one_div_Gamma.continuous.comp Complex.continuous_ofReal)

/-- The reciprocal of the real Gamma function is bounded on every half-line `[a, ∞)`. -/
theorem _root_.Real.exists_abs_inv_Gamma_le (a : ℝ) :
    ∃ C, ∀ s, a ≤ s → |(Real.Gamma s)⁻¹| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Real.continuous_inv_Gamma.continuousOn (s := Set.Icc a 2))
  refine ⟨max C 1, fun s hs => ?_⟩
  rcases le_total s 2 with h | h
  · exact (hC s ⟨hs, h⟩).trans (le_max_left _ _)
  · have h1 : 1 ≤ Real.Gamma s := Real.Gamma_two ▸
      Real.Gamma_strictMonoOn_Ici.monotoneOn Set.self_mem_Ici h h
    rw [abs_inv, abs_of_pos (by linarith)]
    exact (inv_le_one_of_one_le₀ h1).trans (le_max_right _ _)

end TauCeti
