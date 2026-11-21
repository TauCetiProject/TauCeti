/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Bounded real functions and Blackwell's sufficient conditions

The Banach space `TauCeti.BoundedFn ι` of bounded real functions on `ι` with the sup norm is
Mathlib's `lp (fun _ : ι ↦ ℝ) ∞`. Adding `c • 1` to such a function raises each of its values by
the constant `c` (`lp.infty_coeFn_add_smul_one`).

This file proves Blackwell's sufficient conditions (`lp.lipschitzWith_of_mono_of_le_add_const`):
an operator on `lp (fun _ : ι ↦ ℝ) ∞` that is monotone and raises by at most `γ c` when its
argument is raised by a constant `c ≥ 0` is `γ`-Lipschitz. The Bellman operators of a discounted
Markov decision process are contractions for this reason.

## References

* D. Blackwell, *Discounted dynamic programming*, Ann. Math. Statist. **36** (1965), 226–235,
  Theorem 5.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

/-- The Banach space of bounded real functions on `ι` with the sup norm: Mathlib's `lp` space of
real families with exponent `∞`. -/
abbrev BoundedFn (ι : Type*) : Type _ := lp (fun _ : ι ↦ ℝ) ∞

end TauCeti

namespace lp

variable {ι : Type*}

/-- Adding `c • 1` to a bounded real function raises each of its values by the constant `c`. -/
theorem infty_coeFn_add_smul_one (v : lp (fun _ : ι ↦ ℝ) ∞) (c : ℝ) :
    ⇑(v + c • 1) = fun i ↦ v i + c := by
  ext i
  simp only [lp.coeFn_add, lp.coeFn_smul, lp.infty_coeFn_one, Pi.add_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one]

/-- **Blackwell's sufficient conditions.** An operator on the bounded real functions that is
monotone and raises by at most `γ * c` when its argument is raised by the constant `c ≥ 0` is
`γ`-Lipschitz for the sup norm. -/
theorem lipschitzWith_of_mono_of_le_add_const {γ : ℝ≥0}
    {T : lp (fun _ : ι ↦ ℝ) ∞ → lp (fun _ : ι ↦ ℝ) ∞}
    (mono : ∀ ⦃v w : lp (fun _ : ι ↦ ℝ) ∞⦄, (∀ i, v i ≤ w i) → ∀ i, T v i ≤ T w i)
    (le_add_const :
      ∀ (v : lp (fun _ : ι ↦ ℝ) ∞) (c : ℝ), 0 ≤ c → ∀ i, T (v + c • 1) i ≤ T v i + γ * c) :
    LipschitzWith γ T := by
  have key (v w : lp (fun _ : ι ↦ ℝ) ∞) (i : ι) : T v i - T w i ≤ γ * ‖v - w‖ := by
    have hle (j : ι) : v j ≤ (w + ‖v - w‖ • 1 : lp (fun _ : ι ↦ ℝ) ∞) j := by
      have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (v - w) j
      simp only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at h
      rw [infty_coeFn_add_smul_one]
      linarith [le_abs_self (v j - w j)]
    linarith [mono hle i, le_add_const w ‖v - w‖ (norm_nonneg _) i]
  refine LipschitzWith.of_dist_le_mul fun v w ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (by positivity) fun i ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨key v w i, norm_sub_rev v w ▸ key w v i⟩

end lp
