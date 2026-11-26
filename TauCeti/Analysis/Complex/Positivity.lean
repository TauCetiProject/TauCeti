/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Positivity

/-!
# Quantitative positivity bounds for entire functions from Taylor derivatives

If an entire function `h : ℂ → ℂ` has real nonnegative iterated derivatives at `0`, subtracting a
single Taylor monomial `a₀ * z ^ n₀` with `a₀ * n₀! ≤ (iteratedDeriv n₀ h 0).re` preserves
nonnegativity of all Taylor derivatives at `0`. Applying
`Differentiable.nonneg_of_iteratedDeriv_nonneg` to the remainder gives the lower bound
`a₀ * x ^ n₀ ≤ (h x).re` for all `x ≥ 0`.

## Main results

* `Differentiable.mul_pow_le_re_of_iteratedDeriv_nonneg`: Taylor monomial lower bound on `[0, ∞)`
  for entire functions with real nonnegative iterated derivatives at `0`.
-/

public section

open Complex

namespace Differentiable

/-- An entire function `h` whose Taylor derivatives at `0` are real and nonnegative satisfies
`a₀ * x ^ n₀ ≤ (h x).re` for all `x ≥ 0` whenever `a₀ * n₀! ≤ (iteratedDeriv n₀ h 0).re`. -/
theorem mul_pow_le_re_of_iteratedDeriv_nonneg {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hnonneg : ∀ n : ℕ, (iteratedDeriv n h 0).im = 0 ∧ 0 ≤ (iteratedDeriv n h 0).re)
    {n₀ : ℕ} {a₀ : ℝ} (ha₀ : a₀ * (n₀.factorial : ℝ) ≤ (iteratedDeriv n₀ h 0).re)
    {x : ℝ} (hx : 0 ≤ x) :
    a₀ * x ^ n₀ ≤ (h (x : ℂ)).re := by
  have hrem_diff : Differentiable ℂ (fun z : ℂ ↦ h z - (a₀ : ℂ) • z ^ n₀) :=
    hh.sub ((differentiable_id.pow n₀).const_smul (a₀ : ℂ))
  open scoped ComplexOrder in
  have hrem_deriv (n : ℕ) :
      0 ≤ iteratedDeriv n (fun z : ℂ ↦ h z - (a₀ : ℂ) • z ^ n₀) 0 := by
    rw [iteratedDeriv_fun_sub hh.contDiff.contDiffAt (by fun_prop),
      iteratedDeriv_fun_const_smul_field, iteratedDeriv_fun_pow_zero]
    split_ifs with hn
    · subst n
      have hc_eq : iteratedDeriv n₀ h 0 = (((iteratedDeriv n₀ h 0).re : ℝ) : ℂ) :=
        Complex.ext rfl (hnonneg n₀).1
      rw [hc_eq, smul_eq_mul, Complex.nonneg_iff]
      exact ⟨by simpa using sub_nonneg.mpr ha₀, by simp⟩
    · simpa [Complex.nonneg_iff, eq_comm, and_comm] using hnonneg n
  open scoped ComplexOrder in
  have hrem_nonneg : (0 : ℂ) ≤ h (x : ℂ) - (a₀ : ℂ) • (x : ℂ) ^ n₀ :=
    hrem_diff.nonneg_of_iteratedDeriv_nonneg hrem_deriv (Complex.real_le_real.mpr hx)
  open scoped ComplexOrder in
  simpa [sub_nonneg, ← Complex.ofReal_pow] using (Complex.nonneg_iff.mp hrem_nonneg).1

end Differentiable
