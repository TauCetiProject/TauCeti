/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Local complex roots and logarithms

At a nonzero point, a prescribed `k`-th root extends to a root function with a logarithm,
both `C^n` at the point (`TauCeti.exists_contDiffAt_pow_eq_and_exp_eq`). The degree-one
specialization `TauCeti.exists_contDiffAt_exp_eq` supplies a local logarithm without a root
witness. These branches remain available at points on the principal logarithm's branch cut.
-/

public section

open Complex

namespace TauCeti

/-- Near a nonzero `z₀` with a chosen `k`-th root `c`, there is a `k`-th root function `f`
with `f z₀ = c`, together with a logarithm `L` of `f` off `0`. Both are `C^n` at `z₀`,
so holomorphic there for `n ≠ 0`. -/
theorem exists_contDiffAt_pow_eq_and_exp_eq {z₀ c : ℂ} {k : ℕ} (hk : k ≠ 0) (hz₀ : z₀ ≠ 0)
    (hc : c ^ k = z₀) {n : WithTop ℕ∞} :
    ∃ f L : ℂ → ℂ, ContDiffAt ℂ n f z₀ ∧ ContDiffAt ℂ n L z₀ ∧ f z₀ = c ∧
      (∀ z, f z ^ k = z) ∧ ∀ z, z ≠ 0 → exp (L z) = f z := by
  have hc₀ : c ≠ 0 := by rintro rfl; exact hz₀ (by rw [← hc, zero_pow hk])
  let L : ℂ → ℂ := fun z ↦ log c + (k : ℂ)⁻¹ * log (z / z₀)
  have hexp (z : ℂ) (hz : z ≠ 0) : exp (L z) = c * (z / z₀) ^ (k⁻¹ : ℂ) := by
    rw [exp_add, exp_log hc₀, cpow_def_of_ne_zero (div_ne_zero hz hz₀), mul_comm (log _)]
  have hL : ContDiffAt ℂ n L z₀ := contDiffAt_const.add (contDiffAt_const.mul
    ((contDiffAt_log (by rw [div_self hz₀]; exact one_mem_slitPlane)).comp z₀
      (contDiffAt_id.div_const z₀)))
  refine ⟨fun z ↦ c * (z / z₀) ^ (k⁻¹ : ℂ), L, ?_, hL, by simp [div_self hz₀], fun z ↦ ?_, hexp⟩
  · exact (analyticAt_const.mul ((analyticAt_id.div_const (c := z₀)).cpow analyticAt_const
      (by simpa only [id_eq, div_self hz₀] using one_mem_slitPlane))).contDiffAt
  · rw [mul_pow, cpow_nat_inv_pow _ hk, hc, mul_div_cancel₀ _ hz₀]

/-- A nonzero complex point admits a logarithm that is `C^n` at that point, with its
exponential equal to the identity off zero. -/
theorem exists_contDiffAt_exp_eq {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {n : WithTop ℕ∞} :
    ∃ L : ℂ → ℂ, ContDiffAt ℂ n L z₀ ∧ ∀ z, z ≠ 0 → exp (L z) = z := by
  obtain ⟨f, L, -, hL, -, hf, hfL⟩ :=
    exists_contDiffAt_pow_eq_and_exp_eq (n := n) one_ne_zero hz₀ (pow_one z₀)
  refine ⟨L, hL, fun z hz ↦ ?_⟩
  rw [hfL z hz, ← pow_one (f z), hf]

end TauCeti
