/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Convergence of nonnegative Dirichlet series

For nonnegative real coefficients, the real Dirichlet series converges precisely when its
increasing partial sums are bounded. This criterion identifies ordinary convergence with the
summability used by `LSeries`, and provides the convergence input for singularity results at the
abscissa of convergence.
-/

public section

namespace TauCeti

/-- For nonnegative coefficients, boundedness of the real Dirichlet partial sums is equivalent
to summability of the corresponding complex `LSeries` at a real point. The real summands omit the
zero index, as does `LSeries.term`. -/
theorem LSeriesSummable_iff_bounded_sum_range_of_nonneg {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (s : ℝ) :
    LSeriesSummable (fun n ↦ (a n : ℂ)) (s : ℂ) ↔
      ∃ C : ℝ, ∀ N : ℕ,
        ∑ n ∈ Finset.range N, (if n = 0 then 0 else a n * (n : ℝ) ^ (-s)) ≤ C := by
  let b : ℕ → ℝ := fun n ↦ if n = 0 then 0 else a n * (n : ℝ) ^ (-s)
  have hb : ∀ n, 0 ≤ b n := by
    intro n
    simp only [b]
    split_ifs with hn
    · exact le_rfl
    · exact mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hterm (n : ℕ) : LSeries.term (fun n ↦ (a n : ℂ)) (s : ℂ) n = (b n : ℂ) := by
    by_cases hn : n = 0
    · simp [b, hn]
    · rw [LSeries.term_of_ne_zero hn]
      simp only [b, ite_eq_right hn, Complex.ofReal_mul,
        Complex.ofReal_cpow (Nat.cast_nonneg n),
        Complex.ofReal_natCast]
      rw [Complex.ofReal_neg]
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
  have hsummable : LSeriesSummable (fun n ↦ (a n : ℂ)) (s : ℂ) ↔ Summable b := by
    rw [LSeriesSummable, ← Complex.summable_ofReal]
    exact summable_congr fun n ↦ hterm n
  rw [hsummable]
  constructor
  · intro h
    refine ⟨∑' n, b n, fun N ↦ ?_⟩
    exact h.sum_le_tsum (Finset.range N) (fun n hn ↦ hb n)
  · rintro ⟨C, hC⟩
    apply summable_of_sum_range_le hb
    exact hC

end TauCeti
