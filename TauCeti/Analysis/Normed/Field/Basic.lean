/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Separating radii by norms of a nontrivially normed field

In a nontrivially normed field `𝕜` the norms need not be dense, so two radii `0 < r < s` need not
be separated by the norm of an element of `𝕜`. They are separated after raising to a power:
`NormedField.exists_pow_lt_norm_lt_pow` gives `m : ℕ` and `c : 𝕜` with `rᵐ < ‖c‖ < sᵐ`. Compare
`NormedField.exists_lt_norm_lt`, which separates the radii themselves in a densely normed field.
Over an algebraically closed field `m`-th roots exist, so the radii themselves are separated:
`NormedField.exists_lt_norm_lt_of_isAlgClosed`. Iterating, the norms of a sequence decrease
strictly inside any interval `(r, s)`: `NormedField.exists_strictAnti_norm_mem_Ioo_of_isAlgClosed`.
-/

public section

namespace NormedField

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- **Two radii `0 < r < s` are separated by a norm after raising to a power**: there are `m : ℕ`
and `c : 𝕜` with `rᵐ < ‖c‖ < sᵐ`. -/
theorem exists_pow_lt_norm_lt_pow {r s : ℝ} (hr₀ : 0 < r) (hlt : r < s) :
    ∃ (m : ℕ) (c : 𝕜), r ^ m < ‖c‖ ∧ ‖c‖ < s ^ m := by
  -- choose `m` with `‖k‖ < (s / r)ᵐ` and `c` in the shell `sᵐ / ‖k‖ ≤ ‖c‖ < sᵐ`
  obtain ⟨k, hk⟩ := exists_one_lt_norm 𝕜
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖k‖ ((one_lt_div hr₀).mpr hlt)
  obtain ⟨c, -, hcs, hcr, -⟩ :=
    rescale_to_shell hk (pow_pos (hr₀.trans hlt) m) (one_ne_zero' 𝕜)
  rw [smul_eq_mul, mul_one] at hcs hcr
  refine ⟨m, c, lt_of_lt_of_le ?_ hcr, hcs⟩
  rw [lt_div_iff₀ (one_pos.trans hk), ← lt_div_iff₀' (pow_pos hr₀ m), ← div_pow]
  exact hm

/-- **The norms of an algebraically closed nontrivially normed field are dense**: two radii
`0 ≤ r < s` are separated by the norm of an element. This is the conclusion of
`NormedField.exists_lt_norm_lt` without a `DenselyNormedField` instance. -/
theorem exists_lt_norm_lt_of_isAlgClosed [IsAlgClosed 𝕜] {r s : ℝ} (hr₀ : 0 ≤ r) (hlt : r < s) :
    ∃ c : 𝕜, r < ‖c‖ ∧ ‖c‖ < s := by
  -- separate a positive radius `r' ≥ r` from `s`, so that `r = 0` needs no special case
  have hr' : 0 < max r (s / 2) := lt_max_of_lt_right (by linarith)
  have hlt' : max r (s / 2) < s := max_lt hlt (by linarith)
  obtain ⟨m, c, hm, hc⟩ := exists_pow_lt_norm_lt_pow 𝕜 hr' hlt'
  have hm₀ : m ≠ 0 := by
    rintro rfl
    exact (hm.trans hc).ne (by simp)
  obtain ⟨d, rfl⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hm₀)
  rw [norm_pow] at hm hc
  exact ⟨d, (le_max_left _ _).trans_lt ((pow_lt_pow_iff_left₀ hr'.le (norm_nonneg d) hm₀).mp hm),
    (pow_lt_pow_iff_left₀ (norm_nonneg d) (hr'.trans hlt').le hm₀).mp hc⟩

/-- **The norms of an algebraically closed nontrivially normed field contain a strictly decreasing
sequence in any interval** `(r, s)` with `0 ≤ r < s`. -/
theorem exists_strictAnti_norm_mem_Ioo_of_isAlgClosed [IsAlgClosed 𝕜] {r s : ℝ} (hr₀ : 0 ≤ r)
    (hlt : r < s) : ∃ c : ℕ → 𝕜, StrictAnti (fun n ↦ ‖c n‖) ∧ ∀ n, ‖c n‖ ∈ Set.Ioo r s := by
  -- `next y` has norm strictly between `r` and `‖y‖` whenever `r < ‖y‖`
  have hnext (y : 𝕜) : ∃ z : 𝕜, r < ‖y‖ → r < ‖z‖ ∧ ‖z‖ < ‖y‖ := by
    by_cases hy : r < ‖y‖
    · obtain ⟨z, hz⟩ := exists_lt_norm_lt_of_isAlgClosed 𝕜 hr₀ hy
      exact ⟨z, fun _ ↦ hz⟩
    · exact ⟨0, fun h ↦ (hy h).elim⟩
  choose next hnext using hnext
  obtain ⟨c₀, hc₀⟩ := exists_lt_norm_lt_of_isAlgClosed 𝕜 hr₀ hlt
  have hmem (n : ℕ) : r < ‖next^[n] c₀‖ ∧ ‖next^[n] c₀‖ < s := by
    induction n with
    | zero => exact hc₀
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨(hnext _ ih.1).1, (hnext _ ih.1).2.trans ih.2⟩
  refine ⟨fun n ↦ next^[n] c₀, strictAnti_nat_of_succ_lt fun n ↦ ?_, hmem⟩
  simpa only [Function.iterate_succ_apply'] using (hnext _ (hmem n).1).2

end NormedField
