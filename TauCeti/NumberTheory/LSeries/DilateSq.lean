/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.ArithmeticFunction.DilateSq
import TauCeti.NumberTheory.LSeries.Term

/-!
# Dirichlet series of square-dilated arithmetic functions

For any complex arithmetic function `f : ArithmeticFunction ℂ`, its dilation by squares
`f.dilateSq` takes the value `f m` at `m ^ 2` and vanishes off the perfect squares. Consequently,
every non-square term of `LSeries f.dilateSq s` vanishes, and the square-indexed terms reindex to
`LSeries.term f (2 * s)`. This gives both the totalized `L`-series identity
`LSeries f.dilateSq s = LSeries f (2 * s)` and the sharp convergence equivalence
`LSeriesSummable f.dilateSq s ↔ LSeriesSummable f (2 * s)`.

## Main results

* `ArithmeticFunction.LSeries_term_dilateSq_sq`:
  `LSeries.term f.dilateSq s (m ^ 2) = LSeries.term f (2 * s) m`.
* `ArithmeticFunction.LSeries_dilateSq`: `LSeries f.dilateSq s = LSeries f (2 * s)`.
* `ArithmeticFunction.LSeriesSummable_dilateSq_iff`:
  `LSeriesSummable f.dilateSq s ↔ LSeriesSummable f (2 * s)`.
-/

public section

namespace ArithmeticFunction

/-- Terms of `LSeries f.dilateSq s` vanish off the range of squaring. -/
private theorem LSeries_term_dilateSq_eq_zero_of_notMem_range (f : ArithmeticFunction ℂ) (s : ℂ)
    {n : ℕ} (hn : n ∉ Set.range (· ^ 2 : ℕ → ℕ)) :
    LSeries.term (f.dilateSq : ℕ → ℂ) s n = 0 := by
  by_cases h0 : n = 0
  · subst h0
    simp
  · have hfd : f.dilateSq n = 0 := by
      by_contra hne
      exact hn (f.exists_eq_sq_of_dilateSq_apply_ne_zero hne |>.imp fun m hm ↦ hm.symm)
    rw [LSeries.term_of_ne_zero h0, hfd, zero_div]

/-- Reindexing the square-indexed Dirichlet terms of `f.dilateSq` at `s` gives the Dirichlet terms
of `f` at `2 * s`. -/
theorem LSeries_term_dilateSq_sq (f : ArithmeticFunction ℂ) (s : ℂ) (m : ℕ) :
    LSeries.term (f.dilateSq : ℕ → ℂ) s (m ^ 2) = LSeries.term (f : ℕ → ℂ) (2 * s) m := by
  rw [TauCeti.LSeries.term_sq]
  simp [LSeries.term]

/-- **Dirichlet series of a square-dilated arithmetic function.** For every complex arithmetic
function `f` and every `s : ℂ`, `LSeries f.dilateSq s = LSeries f (2 * s)` (both totalized to `0`
when not summable). -/
theorem LSeries_dilateSq (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeries (f.dilateSq : ℕ → ℂ) s = LSeries (f : ℕ → ℂ) (2 * s) := by
  rw [LSeries, LSeries]
  refine (Function.Injective.tsum_eq (Nat.pow_left_injective two_ne_zero) fun n hn ↦ ?_).symm.trans
    (tsum_congr (LSeries_term_dilateSq_sq f s))
  by_contra hnot
  exact hn (LSeries_term_dilateSq_eq_zero_of_notMem_range f s hnot)

/-- **Absolute convergence of a square-dilated Dirichlet series.** `LSeriesSummable f.dilateSq s`
holds if and only if `LSeriesSummable f (2 * s)` holds. -/
theorem LSeriesSummable_dilateSq_iff (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeriesSummable (f.dilateSq : ℕ → ℂ) s ↔ LSeriesSummable (f : ℕ → ℂ) (2 * s) := by
  rw [LSeriesSummable, LSeriesSummable,
    ← (Nat.pow_left_injective two_ne_zero).summable_iff
      fun n hn ↦ LSeries_term_dilateSq_eq_zero_of_notMem_range f s hn]
  simp_rw [Function.comp_def, LSeries_term_dilateSq_sq]

end ArithmeticFunction
