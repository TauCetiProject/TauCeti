/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Weighted geometric majorants over an index and an exponent

For a family `r : ι → E` in a seminormed additive group whose norms are less than one, and
eventually at most `1 - ε`, wherever the weight `w` is nonzero, the double family
`(i, e) ↦ w i * ‖r i‖ ^ (e + 1)` is summable over `ι × ℕ` as soon as `i ↦ w i * ‖r i‖` is
summable. Such double families majorize the Taylor expansions of `-log (1 - r i)` summed over
`i`, and their termwise derivatives.

## Main results

* `TauCeti.summable_mul_norm_pow_succ`: the weighted double family is summable over `ι × ℕ`.
-/

public section

open NNReal

namespace TauCeti

/-- **A weighted geometric family is summable over index and exponent together.**  Let `w : ι → ℝ`
be weights with `i ↦ w i * ‖r i‖` summable, and let `r` be a family in a seminormed additive group
which, *at every index where `w` is nonzero*, has norm less than one and eventually norm at most
`1 - ε`.  Then the double family `(i, e) ↦ w i * ‖r i‖ ^ (e + 1)` is summable over `ι × ℕ`.

Both conditions on `r` are restricted to the support of `w`, and off that support nothing is asked
of `r` at all: a fibre with `w i = 0` is identically zero whatever `r i` is.  The weights are
unrestricted in sign.

The eventual bound cannot be dropped: the fibre at `i` sums to `w i * ‖r i‖ / (1 - ‖r i‖)`, which
is comparable to `w i * ‖r i‖` only where `‖r i‖` stays away from `1`.  Summability of `r` would
give it, but is far stronger: it rules out a family of constant norm with summable weights. -/
theorem summable_mul_norm_pow_succ {ι E : Type*} [SeminormedAddGroup E] {r : ι → E} {w : ι → ℝ}
    (hbd : ∃ ε > 0, ∀ᶠ i in Filter.cofinite, w i ≠ 0 → ‖r i‖ ≤ 1 - ε)
    (hwr : Summable fun i ↦ w i * ‖r i‖) (h1 : ∀ i, w i ≠ 0 → ‖r i‖ < 1) :
    Summable fun ie : ι × ℕ ↦ w ie.1 * ‖r ie.1‖ ^ (ie.2 + 1) := by
  obtain ⟨ε, hε, hfar⟩ := hbd
  -- On the support of `w` the norms have a uniform bound `δ < 1`: `1 - ε` off the finite set `S`
  -- of exceptions, and the largest norm on `S`.
  set S := (Filter.eventually_cofinite.1 hfar).toFinset
  set δ : ℝ := max (1 - ε) (S.sup fun i ↦ ‖r i‖₊ : ℝ≥0)
  have hδ1 : δ < 1 := max_lt (by linarith) <| by
    exact_mod_cast (Finset.sup_lt_iff (by simp)).2 fun i hi ↦ by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_imp] at hi
      exact_mod_cast h1 i hi.1
  have hδ (i) (hi : w i ≠ 0) : ‖r i‖ ≤ δ := by
    by_cases hS : i ∈ S
    · exact le_max_of_le_right (by exact_mod_cast Finset.le_sup (f := fun i ↦ ‖r i‖₊) hS)
    · exact le_max_of_le_left (by simpa [S, hi] using hS)
  have hδ0 : 0 ≤ δ := le_max_of_le_right (by positivity)
  -- The family is dominated by the product of `|w i| * ‖r i‖` and the geometric `δ ^ e`.
  refine (Summable.mul_of_nonneg (summable_abs_iff.2 hwr)
    (summable_geometric_of_lt_one hδ0 hδ1) (fun _ ↦ abs_nonneg _)
    fun _ ↦ pow_nonneg hδ0 _).of_norm_bounded fun ⟨i, e⟩ ↦ ?_
  rcases eq_or_ne (w i) 0 with h | h
  · simp [h]
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm, pow_succ', ← mul_assoc]
  gcongr
  exact hδ i h

end TauCeti
