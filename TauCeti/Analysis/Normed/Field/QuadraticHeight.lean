/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Ultrametric quadratic root bounds and dynamical height bounds

This file collects two elementary bounds used to deduce integrality of torsion values on CM
elliptic curves:

* `TauCeti.norm_le_of_sq_add_mul_eq`: over any ultrametric seminormed commutative ring with
  multiplicative norm, a root `g` of `g ^ 2 + u * g = v` with `‖u‖ ≤ c` and `‖v‖ ≤ c ^ 2`
  satisfies `‖g‖ ≤ c`.
* `TauCeti.le_one_of_forall_exists_pow_le`: a bounded real-valued function `r` on a type `α` such
  that every value `r z > 1` admits some `z'` with `r z ^ k ≤ r z'` (for `2 ≤ k`) satisfies
  `r z ≤ 1` everywhere.
* `TauCeti.le_one_of_forall_exists_sq_le`: the `k = 2` specialization.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/Lib/CM/Integrality/TorsionValues.lean`,
declarations `New.CMLattice.norm_le_of_sq_add_mul_eq` and `New.le_one_of_forall_exists_sq_le`,
generalized from `ℂ_[p]` to any ultrametric ring with multiplicative norm and from squaring to
any exponent `k ≥ 2`.
-/

@[expose] public section

namespace TauCeti

/-- In an ultrametric seminormed commutative ring with multiplicative norm, any root `g` of
`g ^ 2 + u * g = v` with `‖u‖ ≤ c` and `‖v‖ ≤ c ^ 2` satisfies `‖g‖ ≤ c`. -/
theorem norm_le_of_sq_add_mul_eq {R : Type*} [SeminormedCommRing R] [NormMulClass R]
    [IsUltrametricDist R] {g u v : R} {c : ℝ} (hu : ‖u‖ ≤ c) (hv : ‖v‖ ≤ c ^ 2)
    (hg : g ^ 2 + u * g = v) : ‖g‖ ≤ c := by
  by_contra! h_lt
  have hc : 0 ≤ c := (norm_nonneg u).trans hu
  have h_eq : g ^ 2 = u * -g + v := by linear_combination hg
  have h_sq : ‖g‖ ^ 2 ≤ c * ‖g‖ := calc
    ‖g‖ ^ 2 = ‖u * -g + v‖ := by rw [sq, ← norm_mul, ← sq, h_eq]
    _ ≤ max (‖u‖ * ‖g‖) ‖v‖ := by
        simpa [norm_mul, norm_neg] using IsUltrametricDist.norm_add_le_max (u * -g) v
    _ ≤ max (c * ‖g‖) (c ^ 2) := max_le_max (mul_le_mul_of_nonneg_right hu (norm_nonneg g)) hv
    _ = c * ‖g‖ := max_eq_left (by nlinarith)
  nlinarith

/-- A bounded real-valued function `r` such that every value `r z > 1` admits some `z'` with
`r z ^ k ≤ r z'` (for `2 ≤ k`) is bounded above by `1`. -/
theorem le_one_of_forall_exists_pow_le {α : Type*} {r : α → ℝ} {K : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (h_bdd : ∀ z : α, r z ≤ K) (h_pow : ∀ z : α, 1 < r z → ∃ z' : α, r z ^ k ≤ r z')
    (z : α) : r z ≤ 1 := by
  by_contra! h_lt
  have h_iterate (m : ℕ) : ∃ z' : α, r z ^ k ^ m ≤ r z' := by
    induction m with
    | zero => exact ⟨z, by simp⟩
    | succ m ih =>
      obtain ⟨z₁, h₁⟩ := ih
      have hk_pos : 0 < k ^ m := pow_pos (by omega) m
      obtain ⟨z₂, h₂⟩ := h_pow z₁ ((one_lt_pow₀ h_lt hk_pos.ne').trans_le h₁)
      refine ⟨z₂, le_trans ?_ h₂⟩
      rw [pow_succ, pow_mul]
      exact pow_le_pow_left₀ (by positivity) h₁ k
  obtain ⟨n, hn⟩ : ∃ n : ℕ, K < r z ^ n := pow_unbounded_of_one_lt K h_lt
  obtain ⟨z', hz'⟩ := h_iterate n
  have h_exp : r z ^ n ≤ r z ^ k ^ n :=
    pow_le_pow_right₀ h_lt.le (Nat.lt_pow_self (by omega)).le
  exact (hn.trans_le (h_exp.trans hz')).not_ge (h_bdd z')

/-- A bounded real-valued function `r` such that every value `r z > 1` admits some `z'` with
`r z ^ 2 ≤ r z'` is bounded above by `1`. -/
theorem le_one_of_forall_exists_sq_le {α : Type*} {r : α → ℝ} {K : ℝ}
    (h_bdd : ∀ z : α, r z ≤ K) (h_sq : ∀ z : α, 1 < r z → ∃ z' : α, r z ^ 2 ≤ r z')
    (z : α) : r z ≤ 1 :=
  le_one_of_forall_exists_pow_le le_rfl h_bdd h_sq z

end TauCeti
