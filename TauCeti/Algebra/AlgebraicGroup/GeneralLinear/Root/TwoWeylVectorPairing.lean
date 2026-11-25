/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.BigOperators.Dominance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# The pairing with `2ρ` on coweight coordinates of the general linear group

For the diagonal torus of `GL_n` and the upper-triangular Borel subgroup, the sum of the positive
roots `eᵢ - eⱼ`, `i < j`, is `2ρ`. Its pairing with a vector `x` of (rational) coweight coordinates
is `⟨2ρ, x⟩ = ∑_{i < j} (xᵢ - xⱼ)`. For the Newton vector `ν_b` of a class `b ∈ B(GL_n)` this is
the invariant `d_b = ⟨2ρ, ν_b⟩`, the dimension of its central leaf in the geometric applications.

The pairing is strictly monotone for the dominance order `TauCeti.Dominates`: `x ≼ y` gives
`⟨2ρ, x⟩ ≤ ⟨2ρ, y⟩`, with equality only for `x = y`. The reason is the prefix-sum formula
`⟨2ρ, x⟩ = ∑_{k = 0}^{n} (2 ∑_{i < k} xᵢ - ∑_i xᵢ)`.

## Main definitions

* `TauCeti.GeneralLinear.twoWeylVectorPairing`: the pairing `⟨2ρ, x⟩ = ∑_{i < j} (xᵢ - xⱼ)`.

## Main results

* `TauCeti.GeneralLinear.twoWeylVectorPairing_eq_sum_zsmul`: `⟨2ρ, x⟩ = ∑ᵢ (n - 1 - 2i) • xᵢ`, the
  coordinates of `2ρ` of `TauCeti.GeneralLinear.twoWeylVector_diagonalRootBase_apply`.
* `TauCeti.GeneralLinear.twoWeylVectorPairing_eq_sum_prefixSum`: the prefix-sum formula.
* `TauCeti.Dominates.twoWeylVectorPairing_le`, `TauCeti.Dominates.twoWeylVectorPairing_lt`,
  `TauCeti.Dominates.twoWeylVectorPairing_eq_iff`: the pairing is strictly monotone for
  dominance.

## References

* A. Caraiani and P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), §3.1.
-/

public section

open Finset

namespace TauCeti.GeneralLinear

variable {M : Type*} [AddCommGroup M] {n : ℕ}

/-- The pairing `⟨2ρ, x⟩ = ∑_{i < j} (xᵢ - xⱼ)` of a vector `x` of (rational) coweight coordinates
of the diagonal torus of `GL_n` with the sum `2ρ` of the positive roots `eᵢ - eⱼ`, `i < j`, of the
upper-triangular Borel subgroup. For the Newton vector `ν_b` of a class `b ∈ B(GL_n)` this is the
invariant `d_b = ⟨2ρ, ν_b⟩`. -/
def twoWeylVectorPairing (x : Fin n → M) : M :=
  ∑ i, ∑ j ∈ Ioi i, (x i - x j)

/-- The defining formula of `TauCeti.GeneralLinear.twoWeylVectorPairing`: the sum over the
positive roots `eᵢ - eⱼ`, `i < j`. -/
theorem twoWeylVectorPairing_def (x : Fin n → M) :
    twoWeylVectorPairing x = ∑ i, ∑ j ∈ Ioi i, (x i - x j) :=
  (rfl)

/-- **The coordinates of `2ρ`.** `⟨2ρ, x⟩ = ∑ᵢ (n - 1 - 2i) xᵢ`. -/
theorem twoWeylVectorPairing_eq_sum_zsmul (x : Fin n → M) :
    twoWeylVectorPairing x = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) • x i := by
  have hcomm : ∑ i : Fin n, ∑ j ∈ Ioi i, x j = ∑ j : Fin n, ∑ _i ∈ Iio j, x j :=
    sum_comm' fun i j ↦ by simp
  simp only [twoWeylVectorPairing_def, sum_sub_distrib, hcomm, sum_const, Fin.card_Ioi,
    Fin.card_Iio]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have hi := i.isLt
  rw [Nat.sub_sub, ← natCast_zsmul, ← natCast_zsmul, Nat.cast_sub (by omega)]
  push_cast
  module

/-- **The prefix-sum formula for `⟨2ρ, x⟩`.**
`⟨2ρ, x⟩ = ∑_{k = 0}^{n} (2 ∑_{i < k} xᵢ - ∑ᵢ xᵢ)`. -/
theorem twoWeylVectorPairing_eq_sum_prefixSum (x : Fin n → M) :
    twoWeylVectorPairing x = ∑ k ∈ range (n + 1), (2 • prefixSum k x - ∑ i, x i) := by
  rw [sum_sub_distrib, sum_nsmul, sum_range_prefixSum, twoWeylVectorPairing_eq_sum_zsmul,
    sum_const, card_range, ← sum_nsmul, ← sum_nsmul, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have hi := i.isLt
  simp only [← natCast_zsmul, Nat.cast_sub hi.le]
  push_cast
  module

end TauCeti.GeneralLinear

namespace TauCeti.Dominates

open TauCeti.GeneralLinear

variable {M : Type*} {n : ℕ}

/-- The difference of the pairings with `2ρ` along a dominance `x ≼ y` is twice the sum of the
differences of the prefix sums. -/
private theorem twoWeylVectorPairing_sub [AddCommGroup M] [LE M] {x y : Fin n → M}
    (h : Dominates x y) :
    twoWeylVectorPairing y - twoWeylVectorPairing x =
      ∑ k ∈ range (n + 1), 2 • (prefixSum k y - prefixSum k x) := by
  rw [twoWeylVectorPairing_eq_sum_prefixSum, twoWeylVectorPairing_eq_sum_prefixSum,
    ← sum_sub_distrib, (dominates_def.mp h).1]
  exact sum_congr rfl fun _ _ ↦ by rw [nsmul_sub]; abel

variable [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- **`⟨2ρ, ·⟩` is monotone for dominance.** -/
theorem twoWeylVectorPairing_le {x y : Fin n → M} (h : Dominates x y) :
    twoWeylVectorPairing x ≤ twoWeylVectorPairing y := by
  have hle := (dominates_iff_forall_prefixSum_le.mp h).2
  refine sub_nonneg.mp ?_
  rw [h.twoWeylVectorPairing_sub]
  exact sum_nonneg fun k _ ↦ nsmul_nonneg (sub_nonneg.mpr (hle k)) 2

/-- **`⟨2ρ, ·⟩` is strictly monotone for dominance**: along a dominance `x ≼ y` the pairings
are equal only when `x = y`. -/
theorem twoWeylVectorPairing_eq_iff {x y : Fin n → M} (h : Dominates x y) :
    twoWeylVectorPairing x = twoWeylVectorPairing y ↔ x = y := by
  refine ⟨fun heq ↦ ?_, fun hxy ↦ hxy ▸ rfl⟩
  have hle := (dominates_iff_forall_prefixSum_le.mp h).2
  have hsum : ∑ k ∈ range (n + 1), 2 • (prefixSum k y - prefixSum k x) = 0 := by
    rw [← h.twoWeylVectorPairing_sub, heq, sub_self]
  rw [sum_eq_zero_iff_of_nonneg fun k _ ↦ nsmul_nonneg (sub_nonneg.mpr (hle k)) 2] at hsum
  refine eq_of_forall_prefixSum_eq fun k ↦ ?_
  rcases le_or_gt k n with hk | hk
  · have h2 := hsum k (mem_range.mpr (Nat.lt_succ_of_le hk))
    rw [two_nsmul, add_eq_zero_iff_of_nonneg (sub_nonneg.mpr (hle k)) (sub_nonneg.mpr (hle k)),
      and_self, sub_eq_zero] at h2
    exact h2.symm
  · rw [prefixSum_of_le hk.le, prefixSum_of_le hk.le, (dominates_def.mp h).1]

/-- **`⟨2ρ, ·⟩` is strictly monotone for dominance**: a strict dominance `x ≼ y`, `x ≠ y`, gives
`⟨2ρ, x⟩ < ⟨2ρ, y⟩`. -/
theorem twoWeylVectorPairing_lt {x y : Fin n → M} (h : Dominates x y) (hne : x ≠ y) :
    twoWeylVectorPairing x < twoWeylVectorPairing y :=
  h.twoWeylVectorPairing_le.lt_of_ne fun heq ↦ hne (h.twoWeylVectorPairing_eq_iff.mp heq)

end TauCeti.Dominates
