/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Layer-cake counting for families of natural numbers

For a family `k` of natural numbers indexed by a finite set `s`, slice the values at every level
`j` and count the indices above it, `Nⱼ = #{i ∈ s | j < kᵢ}`. Each index is counted once at every
level below its value, so `∑ⱼ Nⱼ = ∑ᵢ kᵢ`, and each pair of indices is counted together at every
level below both values, so `∑ⱼ Nⱼ² = ∑_{i, i'} min kᵢ k_{i'}`.

Combining the two gives the exponent identity behind the Conway–Sloane form of the local density
of a diagonal Jordan form `diag(uᵢ pᵏⁱ)` at an odd prime: the exponent
`∑ⱼ binom(Nⱼ + 1, 2)` of the density, doubled, plus the exponent `∑_{i, i'} (k_{i'} - kᵢ)⁺` of the
cross terms of the `p`-mass, is `(n + 1) ∑ kᵢ`.

## Main results

* `Finset.sum_range_card_filter_lt`: `∑_{j < K} #{i ∈ s | j < kᵢ} = ∑_{i ∈ s} kᵢ` when every `kᵢ`
  is at most `K`.
* `Finset.sum_range_card_filter_lt_mul_self`: `∑_{j < K} #{i ∈ s | j < kᵢ}² = ∑_{i, i' ∈ s}
  min kᵢ k_{i'}` under the same bound.
* `Finset.two_mul_sum_range_choose_add_sum_sum_tsub`:
  `2 ∑_{j < max k} binom(Nⱼ + 1, 2) + ∑_{i, i'} (k_{i'} - kᵢ) = (#s + 1) ∑ kᵢ`.
-/

public section

namespace Finset

variable {ι : Type*} (s : Finset ι) (k : ι → ℕ)

/-- **Layer-cake counting.** If every `kᵢ` with `i ∈ s` is at most `K`, then counting at each level
`j < K` the indices with `j < kᵢ` gives `∑_{i ∈ s} kᵢ`. -/
theorem sum_range_card_filter_lt {K : ℕ} (hK : ∀ i ∈ s, k i ≤ K) :
    ∑ j ∈ range K, #{i ∈ s | j < k i} = ∑ i ∈ s, k i := by
  simp_rw [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← card_filter, show {j ∈ range K | j < k i} = range (k i) by
    ext j; simp only [mem_filter, mem_range]; have := hK i hi; omega, card_range]

/-- **Layer-cake counting for pairs.** If every `kᵢ` with `i ∈ s` is at most `K`, then the sum
over the levels `j < K` of the squared number of indices with `j < kᵢ` is
`∑_{i, i' ∈ s} min kᵢ k_{i'}`. -/
theorem sum_range_card_filter_lt_mul_self {K : ℕ} (hK : ∀ i ∈ s, k i ≤ K) :
    ∑ j ∈ range K, #{i ∈ s | j < k i} * #{i ∈ s | j < k i} =
      ∑ i ∈ s, ∑ i' ∈ s, min (k i) (k i') := by
  simp_rw [card_filter, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  refine sum_congr rfl fun i' _ => ?_
  have hrange : {j ∈ range K | j < min (k i) (k i')} = range (min (k i) (k i')) := by
    ext j; simp only [mem_filter, mem_range]; have := hK i hi; omega
  rw [← card_range (min (k i) (k i')), ← hrange, card_filter]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> omega

/-- **The Conway–Sloane exponent identity.** Twice `∑_{j < max k} binom(Nⱼ + 1, 2)`, where
`Nⱼ = #{i ∈ s | j < kᵢ}`, plus `∑_{i, i' ∈ s} (k_{i'} - kᵢ)` (truncated subtraction) is
`(#s + 1) ∑_{i ∈ s} kᵢ`. The first sum is the exponent of `p` in the local density of the
diagonal Jordan form `diag(uᵢ pᵏⁱ)` at an odd prime, the second is the exponent of `√p` in the
cross terms of its Conway–Sloane `p`-mass. -/
theorem two_mul_sum_range_choose_add_sum_sum_tsub :
    2 * ∑ j ∈ range (s.sup k), (#{i ∈ s | j < k i} + 1).choose 2 +
        ∑ i ∈ s, ∑ i' ∈ s, (k i' - k i) =
      (#s + 1) * ∑ i ∈ s, k i := by
  have hK (i : ι) (hi : i ∈ s) : k i ≤ s.sup k := le_sup hi
  have hchoose (N : ℕ) : 2 * (N + 1).choose 2 = N * N + N := by
    have h := Nat.add_one_mul_choose_eq N 1
    rw [Nat.choose_one_right] at h
    linarith
  calc 2 * ∑ j ∈ range (s.sup k), (#{i ∈ s | j < k i} + 1).choose 2 +
        ∑ i ∈ s, ∑ i' ∈ s, (k i' - k i)
      = ∑ i ∈ s, ∑ i' ∈ s, (min (k i) (k i') + (k i' - k i)) + ∑ i ∈ s, k i := by
        simp_rw [mul_sum, hchoose, sum_add_distrib, sum_range_card_filter_lt s k hK,
          sum_range_card_filter_lt_mul_self s k hK]
        ring
    _ = (#s + 1) * ∑ i ∈ s, k i := by
        rw [sum_comm]
        simp_rw [show ∀ i i', min (k i) (k i') + (k i' - k i) = k i' from fun i i' => by omega]
        simp [sum_const, add_mul, mul_sum, sum_add_distrib]

end Finset
