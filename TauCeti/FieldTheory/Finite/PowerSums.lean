/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.FieldTheory.Finite.Trace

/-!
# Power sums over finite fields

Let `F` be a finite field with `q` elements. Mathlib computes `∑ x, x ^ m = 0` for `m < q - 1`
(`FiniteField.sum_pow_lt_card_sub_one`) and the sums of powers over the units
(`FiniteField.sum_pow_units`). This file extends the first to `0 < m < 2 (q - 1)`, where the sum
is `-1` at `m = q - 1` and `0` otherwise, and deduces two sums used for Jacobi and Gauss sums.

## Main results

* `TauCeti.FiniteField.sum_pow_of_pos_of_lt`: `∑ x, x ^ m = if m = q - 1 then -1 else 0` for
  `0 < m < 2 (q - 1)`.
* `TauCeti.FiniteField.sum_pow_mul_one_sub_pow`: `∑ y, y ^ (q - 2) (1 - y) ^ n = n` for
  `n ≤ q - 1`.
* `TauCeti.FiniteField.sum_pow_mul_trace`: `∑ x, x ^ (q - 2) Tr(x) = -1`, where `Tr` is the trace
  to the prime field `𝔽_p` and `x ^ (q - 2) = x⁻¹`.
-/

public section

open Finset

namespace TauCeti

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F]

/-- The power sums `∑ x, x ^ m` of a finite field of cardinality `q`, for `0 < m < 2 (q - 1)`. -/
theorem sum_pow_of_pos_of_lt {m : ℕ} (hm : 0 < m) (hm' : m < 2 * (Fintype.card F - 1)) :
    ∑ x : F, x ^ m = if m = Fintype.card F - 1 then -1 else 0 := by
  classical
  have hsum : ∑ x : F, x ^ m = ∑ x : Fˣ, (x : F) ^ m := by
    let ι : Fˣ ↪ F := ⟨(↑), Units.val_injective⟩
    refine Eq.trans ?_ (Finset.sum_map univ ι (· ^ m))
    refine (Finset.sum_subset (subset_univ _) fun x _ hx ↦ ?_).symm
    have : x = 0 := by
      by_contra h
      exact hx (mem_map.2 ⟨Units.mk0 x h, mem_univ _, rfl⟩)
    simp [this, hm.ne']
  rw [hsum, _root_.FiniteField.sum_pow_units]
  congr 1
  refine propext ⟨fun ⟨k, hk⟩ ↦ ?_, fun h ↦ h ▸ dvd_rfl⟩
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · omega
    · rfl
    · nlinarith
  rw [hk, hk1, mul_one]

/-- The finite-field sum `∑ y, y ^ (q - 2) (1 - y) ^ n` equals `n` for `n ≤ q - 1`. -/
theorem sum_pow_mul_one_sub_pow (hq : 2 < Fintype.card F) {n : ℕ}
    (hn : n ≤ Fintype.card F - 1) :
    ∑ y : F, y ^ (Fintype.card F - 2) * (1 - y) ^ n = n := by
  have h : ∀ y : F, y ^ (Fintype.card F - 2) * (1 - y) ^ n =
      ∑ m ∈ range (n + 1), (-1) ^ m * (n.choose m : F) * y ^ (Fintype.card F - 2 + m) := by
    intro y
    rw [sub_eq_neg_add, add_pow, mul_sum]
    refine sum_congr rfl fun m _ ↦ ?_
    rw [neg_pow, one_pow, pow_add]
    ring
  simp_rw [h]
  rw [sum_comm]
  simp_rw [← mul_sum]
  rw [sum_eq_single 1]
  · rw [sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_left (by omega)]
    simp
  · intro m hm hm1
    rw [mem_range] at hm
    rw [sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_right (by omega), mul_zero]
  · intro h1
    rw [mem_range, not_lt] at h1
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `∑ x, x⁻¹ Tr(x) = -1` for the trace `Tr` to the prime field, with `x⁻¹` written
`x ^ (q - 2)`. -/
theorem sum_pow_mul_trace {p : ℕ} [hp : Fact p.Prime] [Algebra (ZMod p) F]
    (hq : 2 < Fintype.card F) :
    ∑ x : F, x ^ (Fintype.card F - 2) * algebraMap (ZMod p) F (Algebra.trace (ZMod p) F x) =
      -1 := by
  have hcard : Fintype.card F = p ^ Module.finrank (ZMod p) F := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hn : 0 < Module.finrank (ZMod p) F := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) F) with h | h
    · rw [h, pow_zero] at hcard; omega
    · exact h
  simp_rw [_root_.FiniteField.algebraMap_trace_eq_sum_pow, Nat.card_zmod, mul_sum, ← pow_add]
  rw [sum_comm, sum_eq_single_of_mem 0 (mem_range.2 hn)]
  · rw [pow_zero, sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_left (by omega)]
  · intro i hi hi0
    have hlt : p ^ i < Fintype.card F := hcard ▸ Nat.pow_lt_pow_right hp.out.one_lt (mem_range.1 hi)
    have hge : 2 ≤ p ^ i := le_trans hp.out.two_le (Nat.le_self_pow hi0 p)
    rw [sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_right (by omega)]

end FiniteField

end TauCeti
