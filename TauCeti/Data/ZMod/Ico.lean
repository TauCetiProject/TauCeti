/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The nonzero residues `1, …, n - 1`

The natural numbers `k ∈ Ico 1 n` cast to nonzero residues in `ZMod n`. For a prime `p` these
residues are exactly the units of `ZMod p`, so a sum over `k ∈ Ico 1 p` of a function of the
residue `(k : ZMod p)` is the sum over `(ZMod p)ˣ`. This reindexing turns the
classical sums `∑_{k=1}^{p-1} f(k)` modulo `p` into sums over the multiplicative group of `𝔽_p`.

## Main results

* `ZMod.natCast_ne_zero_of_mem_Ico`: `(k : ZMod n) ≠ 0` for `k ∈ Ico 1 n`.
* `ZMod.sum_val_erase_zero_eq_sum_Ico`: sums over the nonzero representatives in `Ico 1 n`.
* `ZMod.sum_Ico_one_natCast_eq_sum_units`: `∑ k ∈ Ico 1 p, f k = ∑ u : (ZMod p)ˣ, f u`.
-/

public section

open Finset

namespace ZMod

/-- The residues `1, …, n - 1` are nonzero in `ZMod n`. -/
theorem natCast_ne_zero_of_mem_Ico {n k : ℕ} (hk : k ∈ Ico 1 n) : (k : ZMod n) ≠ 0 := by
  rw [mem_Ico] at hk
  rw [Ne, natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hk.1 hk.2

/-- Summing a function of the nonzero representatives modulo `n` gives its sum over
`1, …, n - 1`. -/
theorem sum_val_erase_zero_eq_sum_Ico {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) : ∑ k ∈ univ.erase (0 : ZMod n), f k.val = ∑ k ∈ Ico 1 n, f k := by
  refine sum_bij' (fun k _ ↦ k.val) (fun j _ ↦ (j : ZMod n)) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · exact fun k hk ↦ mem_Ico.mpr ⟨val_pos.mpr (mem_erase.mp hk).1, val_lt k⟩
  · exact fun j hj ↦ mem_erase.mpr ⟨natCast_ne_zero_of_mem_Ico hj, mem_univ _⟩
  · exact fun k _ ↦ natCast_zmod_val k
  · exact fun j hj ↦ (val_natCast n j).trans (Nat.mod_eq_of_lt (mem_Ico.mp hj).2)

/-- A sum over the residues `1, …, p - 1` is a sum over the units of `ZMod p`. -/
theorem sum_Ico_one_natCast_eq_sum_units {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (f : ZMod p → M) : ∑ k ∈ Ico 1 p, f k = ∑ u : (ZMod p)ˣ, f u :=
  sum_bij' (fun k hk ↦ Units.mk0 (k : ZMod p) (natCast_ne_zero_of_mem_Ico hk))
    (fun u _ ↦ (u : ZMod p).val) (fun _ _ ↦ mem_univ _)
    (fun u _ ↦ mem_Ico.2 ⟨Nat.pos_of_ne_zero ((val_ne_zero _).2 u.ne_zero), val_lt _⟩)
    (fun k hk ↦ by simp [val_natCast, Nat.mod_eq_of_lt (mem_Ico.1 hk).2])
    (fun u _ ↦ Units.ext (natCast_zmod_val _)) fun _ _ ↦ rfl

end ZMod
