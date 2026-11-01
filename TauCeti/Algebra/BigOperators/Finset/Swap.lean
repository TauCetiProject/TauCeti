/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Abel

/-!
# Summing after transposing two indices

`TauCeti.sum_swap_apply_add` compares `∑ k ∈ s, F k (Equiv.swap x y k)` with `∑ k ∈ s, F k k`:
away from `x` and `y` the two sums agree termwise, so they differ only in that the terms `F x x`
and `F y y` are replaced by `F x y` and `F y x`. The comparison is stated by adding the two
exchanged pairs to the two sides rather than by subtracting them, so that it holds in a monoid
without subtraction -- in particular over `ℕ`, where a weighted sum `∑ k ∈ s, f k * g k` is a
convenient numerical measure of an arrangement of labels.
-/

public section

namespace TauCeti

/-- **Transposing two indices of a sum trades two diagonal terms for off-diagonal ones.** Every
term other than those at `x` and `y` is unchanged, so adding `F x x + F y y` to the transposed sum
gives the original sum with `F x y + F y x` added. -/
theorem sum_swap_apply_add {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] (F : ι → ι → M)
    {s : Finset ι} {x y : ι} (hx : x ∈ s) (hy : y ∈ s) :
    (∑ k ∈ s, F k (Equiv.swap x y k)) + (F x x + F y y) =
      (∑ k ∈ s, F k k) + (F x y + F y x) := by
  obtain rfl | hne := eq_or_ne x y
  · simp
  have hy' : y ∈ s.erase x := Finset.mem_erase.2 ⟨hne.symm, hy⟩
  -- Split off the terms at `x` and `y`, for an arbitrary summand.
  have split (G : ι → M) : ∑ k ∈ s, G k = G x + (G y + ∑ k ∈ (s.erase x).erase y, G k) := by
    rw [Finset.add_sum_erase _ _ hy', Finset.add_sum_erase _ _ hx]
  -- Away from `x` and `y` the transposition acts trivially.
  have rest : ∑ k ∈ (s.erase x).erase y, F k (Equiv.swap x y k) =
      ∑ k ∈ (s.erase x).erase y, F k k :=
    Finset.sum_congr rfl fun k hk => by
      rw [Equiv.swap_apply_of_ne_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk))
        (Finset.ne_of_mem_erase hk)]
  rw [split fun k => F k (Equiv.swap x y k), split fun k => F k k, rest,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  abel

end TauCeti
