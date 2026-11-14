/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq

/-!
# Reindexing products and sums of residues

Multiplication by a unit modulo `n` permutes `0, …, n - 1`.
-/

public section

namespace Nat

/-- Multiplication by `a` coprime to `n` permutes the residues `0, …, n - 1`, so a product over
them may be reindexed by `r ↦ a r mod n`. -/
@[to_additive Nat.Coprime.sum_range_mul_mod /-- Multiplication by `a` coprime to `n` permutes the
residues `0, …, n - 1`, so a sum over them may be reindexed by `r ↦ a r mod n`. -/]
theorem Coprime.prod_range_mul_mod {M : Type*} [CommMonoid M] {a n : ℕ} (han : a.Coprime n)
    (f : ℕ → M) : ∏ r ∈ Finset.range n, f (a * r % n) = ∏ r ∈ Finset.range n, f r := by
  have hinj : Set.InjOn (fun r ↦ a * r % n) (Finset.range n) := fun x hx y hy hxy ↦
    (ModEq.cancel_left_of_coprime (by rwa [Nat.gcd_comm]) hxy).eq_of_lt_of_lt
      (Finset.mem_range.1 hx) (Finset.mem_range.1 hy)
  have himage : (Finset.range n).image (fun r ↦ a * r % n) = Finset.range n := by
    refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_) (Finset.card_image_of_injOn hinj).ge
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2
      (mod_lt _ (Nat.pos_of_ne_zero (Finset.nonempty_range_iff.1 ⟨r, hr⟩)))
  rw [← Finset.prod_image hinj, himage]

end Nat
