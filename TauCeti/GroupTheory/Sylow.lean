/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow

/-!
# Sylow subgroups of prime order

When a prime `p` divides the order of a finite group exactly once, its Sylow `p`-subgroups have
order `p`. This is the form in which Sylow's theorems are applied to groups such as `S₅`, whose
order `120` is divisible by `5` but not by `25`, and to their subgroups.

## Main results

* `Sylow.card_eq_of_dvd_of_not_sq_dvd`: a Sylow `p`-subgroup has order `p` when `p` divides the
  order of the group but `p ^ 2` does not.
-/

public section

namespace Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

/-- A Sylow `p`-subgroup has order `p` when `p` divides the order of the group exactly once. -/
theorem card_eq_of_dvd_of_not_sq_dvd (P : Sylow p G) (hdvd : p ∣ Nat.card G)
    (hsq : ¬ p ^ 2 ∣ Nat.card G) : Nat.card P = p := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have h1 : p ∣ p ^ n := hn ▸ P.dvd_card_of_dvd_card hdvd
  have h2 : p ^ n ∣ Nat.card G := hn ▸ P.1.card_subgroup_dvd_card
  rcases n with _ | _ | n
  · exact absurd (Nat.le_of_dvd one_pos (by simpa using h1)) hp.out.one_lt.not_ge
  · simpa using hn
  · exact absurd ((pow_dvd_pow p (by omega : 2 ≤ n + 2)).trans h2) hsq

end Sylow
