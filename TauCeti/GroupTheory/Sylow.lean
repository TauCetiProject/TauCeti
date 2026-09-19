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
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h1 := (hp.out.dvd_iff_one_le_factorization hG).1 hdvd
  have h2 := mt (hp.out.pow_dvd_iff_le_factorization (k := 2) hG).2 hsq
  rw [P.card_eq_multiplicity, show (Nat.card G).factorization p = 1 by omega, pow_one]

end Sylow
