/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index

/-!
# Sylow subgroups of prime order

When a prime `p` divides the order of a finite group exactly once, its Sylow `p`-subgroups have
order `p`. This is the form in which Sylow's theorems are applied to groups such as `S₅`, whose
order `120` is divisible by `5` but not by `25`, and to their subgroups.

The file also records the divisibility consequence of having six Sylow `5`-subgroups.

## Main results

* `Sylow.card_eq_of_dvd_of_not_sq_dvd`: a Sylow `p`-subgroup has order `p` when `p` divides the
  order of the group but `p ^ 2` does not.
* `TauCeti.thirty_dvd_natCard_of_card_sylow_five_eq_six`: a finite group with order divisible by
  `5` and six Sylow `5`-subgroups has order divisible by `30`.
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

namespace TauCeti

private local instance sylowFiveFactPrimeFiveDivisibility : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- A finite group of order divisible by `5` with six Sylow `5`-subgroups has order divisible by
`30`. -/
theorem thirty_dvd_natCard_of_card_sylow_five_eq_six {G : Type*} [Group G] [Finite G]
    (h5 : 5 ∣ Nat.card G) (h6 : Nat.card (Sylow 5 G) = 6) : 30 ∣ Nat.card G := by
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have h6G : 6 ∣ Nat.card G := h6 ▸ P.card_eq_index_normalizer ▸ Subgroup.index_dvd_card _
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h6G

end TauCeti
