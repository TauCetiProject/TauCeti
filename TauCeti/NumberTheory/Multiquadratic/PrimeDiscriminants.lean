/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.NumberTheory.Multiquadratic.EvenPrimeDiscriminant
import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminant
import TauCeti.NumberTheory.Multiquadratic.Squarefree
import Mathlib.Data.Rat.Lemmas

/-!
# Prime discriminants

The genus-field layer of the multiquadratic roadmap uses the **prime discriminants**
`-4`, `8`, `-8`, and `p* = (-1)^((p - 1) / 2) p` for odd primes `p`. The files
`PrimeDiscriminant` and `EvenPrimeDiscriminant` develop the odd and 2-adic pieces separately;
this file packages them into one predicate and one radicand map for later genus-field
constructions.

For an odd prime discriminant the radicand is the discriminant itself. For an even prime
discriminant `D ∈ {-4, 8, -8}`, the radicand is `D / 4`, so the three even cases give
`-1`, `2`, and `-2`.

## Main definitions and results

* `TauCeti.Multiquadratic.IsPrimeDiscriminant`: the union of the even prime discriminants and
  odd prime discriminants.
* `TauCeti.Multiquadratic.primeDiscriminantRadicand`: the associated squarefree integer
  radicand.
* `TauCeti.Multiquadratic.squarefree_primeDiscriminantRadicand`: the associated radicand is
  squarefree.
* `TauCeti.Multiquadratic.not_isSquare_primeDiscriminantRadicand_rat`: the associated rational
  radicand is not a square.
-/

namespace TauCeti.Multiquadratic

/-- The prime discriminants: the even prime discriminants `-4`, `8`, `-8`, together with
the odd prime discriminants `p*` for odd natural primes `p`. -/
def IsPrimeDiscriminant (D : ℤ) : Prop :=
  IsEvenPrimeDiscriminant D ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ D = oddPrimeDiscriminant p

/-- The defining disjunction for `IsPrimeDiscriminant`. -/
theorem isPrimeDiscriminant_iff {D : ℤ} :
    IsPrimeDiscriminant D ↔
      IsEvenPrimeDiscriminant D ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ D = oddPrimeDiscriminant p :=
  Iff.rfl

/-- Every even prime discriminant is a prime discriminant. -/
theorem IsEvenPrimeDiscriminant.isPrimeDiscriminant {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) :
    IsPrimeDiscriminant D :=
  Or.inl hD

/-- The discriminant `-4` is a prime discriminant. -/
@[simp] theorem isPrimeDiscriminant_neg_four :
    IsPrimeDiscriminant (-4) :=
  isEvenPrimeDiscriminant_neg_four.isPrimeDiscriminant

/-- The discriminant `8` is a prime discriminant. -/
@[simp] theorem isPrimeDiscriminant_eight :
    IsPrimeDiscriminant 8 :=
  isEvenPrimeDiscriminant_eight.isPrimeDiscriminant

/-- The discriminant `-8` is a prime discriminant. -/
@[simp] theorem isPrimeDiscriminant_neg_eight :
    IsPrimeDiscriminant (-8) :=
  isEvenPrimeDiscriminant_neg_eight.isPrimeDiscriminant

/-- The odd prime discriminant attached to an odd natural prime is a prime discriminant. -/
theorem isPrimeDiscriminant_oddPrimeDiscriminant {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    IsPrimeDiscriminant (oddPrimeDiscriminant p) :=
  Or.inr ⟨p, hp, hodd, rfl⟩

/-- An odd prime discriminant is not one of the even prime discriminants. -/
theorem not_isEvenPrimeDiscriminant_oddPrimeDiscriminant {p : ℕ}
    (hodd : Odd p) :
    ¬ IsEvenPrimeDiscriminant (oddPrimeDiscriminant p) := by
  intro hD
  have hp_ne_four : p ≠ 4 := by
    intro hp4
    have hodd4 : Odd 4 := hp4 ▸ hodd
    rcases hodd4 with ⟨k, hk⟩
    omega
  have hp_ne_eight : p ≠ 8 := by
    intro hp8
    have hodd8 : Odd 8 := hp8 ▸ hodd
    rcases hodd8 with ⟨k, hk⟩
    omega
  rcases hD with hD | hD | hD
  · have hnat : p = 4 := by
      simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs hD
    exact hp_ne_four hnat
  · have hnat : p = 8 := by
      simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs hD
    exact hp_ne_eight hnat
  · have hnat : p = 8 := by
      simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs hD
    exact hp_ne_eight hnat

/-- The squarefree radicand attached to a prime discriminant. In the even cases this divides by
`4`; in the odd cases the discriminant is already squarefree and is used as its own radicand. -/
def primeDiscriminantRadicand (D : ℤ) : ℤ :=
  if D = -4 ∨ D = 8 ∨ D = -8 then evenPrimeDiscriminantRadicand D else D

/-- The defining equation for the prime-discriminant radicand. -/
theorem primeDiscriminantRadicand_def (D : ℤ) :
    primeDiscriminantRadicand D =
      if D = -4 ∨ D = 8 ∨ D = -8 then evenPrimeDiscriminantRadicand D else D :=
  rfl

/-- The prime-discriminant radicand of `-4` is `-1`. -/
@[simp] theorem primeDiscriminantRadicand_neg_four :
    primeDiscriminantRadicand (-4) = -1 := by
  simp [primeDiscriminantRadicand]

/-- The prime-discriminant radicand of `8` is `2`. -/
@[simp] theorem primeDiscriminantRadicand_eight :
    primeDiscriminantRadicand 8 = 2 := by
  simp [primeDiscriminantRadicand]

/-- The prime-discriminant radicand of `-8` is `-2`. -/
@[simp] theorem primeDiscriminantRadicand_neg_eight :
    primeDiscriminantRadicand (-8) = -2 := by
  simp [primeDiscriminantRadicand]

/-- The radicand attached to an even prime discriminant is its even-prime radicand. -/
@[simp]
theorem primeDiscriminantRadicand_of_isEvenPrimeDiscriminant {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) :
    primeDiscriminantRadicand D = evenPrimeDiscriminantRadicand D := by
  rcases hD with rfl | rfl | rfl <;> simp [primeDiscriminantRadicand]

/-- The radicand attached to an odd prime discriminant is the discriminant itself. -/
@[simp]
theorem primeDiscriminantRadicand_oddPrimeDiscriminant {p : ℕ}
    (hodd : Odd p) :
    primeDiscriminantRadicand (oddPrimeDiscriminant p) = oddPrimeDiscriminant p := by
  have hnot : ¬ (oddPrimeDiscriminant p = -4 ∨
      oddPrimeDiscriminant p = 8 ∨ oddPrimeDiscriminant p = -8) := by
    simpa [IsEvenPrimeDiscriminant] using not_isEvenPrimeDiscriminant_oddPrimeDiscriminant hodd
  simp [primeDiscriminantRadicand, hnot]

/-- A prime discriminant is either its own radicand, or four times its radicand in the even
cases. -/
theorem primeDiscriminant_eq_radicand_or_eq_four_mul_radicand {D : ℤ}
    (hD : IsPrimeDiscriminant D) :
    D = primeDiscriminantRadicand D ∨ D = 4 * primeDiscriminantRadicand D := by
  rcases hD with hD | ⟨p, _hp, hodd, rfl⟩
  · exact Or.inr <| by
      rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
      exact evenPrimeDiscriminant_eq_four_mul_radicand hD
  · exact Or.inl <| by rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]

/-- The radicand attached to a prime discriminant is nonzero. -/
theorem primeDiscriminantRadicand_ne_zero {D : ℤ}
    (hD : IsPrimeDiscriminant D) :
    primeDiscriminantRadicand D ≠ 0 := by
  rcases hD with hD | ⟨p, hp, hodd, rfl⟩
  · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
    exact evenPrimeDiscriminantRadicand_ne_zero hD
  · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
    exact (oddPrimeDiscriminant_ne_zero).2 hp.ne_zero

/-- The radicand attached to a prime discriminant is squarefree. -/
theorem squarefree_primeDiscriminantRadicand {D : ℤ}
    (hD : IsPrimeDiscriminant D) :
    Squarefree (primeDiscriminantRadicand D) := by
  rcases hD with hD | ⟨p, hp, hodd, rfl⟩
  · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
    exact squarefree_evenPrimeDiscriminantRadicand hD
  · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
    exact squarefree_oddPrimeDiscriminant hp.squarefree

/-- The radicand attached to a prime discriminant is not a rational square. -/
theorem not_isSquare_primeDiscriminantRadicand_rat {D : ℤ}
    (hD : IsPrimeDiscriminant D) :
    ¬ IsSquare ((primeDiscriminantRadicand D : ℤ) : ℚ) := by
  rcases hD with hD | ⟨p, hp, hodd, rfl⟩
  · rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
    exact not_isSquare_evenPrimeDiscriminantRadicand_rat hD
  · rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
    rw [Rat.isSquare_intCast_iff]
    exact not_isSquare_of_squarefree_of_not_isUnit (squarefree_oddPrimeDiscriminant hp.squarefree)
      (by
        rw [Int.isUnit_iff_natAbs_eq]
        simpa [oddPrimeDiscriminant_natAbs] using hp.ne_one)

/-- An odd prime discriminant has odd radicand congruent to `1` modulo `4`. -/
theorem primeDiscriminantRadicand_mod_four_eq_one_of_odd {p : ℕ}
    (hodd : Odd p) :
    primeDiscriminantRadicand (oddPrimeDiscriminant p) % 4 = 1 := by
  rw [primeDiscriminantRadicand_oddPrimeDiscriminant hodd]
  exact oddPrimeDiscriminant_mod_four_eq_one hodd

/-- An even prime discriminant has radicand congruent to `3` or `2` modulo `4`. -/
theorem primeDiscriminantRadicand_mod_four_eq_three_or_two_of_even {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) :
    primeDiscriminantRadicand D % 4 = 3 ∨ primeDiscriminantRadicand D % 4 = 2 := by
  rw [primeDiscriminantRadicand_of_isEvenPrimeDiscriminant hD]
  exact evenPrimeDiscriminantRadicand_mod_four_eq_three_or_two hD

/-- A prime discriminant is either even, or its associated radicand is congruent to `1`
modulo `4`. -/
theorem isEvenPrimeDiscriminant_or_primeDiscriminantRadicand_mod_four_eq_one {D : ℤ}
    (hD : IsPrimeDiscriminant D) :
    IsEvenPrimeDiscriminant D ∨ primeDiscriminantRadicand D % 4 = 1 := by
  rcases hD with hD | ⟨p, hp, hodd, rfl⟩
  · exact Or.inl hD
  · exact Or.inr (primeDiscriminantRadicand_mod_four_eq_one_of_odd hodd)

end TauCeti.Multiquadratic
