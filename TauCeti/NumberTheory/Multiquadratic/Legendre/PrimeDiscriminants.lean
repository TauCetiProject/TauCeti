/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Basic
public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Even
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants

/-!
# Legendre symbols of prime discriminants

A prime discriminant `D` and its squarefree radicand `primeDiscriminantRadicand D`, both from
`TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants`, generate the same quadratic field
`ℚ(√D)`. Genus theory indexes quadratic characters by prime discriminants, while a multiquadratic
field is presented by square roots of radicands. This file shows that the two have the same
Legendre symbol at every odd prime, so quadratic-residue (splitting) conditions pass freely
between the two conventions, and gives one uniform residue criterion for a prime discriminant.

The prime-discriminant convention used here is the standard genus-theory convention appearing,
for example, in Cox's *Primes of the Form x² + ny²* and Lemmermeyer's *Reciprocity Laws*.

For odd prime discriminants there is nothing to change: the radicand is the discriminant
itself. For the even prime discriminants `-4`, `8`, and `-8`, the discriminant is four times
the radicand, so it has the same Legendre symbol at every odd prime. The uniform criterion
combines the reciprocity law for odd prime discriminants from
`TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Basic` with the supplementary
laws for even prime discriminants from
`TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Even`.

## Main results

* `TauCeti.Multiquadratic.legendreSym_eq_legendreSym_primeDiscriminantRadicand`:
  an integer and its associated prime-discriminant radicand have the same Legendre symbol at an
  odd prime.
* `TauCeti.Multiquadratic.forall_legendreSym_primeDiscriminant_eq_one_iff_radicand`:
  the indexed-family form, which passes a splitting condition from a family of prime
  discriminants to their radicands.
* `TauCeti.Multiquadratic.legendreSym_primeDiscriminant_eq_one_iff`:
  the uniform residue criterion for a prime discriminant.
* `TauCeti.Multiquadratic.legendreSym_primeDiscriminantRadicand_eq_one_iff`:
  the same criterion for the associated squarefree radicand.
-/

public section

namespace TauCeti.Multiquadratic

variable {q : ℕ} [Fact q.Prime]

/-- An integer `D` and its associated prime-discriminant radicand have the same Legendre symbol
at an odd prime `q`. Away from the three even prime discriminants this is just the radicand
definition; in the even-prime cases the two values differ by the square factor `4`. -/
theorem legendreSym_eq_legendreSym_primeDiscriminantRadicand (D : ℤ) (hq : q ≠ 2) :
    legendreSym q D = legendreSym q (primeDiscriminantRadicand D) := by
  rw [primeDiscriminantRadicand_def]
  by_cases hD : D = -4 ∨ D = 8 ∨ D = -8
  · rw [ite_eq_left hD]
    exact legendreSym_evenPrimeDiscriminant_eq_legendreSym_radicand hD hq
  · rw [ite_eq_right hD]

/-- Family form of
`legendreSym_eq_legendreSym_primeDiscriminantRadicand`: the condition that all integers in a
family are quadratic residues modulo an odd prime `q` is equivalent to the same condition on
their associated squarefree radicands. This is the conversion used before applying the
multiquadratic splitting law to genus-field prime discriminants. -/
theorem forall_legendreSym_primeDiscriminant_eq_one_iff_radicand {ι : Type*} (D : ι → ℤ)
    (hq : q ≠ 2) : (∀ i, legendreSym q (D i) = 1) ↔
      ∀ i, legendreSym q (primeDiscriminantRadicand (D i)) = 1 := by
  refine forall_congr' fun i => ?_
  rw [legendreSym_eq_legendreSym_primeDiscriminantRadicand (D i) hq]

/-- The uniform quadratic-residue criterion for a prime discriminant `D` at an odd prime `q`.
For the three even prime discriminants this is the corresponding supplementary congruence
condition on `q`; for an odd prime discriminant `p*` it is the reciprocal condition
`(q / p) = 1`. -/
theorem legendreSym_primeDiscriminant_eq_one_iff {D : ℤ} (hD : IsPrimeDiscriminant D) (hq : q ≠ 2) :
    legendreSym q D = 1 ↔
      (IsEvenPrimeDiscriminant D ∧
        (if D = -4 then q % 4 = 1
        else if D = 8 then q % 8 = 1 ∨ q % 8 = 7
        else q % 8 = 1 ∨ q % 8 = 3)) ∨
      ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧ D = oddPrimeDiscriminant p ∧
        @legendreSym p ⟨hp⟩ (q : ℤ) = 1 := by
  rcases isPrimeDiscriminant_iff.mp hD with hD | ⟨p, hp, hodd, rfl⟩
  · rw [legendreSym_evenPrimeDiscriminant_eq_one_iff hD hq]
    constructor
    · intro h
      exact Or.inl ⟨hD, h⟩
    · rintro (⟨_hD, h⟩ | ⟨p, _hp, hpodd, hDp, _hleg⟩)
      · exact h
      · exact False.elim <| not_isEvenPrimeDiscriminant_oddPrimeDiscriminant hpodd (hDp ▸ hD)
  · have : Fact p.Prime := ⟨hp⟩
    rw [legendreSym_oddPrimeDiscriminant_eq_one_iff
      (p := p) (q := q) (by
        intro hp2
        rcases hodd with ⟨k, hk⟩
        omega) hq]
    constructor
    · intro h
      exact Or.inr ⟨p, hp, hodd, rfl, h⟩
    · rintro (⟨hEven, _h⟩ | ⟨p', hp', hpodd', hDp', hleg⟩)
      · exact False.elim <| not_isEvenPrimeDiscriminant_oddPrimeDiscriminant hodd hEven
      · have hnatAbs : p = p' := by
          simpa [oddPrimeDiscriminant_natAbs] using congrArg Int.natAbs hDp'
        subst p'
        simpa using hleg

/-- The same uniform quadratic-residue criterion as
`legendreSym_primeDiscriminant_eq_one_iff`, stated for the associated squarefree radicand.
This is the form consumed after converting a genus-field prime-discriminant list into
multiquadratic radicands. -/
theorem legendreSym_primeDiscriminantRadicand_eq_one_iff {D : ℤ}
    (hD : IsPrimeDiscriminant D) (hq : q ≠ 2) :
    legendreSym q (primeDiscriminantRadicand D) = 1 ↔
      (IsEvenPrimeDiscriminant D ∧
        (if D = -4 then q % 4 = 1
        else if D = 8 then q % 8 = 1 ∨ q % 8 = 7
        else q % 8 = 1 ∨ q % 8 = 3)) ∨
      ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧ D = oddPrimeDiscriminant p ∧
        @legendreSym p ⟨hp⟩ (q : ℤ) = 1 := by
  rw [← legendreSym_eq_legendreSym_primeDiscriminantRadicand D hq]
  exact legendreSym_primeDiscriminant_eq_one_iff hD hq

/-- Indexed-family form of the uniform prime-discriminant residue criterion. -/
theorem forall_legendreSym_primeDiscriminant_eq_one_iff {ι : Type*} (D : ι → ℤ)
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hq : q ≠ 2) : (∀ i, legendreSym q (D i) = 1) ↔
      ∀ i,
        (IsEvenPrimeDiscriminant (D i) ∧
          (if D i = -4 then q % 4 = 1
          else if D i = 8 then q % 8 = 1 ∨ q % 8 = 7
          else q % 8 = 1 ∨ q % 8 = 3)) ∨
        ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧ D i = oddPrimeDiscriminant p ∧
          @legendreSym p ⟨hp⟩ (q : ℤ) = 1 := by
  refine forall_congr' fun i => ?_
  exact legendreSym_primeDiscriminant_eq_one_iff (hD i) hq

end TauCeti.Multiquadratic
