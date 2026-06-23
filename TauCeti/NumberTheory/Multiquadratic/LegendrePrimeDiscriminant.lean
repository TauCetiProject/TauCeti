/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminant
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Legendre symbols of odd prime discriminants

The genus-field layer of the multiquadratic roadmap uses the odd prime discriminant
`p* = (-1)^((p-1)/2) p` rather than the bare prime radicand `p`. This file records the
small Legendre-symbol API that makes that normalization usable in the prime-splitting law.

For odd primes `p` and `q`, the classical identity `(p* / q) = (q / p)` is exactly
`legendreSym q (oddPrimeDiscriminant p) = legendreSym p q`. The proof is only quadratic
reciprocity plus the supplementary law for `-1`; this file packages that result in the
shape downstream multiquadratic splitting statements need.

## Main results

* `TauCeti.Multiquadratic.legendreSym_oddPrimeDiscriminant` expands the Legendre symbol of
  `p*` at an arbitrary prime `q`.
* `TauCeti.Multiquadratic.legendreSym_oddPrimeDiscriminant_eq_symm` proves
  `(p* / q) = (q / p)` for odd primes.
* `TauCeti.Multiquadratic.legendreSym_oddPrimeDiscriminant_eq_one_iff` rewrites the
  quadratic-residue condition for an odd prime discriminant into the reciprocal symbol.
* `TauCeti.Multiquadratic.forall_legendreSym_oddPrimeDiscriminant_eq_one_iff` is the
  indexed-family form used by the multiquadratic splitting law.
-/

namespace TauCeti.Multiquadratic

open ZMod

variable {p q : ℕ}

/-- Expanding the Legendre symbol of the odd prime discriminant `p*`. This version does not
assume `q` is odd: in the negative case it leaves the factor `legendreSym q (-1)` explicit. -/
theorem legendreSym_oddPrimeDiscriminant (p q : ℕ) [Fact q.Prime] :
    legendreSym q (oddPrimeDiscriminant p) =
      if p % 4 = 1 then legendreSym q (p : ℤ)
      else legendreSym q (-1) * legendreSym q (p : ℤ) := by
  by_cases hp : p % 4 = 1
  · simp [hp]
  · rw [oddPrimeDiscriminant_of_mod_four_ne_one hp]
    rw [if_neg hp, neg_eq_neg_one_mul, legendreSym.mul]

/-- Expanding the Legendre symbol of `p*` at an odd prime `q`, using the supplementary law
`legendreSym q (-1) = χ₄ q`. -/
theorem legendreSym_oddPrimeDiscriminant_of_ne_two (p q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    legendreSym q (oddPrimeDiscriminant p) =
      if p % 4 = 1 then legendreSym q (p : ℤ)
      else χ₄ q * legendreSym q (p : ℤ) := by
  rw [legendreSym_oddPrimeDiscriminant, legendreSym.at_neg_one hq]

/-- For odd primes `p` and `q`, the Legendre symbol of the odd prime discriminant `p*` at
`q` is the reciprocal symbol `(q / p)`. This is the prime-discriminant form of quadratic
reciprocity used by genus-field splitting criteria. -/
theorem legendreSym_oddPrimeDiscriminant_eq_symm [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q (oddPrimeDiscriminant p) = legendreSym p (q : ℤ) := by
  have hpodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out : p.Prime)).resolve_left hp
  rcases Nat.odd_mod_four_iff.mp hpodd with hp1 | hp3
  · rw [oddPrimeDiscriminant_of_mod_four_eq_one hp1]
    exact legendreSym.quadratic_reciprocity_one_mod_four hp1 hq
  · rw [oddPrimeDiscriminant_of_mod_four_eq_three hp3, legendreSym.at_neg hq]
    have hqodd : q % 2 = 1 := (Nat.Prime.eq_two_or_odd (Fact.out : q.Prime)).resolve_left hq
    rcases Nat.odd_mod_four_iff.mp hqodd with hq1 | hq3
    · rw [χ₄_nat_one_mod_four hq1, one_mul]
      exact (legendreSym.quadratic_reciprocity_one_mod_four hq1 hp).symm
    · rw [χ₄_nat_three_mod_four hq3, neg_one_mul,
        legendreSym.quadratic_reciprocity_three_mod_four hp3 hq3, neg_neg]

/-- The quadratic-residue condition for the odd prime discriminant `p*` can be read as the
reciprocal Legendre symbol `(q / p) = 1`. This is the form consumed by the multiquadratic
prime-splitting law after the genus-field radicands have been normalized to prime
discriminants. -/
theorem legendreSym_oddPrimeDiscriminant_eq_one_iff [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q (oddPrimeDiscriminant p) = 1 ↔ legendreSym p (q : ℤ) = 1 := by
  rw [legendreSym_oddPrimeDiscriminant_eq_symm hp hq]

/-- An odd prime discriminant is divisible by `q` exactly when the underlying prime `p` is.
This form is convenient when checking the unramifiedness side of the splitting law. -/
theorem dvd_oddPrimeDiscriminant_iff {p q : ℕ} :
    (q : ℤ) ∣ oddPrimeDiscriminant p ↔ (q : ℤ) ∣ (p : ℤ) := by
  by_cases hp : p % 4 = 1
  · rw [oddPrimeDiscriminant_of_mod_four_eq_one hp]
  · rw [oddPrimeDiscriminant_of_mod_four_ne_one hp, Int.dvd_neg]

/-- An odd prime discriminant is not divisible by `q` exactly when the underlying prime `p`
is not.
The negated form is convenient for the unramifiedness side of the splitting law. -/
@[simp] theorem not_dvd_oddPrimeDiscriminant_iff {p q : ℕ} :
    ¬ (q : ℤ) ∣ oddPrimeDiscriminant p ↔ ¬ (q : ℤ) ∣ (p : ℤ) := by
  exact not_congr dvd_oddPrimeDiscriminant_iff

/-- Family form of `legendreSym_oddPrimeDiscriminant_eq_one_iff`: for a family of odd primes
`p i`, the conditions that all odd prime discriminants `p i*` are quadratic residues modulo
an odd prime `q` are exactly the reciprocal conditions `(q / p i) = 1`. -/
theorem forall_legendreSym_oddPrimeDiscriminant_eq_one_iff {ι : Type*} (p : ι → ℕ)
    {q : ℕ} [Fact q.Prime] (hpprime : ∀ i, (p i).Prime) (hpodd : ∀ i, p i ≠ 2)
    (hq : q ≠ 2) :
    (∀ i, legendreSym q (oddPrimeDiscriminant (p i)) = 1) ↔
      ∀ i, @legendreSym (p i) ⟨hpprime i⟩ (q : ℤ) = 1 := by
  constructor
  · intro h i
    haveI : Fact (p i).Prime := ⟨hpprime i⟩
    have hsymm : legendreSym q (oddPrimeDiscriminant (p i)) =
        @legendreSym (p i) ⟨hpprime i⟩ (q : ℤ) :=
      legendreSym_oddPrimeDiscriminant_eq_symm (p := p i) (q := q) (hpodd i) hq
    exact hsymm ▸ h i
  · intro h i
    haveI : Fact (p i).Prime := ⟨hpprime i⟩
    have hsymm : legendreSym q (oddPrimeDiscriminant (p i)) =
        @legendreSym (p i) ⟨hpprime i⟩ (q : ℤ) :=
      legendreSym_oddPrimeDiscriminant_eq_symm (p := p i) (q := q) (hpodd i) hq
    rw [hsymm]
    exact h i

/-- Family form of unramifiedness for odd prime discriminants: a prime `q` divides none of
the `p i*` exactly when it divides none of the underlying primes `p i`. -/
theorem forall_not_dvd_oddPrimeDiscriminant_iff {ι : Type*} (p : ι → ℕ) {q : ℕ} :
    (∀ i, ¬ (q : ℤ) ∣ oddPrimeDiscriminant (p i)) ↔
      ∀ i, ¬ (q : ℤ) ∣ (p i : ℤ) := by
  simp_rw [not_dvd_oddPrimeDiscriminant_iff]

end TauCeti.Multiquadratic
