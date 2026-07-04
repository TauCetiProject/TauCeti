/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence

/-!
# Prime-discriminant families with at most one even factor

The genus-field layer of the multiquadratic roadmap uses the prime discriminants dividing a
quadratic discriminant. Such a list has at most one even prime discriminant, so it automatically
avoids the only obstruction in
`TauCeti.Multiquadratic.not_isSquare_prod_primeDiscriminantRadicands`: the simultaneous presence
of all three even prime discriminants `-4`, `8`, and `-8`.

This file records that consumer-facing specialization. The underlying square-class arithmetic is
the prime-discriminant independence theorem from
`TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence`; this module only packages the
`at most one even prime discriminant` hypothesis in the form later genus-field code will naturally
have.

## Main results

* `TauCeti.Multiquadratic.not_all_three_evenPrimeDiscriminants_of_forall_even_eq`: a family with
  at most one even prime discriminant cannot contain `-4`, `8`, and `-8`.
* `TauCeti.Multiquadratic.not_isSquare_prod_primeDiscriminantRadicands_of_forall_even_eq`:
  square-class independence of the associated radicands under that hypothesis.
* `TauCeti.Multiquadratic.finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_even_eq`:
  the corresponding full multiquadratic degree statement.
-/

public section

namespace TauCeti.Multiquadratic

/-- A prime-discriminant family with at most one even prime discriminant cannot contain the three
even prime discriminants `-4`, `8`, and `-8` simultaneously.

The hypothesis is stated extensionally: any two indices whose discriminants are even prime
discriminants must carry the same discriminant value. This is the form supplied by the
prime-discriminant factorization of a quadratic discriminant, where there is only one 2-adic
factor. -/
theorem not_all_three_evenPrimeDiscriminants_of_forall_even_eq {ι : Type*} {D : ι → ℤ}
    (heven_unique : ∀ i j,
      IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j) :
    ¬ ((∃ i, D i = -4) ∧ (∃ i, D i = 8) ∧ (∃ i, D i = -8)) := by
  rintro ⟨⟨i4, hi4⟩, ⟨i8, hi8⟩, _⟩
  have hD : D i4 = D i8 :=
    heven_unique i4 i8 (hi4.symm ▸ isEvenPrimeDiscriminant_neg_four)
      (hi8.symm ▸ isEvenPrimeDiscriminant_eight)
  omega

/-- **Square-class independence for prime-discriminant families with at most one even factor.**
Let `D : ι → ℤ` be an injective family of prime discriminants, and assume any two even prime
discriminants in the family are equal as integers. Then no nonempty subset product of the
associated radicands `primeDiscriminantRadicand (D i)` is a rational square.

This is the genus-field specialization of
`not_isSquare_prod_primeDiscriminantRadicands`: the prime discriminants dividing a quadratic
discriminant have at most one even member, so the exceptional product
`(-1) * 2 * (-2) = 4` cannot occur. -/
theorem not_isSquare_prod_primeDiscriminantRadicands_of_forall_even_eq {ι : Type*}
    (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven_unique : ∀ i j,
      IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j) :
    ∀ S : Finset ι, S.Nonempty →
      ¬ IsSquare (∏ i ∈ S, ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) := by
  exact not_isSquare_prod_primeDiscriminantRadicands D hD hinj
    (not_all_three_evenPrimeDiscriminants_of_forall_even_eq heven_unique)

/-- **Full degree for adjoining roots of prime-discriminant radicands with at most one even
factor.** If `D : ι → ℤ` is an injective finite family of prime discriminants with at most one
even member, then adjoining square roots of the associated radicands gives a multiquadratic field
of degree `2 ^ Nat.card ι`.

This is the degree theorem in the form needed for genus-field generator lists coming from prime
discriminants of a quadratic discriminant. -/
theorem finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_even_eq {ι : Type*} [Finite ι]
    {L : Type*} [Field L] [Algebra ℚ L] (D : ι → ℤ)
    (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven_unique : ∀ i j,
      IsEvenPrimeDiscriminant (D i) → IsEvenPrimeDiscriminant (D j) → D i = D j)
    (root : ι → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range root)) = 2 ^ Nat.card ι :=
  finrank_adjoin_roots_primeDiscriminantRadicands D hD hinj
    (not_all_three_evenPrimeDiscriminants_of_forall_even_eq heven_unique) root hroot

end TauCeti.Multiquadratic
