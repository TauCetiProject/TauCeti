/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import TauCeti.FieldTheory.GaloisGroups.Label
import TauCeti.NumberTheory.Multiquadratic.Galois.Group
import TauCeti.NumberTheory.Multiquadratic.Prime.Radicands
import TauCeti.NumberTheory.Multiquadratic.Three.Basic

/-!
# Non-examples: inseparable and reducible polynomials

Three polynomials test that the permutation picture of a Galois group excludes what it should.

* `(X² - 2)²` is not separable, so it has no transitive-group label
  (`TauCeti.not_hasGaloisLabel_of_not_separable`) and does not have full symmetric Galois group
  (`Polynomial.not_hasFullSymmetricGaloisGroup_pow_of_not_isUnit`). It is also reducible, yet its
  Galois group acts transitively on its two distinct roots. It is therefore the witness that
  separability cannot be dropped from `TauCeti.isPretransitive_iff_irreducible`.
* `(X² - 2)(X² - 3)` is separable and reducible. Over `ℚ` its Galois group is the Klein four-group
  `V₄`. It acts on the four roots with two orbits, each of size two: the roots of `X² - 2` and
  the roots of `X² - 3`. Being reducible, the polynomial carries no transitive-group label.
* `X⁵ + X + 1 = (X² + X + 1)(X³ - X² + 1)` is a reducible quintic, so no label `5Tj` is attached
  to it.

The Galois group of `(X² - 2)(X² - 3)` comes from the multiquadratic theory:
`TauCeti.Multiquadratic.nonempty_mulEquiv_gal_definingPolynomial` identifies it with
`(ℤ/2)²`, because `2`, `3` and `6` are not squares in `ℚ`.

## Main results

* `TauCeti.isPretransitive_gal_X_sq_sub_two_sq`: the Galois group of the reducible polynomial
  `(X² - 2)²` acts transitively on its roots.
* `TauCeti.isKleinFour_gal_X_sq_sub_two_mul_X_sq_sub_three`: the Galois group of
  `(X² - 2)(X² - 3)` over `ℚ` is a Klein four-group.
* `TauCeti.natCard_orbit_X_sq_sub_two_mul_X_sq_sub_three` and
  `TauCeti.natCard_orbitQuotient_X_sq_sub_two_mul_X_sq_sub_three`: its root action has two orbits,
  each of size two.
* `TauCeti.not_hasGaloisLabel_X_sq_sub_two_mul_X_sq_sub_three` and
  `TauCeti.not_hasGaloisLabel_X_pow_five_add_X_add_one`: neither polynomial has a label.

## References

* LMFDB, *Galois group labels*, <https://www.lmfdb.org/GaloisGroup/>.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F]

/-! ## The quadratic factors -/

-- `X² - 2` is irreducible over `ℚ`, since `2` is not a square in `ℚ`.
private theorem irreducible_X_sq_sub_two : Irreducible (X ^ 2 - 2 : ℚ[X]) := by
  rw [← C_ofNat]
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => ?_
  have : IsSquare ((2 : ℕ) : ℚ) := ⟨b, by push_cast; rw [← hb]; ring⟩
  exact Nat.prime_two.prime.not_isSquare (Rat.isSquare_natCast_iff.mp this)

private theorem irreducible_X_sq_sub_three : Irreducible (X ^ 2 - 3 : ℚ[X]) := by
  rw [← C_ofNat]; exact NumberField.irreducible_X_sq_sub_three.out

private theorem monic_X_sq_sub_two : (X ^ 2 - 2 : ℚ[X]).Monic := by
  rw [← C_ofNat]; exact monic_X_pow_sub_C _ two_ne_zero

private theorem monic_X_sq_sub_three : (X ^ 2 - 3 : ℚ[X]).Monic := by
  rw [← C_ofNat]; exact monic_X_pow_sub_C _ two_ne_zero

-- A quadratic `X² - a` is not a unit, over any field.
private theorem not_isUnit_X_sq_sub_C (a : F) : ¬ IsUnit (X ^ 2 - C a) := fun hu => by
  simpa [natDegree_X_pow_sub_C] using natDegree_eq_zero_of_isUnit hu

/-! ## `(X² - 2)²`: transitive but reducible -/

/-- `(X² - 2)²` is not separable, over any field. -/
theorem not_separable_X_sq_sub_two_sq : ¬ ((X ^ 2 - 2) ^ 2 : F[X]).Separable := fun h => by
  rw [← C_ofNat] at h
  simpa using (h.of_pow (not_isUnit_X_sq_sub_C _) two_ne_zero).2

/-- `(X² - 2)²` is reducible, over any field. -/
theorem not_irreducible_X_sq_sub_two_sq : ¬ Irreducible ((X ^ 2 - 2) ^ 2 : F[X]) :=
  not_irreducible_pow (by norm_num)

/-- **The Galois group of the reducible polynomial `(X² - 2)²` over `ℚ` acts transitively on its
roots.** Its two distinct roots `±√2` are the roots of the irreducible `X² - 2`. Together with
`TauCeti.not_irreducible_X_sq_sub_two_sq`, this shows that separability cannot be dropped from
`TauCeti.isPretransitive_iff_irreducible`. -/
theorem isPretransitive_gal_X_sq_sub_two_sq :
    MulAction.IsPretransitive ((X ^ 2 - 2) ^ 2 : ℚ[X]).Gal
      (((X ^ 2 - 2) ^ 2 : ℚ[X]).rootSet ((X ^ 2 - 2) ^ 2 : ℚ[X]).SplittingField) :=
  Gal.galActionAux_isPretransitive_of_dvd_pow irreducible_X_sq_sub_two dvd_rfl

/-! ## `(X² - 2)(X² - 3)`: separable and reducible, with group `V₄` -/

/-- `(X² - 2)(X² - 3)` is separable over every field of characteristic zero. -/
theorem separable_X_sq_sub_two_mul_X_sq_sub_three [CharZero F] :
    ((X ^ 2 - 2) * (X ^ 2 - 3) : F[X]).Separable := by
  have h2 : (X ^ 2 - 2 : F[X]).Separable := by
    rw [← C_ofNat]; exact separable_X_pow_sub_C _ (by norm_num) (by norm_num)
  have h3 : (X ^ 2 - 3 : F[X]).Separable := by
    rw [← C_ofNat]; exact separable_X_pow_sub_C _ (by norm_num) (by norm_num)
  exact h2.mul h3 ⟨1, -1, by ring⟩

/-- `(X² - 2)(X² - 3)` is reducible, over any field. -/
theorem not_irreducible_X_sq_sub_two_mul_X_sq_sub_three :
    ¬ Irreducible ((X ^ 2 - 2) * (X ^ 2 - 3) : F[X]) := fun h => by
  rw [← C_ofNat, ← C_ofNat] at h
  exact (h.isUnit_or_isUnit rfl).elim (not_isUnit_X_sq_sub_C _) (not_isUnit_X_sq_sub_C _)

/-- **The Galois group of `(X² - 2)(X² - 3)` over `ℚ` is the Klein four-group.** The splitting
field is `ℚ(√2, √3)`, and the radicands `2` and `3` are square-class independent: none of `2`, `3`
and `6` is a square in `ℚ`. -/
theorem isKleinFour_gal_X_sq_sub_two_mul_X_sq_sub_three :
    IsKleinFour ((X ^ 2 - 2) * (X ^ 2 - 3) : ℚ[X]).Gal := by
  let p : Fin 2 → ℕ := ![2, 3]
  have hdef : Multiquadratic.definingPolynomial (fun i => (p i : ℚ)) =
      ((X ^ 2 - 2) * (X ^ 2 - 3) : ℚ[X]) := by
    rw [Multiquadratic.definingPolynomial_def, ← C_ofNat, ← C_ofNat (n := 3)]
    convert Fin.prod_univ_two fun i => X ^ 2 - C ((p i : ℕ) : ℚ) <;> simp [p]
  obtain ⟨e⟩ := hdef ▸ Multiquadratic.nonempty_mulEquiv_gal_definingPolynomial
    (Multiquadratic.not_isSquare_prod_primes_of_injective p (by decide) (by decide))
  exact
    { card_four := by rw [Nat.card_congr e.toEquiv]; simp [Nat.card_eq_fintype_card]
      exponent_two := by
        rw [Monoid.exponent_eq_of_mulEquiv e, Monoid.exponent_multiplicative,
          AddMonoid.exponent_pi]
        simp [Fin.univ_succ] }

section Orbits

variable (E : Type*) [Field E] [Algebra ℚ E]

-- The minimal polynomial of a root of `(X² - 2)(X² - 3)` is one of its two factors.
private theorem minpoly_eq_of_mem_rootSet_X_sq_sub_two_mul_X_sq_sub_three
    (x : ((X ^ 2 - 2) * (X ^ 2 - 3) : ℚ[X]).rootSet E) :
    minpoly ℚ (x : E) = X ^ 2 - 2 ∨ minpoly ℚ (x : E) = X ^ 2 - 3 := by
  have hx := aeval_eq_zero_of_mem_rootSet x.2
  rw [map_mul] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact .inl (minpoly.eq_of_irreducible_of_monic irreducible_X_sq_sub_two h
      monic_X_sq_sub_two).symm
  · exact .inr (minpoly.eq_of_irreducible_of_monic irreducible_X_sq_sub_three h
      monic_X_sq_sub_three).symm

variable [Fact ((((X ^ 2 - 2) * (X ^ 2 - 3) : ℚ[X]).map (algebraMap ℚ E)).Splits)]

/-- **Each Galois orbit on the roots of `(X² - 2)(X² - 3)` has two elements**: the orbit of a
root is the pair of roots of its irreducible factor `X² - 2` or `X² - 3`. -/
theorem natCard_orbit_X_sq_sub_two_mul_X_sq_sub_three
    (x : ((X ^ 2 - 2) * (X ^ 2 - 3) : ℚ[X]).rootSet E) :
    Nat.card (MulAction.orbit ((X ^ 2 - 2) * (X ^ 2 - 3) : ℚ[X]).Gal x) = 2 := by
  have hsep : (minpoly ℚ (x : E)).Separable :=
    separable_X_sq_sub_two_mul_X_sq_sub_three.of_dvd (minpoly.dvd ℚ _
      (aeval_eq_zero_of_mem_rootSet x.2))
  rw [natCard_orbit_eq_natDegree_minpoly E x hsep]
  rcases minpoly_eq_of_mem_rootSet_X_sq_sub_two_mul_X_sq_sub_three E x with h | h <;>
    · rw [h]; compute_degree!

/-- **The Galois group of `(X² - 2)(X² - 3)` has two orbits on its roots**, one for each
irreducible factor. -/
theorem natCard_orbitQuotient_X_sq_sub_two_mul_X_sq_sub_three :
    Nat.card (MulAction.orbitRel.Quotient ((X ^ 2 - 2) * (X ^ 2 - 3) : ℚ[X]).Gal
      (((X ^ 2 - 2) * (X ^ 2 - 3) : ℚ[X]).rootSet E)) = 2 := by
  rw [natCard_orbitQuotient _ E separable_X_sq_sub_two_mul_X_sq_sub_three.ne_zero,
    Nat.card_eq_two_iff]
  refine ⟨⟨X ^ 2 - 2, irreducible_X_sq_sub_two, monic_X_sq_sub_two, dvd_mul_right _ _⟩,
    ⟨X ^ 2 - 3, irreducible_X_sq_sub_three, monic_X_sq_sub_three, dvd_mul_left _ _⟩,
    fun h => by simpa using congrArg (eval 0) (Subtype.ext_iff.mp h), ?_⟩
  refine Set.eq_univ_of_forall fun q => ?_
  rcases q.irreducible.prime.dvd_or_dvd q.dvd with h | h
  · exact .inl (Subtype.ext (eq_of_monic_of_associated q.monic monic_X_sq_sub_two
      (q.irreducible.associated_of_dvd irreducible_X_sq_sub_two h)))
  · exact .inr (Subtype.ext (eq_of_monic_of_associated q.monic monic_X_sq_sub_three
      (q.irreducible.associated_of_dvd irreducible_X_sq_sub_three h)))

end Orbits

variable {n : ℕ}

/-- **`(X² - 2)(X² - 3)` has no transitive-group label**, in any degree and over any field: a
polynomial with a label is irreducible. -/
theorem not_hasGaloisLabel_X_sq_sub_two_mul_X_sq_sub_three (j : TransitiveGroupIndex n) :
    ¬ HasGaloisLabel ((X ^ 2 - 2) * (X ^ 2 - 3) : F[X]) j := fun h =>
  not_irreducible_X_sq_sub_two_mul_X_sq_sub_three h.irreducible

/-! ## `X⁵ + X + 1`: a reducible quintic -/

/-- `X⁵ + X + 1 = (X² + X + 1)(X³ - X² + 1)` is reducible, over any field. -/
theorem not_irreducible_X_pow_five_add_X_add_one : ¬ Irreducible (X ^ 5 + X + 1 : F[X]) := by
  rw [show (X ^ 5 + X + 1 : F[X]) = (X ^ 2 + X + 1) * (X ^ 3 - X ^ 2 + 1) by ring]
  intro h
  have h2 : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
  have h3 : (X ^ 3 - X ^ 2 + 1 : F[X]).natDegree = 3 := by compute_degree!
  rcases h.isUnit_or_isUnit rfl with hu | hu
  · simp [natDegree_eq_zero_of_isUnit hu] at h2
  · simp [natDegree_eq_zero_of_isUnit hu] at h3

/-- **No label `5Tj` is attached to the reducible quintic `X⁵ + X + 1`**, nor any other label,
over any field. -/
theorem not_hasGaloisLabel_X_pow_five_add_X_add_one (j : TransitiveGroupIndex n) :
    ¬ HasGaloisLabel (X ^ 5 + X + 1 : F[X]) j := fun h =>
  not_irreducible_X_pow_five_add_X_add_one h.irreducible

end TauCeti
