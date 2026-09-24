/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Quartic.Basic
public import TauCeti.RingTheory.Polynomial.FactorDegrees
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.Tactic.NormNum.IsSquare
import TauCeti.Algebra.Polynomial.SpecificDegree
import TauCeti.FieldTheory.GaloisGroups.Reduction
import TauCeti.RingTheory.Polynomial.Cyclotomic.Basic
import TauCeti.RingTheory.Polynomial.Monic.Irreducible

/-!
# The five quartic labels over `ℚ`

One monic integral quartic for each of the five transitive-group labels of degree four, with its
label proved through the quartic decision table of `TauCeti.FieldTheory.GaloisGroups.Quartic.Basic`.

| polynomial | resolvent cubic | discriminant | label |
|---|---|---|---|
| `X⁴ + X + 1` | `X³ - 4X - 1`, irreducible | `229`, not a square | `S₄ = 4T5` |
| `X⁴ + 8X + 12` | `X³ - 48X - 64`, irreducible | `331776 = 576²` | `A₄ = 4T4` |
| `X⁴ - 2` | `X³ + 8X`, one rational root | `-2048`, not a square | `D₄ = 4T3` |
| `X⁴ + 1` | `X³ - 4X`, splits completely | `256 = 16²` | `V₄ = 4T2` |
| `X⁴ + X³ + X² + X + 1` | `X³ - X² - 3X + 2`, one root | `125`, not a square | `C₄ = 4T1` |

The table decides the first, second and fourth rows outright. The third and fifth rows are only
placed in the pair `{4T1, 4T3}` by the table, and a further datum separates them. For
`X⁴ + X³ + X² + X + 1 = Φ₅` the Galois group is `(ℤ/5)ˣ` of order four, the order of `4T1` and
not of `4T3`. For `X⁴ - 2` the reduction modulo `7` factors as `(X - 2)(X - 5)(X² + 4)`, so by
Dedekind's theorem the Galois image contains a transposition, which fixes two roots; a group with
the cyclic label `4T1` has as many elements as there are roots, so it acts freely on them and
contains no such element.

Irreducibility over `ℚ` is proved by Gauss's lemma for `X⁴ + X + 1` and `X⁴ + 8X + 12`, ruling
out integral roots and integral monic quadratic factors by reduction modulo `2` and `5`; by the
Eisenstein criterion at `2` for `X⁴ - 2`; and from the irreducibility of the cyclotomic
polynomials `Φ₈ = X⁴ + 1` and `Φ₅` over `ℚ`.

## Main results

* `TauCeti.hasGaloisLabel_X_pow_four_add_X_add_one`: `X⁴ + X + 1` has label `4T5`.
* `TauCeti.hasGaloisLabel_X_pow_four_add_eight_mul_X_add_twelve`: `X⁴ + 8X + 12` has label `4T4`.
* `TauCeti.hasGaloisLabel_X_pow_four_sub_two`: `X⁴ - 2` has label `4T3`.
* `TauCeti.hasGaloisLabel_X_pow_four_add_one`: `X⁴ + 1` has label `4T2`.
* `TauCeti.hasGaloisLabel_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one`:
  `X⁴ + X³ + X² + X + 1` has label `4T1`.
* The orders `24, 12, 8, 4, 4` of the five Galois groups, as `TauCeti.natCard_gal_*`.

## References

* K. Conrad, *Galois groups of cubics and quartics (not in characteristic 2)*, §3, Examples.
* LMFDB, number fields `4.0.229.1`, `4.0.5184.1`, `4.2.2048.1`, `4.0.256.1` and `4.0.125.1`.
-/

public section

open Polynomial Equiv Equiv.Perm

namespace TauCeti

private instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### `X ^ 4 + X + 1`: the symmetric group, `4T5` -/

/-- `X ^ 4 + X + 1` is irreducible over `ℚ`: it has no root modulo `2`, and a monic quadratic
factor `X² + aX + b` would force `1 = a³ - 2ab` and `1 = a²b - b²`, which has no solution
modulo `2`. -/
theorem irreducible_X_pow_four_add_X_add_one : Irreducible (X ^ 4 + X + 1 : ℚ[X]) := by
  have := irreducible_map_intCast_of_natDegree_eq_four (g := X ^ 4 + X + 1) (by monicity!)
    (by compute_degree!)
    (fun m hm => by
      have h2 := congrArg (Int.cast : ℤ → ZMod 2) hm
      push_cast [eval_add, eval_pow, eval_X, eval_one] at h2
      generalize (m : ZMod 2) = y at h2
      revert y
      decide)
    (fun a b hab => by
      have hform : (X ^ 4 + X + 1 : ℤ[X]) = X ^ 4 + C 0 * X ^ 2 + C 1 * X + C 1 := by simp
      rw [hform, X_sq_add_C_mul_X_add_C_dvd_X_pow_four_add_iff] at hab
      obtain ⟨h1, h0⟩ := hab
      have h1' := congrArg (Int.cast : ℤ → ZMod 2) h1
      have h0' := congrArg (Int.cast : ℤ → ZMod 2) h0
      push_cast at h1' h0'
      generalize (a : ZMod 2) = x at h1' h0'
      generalize (b : ZMod 2) = y at h1' h0'
      revert x y
      decide)
  simpa using this

/-- The resolvent cubic of `X ^ 4 + X + 1` is `X ^ 3 - 4 * X - 1`. -/
theorem quarticD4Spec_specialize_X_pow_four_add_X_add_one :
    quarticD4Spec.specialize ℚ (X ^ 4 + X + 1) = X ^ 3 - 4 * X - 1 := by
  rw [quarticD4Spec_specialize]
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  norm_num [map_ofNat]
  ring

/-- The discriminant of `X ^ 4 + X + 1` is `229`. -/
theorem discr_X_pow_four_add_X_add_one : (X ^ 4 + X + 1 : ℚ[X]).discr = 229 := by
  rw [discr_quarticD4Spec_specialize (by monicity!) (by compute_degree!),
    quarticD4Spec_specialize_X_pow_four_add_X_add_one,
    discr_of_degree_eq_three (by compute_degree!)]
  simp only [coeff_sub, coeff_X_pow, coeff_X, coeff_one, coeff_ofNat_mul]
  norm_num

/-- The resolvent cubic `X ^ 3 - 4 * X - 1` of `X ^ 4 + X + 1` is irreducible over `ℚ`: it has
no root modulo `3`, so no integral root. -/
theorem irreducible_X_pow_three_sub_four_mul_X_sub_one :
    Irreducible (X ^ 3 - 4 * X - 1 : ℚ[X]) := by
  have := irreducible_map_intCast_of_natDegree_eq_three (g := X ^ 3 - 4 * X - 1)
    (by monicity!) (by compute_degree!) fun m hm => by
      have h3 := congrArg (Int.cast : ℤ → ZMod 3) hm
      push_cast [eval_sub, eval_pow, eval_X, eval_mul, eval_one, eval_ofNat] at h3
      generalize (m : ZMod 3) = y at h3
      revert y
      decide
  simpa using this

/-- **`X ^ 4 + X + 1` has label `4T5`**: its Galois group over `ℚ` is the symmetric group on its
four roots. The discriminant `229` is prime, hence not a square, and the resolvent cubic is
irreducible. -/
theorem hasGaloisLabel_X_pow_four_add_X_add_one :
    HasGaloisLabel (X ^ 4 + X + 1 : ℚ[X]) (⟨4, by simp⟩ : TransitiveGroupIndex 4) :=
  (hasGaloisLabel_four_four_iff (by simp) (by monicity!)).mpr
    ⟨irreducible_X_pow_four_add_X_add_one, by compute_degree!,
      by rw [discr_X_pow_four_add_X_add_one]; norm_num,
      by rw [quarticD4Spec_specialize_X_pow_four_add_X_add_one]
         exact irreducible_X_pow_three_sub_four_mul_X_sub_one⟩

/-- The Galois group of `X ^ 4 + X + 1` over `ℚ` has order `24`. -/
theorem natCard_gal_X_pow_four_add_X_add_one : Nat.card (X ^ 4 + X + 1 : ℚ[X]).Gal = 24 := by
  rw [hasGaloisLabel_X_pow_four_add_X_add_one.natCard_gal, natCard_referenceSubgroup_four_four]

/-! ### `X ^ 4 + 8 * X + 12`: the alternating group, `4T4` -/

/-- `X ^ 4 + 8 * X + 12` is irreducible over `ℚ`: it is positive at every integer, being
`(m² - 2)² + 4 (m + 1)² + 4`, and a monic quadratic factor `X² + aX + b` would force
`8 = a³ - 2ab` and `12 = a²b - b²`, which has no solution modulo `5`. -/
theorem irreducible_X_pow_four_add_eight_mul_X_add_twelve :
    Irreducible (X ^ 4 + 8 * X + 12 : ℚ[X]) := by
  have := irreducible_map_intCast_of_natDegree_eq_four (g := X ^ 4 + 8 * X + 12) (by monicity!)
    (by compute_degree!)
    (fun m hm => by
      simp only [eval_add, eval_pow, eval_X, eval_mul, eval_ofNat] at hm
      have hpos : 0 < (m ^ 2 - 2) ^ 2 + 4 * (m + 1) ^ 2 + 4 := by positivity
      nlinarith)
    (fun a b hab => by
      have hform : (X ^ 4 + 8 * X + 12 : ℤ[X]) = X ^ 4 + C 0 * X ^ 2 + C 8 * X + C 12 := by
        simp
      rw [hform, X_sq_add_C_mul_X_add_C_dvd_X_pow_four_add_iff] at hab
      obtain ⟨h1, h0⟩ := hab
      have h1' := congrArg (Int.cast : ℤ → ZMod 5) h1
      have h0' := congrArg (Int.cast : ℤ → ZMod 5) h0
      push_cast at h1' h0'
      generalize (a : ZMod 5) = x at h1' h0'
      generalize (b : ZMod 5) = y at h1' h0'
      revert x y
      decide)
  simpa using this

/-- The resolvent cubic of `X ^ 4 + 8 * X + 12` is `X ^ 3 - 48 * X - 64`. -/
theorem quarticD4Spec_specialize_X_pow_four_add_eight_mul_X_add_twelve :
    quarticD4Spec.specialize ℚ (X ^ 4 + 8 * X + 12) = X ^ 3 - 48 * X - 64 := by
  rw [quarticD4Spec_specialize]
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_ofNat_mul, coeff_ofNat_zero, coeff_ofNat_succ]
  norm_num [map_ofNat]
  ring

/-- The discriminant of `X ^ 4 + 8 * X + 12` is `331776 = 576 ^ 2`. -/
theorem discr_X_pow_four_add_eight_mul_X_add_twelve :
    (X ^ 4 + 8 * X + 12 : ℚ[X]).discr = 331776 := by
  rw [discr_quarticD4Spec_specialize (by monicity!) (by compute_degree!),
    quarticD4Spec_specialize_X_pow_four_add_eight_mul_X_add_twelve,
    discr_of_degree_eq_three (by compute_degree!)]
  simp only [coeff_sub, coeff_X_pow, coeff_ofNat_mul, coeff_X, coeff_ofNat_zero, coeff_ofNat_succ]
  norm_num

/-- The resolvent cubic `X ^ 3 - 48 * X - 64` of `X ^ 4 + 8 * X + 12` is irreducible over `ℚ`:
it has no root modulo `5`, so no integral root. -/
theorem irreducible_X_pow_three_sub_fortyEight_mul_X_sub_sixtyFour :
    Irreducible (X ^ 3 - 48 * X - 64 : ℚ[X]) := by
  have := irreducible_map_intCast_of_natDegree_eq_three (g := X ^ 3 - 48 * X - 64)
    (by monicity!) (by compute_degree!) fun m hm => by
      have h5 := congrArg (Int.cast : ℤ → ZMod 5) hm
      push_cast [eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat] at h5
      generalize (m : ZMod 5) = y at h5
      revert y
      decide
  simpa using this

/-- **`X ^ 4 + 8 * X + 12` has label `4T4`**: its Galois group over `ℚ` is the alternating group
on its four roots. The discriminant `576 ^ 2` is a square and the resolvent cubic is
irreducible. -/
theorem hasGaloisLabel_X_pow_four_add_eight_mul_X_add_twelve :
    HasGaloisLabel (X ^ 4 + 8 * X + 12 : ℚ[X]) (⟨3, by simp⟩ : TransitiveGroupIndex 4) :=
  (hasGaloisLabel_four_three_iff (by simp) (by monicity!)).mpr
    ⟨irreducible_X_pow_four_add_eight_mul_X_add_twelve, by compute_degree!,
      by rw [discr_X_pow_four_add_eight_mul_X_add_twelve]; exact ⟨576, by norm_num⟩,
      by rw [quarticD4Spec_specialize_X_pow_four_add_eight_mul_X_add_twelve]
         exact irreducible_X_pow_three_sub_fortyEight_mul_X_sub_sixtyFour⟩

/-- The Galois group of `X ^ 4 + 8 * X + 12` over `ℚ` has order `12`. -/
theorem natCard_gal_X_pow_four_add_eight_mul_X_add_twelve :
    Nat.card (X ^ 4 + 8 * X + 12 : ℚ[X]).Gal = 12 := by
  rw [hasGaloisLabel_X_pow_four_add_eight_mul_X_add_twelve.natCard_gal,
    natCard_referenceSubgroup_four_three]

/-! ### `X ^ 4 + 1`: the Klein four-group, `4T2` -/

/-- `X ^ 4 + 1` is the eighth cyclotomic polynomial, hence irreducible over `ℚ`. -/
theorem irreducible_X_pow_four_add_one : Irreducible (X ^ 4 + 1 : ℚ[X]) := by
  have hcyc : cyclotomic 8 ℚ = X ^ 4 + 1 := by
    have h8 : (8 : ℕ) = 2 ^ (2 + 1) := by norm_num
    rw [h8, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [Finset.sum_range_succ, add_comm]
  rw [← hcyc]
  exact cyclotomic.irreducible_rat (by norm_num)

/-- The resolvent cubic of `X ^ 4 + 1` is `X ^ 3 - 4 * X`, which splits completely over `ℚ`. -/
theorem quarticD4Spec_specialize_X_pow_four_add_one :
    quarticD4Spec.specialize ℚ (X ^ 4 + 1) = X ^ 3 - 4 * X := by
  rw [quarticD4Spec_specialize]
  simp only [coeff_add, coeff_X_pow, coeff_one]
  norm_num [map_ofNat]
  ring

/-- The discriminant of `X ^ 4 + 1` is `256 = 16 ^ 2`. -/
theorem discr_X_pow_four_add_one : (X ^ 4 + 1 : ℚ[X]).discr = 256 := by
  rw [discr_quarticD4Spec_specialize (by monicity!) (by compute_degree!),
    quarticD4Spec_specialize_X_pow_four_add_one, discr_of_degree_eq_three (by compute_degree!)]
  simp only [coeff_sub, coeff_X_pow, coeff_ofNat_mul, coeff_X]
  norm_num

/-- **`X ^ 4 + 1` has label `4T2`**: its Galois group over `ℚ` is the Klein four-group acting
regularly on its four roots, the primitive eighth roots of unity. The discriminant `16 ^ 2` is a
square and the resolvent cubic `X ^ 3 - 4 * X` has the root `0`. -/
theorem hasGaloisLabel_X_pow_four_add_one :
    HasGaloisLabel (X ^ 4 + 1 : ℚ[X]) (⟨1, by simp⟩ : TransitiveGroupIndex 4) :=
  (hasGaloisLabel_four_one_iff (by simp) (by monicity!)).mpr
    ⟨irreducible_X_pow_four_add_one, by compute_degree!,
      by rw [discr_X_pow_four_add_one]; exact ⟨16, by norm_num⟩,
      ⟨0, by rw [quarticD4Spec_specialize_X_pow_four_add_one]; simp⟩⟩

/-- The Galois group of `X ^ 4 + 1` over `ℚ` has order `4`. -/
theorem natCard_gal_X_pow_four_add_one : Nat.card (X ^ 4 + 1 : ℚ[X]).Gal = 4 := by
  rw [hasGaloisLabel_X_pow_four_add_one.natCard_gal, natCard_referenceSubgroup_four_one]

/-! ### `X ^ 4 + X ^ 3 + X ^ 2 + X + 1`: the cyclic group, `4T1` -/

/-- `X ^ 4 + X ^ 3 + X ^ 2 + X + 1` is the fifth cyclotomic polynomial, hence irreducible over
`ℚ`. -/
theorem irreducible_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one :
    Irreducible (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X]) := by
  rw [← cyclotomic_five ℚ]
  exact cyclotomic.irreducible_rat (by norm_num)

/-- The Galois group of `X ^ 4 + X ^ 3 + X ^ 2 + X + 1` over `ℚ` has order `4`: it is the unit
group of `ℤ/5`. -/
theorem natCard_gal_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one :
    Nat.card (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X]).Gal = 4 := by
  -- The `ℚ`-algebra structure of the cyclotomic field is passed explicitly: instance search
  -- would otherwise pick the generic rational algebra of a characteristic-zero division ring,
  -- which is propositionally but not definitionally the one the cyclotomic-extension instance
  -- is stated for.
  have e := @galCyclotomicEquivUnitsZMod 5 _ ℚ _ (CyclotomicField 5 ℚ) _
    (CyclotomicField.algebra 5 ℚ) inferInstance (cyclotomic.irreducible_rat (by norm_num))
  rw [← cyclotomic_five ℚ, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card_units]

/-- The resolvent cubic of `X ^ 4 + X ^ 3 + X ^ 2 + X + 1` is `X ^ 3 - X ^ 2 - 3 * X + 2`, with
the rational root `2`. -/
theorem quarticD4Spec_specialize_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one :
    quarticD4Spec.specialize ℚ (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) = X ^ 3 - X ^ 2 - 3 * X + 2 := by
  rw [quarticD4Spec_specialize]
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  norm_num [map_ofNat]
  ring

/-- The discriminant of `X ^ 4 + X ^ 3 + X ^ 2 + X + 1` is `125 = 5 ^ 3`. -/
theorem discr_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one :
    (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X]).discr = 125 := by
  rw [discr_quarticD4Spec_specialize (by monicity!) (by compute_degree!),
    quarticD4Spec_specialize_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one,
    discr_of_degree_eq_three (by compute_degree!)]
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_ofNat_mul, coeff_X, coeff_ofNat_zero,
    coeff_ofNat_succ]
  norm_num

/-- **`X ^ 4 + X ^ 3 + X ^ 2 + X + 1` has label `4T1`**: its Galois group over `ℚ` is cyclic of
order four, acting regularly on the primitive fifth roots of unity. The discriminant `125` is not
a square and the resolvent cubic has the rational root `2`, which places the label in
`{4T1, 4T3}`; the order `4` of the Galois group rules out `4T3`, of order `8`. -/
theorem hasGaloisLabel_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one :
    HasGaloisLabel (X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : ℚ[X])
      (⟨0, by simp⟩ : TransitiveGroupIndex 4) := by
  have hor := (hasGaloisLabel_four_zero_or_two_iff (by simp) (by monicity!)).mpr
    ⟨irreducible_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one, by compute_degree!,
      by rw [discr_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one]; norm_num,
      ⟨2, by
        rw [quarticD4Spec_specialize_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one,
          IsRoot.def]
        simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat]
        norm_num⟩⟩
  refine hor.resolve_right fun h => ?_
  have hcard := h.natCard_gal
  rw [natCard_gal_X_pow_four_add_X_pow_three_add_X_sq_add_X_add_one,
    natCard_referenceSubgroup_four_two] at hcard
  omega

/-! ### `X ^ 4 - 2`: the dihedral group, `4T3` -/

private theorem monic_X_pow_four_sub_two_int : (X ^ 4 - 2 : ℤ[X]).Monic := by monicity!

private theorem map_X_pow_four_sub_two :
    (X ^ 4 - 2 : ℤ[X]).map (Int.castRingHom ℚ) = X ^ 4 - 2 := by simp

/-- `X ^ 4 - 2` is irreducible over `ℚ`, by the Eisenstein criterion at the prime `2`. -/
theorem irreducible_X_pow_four_sub_two : Irreducible (X ^ 4 - 2 : ℚ[X]) := by
  have hint : Irreducible (X ^ 4 - 2 : ℤ[X]) := by
    have hdeg : (X ^ 4 - 2 : ℤ[X]).natDegree = 4 := by compute_degree!
    have h2 : (Ideal.span {(2 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
    refine irreducible_of_eisenstein_criterion h2 ?_ ?_ ?_ ?_
      monic_X_pow_four_sub_two_int.isPrimitive
    · rw [monic_X_pow_four_sub_two_int.leadingCoeff, Ideal.mem_span_singleton]
      decide
    · intro n hn
      rw [degree_eq_natDegree monic_X_pow_four_sub_two_int.ne_zero, hdeg] at hn
      have hn4 : n < 4 := by exact_mod_cast hn
      rw [Ideal.mem_span_singleton]
      interval_cases n <;> simp [coeff_X_pow, coeff_ofNat_zero, coeff_ofNat_succ]
    · rw [degree_eq_natDegree monic_X_pow_four_sub_two_int.ne_zero, hdeg]
      norm_num
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simp only [coeff_sub, coeff_X_pow, coeff_ofNat_zero]
      decide
  rw [← map_X_pow_four_sub_two]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    monic_X_pow_four_sub_two_int.isPrimitive).mp hint

/-- The resolvent cubic of `X ^ 4 - 2` is `X ^ 3 + 8 * X`, with the rational root `0`. -/
theorem quarticD4Spec_specialize_X_pow_four_sub_two :
    quarticD4Spec.specialize ℚ (X ^ 4 - 2) = X ^ 3 + 8 * X := by
  rw [quarticD4Spec_specialize]
  simp only [coeff_sub, coeff_X_pow, coeff_ofNat_zero, coeff_ofNat_succ]
  norm_num [map_ofNat]

/-- The discriminant of `X ^ 4 - 2` over `ℚ` is `-2048 = -2 ^ 11`. -/
theorem discr_X_pow_four_sub_two : (X ^ 4 - 2 : ℚ[X]).discr = -2048 := by
  rw [discr_quarticD4Spec_specialize (by monicity!) (by compute_degree!),
    quarticD4Spec_specialize_X_pow_four_sub_two, discr_of_degree_eq_three (by compute_degree!)]
  simp only [coeff_add, coeff_X_pow, coeff_ofNat_mul, coeff_X]
  norm_num

/-- The discriminant of `X ^ 4 - 2` over `ℤ` is `-2048 = -2 ^ 11`, so every odd prime is a good
prime for `X ^ 4 - 2`. -/
theorem discr_X_pow_four_sub_two_int : (X ^ 4 - 2 : ℤ[X]).discr = -2048 := by
  have h := monic_X_pow_four_sub_two_int.discr_map (Int.castRingHom ℚ)
  rw [map_X_pow_four_sub_two, discr_X_pow_four_sub_two, eq_intCast] at h
  exact_mod_cast h.symm

/-- Modulo `7`, `X ^ 4 - 2` factors as `(X - 2)(X - 5)(X ^ 2 + 4)`, where `X ^ 2 + 4` is
irreducible because `-4 = 3` is not a square modulo `7`. Its factor degrees are `{1, 1, 2}`. -/
theorem _root_.Polynomial.factorDegrees_X_pow_four_sub_two_seven :
    (X ^ 4 - 2 : ℤ[X]).factorDegrees 7 = {1, 1, 2} := by
  have hquaddeg : (X ^ 2 + C 4 : (ZMod 7)[X]).natDegree = 2 := by compute_degree!
  have hquad : Irreducible (X ^ 2 + C 4 : (ZMod 7)[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hquaddeg]
      decide
    · intro x
      rw [IsRoot.def]
      simp only [eval_add, eval_pow, eval_X, eval_C]
      fin_cases x <;> decide
  have hirr : ∀ q ∈ ({X - C 2, X - C 5, X ^ 2 + C 4} : Multiset (ZMod 7)[X]), Irreducible q := by
    intro q hq
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact irreducible_X_sub_C 2
    · exact irreducible_X_sub_C 5
    · exact hquad
  have hmap : (X ^ 4 - 2 : ℤ[X]).map (Int.castRingHom (ZMod 7)) =
      ({X - C 2, X - C 5, X ^ 2 + C 4} : Multiset (ZMod 7)[X]).prod := by
    simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, map_ofNat]
    have h7 : (7 : (ZMod 7)[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero (ZMod 7)[X] 7
    linear_combination (X ^ 3 - 2 * X ^ 2 + 4 * X - 6) * h7
  rw [factorDegrees_eq_map_natDegree_of_map_eq_prod hirr hmap]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, natDegree_X_sub_C,
    hquaddeg]

attribute [local instance] Gal.splits_ℚ_ℂ

open scoped Classical in
/-- **`X ^ 4 - 2` does not have cyclic Galois group.** Modulo `7` it factors with exactly one
quadratic factor, so by Dedekind's theorem its Galois image contains a transposition, which fixes
two of the four roots. A group with the cyclic label `4T1` has order four and acts freely on the
four roots, so it contains no such element. -/
theorem not_hasGaloisLabel_four_zero_X_pow_four_sub_two :
    ¬ HasGaloisLabel (X ^ 4 - 2 : ℚ[X]) (⟨0, by simp⟩ : TransitiveGroupIndex 4) := by
  intro h
  rw [← map_X_pow_four_sub_two] at h
  have hd : (X ^ 4 - 2 : ℤ[X]).discr ≠ 0 := by rw [discr_X_pow_four_sub_two_int]; norm_num
  obtain ⟨τ, ⟨σ, rfl⟩, hτ⟩ := exists_isSwap_mem_range_galActionHom monic_X_pow_four_sub_two_int 7
    (by rw [discr_X_pow_four_sub_two_int]; decide)
    (by rw [factorDegrees_X_pow_four_sub_two_seven]; decide)
    (by rw [factorDegrees_X_pow_four_sub_two_seven]; decide)
  have hcard : Fintype.card (((X ^ 4 - 2 : ℤ[X]).map (Int.castRingHom ℚ)).rootSet ℂ) = 4 := by
    rw [← Nat.card_eq_fintype_card, natCard_rootSet_complex_eq_natDegree hd]
    compute_degree!
  -- A transposition moves two of the four roots, so it fixes one.
  have hne : (Gal.galActionHom _ ℂ σ).support ≠ Finset.univ := fun huniv => by
    have h2 := card_support_eq_two.mpr hτ
    rw [huniv, Finset.card_univ, hcard] at h2
    omega
  obtain ⟨x, hx⟩ : ∃ x, x ∉ (Gal.galActionHom _ ℂ σ).support := by
    simpa [Finset.eq_univ_iff_forall] using hne
  have hfix : σ • x = x := by
    have := notMem_support.mp hx
    simpa [Gal.galActionHom, MulAction.toPermHom_apply, MulAction.toPerm_apply] using this
  have hσ : σ = 1 := h.eq_one_of_smul_eq_self natCard_referenceSubgroup_four_zero hfix
  exact hτ.isCycle.ne_one (by rw [hσ, map_one])

/-- **`X ^ 4 - 2` has label `4T3`**: its Galois group over `ℚ` is dihedral of order eight. The
discriminant `-2048` is not a square and the resolvent cubic `X ^ 3 + 8 * X` has the rational root
`0`, which places the label in `{4T1, 4T3}`; the transposition exhibited by the factorization
modulo `7` rules out `4T1`. -/
theorem hasGaloisLabel_X_pow_four_sub_two :
    HasGaloisLabel (X ^ 4 - 2 : ℚ[X]) (⟨2, by simp⟩ : TransitiveGroupIndex 4) := by
  have hor := (hasGaloisLabel_four_zero_or_two_iff (by simp) (by monicity!)).mpr
    ⟨irreducible_X_pow_four_sub_two, by compute_degree!,
      by rw [discr_X_pow_four_sub_two]; norm_num,
      ⟨0, by rw [quarticD4Spec_specialize_X_pow_four_sub_two]; simp⟩⟩
  exact hor.resolve_left not_hasGaloisLabel_four_zero_X_pow_four_sub_two

/-- The Galois group of `X ^ 4 - 2` over `ℚ` has order `8`. -/
theorem natCard_gal_X_pow_four_sub_two : Nat.card (X ^ 4 - 2 : ℚ[X]).Gal = 8 := by
  rw [hasGaloisLabel_X_pow_four_sub_two.natCard_gal, natCard_referenceSubgroup_four_two]

end TauCeti
