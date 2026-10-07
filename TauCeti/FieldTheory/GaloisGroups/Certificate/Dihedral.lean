/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Check

import TauCeti.Algebra.Polynomial.SpecificDegree
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Trinomial
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar

/-!
# A dihedral quintic certificate

The polynomial `X⁵ - 5X - 12` has Galois group the dihedral group `D₅` of order `10`, the label
`5T2`; it defines the LMFDB number field `5.1.1000000.1`. This module certifies that label by the
dihedral route of `TauCeti.QuinticCertificate`:

* `X⁵ - 5X - 12` is irreducible modulo `7`, which makes the Galois action transitive;
* its discriminant is `8000² = 2¹² · 5⁶`, a square, so the Galois group is even;
* its resolvent sextic `X⁶ - 40X⁵ + 1000X⁴ - 20000X³ + 250000X² - 66400000X + 976000000` has the
  integral root `40` and is separable, since it is already separable modulo `7`; so the Galois
  group lies in a conjugate of `F₂₀`;
* modulo `3` it factors as `X (X² + X + 2) (X² + 2X + 2)`, of type `(1,2,2)`, which exhibits an
  element of order two in the Galois group, and so rules out the cyclic label `5T1`.

The discriminant and the sextic alone do not separate `5T1` from `5T2`: the cyclic quintic
`X⁵ + X⁴ - 4X³ - 3X² + 3X + 1` also has a square discriminant and a separable resolvent sextic
with an integral root. The factorization of type `(1,2,2)` is the datum that
does. Conversely, every factorization type of `X⁵ - 5X - 12` at a good prime is a cycle type of
`D₅ ≤ A₅`, so no factorization excludes `A₅`; that upper bound comes from the sextic
(`TauCeti.factorDegrees_do_not_distinguish_D5_A5`).

## Main results

* `TauCeti.discr_X_pow_five_sub_five_mul_X_sub_twelve`: the discriminant is `8000²`.
* `TauCeti.hasSexticRoot_X_pow_five_sub_five_mul_X_sub_twelve`: `40` is a root of the separable
  resolvent sextic.
* `Polynomial.factorDegrees_X_pow_five_sub_five_mul_X_sub_twelve_seven`: the reduction modulo `7`
  is irreducible.
* `Polynomial.factorDegrees_X_pow_five_sub_five_mul_X_sub_twelve_three`: the reduction modulo `3`
  has factor degrees `(1,2,2)`.
* `TauCeti.QuinticCertificate.check_X_pow_five_sub_five_mul_X_sub_twelve`: the dihedral-route
  certificate checks.
* `TauCeti.hasGaloisLabel_X_pow_five_sub_five_mul_X_sub_twelve`: `X⁵ - 5X - 12` has label `5T2`,
  and `TauCeti.natCard_gal_X_pow_five_sub_five_mul_X_sub_twelve`: its Galois group has order `10`.
* `TauCeti.factorDegrees_do_not_distinguish_D5_A5`: every factorization type of `X⁵ - 5X - 12`
  at a good prime is the full cycle type of an even permutation, although the Galois image does
  not contain `A₅`.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), 387–401.
-/

public section

open Polynomial

namespace TauCeti

/-- The discriminant of `X⁵ - 5X - 12` is `8000² = 2¹² · 5⁶`. -/
theorem discr_X_pow_five_sub_five_mul_X_sub_twelve :
    (X ^ 5 - 5 * X - 12 : ℤ[X]).discr = 8000 ^ 2 := by
  let f : ℤ[X] := X ^ 5 - 5 * X - 12
  let g : ℤ[X] := X ^ 4 - 1
  have hf : f.Monic := by dsimp [f]; monicity!
  have hdeg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  have hgdeg : g.natDegree = 4 := by dsimp [g]; compute_degree!
  have hder : f.derivative = C 5 * g := by
    simp [f, g]
    ring
  have hres := resultant_deriv (f := f) (natDegree_pos_iff_degree_pos.mp (by omega))
  rw [hdeg, hf.leadingCoeff, hder] at hres
  norm_num at hres
  -- Removing a multiple of the quartic leaves a linear polynomial in the resultant.
  have hred : f = C (-4) * (X - C (-3)) + g * X := by simp [f, g]; ring
  have hresult : f.resultant g 5 4 = (-4) ^ 4 * 80 := by
    rw [hred, resultant_add_mul_left _ _ _ 5 4 (by simp) (by omega)]
    rw [resultant_add_left_deg _ _ 1 4 4 (by compute_degree!)]
    rw [resultant_C_mul_left, resultant_X_sub_C_left _ _ _ (by omega)]
    norm_num [g, coeff_one]
  rw [resultant_C_mul_right, hresult] at hres
  norm_num at hres
  exact hres.symm

/-- The integer `40` is a root of the resolvent sextic of `X⁵ - 5X - 12`, and that sextic has
nonzero discriminant: its reduction modulo `7` is already separable. -/
theorem hasSexticRoot_X_pow_five_sub_five_mul_X_sub_twelve :
    HasSexticRoot (X ^ 5 - 5 * X - 12) 40 := by
  refine HasSexticRoot.mk isRoot_resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve ?_
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hsep :
      ((resolventSextic (X ^ 5 - 5 * X - 12)).map (Int.castRingHom (ZMod 7))).Separable := by
    rw [resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve]
    norm_num only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_ofNat]
    reduce_mod_char
    -- A Bézout identity between the reduced sextic and its derivative.
    refine ⟨3 * X ^ 4 - X ^ 3 - X ^ 2 - 3, 3 * X ^ 5 + 3 * X ^ 3 + 3 * X ^ 2 + 2, ?_⟩
    simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_ofNat, derivative_X,
      Nat.cast_ofNat, C_ofNat, zero_mul, zero_add, mul_one]
    ring_nf
    reduce_mod_char
  intro h
  exact ((monic_resolventSextic _).separable_map_zmod_iff_not_dvd_discr 7).mp hsep
    (h ▸ dvd_zero _)

end TauCeti

namespace Polynomial

local instance fact_prime_seven_dihedral : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The reduction of `X⁵ - 5X - 12` modulo `7` is irreducible: it has no root and no monic
quadratic factor in `𝔽₇`. -/
theorem irreducible_X_pow_five_sub_five_mul_X_sub_twelve_zmod_seven :
    Irreducible (X ^ 5 - 5 * X - 12 : (ZMod 7)[X]) := by
  have hf : (X ^ 5 - 5 * X - 12 : (ZMod 7)[X]) = X ^ 5 + C (-5) * X + C (-12) := by
    simp only [map_neg, C_ofNat]
    ring
  rw [hf]
  exact irreducible_X_pow_five_add_C_mul_X_add_C (by decide) (by decide)

/-- `X⁵ - 5X - 12` has a single irreducible factor of degree five modulo `7`. -/
@[simp] theorem factorDegrees_X_pow_five_sub_five_mul_X_sub_twelve_seven :
    (X ^ 5 - 5 * X - 12 : ℤ[X]).factorDegrees 7 = {5} := by
  rw [factorDegrees_eq_singleton_iff]
  norm_num only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_ofNat]
  exact ⟨irreducible_X_pow_five_sub_five_mul_X_sub_twelve_zmod_seven, by compute_degree!⟩

/-- The reduction of `X⁵ - 5X - 12` modulo `3` is `X (X² + X + 2) (X² + 2X + 2)`, with factor
degrees `{1, 2, 2}`. -/
@[simp] theorem factorDegrees_X_pow_five_sub_five_mul_X_sub_twelve_three :
    (X ^ 5 - 5 * X - 12 : ℤ[X]).factorDegrees 3 = {1, 2, 2} := by
  have h3 : (3 : (ZMod 3)[X]) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (ZMod 3)[X] 3
  have hd₁ : (X ^ 2 + X + 2 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
  have hd₂ : (X ^ 2 + 2 * X + 2 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
  let factors : Multiset (ZMod 3)[X] := {X, X ^ 2 + X + 2, X ^ 2 + 2 * X + 2}
  have hfactors : ∀ p ∈ factors, Irreducible p := by
    intro p hp
    simp only [factors, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact irreducible_X
    · refine irreducible_of_degree_le_three_of_not_isRoot (by simp [hd₁]) fun x => ?_
      simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_ofNat]
      fin_cases x <;> decide
    · refine irreducible_of_degree_le_three_of_not_isRoot (by simp [hd₂]) fun x => ?_
      simp only [IsRoot.def, eval_add, eval_pow, eval_mul, eval_X, eval_ofNat]
      fin_cases x <;> decide
  have hprod : (X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom (ZMod 3)) = factors.prod := by
    norm_num [factors]
    linear_combination (-X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 - 3 * X - 4 : (ZMod 3)[X]) * h3
  rw [factorDegrees_eq_map_natDegree_of_map_eq_prod hfactors hprod]
  simp [factors, hd₁, hd₂]

end Polynomial

namespace TauCeti

/-- The dihedral-route certificate for `X⁵ - 5X - 12` checks: it is irreducible modulo `7`, its
discriminant is `8000²`, `40` is a root of its separable resolvent sextic, and it has factor
degrees `(1,2,2)` modulo `3`. Neither `7` nor `3` divides the discriminant. -/
@[simp] theorem QuinticCertificate.check_X_pow_five_sub_five_mul_X_sub_twelve :
    (QuinticCertificate.dihedral 7 3 8000 40).check (X ^ 5 - 5 * X - 12) = true := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hgood7 : IsGoodPrime (X ^ 5 - 5 * X - 12) 7 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_five_mul_X_sub_twelve]
    decide
  have hgood3 : IsGoodPrime (X ^ 5 - 5 * X - 12) 3 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_five_mul_X_sub_twelve]
    decide
  rw [QuinticCertificate.check_eq_true_iff, QuinticCertificate.verifies_dihedral_iff]
  exact ⟨HasFactorDegrees.mk hgood7 factorDegrees_X_pow_five_sub_five_mul_X_sub_twelve_seven,
    discr_X_pow_five_sub_five_mul_X_sub_twelve,
    hasSexticRoot_X_pow_five_sub_five_mul_X_sub_twelve,
    HasFactorDegrees.mk hgood3 factorDegrees_X_pow_five_sub_five_mul_X_sub_twelve_three⟩

/-- **`X⁵ - 5X - 12` has Galois label `5T2`**: its Galois group over `ℚ` is the dihedral group
`D₅` of order `10`. -/
theorem hasGaloisLabel_X_pow_five_sub_five_mul_X_sub_twelve :
    HasGaloisLabel ((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ))
      (⟨1, by simp⟩ : TransitiveGroupIndex 5) := by
  have h := QuinticCertificate.check_sound (by monicity! : (X ^ 5 - 5 * X - 12 : ℤ[X]).Monic)
    QuinticCertificate.check_X_pow_five_sub_five_mul_X_sub_twelve
  rwa [QuinticCertificate.label_dihedral] at h

/-- The Galois group of `X⁵ - 5X - 12` over `ℚ` has order `10`. -/
theorem natCard_gal_X_pow_five_sub_five_mul_X_sub_twelve :
    Nat.card (X ^ 5 - 5 * X - 12 : ℚ[X]).Gal = 10 := by
  have hmap : (X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ) = X ^ 5 - 5 * X - 12 := by
    simp
  rw [← hmap, hasGaloisLabel_X_pow_five_sub_five_mul_X_sub_twelve.natCard_gal,
    natCard_referenceSubgroup_five_one]

attribute [local instance] Gal.splits_ℚ_ℂ

local instance factSplitsSplittingField_dihedral (f : ℚ[X]) :
    Fact ((f.map (algebraMap ℚ f.SplittingField)).Splits) :=
  ⟨SplittingField.splits f⟩

open scoped Classical in
/-- **Factorization types do not separate `D₅` from `A₅`.** At every prime `p` not dividing the
discriminant, the degrees of the irreducible factors of `X⁵ - 5X - 12` modulo `p` are the full
cycle type of an even permutation of its complex roots; yet its Galois image, the dihedral group
of order `10`, does not contain the alternating group. So no factorization type of this
polynomial, at any good prime, rules out the label `5T4`: factorization types only exhibit
elements of the Galois image, and every element of `D₅` lies in `A₅`. The upper bound that
excludes `A₅` comes from the root `40` of the resolvent sextic instead. -/
theorem factorDegrees_do_not_distinguish_D5_A5 :
    (∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ (X ^ 5 - 5 * X - 12 : ℤ[X]).discr →
      ∃ σ ∈ alternatingGroup (((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ)).rootSet ℂ),
        σ.fullCycleType = (X ^ 5 - 5 * X - 12 : ℤ[X]).factorDegrees p) ∧
      ¬ alternatingGroup (((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ)).rootSet ℂ) ≤
        (Gal.galActionHom ((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ)) ℂ).range := by
  have hf : (X ^ 5 - 5 * X - 12 : ℤ[X]).Monic := by monicity!
  have hdeg : (X ^ 5 - 5 * X - 12 : ℤ[X]).natDegree = 5 := by compute_degree!
  have hroots :
      Nat.card (((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ)).rootSet ℂ) = 5 := by
    rw [natCard_rootSet_complex_eq_natDegree
      (by rw [discr_X_pow_five_sub_five_mul_X_sub_twelve]; norm_num), hdeg]
  -- The label `5T2` makes the Galois image even, read in the splitting field; transport along
  -- the identification of the roots there with the complex roots preserves signs.
  have hA₀ :=
    hasGaloisLabel_X_pow_five_sub_five_mul_X_sub_twelve.range_le_alternatingGroup_iff.mpr
      referenceSubgroup_five_one_le_alternatingGroup
  have hA : (Gal.galActionHom ((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ)) ℂ).range ≤
      alternatingGroup (((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ)).rootSet ℂ) := by
    rintro _ ⟨g, rfl⟩
    rw [Gal.galActionHom_eq_permCongr (E := ((X ^ 5 - 5 * X - 12 : ℤ[X]).map
      (Int.castRingHom ℚ)).SplittingField) _ ℂ g, Equiv.Perm.mem_alternatingGroup,
      Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.mp (hA₀ ⟨g, rfl⟩)
  refine ⟨fun p _ hp => ?_, fun hle => ?_⟩
  · obtain ⟨σ, hσ, htype⟩ := exists_mem_range_galActionHom_fullCycleType_eq_factorDegrees hf p hp
    exact ⟨σ, hA hσ, htype⟩
  · have : Nontrivial (((X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ)).rootSet ℂ) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hroots]; norm_num)
    have hmap : (X ^ 5 - 5 * X - 12 : ℤ[X]).map (Int.castRingHom ℚ) = X ^ 5 - 5 * X - 12 := by
      simp
    have hcard := Subgroup.card_le_of_le hle
    rw [nat_card_alternatingGroup, hroots, natCard_galActionHom_range, hmap,
      natCard_gal_X_pow_five_sub_five_mul_X_sub_twelve] at hcard
    norm_num [Nat.factorial] at hcard

end TauCeti
