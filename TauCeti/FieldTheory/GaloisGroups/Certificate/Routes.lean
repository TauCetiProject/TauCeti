/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Evidence
public import TauCeti.FieldTheory.GaloisGroups.Label

import TauCeti.FieldTheory.GaloisGroups.Quintic
import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification

/-!
# Soundness of the quintic certificate routes

A monic integral quintic `f` that is irreducible over `ℚ` carries exactly one of the
transitive-group labels `5T1`, …, `5T5`. This file shows how finite evidence about `f` determines
that label. Each theorem is one sound route from evidence to a label:

| route | evidence besides irreducibility over `ℚ` | label |
|---|---|---|
| dihedral | `disc f` a square, a root of the separable sextic, factor degrees `(1,2,2)` | `5T2` |
| Frobenius | `disc f` not a square, a root of the separable sextic | `5T3` |
| alternating | `disc f` a square, factor degrees `(1,1,3)` | `5T4` |
| symmetric | factor degrees `(2,3)` | `5T5` |

Here "the separable sextic" is the integral resolvent sextic `TauCeti.resolventSextic f` with
nonzero discriminant, as packaged by `TauCeti.HasSexticRoot`, and factor degrees are taken modulo
a prime not dividing `disc f`, as packaged by `TauCeti.HasFactorDegrees`. Irreducibility over `ℚ`
is what makes the Galois action transitive; finite evidence for it is an irreducible reduction
modulo some prime, through `TauCeti.HasFactorDegrees.irreducible_map_rat`, and the degree is then
read off by `TauCeti.HasFactorDegrees.sum_eq_natDegree`.

The discriminant and the sextic bound the Galois group from above, while a factorization modulo
a good prime exhibits an element of the Galois group and so bounds it from below. The discriminant
and the sextic alone do not separate `5T1` from `5T2`; in the dihedral route, factor degrees
`(1,2,2)` exhibit an element of order two, which the cyclic group of order five does not have.
In the alternating route, factor degrees `(1,1,3)` exhibit an element of order three, which
leaves only `5T4` and `5T5`, and the square discriminant excludes `5T5`. In the symmetric route,
factor degrees `(2,3)` exhibit an element whose cube is a transposition, and a transitive group of
prime degree containing a transposition is the full symmetric group.

## Main results

* `TauCeti.hasGaloisLabel_five_one_of_isSquare_discr_of_hasSexticRoot`: the dihedral route.
* `TauCeti.hasGaloisLabel_five_two_of_not_isSquare_discr_of_hasSexticRoot`: the Frobenius route.
* `TauCeti.hasGaloisLabel_five_three_of_isSquare_discr_of_hasFactorDegrees`: the alternating
  route.
* `TauCeti.hasGaloisLabel_five_four_of_hasFactorDegrees`: the symmetric route.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), §2.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, §6.3.
-/

public section

open Polynomial

namespace TauCeti

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

variable {f : ℤ[X]} {q : ℕ}

/-- The degree of a monic integral quintic is still five over `ℚ`. -/
private theorem natDegree_map_rat_eq_five (hf : f.Monic) (hdeg : f.natDegree = 5) :
    (f.map (Int.castRingHom ℚ)).natDegree = 5 := by
  rwa [hf.natDegree_map]

/-- **The dihedral route: `5T2`.** A monic integral quintic, irreducible over `ℚ`, whose
discriminant is a square, whose resolvent sextic is separable with an integral root, and whose
factor degrees modulo a prime not dividing its discriminant are `(1,2,2)`, has the dihedral group
of order ten on its five roots. -/
theorem hasGaloisLabel_five_one_of_isSquare_discr_of_hasSexticRoot (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdisc : IsSquare f.discr) {a : ℤ} (ha : HasSexticRoot f a)
    (hq : HasFactorDegrees f q {1, 2, 2}) :
    HasGaloisLabel (f.map (Int.castRingHom ℚ)) (⟨1, by simp⟩ : TransitiveGroupIndex 5) := by
  have hdeg : f.natDegree = 5 := by
    rw [← hq.sum_eq_natDegree hf]
    decide
  refine (hasGaloisLabel_five_zero_or_one_of_isSquare_discr_of_isRoot (hf.map _)
    (by simp) (PerfectField.separable_of_irreducible hirr) hirr
    (natDegree_map_rat_eq_five hf hdeg) (hf.isSquare_discr_map_rat_iff.mpr hdisc)
    ha.separable_specialize_rat ha.isRoot_specialize_rat).resolve_left fun h0 => ?_
  -- The cyclic group of order five has no element of order two.
  obtain ⟨σ, hσ, h2⟩ := hq.exists_orderOf_eq_two hf
  have h := h0.orderOf_dvd_natCard_referenceSubgroup hσ
  rw [h2, natCard_referenceSubgroup_five_zero] at h
  norm_num at h

/-- **The Frobenius route: `5T3`.** A monic integral quintic, irreducible over `ℚ`, whose
discriminant is not a square, and whose resolvent sextic is separable with an integral root, has
the Frobenius group of order twenty on its five roots. -/
theorem hasGaloisLabel_five_two_of_not_isSquare_discr_of_hasSexticRoot (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hdeg : f.natDegree = 5)
    (hdisc : ¬ IsSquare f.discr) {a : ℤ} (ha : HasSexticRoot f a) :
    HasGaloisLabel (f.map (Int.castRingHom ℚ)) (⟨2, by simp⟩ : TransitiveGroupIndex 5) :=
  hasGaloisLabel_five_two_of_not_isSquare_discr_of_isRoot (hf.map _) (by simp) hirr
    (natDegree_map_rat_eq_five hf hdeg) (hf.isSquare_discr_map_rat_iff.not.mpr hdisc)
    ha.separable_specialize_rat ha.isRoot_specialize_rat

/-- **The alternating route: `5T4`.** A monic integral quintic, irreducible over `ℚ`, whose
discriminant is a square, and whose factor degrees modulo a prime not dividing its discriminant
are `(1,1,3)`, has the alternating group on its five roots. -/
theorem hasGaloisLabel_five_three_of_isSquare_discr_of_hasFactorDegrees (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdisc : IsSquare f.discr) (hq : HasFactorDegrees f q {1, 1, 3}) :
    HasGaloisLabel (f.map (Int.castRingHom ℚ)) (⟨3, by simp⟩ : TransitiveGroupIndex 5) := by
  have hdeg : f.natDegree = 5 := by
    rw [← hq.sum_eq_natDegree hf]
    decide
  obtain ⟨j, hj, -⟩ := existsUnique_hasGaloisLabel_five
    (PerfectField.separable_of_irreducible hirr) hirr (natDegree_map_rat_eq_five hf hdeg)
  -- The square discriminant leaves the even labels `5T1`, `5T2` and `5T4`.
  have hpar := (hj.isSquare_discr_iff_five (hf.map _) (by simp)).mp
    (hf.isSquare_discr_map_rat_iff.mpr hdisc)
  -- An element of order three rules out `5T1` and `5T2`, of orders `5` and `10`.
  obtain ⟨σ, hσ, h3⟩ := hq.exists_orderOf_eq_three hf
  have h := hj.orderOf_dvd_natCard_referenceSubgroup hσ
  rw [h3] at h
  obtain ⟨b, hb⟩ := j
  dsimp only at hpar
  obtain rfl : b = 3 := by
    rw [numTransitiveGroups_five] at hb
    interval_cases b
    · rw [natCard_referenceSubgroup_five_zero] at h
      norm_num at h
    · rw [natCard_referenceSubgroup_five_one] at h
      norm_num at h
    all_goals omega
  exact hj

/-- **The symmetric route: `5T5`.** A monic integral quintic, irreducible over `ℚ`, whose factor
degrees modulo a prime not dividing its discriminant are `(2,3)`, has the full symmetric group on
its five roots. -/
theorem hasGaloisLabel_five_four_of_hasFactorDegrees (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hq : HasFactorDegrees f q {2, 3}) :
    HasGaloisLabel (f.map (Int.castRingHom ℚ)) (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
  have hdeg : f.natDegree = 5 := by
    rw [← hq.sum_eq_natDegree hf]
    decide
  obtain ⟨hq', hgood, hfac⟩ := hq.exists_fact
  let _ := hq'
  have hgood' := (isGoodPrime_iff f q).mp hgood
  -- The factor degrees `(2,3)` exhibit a transposition, so the Galois image is everything.
  have hsurj := surjective_galActionHom_of_prime_natDegree hf hirr (hdeg ▸ Nat.prime_five) q
    hgood' (by rw [hfac]; decide) (by rw [hfac]; decide)
  exact hasGaloisLabel_five_four_of_surjective_galActionHom
    (PerfectField.separable_of_irreducible hirr) hirr (natDegree_map_rat_eq_five hf hdeg) hsurj

end TauCeti
