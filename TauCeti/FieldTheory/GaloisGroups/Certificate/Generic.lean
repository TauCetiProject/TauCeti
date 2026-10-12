/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Evidence
public import TauCeti.FieldTheory.GaloisGroups.Quintic

/-!
# A generic symmetric quintic from two factorizations

An irreducible reduction of a monic quintic makes its Galois action transitive. A second good
reduction with factor degrees `(1,1,1,2)` exhibits a transposition. In prime degree these two
facts force the full symmetric group, so the polynomial has label `5T5`. The result applies to
any monic integral polynomial with these two pieces of factorization evidence.

## Main result

* `TauCeti.hasGaloisLabel_five_four_of_factorDegrees_five_and_one_one_one_two`:
  two factorizations certify the symmetric quintic label.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- A monic integral quintic that is irreducible at one good prime and has factor degrees
`(1,1,1,2)` at another good prime has Galois label `5T5`. -/
theorem hasGaloisLabel_five_four_of_factorDegrees_five_and_one_one_one_two
    {f : ℤ[X]} {p q : ℕ} (hf : f.Monic)
    (hp : HasFactorDegrees f p {5}) (hq : HasFactorDegrees f q {1, 1, 1, 2}) :
    HasGaloisLabel (f.map (Int.castRingHom ℚ))
      (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
  have hirr : Irreducible (f.map (Int.castRingHom ℚ)) := hp.irreducible_map_rat hf
  have hdeg : f.natDegree = 5 := by
    simpa using (hp.sum_eq_natDegree hf).symm
  obtain ⟨hqprime, hgood, hfac⟩ := hq.exists_fact
  let _ := hqprime
  have htwo : (f.factorDegrees q).count 2 = 1 := by
    rw [hfac]
    decide
  have hodd : ∀ k ∈ f.factorDegrees q, k ≠ 2 → Odd k := by
    rw [hfac]
    intro k hk hne
    simp_all
  have hsurj := surjective_galActionHom_of_prime_natDegree hf hirr
    (hdeg ▸ Nat.prime_five) q ((isGoodPrime_iff f q).mp hgood) htwo hodd
  exact hasGaloisLabel_five_four_of_surjective_galActionHom
    (PerfectField.separable_of_irreducible hirr) hirr
    (by rw [hf.natDegree_map (Int.castRingHom ℚ)]; exact hdeg) hsurj

end TauCeti
