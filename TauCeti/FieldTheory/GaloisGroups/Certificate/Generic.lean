/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Evidence
public import TauCeti.FieldTheory.GaloisGroups.Quintic
public import TauCeti.FieldTheory.GaloisGroups.Symmetric.Basic

/-!
# Prime-degree symmetric Galois groups and generic quintics from two factorizations

For a monic integral polynomial `f : ℤ[X]` and a prime `d`, an irreducible reduction modulo a good
prime `p` (`HasFactorDegrees f p {d}`) proves irreducibility over `ℚ`, forces `f.natDegree = d`,
and makes the Galois action transitive. A second good reduction modulo `q` whose factor degrees `t`
have a single `2` and odd remaining entries — in particular `Multiset.replicate (d - 2) 1 + {2}` —
exhibits a transposition. Together they force the full symmetric Galois group `S_d`, hence
non-solvability for `d ≥ 5` and the quintic transitive-group label `5T5` at `d = 5`.

## Main results

* `TauCeti.hasFullSymmetricGaloisGroup_of_prime_factorDegrees`: full symmetric Galois group `S_d`
  in prime degree `d` from `{d}` and a good reduction with a single `2` and odd remaining degrees.
* `TauCeti.not_isSolvable_gal_of_prime_factorDegrees`: non-solvability consequence for `d ≥ 5`.
* `TauCeti.hasFullSymmetricGaloisGroup_of_prime_and_replicate_one_add_two`: specialization to the
  `{d}` and `{1, …, 1, 2}` Frobenius-cycle pattern.
* `TauCeti.hasGaloisLabel_five_four_of_factorDegrees_five_and_one_one_one_two`: degree-five
  specialization certifying the symmetric quintic label `5T5`.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- **Full symmetric Galois group in prime degree from two good-prime factor-degree patterns.**
Let `f : ℤ[X]` be monic and `d` be prime. If `f` is irreducible modulo a good prime `p`
(`HasFactorDegrees f p {d}`) and modulo a good prime `q` has factor degrees `t` with a single `2`
and all other entries odd (`HasFactorDegrees f q t`), then `f.map (Int.castRingHom ℚ)` has full
symmetric Galois group `S_d`. -/
theorem hasFullSymmetricGaloisGroup_of_prime_factorDegrees {f : ℤ[X]} (hf : f.Monic)
    {d p q : ℕ} {t : Multiset ℕ} (hd : d.Prime)
    (hp : HasFactorDegrees f p {d}) (hq : HasFactorDegrees f q t)
    (htwo : t.count 2 = 1) (hodd : ∀ k ∈ t, k ≠ 2 → Odd k) :
    (f.map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup := by
  have hirr : Irreducible (f.map (Int.castRingHom ℚ)) := hp.irreducible_map_rat hf
  have hdeg : f.natDegree = d := by simpa using (hp.sum_eq_natDegree hf).symm
  obtain ⟨hq_fact, hq_good, hq_fac⟩ := hq.exists_fact
  let _ := hq_fact
  rw [hasFullSymmetricGaloisGroup_iff_separable_and_surjective_galActionHom ℂ]
  refine ⟨hirr.separable, surjective_galActionHom_of_prime_natDegree hf hirr
    (hdeg ▸ hd) q ((isGoodPrime_iff f q).mp hq_good) ?_ ?_⟩
  · rwa [hq_fac]
  · rwa [hq_fac]

/-- For a prime `d ≥ 5`, a monic polynomial `f : ℤ[X]` with `HasFactorDegrees f p {d}` and
`HasFactorDegrees f q t` where `t` has a single `2` and odd remaining entries has non-solvable
Galois group over `ℚ`. -/
theorem not_isSolvable_gal_of_prime_factorDegrees {f : ℤ[X]} (hf : f.Monic)
    {d p q : ℕ} {t : Multiset ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hp : HasFactorDegrees f p {d}) (hq : HasFactorDegrees f q t)
    (htwo : t.count 2 = 1) (hodd : ∀ k ∈ t, k ≠ 2 → Odd k) :
    ¬ Group.IsSolvable (f.map (Int.castRingHom ℚ)).Gal := by
  have hdeg : (f.map (Int.castRingHom ℚ)).natDegree = d := by
    rw [hf.natDegree_map]
    simpa using (hp.sum_eq_natDegree hf).symm
  exact (hasFullSymmetricGaloisGroup_of_prime_factorDegrees hf hd hp hq htwo hodd).not_isSolvable
    (hdeg ▸ hd5)

/-- The multiset `Multiset.replicate n 1 + {2}` contains `2` with multiplicity `1` and has every
other entry odd. -/
theorem count_two_and_odd_replicate_one_add_two (n : ℕ) :
    (Multiset.replicate n 1 + {2}).count 2 = 1 ∧
      ∀ k ∈ Multiset.replicate n 1 + ({2} : Multiset ℕ), k ≠ 2 → Odd k := by
  refine ⟨by simp [Multiset.count_replicate], fun k hk hk2 ↦ ?_⟩
  rcases Multiset.mem_add.mp hk with hk1 | hk2'
  · rw [Multiset.eq_of_mem_replicate hk1]
    exact odd_one
  · exact absurd (Multiset.mem_singleton.mp hk2') hk2

/-- **The `{d}` + `{1, …, 1, 2}` Frobenius-cycle certificate in prime degree.** If a monic
polynomial `f : ℤ[X]` is irreducible of prime degree `d` modulo a good prime `p` and splits modulo
a good prime `q` into `d - 2` linear factors and one irreducible quadratic factor, then
`f.map (Int.castRingHom ℚ)` has full symmetric Galois group `S_d`. -/
theorem hasFullSymmetricGaloisGroup_of_prime_and_replicate_one_add_two {f : ℤ[X]} (hf : f.Monic)
    {d p q : ℕ} (hd : d.Prime) (hp : HasFactorDegrees f p {d})
    (hq : HasFactorDegrees f q (Multiset.replicate (d - 2) 1 + {2})) :
    (f.map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup :=
  let ⟨htwo, hodd⟩ := count_two_and_odd_replicate_one_add_two (d - 2)
  hasFullSymmetricGaloisGroup_of_prime_factorDegrees hf hd hp hq htwo hodd

/-- A monic integral quintic that is irreducible at one good prime and has factor degrees
`(1,1,1,2)` at another good prime has Galois label `5T5`. -/
theorem hasGaloisLabel_five_four_of_factorDegrees_five_and_one_one_one_two
    {f : ℤ[X]} {p q : ℕ} (hf : f.Monic)
    (hp : HasFactorDegrees f p {5}) (hq : HasFactorDegrees f q {1, 1, 1, 2}) :
    HasGaloisLabel (f.map (Int.castRingHom ℚ))
      (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
  have hq' : HasFactorDegrees f q (Multiset.replicate (5 - 2) 1 + {2}) := by
    convert hq using 1
    decide
  have hsym := hasFullSymmetricGaloisGroup_of_prime_and_replicate_one_add_two
    hf Nat.prime_five hp hq'
  have hdeg : (f.map (Int.castRingHom ℚ)).natDegree = 5 := by
    rw [hf.natDegree_map]
    simpa using (hp.sum_eq_natDegree hf).symm
  exact hasGaloisLabel_five_four_of_surjective_galActionHom hsym.separable
    (hp.irreducible_map_rat hf) hdeg
    ((hasFullSymmetricGaloisGroup_iff_separable_and_surjective_galActionHom ℂ).mp hsym).2

end TauCeti
