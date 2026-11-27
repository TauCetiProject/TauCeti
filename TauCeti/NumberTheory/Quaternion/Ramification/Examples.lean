/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Quaternion.Ramification.Discriminant
import TauCeti.NumberTheory.LocalField.Quaternion.Examples

/-!
# Worked examples: the ramified places of a quaternion algebra

This file checks the ramification predicates of `TauCeti.NumberTheory.Quaternion.Ramification.Basic`
on two classical examples.

**Hamilton's quaternions.** Over every number field, `ℍ[F,-1,-1]` is ramified at every real
place, since `-1` is negative there. Over `ℚ` it is ramified at the prime `p` exactly when
`p = 2`: the symbol `(-1, -1)_{ℚ_p}` is `+1` for odd `p` by Hensel's lemma and `-1` at `p = 2`.
So `ℍ[ℚ,-1,-1]` is ramified at exactly one finite and one real place, and `1 + 1 = 2` is even, as
the parity theorem `even_card_ramifiedFinitePlaces_add_card_ramifiedRealPlaces` demands. Its
discriminant is `D = 2`, which here equals the ramification bound `2`.

**Split symbols.** `ℍ[F,1,b]` is isomorphic to `M₂(F)`, so it is ramified nowhere and its
discriminant is the unit ideal. For `ℍ[ℚ,1,7]` the ramification bound is `14` while `D = 1`: the
discriminant is not the radical of the bound.

## Main results

* `TauCeti.QuaternionAlgebra.isRamifiedAtPrime_neg_one_neg_one_iff`: `ℍ[ℚ,-1,-1]` is ramified at
  `p` exactly when `p = 2`.
* `TauCeti.QuaternionAlgebra.ramifiedFinitePlaces_neg_one_neg_one_rat`: its only ramified finite
  place is the place above `2`.
* `TauCeti.QuaternionAlgebra.ramifiedRealPlaces_neg_one_neg_one`: `ℍ[F,-1,-1]` is ramified at
  every real place.
* `TauCeti.QuaternionAlgebra.discNat_neg_one_neg_one`: `ℍ[ℚ,-1,-1]` has discriminant `D = 2`.
* `TauCeti.QuaternionAlgebra.ramifiedFinitePlaces_one_left`,
  `TauCeti.QuaternionAlgebra.ramifiedRealPlaces_one_left`: `ℍ[F,1,b]` is ramified nowhere.
* `TauCeti.QuaternionAlgebra.discIdeal_one_left`, `TauCeti.QuaternionAlgebra.discNat_one_left`:
  `ℍ[F,1,b]` has unit discriminant.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021),
  Chapter 14.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace

namespace TauCeti.QuaternionAlgebra

variable {F : Type*} [Field F] [NumberField F]

/-! ### Hamilton's quaternions -/

/-- **Hamilton's quaternions over `ℚ`** are ramified at the prime `p` exactly when `p = 2`. -/
theorem isRamifiedAtPrime_neg_one_neg_one_iff (p : ℕ) [Fact p.Prime] :
    IsRamifiedAtPrime (-1) (-1) p ↔ p = 2 := by
  have hneg : Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom (-1) = -1 := Units.ext (by simp)
  rw [isRamifiedAtPrime_def, hneg]
  rcases eq_or_ne p 2 with rfl | hp
  · simpa using hilbertSymbol_neg_one_neg_one_padicTwo
  · simp only [Padic.hilbertSymbol_neg_one_neg_one_of_ne_two p hp, hp, iff_false]
    decide

/-- The only finite place at which Hamilton's quaternions `ℍ[ℚ,-1,-1]` are ramified is the place
above `2`. -/
theorem ramifiedFinitePlaces_neg_one_neg_one_rat :
    ramifiedFinitePlaces (-1 : ℚˣ) (-1) =
      {(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩} := by
  ext v
  obtain ⟨⟨p, hp⟩, rfl⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.surjective v
  have : Fact p.Prime := ⟨hp⟩
  rw [mem_ramifiedFinitePlaces, ← isRamifiedAtPrime_iff_isRamifiedAt, Finset.mem_singleton,
    isRamifiedAtPrime_neg_one_neg_one_iff]
  refine ⟨fun h ↦ by subst h; rfl, fun h ↦ ?_⟩
  exact congrArg (fun q : Nat.Primes ↦ (q : ℕ))
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h)

open Classical in
/-- Hamilton's quaternions `ℍ[F,-1,-1]` are ramified at every real place of `F`. -/
theorem ramifiedRealPlaces_neg_one_neg_one :
    ramifiedRealPlaces (-1 : Fˣ) (-1) = Finset.univ := by
  ext w
  simp [isRamifiedAtReal_iff]

open Classical in
/-- Hamilton's quaternions over `ℚ` are ramified at one finite and one real place, `1 + 1 = 2`
places in all. -/
example : (ramifiedFinitePlaces (-1 : ℚˣ) (-1)).card = 1 ∧
    (ramifiedRealPlaces (-1 : ℚˣ) (-1)).card = 1 := by
  refine ⟨by rw [ramifiedFinitePlaces_neg_one_neg_one_rat, Finset.card_singleton], ?_⟩
  rw [ramifiedRealPlaces_neg_one_neg_one, Finset.card_univ, Fintype.card_eq_one_iff]
  exact ⟨⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩

/-- **Hamilton's quaternions over `ℚ`** have discriminant `D = 2`. -/
theorem discNat_neg_one_neg_one : discNat (-1 : ℚˣ) (-1) = 2 := by
  rw [discNat_def, ramifiedFinitePlaces_neg_one_neg_one_rat, Finset.prod_singleton]
  exact Rat.HeightOneSpectrum.natGenerator_primesEquiv_symm ⟨2, Nat.prime_two⟩

/-- The ramification bound of Hamilton's quaternions over `ℚ` is `2`, equal to their
discriminant. -/
example : ramificationBound (-1 : ℚˣ) (-1) = 2 := by
  norm_num [ramificationBound_def]

/-! ### Split symbols -/

variable (b : Fˣ)

/-- The split symbol algebra `ℍ[F,1,b]` is ramified at no finite place. -/
theorem ramifiedFinitePlaces_one_left : ramifiedFinitePlaces (1 : Fˣ) b = ∅ := by
  ext v
  simp [isRamifiedAt_def]

/-- The split symbol algebra `ℍ[F,1,b]` is ramified at no real place. -/
theorem ramifiedRealPlaces_one_left : ramifiedRealPlaces (1 : Fˣ) b = ∅ := by
  ext w
  simp [isRamifiedAtReal_iff]

/-- The split symbol algebra `ℍ[F,1,b]` has unit discriminant. -/
theorem discIdeal_one_left : discIdeal (1 : Fˣ) b = 1 :=
  discIdeal_eq_one_iff.2 (ramifiedFinitePlaces_one_left b)

/-- The split symbol algebra `ℍ[ℚ,1,b]` has discriminant `D = 1`. -/
theorem discNat_one_left (b : ℚˣ) : discNat 1 b = 1 :=
  discNat_eq_one_iff.2 (ramifiedFinitePlaces_one_left b)

/-- For the split symbol algebra `ℍ[ℚ,1,7]` the ramification bound is `14`, but the discriminant
is `D = 1`. -/
example : ramificationBound 1 (Units.mk0 (7 : ℚ) (by norm_num)) = 14 ∧
    discNat 1 (Units.mk0 (7 : ℚ) (by norm_num)) = 1 := by
  refine ⟨?_, discNat_one_left _⟩
  norm_num [ramificationBound_def]

end TauCeti.QuaternionAlgebra
