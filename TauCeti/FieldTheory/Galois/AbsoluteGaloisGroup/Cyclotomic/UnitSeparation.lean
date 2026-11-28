/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Rational

/-!
# Separation by powers of the cyclotomic character

Reduction of the `p`-adic cyclotomic image modulo `p` has index in `(ℤ/pℤ)ˣ` dividing
`[K : ℚ]`. Lifting a generator of this cyclic residue image gives a single Galois element
at which all the powers with exponent smaller than the residue image order are separated
by units. The separation problem comes from `New.Selmer.exists_isUnit_cyclotomicChar_pow_sub_one`
in `grh/src/New/Congruences/FirstOrder/DenominatorBound.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace TauCeti

/-- The residue image of the cyclotomic character has index dividing the degree of the
base field over `ℚ`, with the degree set to zero in infinite dimension. -/
theorem index_map_range_localCyclotomicCharacter_toZMod_dvd_finrank (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharZero K] :
    ((localCyclotomicCharacter p K).range.map
      (Units.map (PadicInt.toZMod (p := p)).toMonoidHom)).index ∣
      Module.finrank ℚ K := by
  by_cases hK : FiniteDimensional ℚ K
  swap
  · rw [Module.finrank_of_not_finite hK]
    exact dvd_zero _
  have h := relIndex_range_localCyclotomicCharacter_dvd_finrank p ℚ K
  rw [MonoidHom.range_eq_top.mpr (surjective_localCyclotomicCharacter_rat p),
    Subgroup.relIndex_top_right] at h
  exact ((localCyclotomicCharacter p K).range.index_map_dvd
    (IsLocalRing.surjective_units_map_of_local_ringHom PadicInt.toZMod
      (ZMod.ringHom_surjective _) inferInstance)).trans h

/-- There is a Galois element whose cyclotomic character to the power `k` differs from `1`
by a unit exactly when `k` is not divisible by the size of the residue image. The same
Galois element works for every exponent. -/
theorem exists_isUnit_localCyclotomicCharacter_pow_sub_one_iff (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] :
    ∃ g : Field.absoluteGaloisGroup K, ∀ k : ℕ,
      IsUnit ((localCyclotomicCharacter p K g : ℤ_[p]) ^ k - 1) ↔
        ¬ Nat.card ((localCyclotomicCharacter p K).range.map
          (Units.map (PadicInt.toZMod (p := p)).toMonoidHom)) ∣ k := by
  let f := (Units.map (PadicInt.toZMod (p := p)).toMonoidHom).comp (localCyclotomicCharacter p K)
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic f.range)
  obtain ⟨g, hg⟩ := a.property
  have horder : orderOf (f g) = Nat.card f.range := by
    rw [hg]
    exact (orderOf_injective f.range.subtype Subtype.coe_injective a).trans ha
  refine ⟨g, fun k ↦ ?_⟩
  rw [← MonoidHom.range_comp, ← horder, orderOf_dvd_iff_pow_eq_one]
  -- Unit membership is reflected by reduction; the unit and its underlying residue
  -- have the same power test by injectivity of `Units.val`.
  rw [← isUnit_map_iff PadicInt.toZMod, isUnit_iff_ne_zero, map_sub, map_pow, map_one,
    sub_ne_zero]
  exact not_congr (Units.ext_iff (u := (f g) ^ k) (v := 1)).symm

/-- If `(n - 1) [K : ℚ] < p - 1`, one Galois element separates the first `n` powers of the
`p`-adic cyclotomic character: every positive difference of exponents below `n` gives
a unit after subtracting `1` from the corresponding power. -/
theorem exists_isUnit_localCyclotomicCharacter_pow_sub_one (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [CharZero K] [FiniteDimensional ℚ K] {n : ℕ}
    (hn : (n - 1) * Module.finrank ℚ K < p - 1) :
    ∃ g : Field.absoluteGaloisGroup K, ∀ k : ℕ, 0 < k → k < n →
      IsUnit ((localCyclotomicCharacter p K g : ℤ_[p]) ^ k - 1) := by
  let H := (localCyclotomicCharacter p K).range.map
    (Units.map (PadicInt.toZMod (p := p)).toMonoidHom)
  have hidx : H.index ∣ Module.finrank ℚ K :=
    index_map_range_localCyclotomicCharacter_toZMod_dvd_finrank p K
  have hcard : H.index * Nat.card H = p - 1 := by
    simpa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
      using H.index_mul_card
  have hle : n ≤ Nat.card H := by
    by_contra! hlt
    have h := Nat.mul_le_mul (Nat.le_of_dvd Module.finrank_pos hidx)
      (Nat.le_sub_one_of_lt hlt)
    rw [hcard, mul_comm (Module.finrank ℚ K)] at h
    exact hn.not_ge h
  obtain ⟨g, hg⟩ := exists_isUnit_localCyclotomicCharacter_pow_sub_one_iff p K
  exact ⟨g, fun k hk hkn ↦ (hg k).mpr (Nat.not_dvd_of_pos_of_lt hk (hkn.trans_le hle))⟩

end TauCeti
