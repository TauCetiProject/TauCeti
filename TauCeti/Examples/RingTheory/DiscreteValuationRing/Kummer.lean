/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime
import TauCeti.RingTheory.DiscreteValuationRing.Kummer

/-!
# Tests for Kummer extensions of a discrete valuation ring

For a height-one prime `v` of `ℤ` containing a prime number `p`, the localization
`ℤ_(v) = Localization.AtPrime v.asIdeal` is `ℤ_(p)`: a discrete valuation ring with fraction field
`ℚ` and uniformizer `p`
(`IsDedekindDomain.HeightOneSpectrum.irreducible_natCast_localizationAtPrime`).
A field `L` generated over `ℚ` by a square root `α` of `p` is `ℚ(√p)`, and the results of
`TauCeti.RingTheory.DiscreteValuationRing.Kummer` (Stacks, Lemma 15.116.2) compute the integral
closure of `ℤ_(p)` in it.

* For `p = 3` the integral closure is `ℤ_(3)[√3]`, a discrete valuation ring whose maximal ideal
  has ramification index `2` over `ℤ_(3)`.
* For `p = 2` the same holds: `[ℚ(√2) : ℚ] = 2`, the integral closure is `ℤ_(2)[√2]`, a discrete
  valuation ring with ramification index `2`, and `ℚ(√2)` is totally ramified with respect to
  `ℤ_(2)`. Since the residue characteristic `2` divides the ramification index, `ℚ(√2)` is not
  tamely ramified with respect to `ℤ_(2)`.
-/

open IntermediateField IsDedekindDomain IsLocalRing Polynomial

namespace TauCeti

variable (v : HeightOneSpectrum ℤ) {L : Type*} [Field L] [Algebra ℚ L]
  [Algebra (Localization.AtPrime v.asIdeal) L] [IsScalarTower (Localization.AtPrime v.asIdeal) ℚ L]

/-- *test_kummer_three*: for `A = ℤ_(3)` and `L = ℚ(√3)`, the integral closure of `A` in `L` is
`A[√3]`, a discrete valuation ring whose maximal ideal has ramification index `2` over `A`. -/
example (hv : (3 : ℤ) ∈ v.asIdeal) {α : L} (hα : α ^ 2 = 3) (hgen : ℚ⟮α⟯ = ⊤) :
    integralClosure (Localization.AtPrime v.asIdeal) L =
        Algebra.adjoin (Localization.AtPrime v.asIdeal) {α} ∧
      IsDiscreteValuationRing (integralClosure (Localization.AtPrime v.asIdeal) L) ∧
      ∀ (P : Ideal (integralClosure (Localization.AtPrime v.asIdeal) L)) [P.IsMaximal],
        P.ramificationIdx (Localization.AtPrime v.asIdeal) = 2 := by
  have hπ := v.irreducible_natCast_localizationAtPrime Nat.prime_three (by exact_mod_cast hv)
  have hα' : α ^ 2 = algebraMap (Localization.AtPrime v.asIdeal) L (3 : ℕ) := by
    rw [map_natCast, hα, Nat.cast_ofNat]
  exact ⟨IsDiscreteValuationRing.integralClosure_eq_adjoin_of_pow_eq_of_irreducible
      (K := ℚ) hπ two_ne_zero hα' hgen,
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      (K := ℚ) hπ two_ne_zero hα' hgen,
    fun P _ ↦ IsDiscreteValuationRing.ramificationIdx_eq_of_pow_eq_of_irreducible
      (K := ℚ) hπ two_ne_zero hα' hgen P⟩

/-- *test_kummer_wild*: for `A = ℤ_(2)` and `L = ℚ(√2)`, clauses (1)–(5) of Stacks,
Lemma 15.116.2 hold: `[L : ℚ] = 2`, the integral closure of `A` in `L` is `A[√2]`, where `√2`
has minimal polynomial `X ^ 2 - 2` over `A`, it is a discrete valuation ring, its maximal ideal
has ramification index `2` over `A`, and `L` is totally ramified with respect to `A`. But `L` is
not tamely ramified with respect to `A`. -/
example (hv : (2 : ℤ) ∈ v.asIdeal) {α : L} (hα : α ^ 2 = 2) (hgen : ℚ⟮α⟯ = ⊤) :
    Module.finrank ℚ L = 2 ∧
      integralClosure (Localization.AtPrime v.asIdeal) L =
        Algebra.adjoin (Localization.AtPrime v.asIdeal) {α} ∧
      minpoly (Localization.AtPrime v.asIdeal) α = X ^ 2 - C 2 ∧
      IsDiscreteValuationRing (integralClosure (Localization.AtPrime v.asIdeal) L) ∧
      (∀ (P : Ideal (integralClosure (Localization.AtPrime v.asIdeal) L)) [P.IsMaximal],
        P.ramificationIdx (Localization.AtPrime v.asIdeal) = 2) ∧
      Algebra.IsTotallyRamifiedWRT (Localization.AtPrime v.asIdeal) L ∧
      ¬ Algebra.IsTamelyRamifiedWRT (Localization.AtPrime v.asIdeal) L := by
  have hπ := v.irreducible_natCast_localizationAtPrime Nat.prime_two (by exact_mod_cast hv)
  have hα' : α ^ 2 = algebraMap (Localization.AtPrime v.asIdeal) L (2 : ℕ) := by
    rw [map_natCast, hα, Nat.cast_ofNat]
  have := FaithfulSMul.trans (Localization.AtPrime v.asIdeal) ℚ L
  refine ⟨IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible
      (K := ℚ) hπ two_ne_zero hα' hgen,
    IsDiscreteValuationRing.integralClosure_eq_adjoin_of_pow_eq_of_irreducible
      (K := ℚ) hπ two_ne_zero hα' hgen,
    by simpa using
      IsDiscreteValuationRing.minpoly_eq_of_pow_eq_of_irreducible hπ two_ne_zero hα',
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      (K := ℚ) hπ two_ne_zero hα' hgen,
    fun P _ ↦ IsDiscreteValuationRing.ramificationIdx_eq_of_pow_eq_of_irreducible
      (K := ℚ) hπ two_ne_zero hα' hgen P,
    IsDiscreteValuationRing.isTotallyRamifiedWRT_of_pow_eq_of_irreducible
      (K := ℚ) hπ two_ne_zero hα' hgen, ?_⟩
  -- The ramification index `2` is the uniformizer, so it vanishes in the residue field.
  rw [IsDiscreteValuationRing.isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible
    (K := ℚ) hπ two_ne_zero hα' hgen, ← map_natCast (Ideal.Quotient.mk _),
    Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_maximalIdeal _).mpr hπ.not_isUnit)]
  exact not_isUnit_zero

end TauCeti
