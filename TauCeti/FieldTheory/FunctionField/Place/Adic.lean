/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# Places attached to the height-one primes of a Dedekind model

Let `k` be a field and `R` a Dedekind domain which is a `k`-algebra, with fraction field `F`.
Every height-one prime `p` of `R` gives a place of `F / k`: the normalized `p`-adic valuation
is surjective onto `ℤᵐ⁰` by `IsDedekindDomain.HeightOneSpectrum.valuation_surjective`, and it is
trivial on `k` because the nonzero constants are units of `R`. Distinct primes give distinct
places, and the residue field of the place is the residue field `R ⧸ p` of the prime, so the
degree of the place is `[R ⧸ p : k]`.

This is the affine half of the place vocabulary: applied to `R = k[X]` and `F = k(x)` it produces
the finite places of the rational function field (Stichtenoth, *Algebraic Function Fields and
Codes*, second edition, Proposition 1.2.1(a)), and applied to the integral closure of `k[x]` in a
function field it produces the places of a chosen affine model.

## Main definitions

* `TauCeti.Place.ofPrime`: the place of `F / k` attached to a height-one prime of `R`.
* `TauCeti.Place.integersOfPrimeEquiv`: the valuation ring of that place is the localization of `R`
  at `p`.

Reduction `R → F_P` at an adic place is the canonical map
`algebraMap R (TauCeti.Place.ofPrime k F p).ResidueField`.

## Main results

* `TauCeti.Place.ofPrime_injective`: distinct height-one primes give distinct places.
* `TauCeti.Place.quotientAlgEquivResidueFieldOfPrime`: the residue field of `Place.ofPrime k F p`
  is `R ⧸ p`, as a `k`-algebra. `TauCeti.Place.quotientAlgEquivResidueFieldOfPrime_mk` computes
  this equivalence on quotient representatives, and `TauCeti.Place.degree_ofPrime` reads off the
  degree of the place. The valuation ring is the localization of `R` at `p`, so this is Mathlib's
  `IsLocalization.AtPrime.equivQuotMaximalIdeal`.
* `TauCeti.Place.ord_ofPrime_algebraMap`: the order of `r : R` at the place is the multiplicity of
  `p` in `(r)`; `TauCeti.Place.isUniformizer_ofPrime_algebraMap` specializes this to a generator of
  `p`, which is therefore a prime element for the place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.1 and III.2.
* The adic valuation of a height-one prime, its valuation subring and the identification of that
  subring with the localization at the prime are
  `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` (María Inés de Frutos-Fernández); the
  residue field of a localization at a prime is
  `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`.
-/

public section

noncomputable section

open scoped WithZero

open IsDedekindDomain

namespace TauCeti

universe u v w

variable (k : Type u) (F : Type v) {R : Type w} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F]

namespace Place

/-- The place of `F / k` attached to a height-one prime `p` of a Dedekind `k`-algebra `R` with
fraction field `F`: the normalized `p`-adic valuation. -/
def ofPrime (p : HeightOneSpectrum R) : Place k F where
  valuation := p.valuation F
  valuation_surjective := p.valuation_surjective F
  isTrivialOn := inferInstance

@[simp]
theorem valuation_ofPrime (p : HeightOneSpectrum R) : (ofPrime k F p).valuation = p.valuation F :=
  (rfl)

variable (p : HeightOneSpectrum R)

theorem integers_ofPrime :
    (ofPrime k F p).integers = HeightOneSpectrum.valuationSubringAtPrime F p := by
  rw [integers_def, valuation_ofPrime,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]

/-- Distinct height-one primes give distinct places: the place remembers its prime. -/
theorem ofPrime_injective : Function.Injective (ofPrime k F (R := R)) := fun p q h => by
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  rw [← valuation_ofPrime k F p, ← valuation_ofPrime k F q, h]

/-! ### Orders of elements of `R` -/

theorem algebraMap_mem_integers_ofPrime (r : R) : algebraMap R F r ∈ (ofPrime k F p).integers :=
  ((ofPrime k F p).mem_integers_iff).mpr (by rw [valuation_ofPrime]; exact p.valuation_le_one r)

/-- The valuation of the place of `p` extends the `p`-adic valuation of the model. -/
theorem valuation_ofPrime_algebraMap (r : R) :
    (ofPrime k F p).valuation (algebraMap R F r) = p.intValuation r := by
  rw [valuation_ofPrime, HeightOneSpectrum.valuation_of_algebraMap]

/-- The elements of the model with a zero at the place of `p` are exactly the elements of `p`. -/
theorem valuation_ofPrime_algebraMap_lt_one_iff {r : R} :
    (ofPrime k F p).valuation (algebraMap R F r) < 1 ↔ r ∈ p.asIdeal := by
  rw [valuation_ofPrime, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem ord_ofPrime_algebraMap_nonneg (r : R) : 0 ≤ (ofPrime k F p).ord (algebraMap R F r) :=
  ((ofPrime k F p).mem_integers_iff_ord_nonneg).mp (algebraMap_mem_integers_ofPrime k F p r)

/-- An element of `R` has positive order at `ofPrime k F p` exactly when it lies in `p`. -/
theorem ord_ofPrime_algebraMap_pos_iff_mem {r : R} (hr : r ≠ 0) :
    0 < (ofPrime k F p).ord (algebraMap R F r) ↔ r ∈ p.asIdeal := by
  have hr' : algebraMap R F r ≠ 0 := IsFractionRing.to_map_eq_zero_iff.ne.mpr hr
  rw [← (ofPrime k F p).valuation_lt_one_iff_ord_pos hr',
    valuation_ofPrime_algebraMap_lt_one_iff]

/-- The order of an element of `R` at the place `ofPrime k F p` is the multiplicity of `p` in the
principal ideal it generates. -/
theorem ord_ofPrime_algebraMap {r : R} (hr : r ≠ 0) :
    (ofPrime k F p).ord (algebraMap R F r) = multiplicity p.asIdeal (Ideal.span {r}) := by
  have hr' : algebraMap R F r ≠ 0 := IsFractionRing.to_map_eq_zero_iff.ne.mpr hr
  rw [(ofPrime k F p).ord_eq_iff_valuation_eq_exp_neg hr', valuation_ofPrime_algebraMap,
    p.intValuation_eq_exp_neg_multiplicity hr]

/-- A generator of `p` is a prime element for the place `ofPrime k F p`, i.e. a uniformizer for its
normalized valuation. -/
theorem isUniformizer_ofPrime_algebraMap {π : R} (h : p.asIdeal = Ideal.span {π}) :
    (ofPrime k F p).valuation.IsUniformizer (algebraMap R F π) := by
  have hπ : π ≠ 0 := by
    rintro rfl
    exact p.ne_bot (by simp [h])
  have hπ' : algebraMap R F π ≠ 0 := IsFractionRing.to_map_eq_zero_iff.ne.mpr hπ
  rw [isUniformizer_iff_ord_eq_one, (ofPrime k F p).ord_eq_iff_valuation_eq_exp_neg hπ',
    valuation_ofPrime_algebraMap, p.intValuation_singleton hπ h]

/-! ### The residue field -/

/-- `R` maps into the valuation ring of `ofPrime k F p`: every element is integral there. -/
instance : Algebra R (ofPrime k F p).integers :=
  ((algebraMap R F).codRestrict _ (algebraMap_mem_integers_ofPrime k F p)).toAlgebra

instance : IsScalarTower R (ofPrime k F p).integers F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : IsScalarTower k R (ofPrime k F p).integers :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (IsScalarTower.algebraMap_apply k R F c)

/-- **The valuation ring of an adic place is the localization at its prime**, by
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring`. -/
def integersOfPrimeEquiv :
    HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[R] (ofPrime k F p).integers :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (integers_ofPrime k F p).symm)) fun _ => rfl

/-- The equivalence from the localization at `p` to the integers of the adic place preserves
the underlying element of `F`. -/
@[simp]
theorem integersOfPrimeEquiv_apply (x : HeightOneSpectrum.valuationSubringAtPrime F p) :
    ((integersOfPrimeEquiv k F p x : (ofPrime k F p).integers) : F) = x :=
  (rfl)

instance : IsLocalization.AtPrime ((ofPrime k F p).integers) p.asIdeal :=
  IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl (integersOfPrimeEquiv k F p)

variable {k F p}

/-- Reduction from `R` at an adic place vanishes exactly on its prime ideal. -/
@[simp]
theorem algebraMap_residueField_ofPrime_eq_zero_iff {r : R} :
    algebraMap R (ofPrime k F p).ResidueField r = 0 ↔ r ∈ p.asIdeal := by
  rw [algebraMap_residueField, IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff ((ofPrime k F p).integers) p.asIdeal r

variable (k F p)

/-- **The residue field of an adic place is the residue field of its prime**: reduction at
`ofPrime k F p` identifies `R ⧸ p` with `F_P`, as `k`-algebras. Its valuation ring is the
localization of `R` at `p`, so this is Mathlib's
`IsLocalization.AtPrime.equivQuotMaximalIdeal`, restricted from `R` to `k`. -/
def quotientAlgEquivResidueFieldOfPrime : (R ⧸ p.asIdeal) ≃ₐ[k] (ofPrime k F p).ResidueField :=
  haveI := p.isMaximal
  (IsLocalization.AtPrime.equivQuotMaximalIdeal p.asIdeal
    ((ofPrime k F p).integers)).restrictScalars k

@[simp]
theorem quotientAlgEquivResidueFieldOfPrime_mk (r : R) :
    quotientAlgEquivResidueFieldOfPrime k F p (Ideal.Quotient.mk p.asIdeal r) =
      algebraMap R (ofPrime k F p).ResidueField r := by
  have := p.isMaximal
  rw [← Ideal.Quotient.algebraMap_eq]
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal p.asIdeal ((ofPrime k F p).integers)
  exact (AlgEquiv.restrictScalars_apply k e _).trans (e.commutes r)

/-- The degree of an adic place is the degree of the residue field of its prime. -/
theorem degree_ofPrime : (ofPrime k F p).degree = Module.finrank k (R ⧸ p.asIdeal) := by
  rw [degree_eq_finrank, ← (quotientAlgEquivResidueFieldOfPrime k F p).toLinearEquiv.finrank_eq]

instance finiteDimensional_residueField_ofPrime [Module.Finite k (R ⧸ p.asIdeal)] :
    Module.Finite k (ofPrime k F p).ResidueField :=
  Module.Finite.equiv (quotientAlgEquivResidueFieldOfPrime k F p).toLinearEquiv

end Place

end TauCeti
