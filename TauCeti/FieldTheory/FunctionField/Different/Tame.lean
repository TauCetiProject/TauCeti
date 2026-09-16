/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.RingTheory.DedekindDomain.Different

/-!
# The different exponent of a tame or wild place

Let `F' / k'` be an extension of the algebraic function field `F / k` with `F' / F` finite and
separable, and let `P'` be a place of `F' / k'` over `P = P'.restrict k F`.  Dedekind's different
theorem (Stichtenoth, Theorem 3.5.1) says that `d(P' ∣ P) ≥ e(P' ∣ P) - 1` always, with equality
exactly when the place is **tame**.  The inequality is
`TauCeti.Place.ramificationIdx_le_differentExponent_add_one`; this file supplies the second part:
`e(P' ∣ P) = d(P' ∣ P) + 1` holds exactly at the places where the residue extension of the local
model is separable and the residue characteristic does not divide `e(P' ∣ P)`, and at every other
place `d(P' ∣ P) ≥ e(P' ∣ P)` (Stichtenoth, Corollary 3.5.5).

Everything is read on the local model `𝒪_P ⊆ 𝒪'_P` of
`TauCeti/FieldTheory/FunctionField/Different/Basic.lean`, where the different exponent lives, so
the two conditions are stated for the centre `𝔓` of `P'` on `𝒪'_P` over the maximal ideal of the
discrete valuation ring `𝒪_P`, whose residue ring is the residue field of `P`
(`TauCeti.Place.center_restrict_asIdeal_eq_maximalIdeal`).  This is the same ideal-theoretic
reading of the residue extension that `TauCeti.Place.differentExponent_eq_zero_iff` uses for
unramifiedness.  The theorem behind it is `TauCeti.pow_ramificationIdx_dvd_differentIdeal_iff`.

Stichtenoth assumes a perfect constant field, under which residue extensions are separable and
tameness is the single condition that the characteristic does not divide `e(P' ∣ P)`.  No such
assumption is made here: over an imperfect residue field an inseparable residue extension already
forces `d(P' ∣ P) ≥ e(P' ∣ P)`, even at `e(P' ∣ P) = 1`, so the separability condition is part of
the statement.

## Main results

* `TauCeti.Place.ramificationIdx_eq_differentExponent_add_one_iff`: **Dedekind's different theorem,
  second part** (Stichtenoth, Theorem 3.5.1(b)), in the subtraction-free form
  `e(P' ∣ P) = d(P' ∣ P) + 1`, holding exactly at the tame places;
  `TauCeti.Place.ramificationIdx_eq_differentExponent_add_one` is its tame direction.
* `TauCeti.Place.ramificationIdx_le_differentExponent_iff` and
  `TauCeti.Place.ramificationIdx_le_differentExponent`: `e(P' ∣ P) ≤ d(P' ∣ P)` exactly at the
  places that are not tame, in particular at every wild place (Stichtenoth, Corollary 3.5.5).
* `TauCeti.Divisor.coeff_different_add_one_eq_ramificationIdx_iff`,
  `TauCeti.Divisor.coeff_different_add_one_eq_ramificationIdx` and
  `TauCeti.Divisor.ramificationIdx_le_coeff_different`: the same statements read on the different
  divisor.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.1 and Corollary 3.5.5.
-/

public section

open IsDedekindDomain

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k F] [Algebra F F'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
variable [Algebra.IsSeparable F F']

attribute [local instance 10] Place.algebraIntegersExtension
  Place.isScalarTowerIntegersExtension

namespace Place

variable (k F) (P' : Place k' F')

/-- **The different exponent reaches the ramification index exactly at the non-tame places**
(Stichtenoth, Theorem 3.5.1(b) and Corollary 3.5.5): the different exponent of `P'` is at least its
ramification index exactly when
the place is not tame, that is, when the residue extension of the local model is inseparable or the
ramification index vanishes in the residue field of `P`.

The residue extension is read on the local model, between the residue ring of the maximal ideal of
the discrete valuation ring `𝒪_P` — which is the residue field of `P`, by
`TauCeti.Place.center_restrict_asIdeal_eq_maximalIdeal` — and the residue ring of the centre of
`P'` on `𝒪'_P`. -/
theorem ramificationIdx_le_differentExponent_iff :
    ramificationIdx F P' ≤ differentExponent k F P' ↔
      ¬ Algebra.IsSeparable
          (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
          (integralClosure ((P'.restrict k F).integers) F' ⧸
            (centerIntegralClosure k F P').asIdeal) ∨
        ((ramificationIdx F P' : ℕ) :
          ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) =
          0 := by
  have hS := algebraMap_mem_integers_of_mem_integralClosure k F P'
  have hpbot : IsLocalRing.maximalIdeal ((P'.restrict k F).integers) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field _
  have hmax : (centerIntegralClosure k F P').asIdeal.IsMaximal :=
    (centerIntegralClosure k F P').isPrime.isMaximal (centerIntegralClosure k F P').ne_bot
  have hidx : (centerIntegralClosure k F P').asIdeal.ramificationIdx
      ((P'.restrict k F).integers) = ramificationIdx F P' := by
    rw [centerIntegralClosure_def]
    exact (ramificationIdx_eq_ramificationIdx_center
      (R := ((P'.restrict k F).integers)) k F P' hS).symm
  rw [← pow_dvd_differentIdeal_iff_le_differentExponent, ← hidx]
  exact pow_ramificationIdx_dvd_differentIdeal_iff _ hpbot _

/-- **The different exponent of a wild place** (Stichtenoth, Corollary 3.5.5): if the ramification
index of `P'` vanishes in the residue field of `P`, then `e(P' ∣ P) ≤ d(P' ∣ P)`.  Unlike the tame
equality, this needs no hypothesis on the residue extension. -/
theorem ramificationIdx_le_differentExponent
    (hwild : ((ramificationIdx F P' : ℕ) :
      ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) = 0) :
    ramificationIdx F P' ≤ differentExponent k F P' :=
  (ramificationIdx_le_differentExponent_iff k F P').mpr (.inr hwild)

/-- **Dedekind's different theorem, second part** (Stichtenoth, Theorem 3.5.1(b)): the different
exponent of `P'` is exactly one less than its ramification index if and only if the place is tame,
that is, the residue extension of the local model is separable and the ramification index is
invertible in the residue field of `P`.  It is stated as `e(P' ∣ P) = d(P' ∣ P) + 1` so that no
truncated subtraction of natural numbers appears.

Over an imperfect residue field the separability condition is genuinely needed: an inseparable
residue extension already forces `d(P' ∣ P) ≥ e(P' ∣ P)`, by
`TauCeti.Place.ramificationIdx_le_differentExponent_iff`. -/
theorem ramificationIdx_eq_differentExponent_add_one_iff :
    ramificationIdx F P' = differentExponent k F P' + 1 ↔
      Algebra.IsSeparable
          (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
          (integralClosure ((P'.restrict k F).integers) F' ⧸
            (centerIntegralClosure k F P').asIdeal) ∧
        ((ramificationIdx F P' : ℕ) :
          ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) ≠
          0 := by
  have hle := ramificationIdx_le_differentExponent_add_one k F P'
  have hiff : ramificationIdx F P' = differentExponent k F P' + 1 ↔
      ¬ ramificationIdx F P' ≤ differentExponent k F P' := ⟨fun _ ↦ by omega, fun _ ↦ by omega⟩
  rw [hiff, ramificationIdx_le_differentExponent_iff, not_or, not_not]

/-- **Dedekind's different theorem in the tame case** (Stichtenoth, Theorem 3.5.1(b)): at a place
`P'` whose local model has separable residue extension and whose ramification index is invertible
in the residue field of `P`, the different exponent is exactly one less than the ramification
index.  It is stated as `e(P' ∣ P) = d(P' ∣ P) + 1` so that no truncated subtraction of natural
numbers appears. -/
theorem ramificationIdx_eq_differentExponent_add_one
    [hsep : Algebra.IsSeparable
      (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
      (integralClosure ((P'.restrict k F).integers) F' ⧸ (centerIntegralClosure k F P').asIdeal)]
    (htame : ((ramificationIdx F P' : ℕ) :
      ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) ≠ 0) :
    ramificationIdx F P' = differentExponent k F P' + 1 :=
  (ramificationIdx_eq_differentExponent_add_one_iff k F P').mpr ⟨hsep, htame⟩

end Place

namespace Divisor

/-- **The different divisor at a wild place** (Stichtenoth, Corollary 3.5.5): if the
ramification index of `P'` vanishes in the residue field of `P`, then the coefficient of `P'` in
`Diff(F'/F)` is at least `e(P' ∣ P)`. -/
theorem ramificationIdx_le_coeff_different (hF : IsFunctionField k F) (P' : Place k' F')
    (hwild : ((Place.ramificationIdx F P' : ℕ) :
      ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) = 0) :
    (Place.ramificationIdx F P' : ℤ) ≤ (different k' F' hF).coeff P' := by
  rw [coeff_different]
  exact_mod_cast Place.ramificationIdx_le_differentExponent k F P' hwild

/-- **The different divisor detects tameness** (Stichtenoth, Theorem 3.5.1(b) and Remark 3.4.4):
the coefficient of `P'` in `Diff(F'/F)` is `e(P' ∣ P) - 1`, stated without subtraction, exactly
when the residue extension of the local model is separable and the ramification index is
invertible in the residue field of `P`. -/
theorem coeff_different_add_one_eq_ramificationIdx_iff (hF : IsFunctionField k F)
    (P' : Place k' F') :
    (different k' F' hF).coeff P' + 1 = (Place.ramificationIdx F P' : ℤ) ↔
      Algebra.IsSeparable
          (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
          (integralClosure ((P'.restrict k F).integers) F' ⧸
            (Place.centerIntegralClosure k F P').asIdeal) ∧
        ((Place.ramificationIdx F P' : ℕ) :
          ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) ≠
          0 := by
  rw [coeff_different, ← Place.ramificationIdx_eq_differentExponent_add_one_iff, eq_comm]
  norm_cast

/-- **The different divisor at a tame place** (Stichtenoth, Theorem 3.5.1(b) and Remark 3.4.4):
the coefficient of a tame place `P'` in `Diff(F'/F)` is `e(P' ∣ P) - 1`, stated without
subtraction. -/
theorem coeff_different_add_one_eq_ramificationIdx (hF : IsFunctionField k F) (P' : Place k' F')
    [Algebra.IsSeparable
      (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
      (integralClosure ((P'.restrict k F).integers) F' ⧸
        (Place.centerIntegralClosure k F P').asIdeal)]
    (htame : ((Place.ramificationIdx F P' : ℕ) :
      ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) ≠ 0) :
    (different k' F' hF).coeff P' + 1 = (Place.ramificationIdx F P' : ℤ) :=
  (coeff_different_add_one_eq_ramificationIdx_iff hF P').mpr ⟨‹_›, htame⟩

end Divisor

end TauCeti
