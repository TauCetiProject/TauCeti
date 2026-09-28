/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower
public import TauCeti.NumberTheory.NumberField.Cyclotomic.SeventhCyclotomic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import Mathlib.Tactic.NormNum.Prime

/-!
# Frobenius at three in the seventh cyclotomic field

The residue of three generates the units modulo seven. Its square generates the subgroup fixing
the quadratic intermediate field. At a prime above three, restriction to that field has residue
degree two, and the relative Frobenius is the square of the absolute Frobenius. In particular the
relative Frobenius has order three, not six. This gives a concrete check on the power in the
Frobenius tower law.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section
noncomputable section

open Ideal NumberField IsCyclotomicExtension IntermediateField
open scoped NumberField

namespace NumberField.Chebotarev

open TauCeti.NumberField

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

private instance : IsGalois ℚ L := IsCyclotomicExtension.isGalois {7} ℚ L

private theorem seven_not_mem_of_absNorm_three
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = 3) : (7 : 𝓞 ℚ) ∉ 𝔭.asIdeal := by
  intro h
  have hdvd := (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mp h
  rw [h𝔭] at hdvd
  norm_num at hdvd

private theorem isUnramifiedAt_of_absNorm_three
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = 3)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
  IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem L 7
    (seven_not_mem_of_absNorm_three 𝔭 h𝔭) Q

/-- At every prime above three, the arithmetic Frobenius is the automorphism with exponent
three, rather than its inverse. -/
theorem isArithFrobAt_frobeniusThreeSeven
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = 3)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    IsArithFrobAt (𝓞 ℚ) (frobeniusThreeSeven (L := L)) Q := by
  have hm := seven_not_mem_of_absNorm_three 𝔭 h𝔭
  have _ : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
    isUnramifiedAt_of_absNorm_three 𝔭 h𝔭 Q
  apply (TauCeti.NumberField.isArithFrobAt_iff_galEquivZMod_eq_absNorm 𝔭 hm Q _).2
  rw [galEquivZMod_frobeniusThreeSeven, h𝔭]
  rfl

/-- At a prime above three, the prime below it in the quadratic fixed field has residue degree
two over `ℚ`. -/
theorem inertiaDeg_under_frobeniusThreeSevenQuadraticField
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = 3)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    (Q.under (𝓞 ↥(frobeniusThreeSevenQuadraticField (L := L)))).inertiaDeg (𝓞 ℚ) = 2 := by
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  have _ : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
    isUnramifiedAt_of_absNorm_three 𝔭 h𝔭 Q
  rw [frobeniusThreeSevenQuadraticField_eq_fixedField,
    Ideal.inertiaDeg_under_fixedField_zpowers_pow Q hQ
      (isArithFrobAt_frobeniusThreeSeven 𝔭 h𝔭 Q) 2,
    orderOf_frobeniusThreeSeven]
  decide

/-- At a prime above three, raising the base from `ℚ` to the quadratic intermediate field
squares the arithmetic Frobenius. Its image in `Gal(L/ℚ)` is the automorphism with exponent
`3² = 2` modulo seven, of order three. -/
theorem exists_isArithFrobAt_and_restrictScalars_eq_frobeniusThreeSeven_sq_and_orderOf_eq_three
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = 3)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    ∃ τ : L ≃ₐ[(frobeniusThreeSevenQuadraticField (L := L))] L,
      IsArithFrobAt (𝓞 (frobeniusThreeSevenQuadraticField (L := L))) τ Q ∧
        AlgEquiv.restrictScalars ℚ τ = frobeniusThreeSeven (L := L) ^ 2 ∧
        orderOf τ = 3 := by
  rw [frobeniusThreeSevenQuadraticField_eq_fixedField]
  let E := fixedField (Subgroup.zpowers (frobeniusThreeSeven (L := L) ^ 2))
  have : IsScalarTower ℚ E L := E.isScalarTower_mid'
  have : IsGalois E L := IsGalois.of_fixed_field L
    (Subgroup.zpowers (frobeniusThreeSeven (L := L) ^ 2))
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  have hσ := isArithFrobAt_frobeniusThreeSeven 𝔭 h𝔭 Q
  have _ : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
    isUnramifiedAt_of_absNorm_three 𝔭 h𝔭 Q
  have hdeg := inertiaDeg_under_frobeniusThreeSevenQuadraticField 𝔭 h𝔭 Q
  rw [frobeniusThreeSevenQuadraticField_eq_fixedField] at hdeg
  obtain ⟨τ, hτ⟩ := NumberField.exists_isArithFrobAt E Q hQ
  have hpower : AlgEquiv.restrictScalars ℚ τ = frobeniusThreeSeven (L := L) ^ 2 := by
    simpa only [E, hdeg] using
      (NumberField.restrictScalars_eq_pow_inertiaDeg (K := ℚ) (M := E) hσ hτ)
  refine ⟨τ, hτ, hpower, ?_⟩
  rw [← orderOf_injective (AlgEquiv.restrictScalarsHom ℚ)
    (AlgEquiv.restrictScalars_injective ℚ), AlgEquiv.restrictScalarsHom_apply,
    hpower, orderOf_frobeniusThreeSeven_sq]

end NumberField.Chebotarev

end
