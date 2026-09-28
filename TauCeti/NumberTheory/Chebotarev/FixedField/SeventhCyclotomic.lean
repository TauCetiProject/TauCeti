/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
public import TauCeti.NumberTheory.NumberField.Frobenius.Tower
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import Mathlib.RingTheory.ZMod.UnitsCyclic
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

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

private instance : IsGalois ℚ L := IsCyclotomicExtension.isGalois {7} ℚ L

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem seven_not_mem_of_absNorm_three
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = 3) : (7 : 𝓞 ℚ) ∉ 𝔭.asIdeal := by
  intro h
  have hdvd := (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mp h
  rw [h𝔭] at hdvd
  norm_num at hdvd

/-- The cyclotomic automorphism with exponent three modulo seven. -/
def frobeniusThreeSeven : L ≃ₐ[ℚ] L :=
  (Rat.galEquivZMod 7 L).symm (Units.mk0 (3 : ZMod 7) (by decide))

/-- The exponent of `frobeniusThreeSeven` on a primitive seventh root of unity is three. -/
theorem autToPow_frobeniusThreeSeven :
    ((zeta_spec 7 ℚ L).autToPow ℚ (frobeniusThreeSeven (L := L)) : ZMod 7) = 3 := by
  rw [(zeta_spec 7 ℚ L).autToPow_eq_unitsMap_galEquivZMod dvd_rfl,
    ZMod.unitsMap_self, MonoidHom.id_apply]
  simp only [frobeniusThreeSeven, MulEquiv.apply_symm_apply, Units.val_mk0]

/-- The cyclotomic automorphism with exponent three modulo seven has order six. -/
theorem orderOf_frobeniusThreeSeven : orderOf (frobeniusThreeSeven (L := L)) = 6 := by
  rw [frobeniusThreeSeven, ← (Rat.galEquivZMod 7 L).orderOf_eq,
    MulEquiv.apply_symm_apply, ← orderOf_units]
  exact (orderOf_eq_iff (by decide : 0 < 6)).mpr (by decide)

/-- The fixed field of the square of the Frobenius at three is the quadratic intermediate field
of a seventh cyclotomic extension. -/
def frobeniusThreeSevenQuadraticField : IntermediateField ℚ L :=
  fixedField (Subgroup.zpowers (frobeniusThreeSeven (L := L) ^ 2))

/-- An element is in the quadratic fixed field precisely when the square of the Frobenius at
three fixes it. -/
@[simp]
theorem mem_frobeniusThreeSevenQuadraticField_iff (x : L) :
    x ∈ frobeniusThreeSevenQuadraticField (L := L) ↔
      (frobeniusThreeSeven (L := L) ^ 2) x = x := by
  let σ := frobeniusThreeSeven (L := L) ^ 2
  change x ∈ fixedField (Subgroup.zpowers σ) ↔ σ x = x
  rw [mem_fixedField_iff]
  constructor
  · intro hx
    exact hx σ (Subgroup.mem_zpowers σ)
  · intro hx τ hτ
    have hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) x := by
      simpa [MulAction.mem_stabilizer_iff] using hx
    have hs := Subgroup.zpowers_le_of_mem hσ hτ
    simpa [MulAction.mem_stabilizer_iff] using hs

/-- The square of the Frobenius with exponent three has order three. -/
theorem orderOf_frobeniusThreeSeven_sq :
    orderOf (frobeniusThreeSeven (L := L) ^ 2) = 3 := by
  rw [orderOf_pow, orderOf_frobeniusThreeSeven]
  decide

/-- The square of the Frobenius at three acts with exponent two on a primitive seventh root. -/
@[simp]
theorem autToPow_frobeniusThreeSeven_sq :
    ((zeta_spec 7 ℚ L).autToPow ℚ (frobeniusThreeSeven (L := L)) : ZMod 7) ^ 2 = 2 := by
  rw [autToPow_frobeniusThreeSeven]
  decide

/-- The field fixed by the square of the Frobenius at three has degree two over `ℚ`. -/
@[simp] theorem finrank_frobeniusThreeSevenQuadraticField :
    Module.finrank ℚ (frobeniusThreeSevenQuadraticField (L := L)) = 2 := by
  have hrel : Module.finrank (frobeniusThreeSevenQuadraticField (L := L)) L = 3 := by
    rw [frobeniusThreeSevenQuadraticField, IntermediateField.finrank_fixedField_eq_card,
      Nat.card_zpowers, orderOf_frobeniusThreeSeven_sq]
  have htot : Module.finrank ℚ L = 6 := by
    rw [IsCyclotomicExtension.Rat.finrank 7 L,
      Nat.totient_prime (by norm_num : Nat.Prime 7)]
  have htower := Module.finrank_mul_finrank ℚ (frobeniusThreeSevenQuadraticField (L := L)) L
  rw [hrel, htot] at htower
  omega

/-- At every prime above three, the arithmetic Frobenius is the automorphism with exponent
three, rather than its inverse. -/
theorem frobeniusThreeSeven_isArithFrobAt
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = 3)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    IsArithFrobAt (𝓞 ℚ) (frobeniusThreeSeven (L := L)) Q := by
  have hm := seven_not_mem_of_absNorm_three 𝔭 h𝔭
  have _ : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
    IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem L 7 hm Q
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  let _ : Finite (𝓞 L ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQ
  let σ := arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) Q
  have hσ : IsArithFrobAt (𝓞 ℚ) σ Q := IsArithFrobAt.arithFrobAt _ _ _
  have hζ := zeta_spec 7 ℚ L
  have h := hσ.autToPow_eq_absNorm hζ 𝔭 hm Q
  rw [hζ.autToPow_eq_unitsMap_galEquivZMod dvd_rfl,
    ZMod.unitsMap_self, MonoidHom.id_apply, h𝔭] at h
  have hσeq : σ = frobeniusThreeSeven (L := L) := by
    apply (Rat.galEquivZMod 7 L).injective
    apply Units.ext
    simpa only [frobeniusThreeSeven, MulEquiv.apply_symm_apply, Units.val_mk0,
      Nat.cast_ofNat] using h
  exact hσeq ▸ hσ

/-- A Frobenius at a prime above three has residue degree two in the quadratic fixed field. -/
private theorem inertiaDeg_under_frobeniusThreeSevenQuadraticField
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 ℚ) Q]
    (hσ : IsArithFrobAt (𝓞 ℚ) (frobeniusThreeSeven (L := L)) Q) :
    (Q.under (𝓞 ↥(frobeniusThreeSevenQuadraticField (L := L)))).inertiaDeg (𝓞 ℚ) = 2 := by
  rw [frobeniusThreeSevenQuadraticField,
    Ideal.inertiaDeg_under_fixedField_eq_relIndex Q hQ _ hσ,
    ← zpow_natCast, Subgroup.relIndex_zpowers_zpow,
    orderOf_frobeniusThreeSeven]
  decide

/-- At a prime above three, raising the base from `ℚ` to the quadratic intermediate field
squares the arithmetic Frobenius. Its image in `Gal(L/ℚ)` is the automorphism with exponent
`3² = 2` modulo seven, of order three. -/
theorem exists_isArithFrobAt_seventhCyclotomic
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : Ideal.absNorm 𝔭.asIdeal = 3)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    ∃ τ : L ≃ₐ[(frobeniusThreeSevenQuadraticField (L := L))] L,
      IsArithFrobAt (𝓞 (frobeniusThreeSevenQuadraticField (L := L))) τ Q ∧
        AlgEquiv.restrictScalars ℚ τ = frobeniusThreeSeven (L := L) ^ 2 ∧
        orderOf τ = 3 := by
  let E := frobeniusThreeSevenQuadraticField (L := L)
  have : IsScalarTower ℚ E L := E.isScalarTower_mid'
  have : IsGalois E L := IsGalois.of_fixed_field L
    (Subgroup.zpowers (frobeniusThreeSeven (L := L) ^ 2))
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  have hσ := frobeniusThreeSeven_isArithFrobAt 𝔭 h𝔭 Q
  have hur : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
    IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem L 7
      (seven_not_mem_of_absNorm_three 𝔭 h𝔭) Q
  have _ := hur
  have hdeg := inertiaDeg_under_frobeniusThreeSevenQuadraticField Q hQ hσ
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
