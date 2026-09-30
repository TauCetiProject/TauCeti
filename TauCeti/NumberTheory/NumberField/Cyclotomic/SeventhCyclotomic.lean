/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.FieldTheory.Galois.FixedField
import Mathlib.Tactic.NormNum.Prime

/-!
# The quadratic subfield of a seventh cyclotomic field

The automorphism with cyclotomic exponent three has order six. The fixed field of its square
has degree two over `ℚ`.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section
noncomputable section

open Ideal NumberField IsCyclotomicExtension IntermediateField
open scoped NumberField

namespace TauCeti.NumberField

variable {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

private instance : IsGalois ℚ L := IsCyclotomicExtension.isGalois {7} ℚ L

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The cyclotomic automorphism with exponent three modulo seven. -/
def frobeniusThreeSeven : L ≃ₐ[ℚ] L :=
  (Rat.galEquivZMod 7 L).symm (Units.mk0 (3 : ZMod 7) (by decide))

/-- The exponent of `frobeniusThreeSeven` on a primitive seventh root of unity is three. -/
@[simp]
theorem autToPow_frobeniusThreeSeven :
    ((zeta_spec 7 ℚ L).autToPow ℚ (frobeniusThreeSeven (L := L)) : ZMod 7) = 3 := by
  rw [(zeta_spec 7 ℚ L).autToPow_eq_unitsMap_galEquivZMod dvd_rfl,
    ZMod.unitsMap_self, MonoidHom.id_apply]
  simp only [frobeniusThreeSeven, MulEquiv.apply_symm_apply, Units.val_mk0]

/-- The cyclotomic automorphism with exponent three modulo seven has order six. -/
@[simp]
theorem orderOf_frobeniusThreeSeven : orderOf (frobeniusThreeSeven (L := L)) = 6 := by
  rw [frobeniusThreeSeven, ← (Rat.galEquivZMod 7 L).orderOf_eq,
    MulEquiv.apply_symm_apply, ← orderOf_units]
  exact (orderOf_eq_iff (by decide : 0 < 6)).mpr (by decide)

/-- The fixed field of the square of the Frobenius at three is the quadratic intermediate field
of a seventh cyclotomic extension. -/
def seventhCyclotomicQuadraticSubfield : IntermediateField ℚ L :=
  fixedField (Subgroup.zpowers (frobeniusThreeSeven (L := L) ^ 2))

/-- The quadratic subfield as a fixed field. -/
theorem seventhCyclotomicQuadraticSubfield_def :
    seventhCyclotomicQuadraticSubfield (L := L) =
      fixedField (Subgroup.zpowers (frobeniusThreeSeven (L := L) ^ 2)) := by
  unfold seventhCyclotomicQuadraticSubfield
  rfl

/-- An element is in the quadratic fixed field precisely when the square of the Frobenius at
three fixes it. -/
@[simp]
theorem mem_seventhCyclotomicQuadraticSubfield_iff (x : L) :
    x ∈ seventhCyclotomicQuadraticSubfield (L := L) ↔
      (frobeniusThreeSeven (L := L) ^ 2) x = x := by
  rw [seventhCyclotomicQuadraticSubfield_def]
  exact IntermediateField.mem_fixedField_zpowers_iff _ _

/-- The square of the Frobenius with exponent three has order three. -/
@[simp]
theorem orderOf_frobeniusThreeSeven_sq :
    orderOf (frobeniusThreeSeven (L := L) ^ 2) = 3 := by
  rw [orderOf_pow, orderOf_frobeniusThreeSeven]
  decide

/-- The square of the Frobenius at three acts with exponent two on a primitive seventh root. -/
-- Not a simp lemma: `map_pow` and `autToPow_frobeniusThreeSeven` normalize its left-hand side.
theorem autToPow_frobeniusThreeSeven_sq :
    ((zeta_spec 7 ℚ L).autToPow ℚ (frobeniusThreeSeven (L := L) ^ 2) : ZMod 7) = 2 := by
  rw [map_pow, Units.val_pow_eq_pow_val, autToPow_frobeniusThreeSeven]
  decide

/-- The field fixed by the square of the Frobenius at three has degree two over `ℚ`. -/
@[simp] theorem finrank_seventhCyclotomicQuadraticSubfield :
    Module.finrank ℚ (seventhCyclotomicQuadraticSubfield (L := L)) = 2 := by
  have htower := IntermediateField.finrank_fixedField_zpowers_mul_orderOf
    (frobeniusThreeSeven (L := L) ^ 2)
  have htot : Module.finrank ℚ L = 6 := by
    rw [IsCyclotomicExtension.Rat.finrank 7 L,
      Nat.totient_prime (by norm_num : Nat.Prime 7)]
  rw [← seventhCyclotomicQuadraticSubfield_def,
    orderOf_frobeniusThreeSeven_sq, htot] at htower
  omega

end TauCeti.NumberField

end
