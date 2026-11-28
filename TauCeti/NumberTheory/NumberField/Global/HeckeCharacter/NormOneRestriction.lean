/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Splitting
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.CM
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Shift
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Archimedean
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Compatibility

/-!
# Restriction of splitting characters to norm-one ideles

A Hecke character restricts to a circle-valued character of the norm-one ideles and is trivial
on the principal ideles in that subgroup. For a splitting character, the restriction has
weight one in the chosen CM type and trivial tame part. Its pullback along `x ↦ x / conj x`
recovers the square of the splitting character.

The restriction and pullback identities are those of `New.WeilData.upsilonU1_hasWeight` and
`New.WeilData.baseChange_upsilonU1` in
`grh/src/Lib/ClassField/HeckeCharacter/SplitTameCharacters.lean` of lsernau/grh-lean
(revision `72fead1`).
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.IsCMField
open scoped AdeleGaloisAction

namespace TauCeti.GlobalNumberFields.HeckeCharacter

variable {E : Type} [Field E] [NumberField E]

/-- A Hecke character takes values of absolute value one on the relative norm-one ideles. -/
theorem norm_apply_cmNormOneIdeles (χ : HeckeCharacter E) (x : cmNormOneIdeles E) :
    ‖(χ (x.val : IdeleClassGroup (𝓞 E) E) : ℂ)‖ = 1 := by
  have hx := mem_cmNormOneIdeles_iff_ideleNormMap_eq_one.mp x.property
  rw [χ.norm_apply_eq_rpow_shift, ideleClassNorm_mk,
    ← ideleNorm_ideleNormMap (K := maximalRealSubfield E) x.val, hx, map_one]
  simp

/-- Restrict a Hecke character to the relative norm-one ideles of `E`, with values in the circle. -/
noncomputable def normOneRestriction (χ : HeckeCharacter E) : cmNormOneIdeles E →ₜ* Circle where
  toFun x := ⟨χ (x.val : IdeleClassGroup (𝓞 E) E),
    mem_sphere_zero_iff_norm.mpr (χ.norm_apply_cmNormOneIdeles x)⟩
  map_one' := Circle.ext (by simp)
  map_mul' x y := Circle.ext (by simp; rfl)
  continuous_toFun :=
    ((Units.continuous_val.comp χ.continuous).comp
      (QuotientGroup.continuous_mk.comp continuous_subtypeVal)).subtype_mk _

/-- Evaluation of the restriction agrees with the Hecke character on the underlying idele class. -/
@[simp] theorem coe_normOneRestriction_apply (χ : HeckeCharacter E) (x : cmNormOneIdeles E) :
    (χ.normOneRestriction x : ℂ) = χ (x.val : IdeleClassGroup (𝓞 E) E) := (rfl)

/-- The restricted character is automorphic: it kills the principal norm-one ideles. -/
theorem normOneRestriction_apply_of_mem_principalSubgroup (χ : HeckeCharacter E)
    (x : cmNormOneIdeles E) (hx : x.val ∈ IdeleGroup.principalSubgroup (𝓞 E) E) :
    χ.normOneRestriction x = 1 := by
  apply Circle.ext
  rw [coe_normOneRestriction_apply, (QuotientGroup.eq_one_iff _).2 hx, map_one]
  rfl

variable [IsCMField E]

/-- If conjugation inverts the value of a Hecke character at `x`, then the pullback of its
norm-one restriction along division by conjugation takes the square of that value at `x`.
Splitting characters satisfy the inversion condition at every idele. -/
theorem normOneRestriction_ideleDivConj_eq_sq (χ : HeckeCharacter E) (x : IdeleGroup (𝓞 E) E)
    (hx : χ (complexConj E • (x : IdeleClassGroup (𝓞 E) E)) =
      (χ (x : IdeleClassGroup (𝓞 E) E))⁻¹) :
    Circle.toUnits (χ.normOneRestriction (ideleDivConj x)) =
      (χ ^ 2) (x : IdeleClassGroup (𝓞 E) E) := by
  apply Units.ext
  simp [← ideleClass_smul_mk, hx, div_eq_mul_inv, pow_two]

namespace IsSplitting

variable {υ : HeckeCharacter E} {Φ : CMType E}

/-- On norm-one ideles with integral finite part, the restriction of a splitting character
has weight one at every embedding of its CM type, with trivial tame part. -/
theorem normOneRestriction_apply_of_mem_integralUnits (hυ : υ.IsSplitting Φ)
    (x : cmNormOneIdeles E)
    (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ FiniteAdeleRing.integralUnits (𝓞 E) E) :
    (υ.normOneRestriction x : ℂ) =
      ∏ w : InfinitePlace E, Φ.completionEmbedding w (w.ideleInfiniteCoord x.val) := by
  rw [coe_normOneRestriction_apply, hυ.apply_of_mem_integralUnits _ hx]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  have hnorm := norm_extensionEmbedding_ideleInfiniteCoord w
    ⟨x.val, mem_cmNormOneIdeles_iff_ideleNormMap_eq_one.mp x.property⟩
  have h := (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
    (w.ideleInfiniteCoord x.val : w.Completion)
  rw [← h, hnorm, Complex.ofReal_one, div_one]

end IsSplitting

end TauCeti.GlobalNumberFields.HeckeCharacter
