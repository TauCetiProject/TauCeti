/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Congruence
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import TauCeti.NumberTheory.NumberField.CMField.IntegralNormOne
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield

/-!
# Principal integral norm-one ideles of a CM field

The principal norm-one ideles in a congruence subgroup are exactly the diagonal images
of the congruence units that are roots of unity. At the trivial modulus this identifies the
intersection on which a prescribed character of the integral norm-one ideles must be
trivial if it is to extend to an automorphic character of the norm-one torus.

The compatibility condition is the one in `New.AutChar.exists_hasWeight_of_prod_eq_one`,
`grh/src/Lib/ClassField/HeckeCharacter/Basic.lean` of lsernau/grh-lean at revision `72fead1`.
-/

public section

open NumberField NumberField.IsCMField

namespace TauCeti.GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- An integral unit of a CM field has principal idele of relative norm one exactly when
it is a root of unity. -/
theorem ideleNormMap_unitEmbedding_ringOfIntegers_eq_one_iff (u : (𝓞 E)ˣ) :
    ideleNormMap (maximalRealSubfield E) E
      (IdeleGroup.unitEmbedding (𝓞 E) E (Units.map (algebraMap (𝓞 E) E) u)) = 1 ↔
      u ∈ NumberField.Units.torsion E := by
  let a : Eˣ := Units.map (algebraMap (𝓞 E) E) u
  let F := maximalRealSubfield E
  have hinj : Function.Injective (IdeleGroup.unitEmbedding (𝓞 F) F) := by
    intro x y h
    apply Units.ext
    apply AdeleRing.algebraMap_injective (R := 𝓞 F)
    simpa only [IdeleGroup.val_unitEmbedding_apply] using congrArg Units.val h
  rw [ideleNormMap_unitEmbedding, ← map_one (IdeleGroup.unitEmbedding (𝓞 F) F), hinj.eq_iff]
  have hnorm : Algebra.normUnits F a = 1 ↔ (a : E) * complexConj E a = 1 := by
    rw [Units.ext_iff, Units.val_one, Algebra.coe_normUnits,
      ← (algebraMap F E).injective.eq_iff, map_one,
      algebraMap_norm_eq_mul_complexConj]
  rw [hnorm, NumberField.Units.torsion, CommGroup.mem_torsion]
  let f := (Units.coeHom E).comp (Units.map (algebraMap (𝓞 E) E).toMonoidHom)
  have hf : Function.Injective f := Units.val_injective.comp
    (Units.map_injective RingOfIntegers.coe_injective)
  rw [← hf.isOfFinOrder_iff, isOfFinOrder_iff_isIntegral_and_mul_complexConj_eq_one]
  exact (and_iff_right (RingOfIntegers.isIntegral_coe (u : 𝓞 E))).symm

/-- At any modulus of a CM field, the principal ideles of relative norm one in the idele
congruence subgroup are the diagonal image of the roots of unity in the unit congruence
subgroup. At modulus one this image contains every root of unity. -/
theorem ideleCongruenceSubgroup_inf_principal_inf_ker_ideleNormMap (𝔪 : Modulus E) :
    (ideleCongruenceSubgroup 𝔪 ⊓ IdeleGroup.principalSubgroup (𝓞 E) E) ⊓
        (ideleNormMap (maximalRealSubfield E) E).toMonoidHom.ker =
      (unitsCongruenceSubgroup 𝔪 ⊓ NumberField.Units.torsion E).map
        ((IdeleGroup.unitEmbedding (𝓞 E) E).comp (Units.map (algebraMap (𝓞 E) E))) := by
  ext x
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom,
    Subgroup.mem_map]
  constructor
  · rintro ⟨⟨hx, ⟨a, rfl⟩⟩, hnorm⟩
    obtain ⟨u, hu, rfl⟩ := unitEmbedding_mem_ideleCongruenceSubgroup_iff.mp hx
    exact ⟨u, ⟨hu, (ideleNormMap_unitEmbedding_ringOfIntegers_eq_one_iff u).mp hnorm⟩, rfl⟩
  · rintro ⟨u, ⟨hu, htor⟩, rfl⟩
    exact ⟨⟨unitEmbedding_mem_ideleCongruenceSubgroup_iff.mpr ⟨u, hu, rfl⟩, ⟨_, rfl⟩⟩,
      (ideleNormMap_unitEmbedding_ringOfIntegers_eq_one_iff u).mpr htor⟩

end TauCeti.GlobalNumberFields
