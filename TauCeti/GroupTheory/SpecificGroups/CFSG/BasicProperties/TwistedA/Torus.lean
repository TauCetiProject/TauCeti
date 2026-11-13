/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.UnitaryRankOne

/-!
# A torus and fixed Weyl representative in the Steinberg fixed points of `²A₂(q)`

The finite special unitary model with signed reversal Gram matrix is identified with the
actual Steinberg fixed points by `TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints`.
Transport the injective diagonal-torus parametrization and the signed reversal Weyl
representative along this identification. The representative has square one, normalizes
the torus by `t ↦ σ(t)⁻¹`, and lies outside it, including in characteristic two.

The coefficient formula records the actual matrix over the algebraic closure, not merely
an abstract isomorphic copy. No generation, Bruhat decomposition or simplicity is asserted.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.TypeALieIndex

variable (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid)

local notation "d" => ofTwistedA 2 q hv
local notation "K" => GaloisField (ValidLieTypeIndex.characteristic (Subtype.val d))
  (ValidLieTypeIndex.fieldExponent (Subtype.val d) * 2)
local notation "σ" => iterateFrobenius K (ValidLieTypeIndex.characteristic (Subtype.val d))
  (ValidLieTypeIndex.fieldExponent (Subtype.val d))
local notation "hσ" => @ValidLieTypeIndex.involutive_iterateFrobenius_galoisField
  (Subtype.val d)

/-- The diagonal torus parametrization in the exact Steinberg fixed points of `²A₂(q)`. -/
def unitaryTorusHom : Kˣ →* (d).FixedPoints :=
  (specialIsometryEquivFixedPoints 2 q hv).toMonoidHom.comp
    (UnitaryRankOne.torusHom K σ hσ)

/-- The exact-carrier parametrization factors through the special-isometry comparison. -/
theorem unitaryTorusHom_def :
    unitaryTorusHom q hv = (specialIsometryEquivFixedPoints 2 q hv).toMonoidHom.comp
      (UnitaryRankOne.torusHom K σ hσ) := by rfl

/-- The comparison sends each unitary torus parameter to the exact-carrier torus parameter. -/
@[simp]
theorem specialIsometryEquivFixedPoints_torusHom (t : Kˣ) :
    specialIsometryEquivFixedPoints 2 q hv (UnitaryRankOne.torusHom K σ hσ t) =
      unitaryTorusHom q hv t := by rfl

/-- The comparison identifies the unitary torus with the range on the exact carrier. -/
@[simp]
theorem map_specialIsometryEquivFixedPoints_torus :
    (UnitaryRankOne.torus K σ hσ).map
        (specialIsometryEquivFixedPoints 2 q hv : UnitaryRankOne.Group K σ →* (d).FixedPoints) =
      (unitaryTorusHom q hv).range := by
  simp only [UnitaryRankOne.torus_def, unitaryTorusHom_def, MonoidHom.range_comp,
    MulEquiv.toMonoidHom_eq_coe]

/-- The torus parameter gives the stated diagonal matrix over the algebraic closure. -/
@[simp]
theorem coe_unitaryTorusHom (t : Kˣ) :
    ((d).carrierEquivSpecialLinear (unitaryTorusHom q hv t : (d).AmbientGroup) :
        Matrix (Fin ((d).1.rank + 1)) (Fin ((d).1.rank + 1)) (d).1.Closure) =
      (diagonal ![(t : K), σ (t : K) * ↑t⁻¹, σ (↑t⁻¹ : K)]).map
        ((d).1.extensionGaloisFieldEmbedding 2 two_ne_zero) := by
  simpa only [unitaryTorusHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    UnitaryRankOne.coe_torusHom] using
    coe_specialIsometryEquivFixedPoints 2 q hv (UnitaryRankOne.torusHom K σ hσ t)

/-- The torus parametrization remains injective on the exact carrier. -/
theorem unitaryTorusHom_injective : Function.Injective (unitaryTorusHom q hv) :=
  (specialIsometryEquivFixedPoints 2 q hv).injective.comp
    (UnitaryRankOne.torusHom_injective K σ hσ)

/-- The signed reversal gives an actual Steinberg-fixed representative of the nontrivial
relative Weyl element. -/
def unitaryFixedWeylRepresentative : (d).FixedPoints :=
  specialIsometryEquivFixedPoints 2 q hv (UnitaryRankOne.weyl K σ)

/-- The comparison sends the unitary Weyl element to the fixed Weyl representative. -/
@[simp]
theorem specialIsometryEquivFixedPoints_weyl :
    specialIsometryEquivFixedPoints 2 q hv (UnitaryRankOne.weyl K σ) =
      unitaryFixedWeylRepresentative q hv := by rfl

/-- The Steinberg-fixed representative is the signed reversal matrix over the closure. -/
@[simp]
theorem coe_unitaryFixedWeylRepresentative :
    ((d).carrierEquivSpecialLinear
        (unitaryFixedWeylRepresentative q hv : (d).AmbientGroup) :
          Matrix (Fin ((d).1.rank + 1)) (Fin ((d).1.rank + 1)) (d).1.Closure) =
      (typeAGraphConjugator 2 (d).1.Closure : Matrix (Fin 3) (Fin 3) (d).1.Closure) := by
  rw [unitaryFixedWeylRepresentative, coe_specialIsometryEquivFixedPoints,
    UnitaryRankOne.coe_weyl]
  have hmap := congrArg Units.val (map_typeAGraphConjugator
    ((d).1.extensionGaloisFieldEmbedding 2 two_ne_zero) 2)
  rwa [Units.coe_map, MonoidHom.coe_ofClass, RingHom.mapMatrix_apply] at hmap

/-- The fixed Weyl representative has square one. -/
@[simp]
theorem unitaryFixedWeylRepresentative_mul_self :
    unitaryFixedWeylRepresentative q hv * unitaryFixedWeylRepresentative q hv = 1 := by
  rw [unitaryFixedWeylRepresentative, ← map_mul, UnitaryRankOne.weyl_mul_self, map_one]

/-- The fixed Weyl representative is its own inverse. -/
@[simp]
theorem unitaryFixedWeylRepresentative_inv :
    (unitaryFixedWeylRepresentative q hv)⁻¹ = unitaryFixedWeylRepresentative q hv :=
  inv_eq_of_mul_eq_one_right (unitaryFixedWeylRepresentative_mul_self q hv)

/-- Weyl conjugation of the exact torus acts on parameters by inverse field conjugation. -/
theorem unitaryFixedWeylRepresentative_mul_unitaryTorusHom_mul_unitaryFixedWeylRepresentative
    (t : Kˣ) :
    unitaryFixedWeylRepresentative q hv * unitaryTorusHom q hv t *
        unitaryFixedWeylRepresentative q hv =
      unitaryTorusHom q hv ((Units.map (σ).toMonoidHom t)⁻¹) := by
  simpa only [unitaryFixedWeylRepresentative, unitaryTorusHom,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul] using
      congrArg (specialIsometryEquivFixedPoints 2 q hv)
        (UnitaryRankOne.weyl_mul_torusHom_mul_weyl K σ hσ t)

/-- The fixed Weyl representative normalizes the parametrized torus on the exact carrier. -/
theorem unitaryFixedWeylRepresentative_mem_normalizer_range_unitaryTorusHom :
    unitaryFixedWeylRepresentative q hv ∈
      Subgroup.normalizer ((unitaryTorusHom q hv).range : Set (d).FixedPoints) := by
  rw [← map_specialIsometryEquivFixedPoints_torus,
    ← specialIsometryEquivFixedPoints_weyl]
  simpa only [MonoidHom.coe_ofClass] using
    Subgroup.le_normalizer_map (H := UnitaryRankOne.torus K σ hσ)
      (specialIsometryEquivFixedPoints 2 q hv : UnitaryRankOne.Group K σ →* (d).FixedPoints)
      (Subgroup.mem_map.mpr ⟨UnitaryRankOne.weyl K σ,
        UnitaryRankOne.weyl_mem_normalizer_torus K σ hσ, rfl⟩)

/-- The fixed Weyl representative lies outside the parametrized torus. -/
theorem unitaryFixedWeylRepresentative_notMem_range_unitaryTorusHom :
    unitaryFixedWeylRepresentative q hv ∉ (unitaryTorusHom q hv).range := by
  rintro ⟨t, ht⟩
  apply UnitaryRankOne.weyl_notMem_torus K σ hσ
  rw [UnitaryRankOne.mem_torus_iff]
  rw [← specialIsometryEquivFixedPoints_torusHom,
    ← specialIsometryEquivFixedPoints_weyl] at ht
  exact ⟨t, (specialIsometryEquivFixedPoints 2 q hv).injective ht⟩

end TauCeti.TypeALieIndex
