/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.ZMod
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
import TauCeti.Algebra.Module.LinearMap.Defs

/-!
# `N`-torsion of line-bundle classes and linear pullback

For every natural number `N`, the `N`-torsion subgroup
`AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ)` of the additively written Picard
group of a scheme `X` carries the canonical `ZMod N`-module structure
`AddSubgroup.torsionBy.zmodModule`, and the `ℤ`-linear pullback `f.picardPullbackLinearMap`
along a morphism `f : X ⟶ Y` restricts to a `ZMod N`-linear map
`f.picardPullbackTorsionLinearMap N` via `AddMonoidHom.torsionByZModLinearMap`.

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.torsionByModule`: the canonical `ZMod N`-module
  structure on `Pic(X)[N]`.
* `AlgebraicGeometry.Scheme.Hom.picardPullbackTorsionLinearMap`: `ZMod N`-linear pullback on
  `N`-torsion line-bundle classes, upgraded to
  `CategoryTheory.Iso.picardPullbackTorsionLinearEquiv` for scheme isomorphisms.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

/-- The canonical `ZMod N`-module structure on the `N`-torsion subgroup `Pic(X)[N]` of
`Additive (LineBundleClass X)`. -/
instance torsionByModule (X : Scheme.{u}) (N : ℕ) :
    Module (ZMod N) (AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ)) :=
  AddSubgroup.torsionBy.zmodModule

end TauCeti.AlgebraicGeometry.LineBundleClass

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry (LineBundleClass)

universe u

variable {X Y Z : Scheme.{u}}

/-- Pullback of `N`-torsion line-bundle classes along a scheme morphism `f : X ⟶ Y`, packaged as a
`ZMod N`-linear map `Pic(Y)[N] →ₗ[ZMod N] Pic(X)[N]`. -/
def picardPullbackTorsionLinearMap (f : X ⟶ Y) (N : ℕ) :
    AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ) →ₗ[ZMod N]
      AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ) :=
  f.picardPullbackLinearMap.toAddMonoidHom.torsionByZModLinearMap N

/-- On underlying additive Picard classes, `f.picardPullbackTorsionLinearMap N` acts as
`f.picardPullbackLinearMap`. -/
@[simp]
lemma coe_picardPullbackTorsionLinearMap_apply (f : X ⟶ Y) (N : ℕ)
    (a : AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ)) :
    (f.picardPullbackTorsionLinearMap N a : Additive (LineBundleClass X)) =
      f.picardPullbackLinearMap a.val := by
  rw [picardPullbackTorsionLinearMap, AddMonoidHom.coe_torsionByZModLinearMap_apply,
    LinearMap.toAddMonoidHom_coe]

/-- Pullback of `N`-torsion along the identity morphism is the identity `ZMod N`-linear map. -/
@[simp]
lemma picardPullbackTorsionLinearMap_id (X : Scheme.{u}) (N : ℕ) :
    picardPullbackTorsionLinearMap (𝟙 X) N = LinearMap.id := by
  rw [picardPullbackTorsionLinearMap, picardPullbackLinearMap_id, LinearMap.toAddMonoidHom_id]
  exact AddMonoidHom.torsionByZModLinearMap_id N

/-- `picardPullbackTorsionLinearMap` is contravariantly functorial under composition of scheme
morphisms. -/
@[simp]
lemma picardPullbackTorsionLinearMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (N : ℕ) :
    picardPullbackTorsionLinearMap (f ≫ g) N =
      f.picardPullbackTorsionLinearMap N ∘ₗ g.picardPullbackTorsionLinearMap N := by
  rw [picardPullbackTorsionLinearMap, picardPullbackTorsionLinearMap,
    picardPullbackTorsionLinearMap, picardPullbackLinearMap_comp, LinearMap.toAddMonoidHom_comp]
  exact AddMonoidHom.torsionByZModLinearMap_comp
    f.picardPullbackLinearMap.toAddMonoidHom g.picardPullbackLinearMap.toAddMonoidHom N

/-- Post-composing `g.picardPullbackTorsionLinearMap N` with a `ZMod N`-torsion restriction of `φ`
agrees with restricting `φ ∘ₗ g.picardPullbackLinearMap`. -/
lemma torsionByZModLinearMap_comp_picardPullbackTorsionLinearMap {A : Type*} [AddCommGroup A]
    (N : ℕ) [Module (ZMod N) (AddSubgroup.torsionBy A (N : ℤ))]
    (φ : Additive (LineBundleClass X) →ₗ[ℤ] A) (g : X ⟶ Y) :
    φ.toAddMonoidHom.torsionByZModLinearMap N ∘ₗ g.picardPullbackTorsionLinearMap N =
      (φ ∘ₗ g.picardPullbackLinearMap).toAddMonoidHom.torsionByZModLinearMap N := by
  rw [picardPullbackTorsionLinearMap, LinearMap.toAddMonoidHom_comp]
  exact (AddMonoidHom.torsionByZModLinearMap_comp φ.toAddMonoidHom
    g.picardPullbackLinearMap.toAddMonoidHom N).symm

end AlgebraicGeometry.Scheme.Hom

namespace CategoryTheory.Iso

open TauCeti.AlgebraicGeometry (LineBundleClass)

universe u

variable {X Y Z : Scheme.{u}}

/-- The underlying additive homomorphism of `MulEquiv.toAdditive (LineBundleClass.pullbackEquiv e)`
agrees with `e.hom.picardPullbackLinearMap.toAddMonoidHom`. -/
private lemma toAddMonoidHom_toAdditive_pullbackEquiv (e : X ≅ Y) :
    (MulEquiv.toAdditive (LineBundleClass.pullbackEquiv e)).toAddMonoidHom =
      e.hom.picardPullbackLinearMap.toAddMonoidHom := by
  ext a
  apply Additive.toMul.injective
  simp

/-- An isomorphism of schemes induces a `ZMod N`-linear equivalence on `N`-torsion Picard subgroups.
-/
def picardPullbackTorsionLinearEquiv (e : X ≅ Y) (N : ℕ) :
    AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ) ≃ₗ[ZMod N]
      AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ) :=
  (MulEquiv.toAdditive (LineBundleClass.pullbackEquiv e)).torsionByZModLinearEquiv N

/-- The underlying `ZMod N`-linear map of `e.picardPullbackTorsionLinearEquiv N` is
`e.hom.picardPullbackTorsionLinearMap N`. -/
@[simp]
lemma toLinearMap_picardPullbackTorsionLinearEquiv (e : X ≅ Y) (N : ℕ) :
    (e.picardPullbackTorsionLinearEquiv N).toLinearMap =
      e.hom.picardPullbackTorsionLinearMap N := by
  rw [picardPullbackTorsionLinearEquiv, AddEquiv.toLinearMap_torsionByZModLinearEquiv,
    toAddMonoidHom_toAdditive_pullbackEquiv,
    AlgebraicGeometry.Scheme.Hom.picardPullbackTorsionLinearMap]

/-- Applying `e.picardPullbackTorsionLinearEquiv N` agrees with
`e.hom.picardPullbackTorsionLinearMap N`. -/
@[simp]
lemma picardPullbackTorsionLinearEquiv_apply (e : X ≅ Y) (N : ℕ)
    (a : AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ)) :
    e.picardPullbackTorsionLinearEquiv N a = e.hom.picardPullbackTorsionLinearMap N a := by
  rw [← LinearEquiv.coe_toLinearMap, toLinearMap_picardPullbackTorsionLinearEquiv]

/-- The inverse of `e.picardPullbackTorsionLinearEquiv N` is
`e.symm.picardPullbackTorsionLinearEquiv N`. -/
@[simp]
lemma picardPullbackTorsionLinearEquiv_symm (e : X ≅ Y) (N : ℕ) :
    (e.picardPullbackTorsionLinearEquiv N).symm = e.symm.picardPullbackTorsionLinearEquiv N := by
  rw [picardPullbackTorsionLinearEquiv, AddEquiv.torsionByZModLinearEquiv_symm,
    picardPullbackTorsionLinearEquiv]
  congr 1
  ext a
  apply Additive.toMul.injective
  simp

/-- `picardPullbackTorsionLinearEquiv` of the identity scheme isomorphism is the identity
`ZMod N`-linear equivalence. -/
@[simp]
lemma picardPullbackTorsionLinearEquiv_refl (X : Scheme.{u}) (N : ℕ) :
    picardPullbackTorsionLinearEquiv (Iso.refl X) N = LinearEquiv.refl (ZMod N) _ := by
  ext a
  simp

/-- `picardPullbackTorsionLinearEquiv` reverses composition of scheme isomorphisms. -/
@[simp]
lemma picardPullbackTorsionLinearEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) (N : ℕ) :
    picardPullbackTorsionLinearEquiv (e ≪≫ f) N =
      (f.picardPullbackTorsionLinearEquiv N).trans (e.picardPullbackTorsionLinearEquiv N) := by
  ext a
  simp [LineBundleClass.pullback_comp]

end CategoryTheory.Iso

end
