/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.ZMod
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# `N`-torsion of line-bundle classes and linear pullback

For every natural number `N`, the `N`-torsion subgroup
`AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ)` of the additively written Picard
group of a scheme `X` carries the canonical `ZMod N`-module structure
`AddSubgroup.torsionBy.zmodModule`, and the `ℤ`-linear pullback `LineBundleClass.pullbackLinearMap`
along a morphism `f : X ⟶ Y` restricts to a `ZMod N`-linear map
`LineBundleClass.pullbackTorsionLinearMap f N` via `AddMonoidHom.torsionByZModLinearMap`.

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.torsionByModule`: the canonical `ZMod N`-module
  structure on `Pic(X)[N]`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.pullbackTorsionLinearMap`: `ZMod N`-linear pullback on
  `N`-torsion line-bundle classes, upgraded to `pullbackTorsionLinearEquiv` for scheme isomorphisms.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {X Y Z : Scheme.{u}}

/-- The canonical `ZMod N`-module structure on the `N`-torsion subgroup `Pic(X)[N]` of
`Additive (LineBundleClass X)`. -/
instance torsionByModule (X : Scheme.{u}) (N : ℕ) :
    Module (ZMod N) (AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ)) :=
  AddSubgroup.torsionBy.zmodModule

/-- Pullback of `N`-torsion line-bundle classes along a scheme morphism `f : X ⟶ Y`, packaged as a
`ZMod N`-linear map `Pic(Y)[N] →ₗ[ZMod N] Pic(X)[N]`. -/
def pullbackTorsionLinearMap (f : X ⟶ Y) (N : ℕ) :
    AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ) →ₗ[ZMod N]
      AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ) :=
  (pullbackLinearMap f).toAddMonoidHom.torsionByZModLinearMap N

/-- On underlying additive Picard classes, `pullbackTorsionLinearMap f N` acts as
`pullbackLinearMap f`. -/
@[simp]
lemma coe_pullbackTorsionLinearMap_apply (f : X ⟶ Y) (N : ℕ)
    (a : AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ)) :
    (pullbackTorsionLinearMap f N a : Additive (LineBundleClass X)) =
      pullbackLinearMap f a.val := by
  rw [pullbackTorsionLinearMap, AddMonoidHom.coe_torsionByZModLinearMap_apply,
    LinearMap.toAddMonoidHom_coe]

/-- Pullback of `N`-torsion along the identity morphism is the identity `ZMod N`-linear map. -/
@[simp]
lemma pullbackTorsionLinearMap_id (X : Scheme.{u}) (N : ℕ) :
    pullbackTorsionLinearMap (𝟙 X) N = LinearMap.id := by
  rw [pullbackTorsionLinearMap, pullbackLinearMap_id]
  exact LinearMap.toAddMonoidHom_torsionByZModLinearMap_id N

/-- `pullbackTorsionLinearMap` is contravariantly functorial under composition of scheme morphisms.
-/
@[simp]
lemma pullbackTorsionLinearMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (N : ℕ) :
    pullbackTorsionLinearMap (f ≫ g) N =
      pullbackTorsionLinearMap f N ∘ₗ pullbackTorsionLinearMap g N := by
  rw [pullbackTorsionLinearMap, pullbackTorsionLinearMap, pullbackTorsionLinearMap,
    pullbackLinearMap_comp]
  exact LinearMap.toAddMonoidHom_torsionByZModLinearMap_comp
    (pullbackLinearMap f) (pullbackLinearMap g) N

/-- Post-composing `pullbackTorsionLinearMap g N` with a `ZMod N`-torsion restriction of `φ`
agrees with restricting `φ ∘ₗ pullbackLinearMap g`. -/
lemma torsionByZModLinearMap_comp_pullbackTorsionLinearMap {A : Type*} [AddCommGroup A]
    (N : ℕ) [Module (ZMod N) (AddSubgroup.torsionBy A (N : ℤ))]
    (φ : Additive (LineBundleClass X) →ₗ[ℤ] A) (g : X ⟶ Y) :
    φ.toAddMonoidHom.torsionByZModLinearMap N ∘ₗ pullbackTorsionLinearMap g N =
      (φ ∘ₗ pullbackLinearMap g).toAddMonoidHom.torsionByZModLinearMap N := by
  rw [pullbackTorsionLinearMap]
  exact (LinearMap.toAddMonoidHom_torsionByZModLinearMap_comp φ (pullbackLinearMap g) N).symm

/-- The underlying additive homomorphism of `MulEquiv.toAdditive (pullbackEquiv e)` agrees with
`(pullbackLinearMap e.hom).toAddMonoidHom`. -/
private lemma toAddMonoidHom_toAdditive_pullbackEquiv (e : X ≅ Y) :
    (MulEquiv.toAdditive (pullbackEquiv e)).toAddMonoidHom =
      (pullbackLinearMap e.hom).toAddMonoidHom := by
  ext a
  apply Additive.toMul.injective
  simp

/-- An isomorphism of schemes induces a `ZMod N`-linear equivalence on `N`-torsion Picard subgroups.
-/
def pullbackTorsionLinearEquiv (e : X ≅ Y) (N : ℕ) :
    AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ) ≃ₗ[ZMod N]
      AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ) :=
  (MulEquiv.toAdditive (pullbackEquiv e)).torsionByZModLinearEquiv N

/-- The underlying `ZMod N`-linear map of `pullbackTorsionLinearEquiv e N` is
`pullbackTorsionLinearMap e.hom N`. -/
lemma toLinearMap_pullbackTorsionLinearEquiv (e : X ≅ Y) (N : ℕ) :
    (pullbackTorsionLinearEquiv e N).toLinearMap = pullbackTorsionLinearMap e.hom N := by
  rw [pullbackTorsionLinearEquiv, AddEquiv.toLinearMap_torsionByZModLinearEquiv,
    toAddMonoidHom_toAdditive_pullbackEquiv, pullbackTorsionLinearMap]

/-- Applying `pullbackTorsionLinearEquiv e N` agrees with `pullbackTorsionLinearMap e.hom N`. -/
@[simp]
lemma pullbackTorsionLinearEquiv_apply (e : X ≅ Y) (N : ℕ)
    (a : AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ)) :
    pullbackTorsionLinearEquiv e N a = pullbackTorsionLinearMap e.hom N a := by
  rw [← LinearEquiv.coe_toLinearMap, toLinearMap_pullbackTorsionLinearEquiv]

/-- The inverse of `pullbackTorsionLinearEquiv e N` is `pullbackTorsionLinearEquiv e.symm N`. -/
@[simp]
lemma pullbackTorsionLinearEquiv_symm (e : X ≅ Y) (N : ℕ) :
    (pullbackTorsionLinearEquiv e N).symm = pullbackTorsionLinearEquiv e.symm N := by
  rw [pullbackTorsionLinearEquiv, AddEquiv.torsionByZModLinearEquiv_symm,
    pullbackTorsionLinearEquiv]
  congr 1
  ext a
  apply Additive.toMul.injective
  simp

end TauCeti.AlgebraicGeometry.LineBundleClass

end
