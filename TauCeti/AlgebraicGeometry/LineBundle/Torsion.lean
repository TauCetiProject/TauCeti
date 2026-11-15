/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# `N`-torsion of line-bundle classes and linear pullback

For every natural number `N`, the `N`-torsion subgroup
`AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ)` of the additively written Picard
group of a scheme `X` carries the canonical `ZMod N`-module structure
`AddSubgroup.torsionBy.zmodModule`, and the `ℤ`-linear pullback `LineBundleClass.pullbackLinearMap`
along a morphism `f : X ⟶ Y` restricts to a `ZMod N`-linear map
`LineBundleClass.pullbackTorsionLinearMap f N` via `TauCeti.torsionByMap`.

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
  AddMonoidHom.toZModLinearMap N
    (M := AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ))
    (M₁ := AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ))
    (TauCeti.torsionByMap (N : ℤ) (pullbackLinearMap f)).toAddMonoidHom

/-- On underlying additive Picard classes, `pullbackTorsionLinearMap f N` acts as
`pullbackLinearMap f`. -/
@[simp]
lemma coe_pullbackTorsionLinearMap_apply (f : X ⟶ Y) (N : ℕ)
    (a : AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ)) :
    (pullbackTorsionLinearMap f N a : Additive (LineBundleClass X)) = pullbackLinearMap f a.val :=
  TauCeti.coe_torsionByMap_apply (N : ℤ) (pullbackLinearMap f) a

/-- Pullback of `N`-torsion along the identity morphism is the identity `ZMod N`-linear map. -/
@[simp]
lemma pullbackTorsionLinearMap_id (X : Scheme.{u}) (N : ℕ) :
    pullbackTorsionLinearMap (𝟙 X) N = LinearMap.id := by
  ext a
  simp

/-- `pullbackTorsionLinearMap` is contravariantly functorial under composition of scheme morphisms.
-/
@[simp]
lemma pullbackTorsionLinearMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (N : ℕ) :
    pullbackTorsionLinearMap (f ≫ g) N =
      pullbackTorsionLinearMap f N ∘ₗ pullbackTorsionLinearMap g N := by
  ext a
  simp [pullback_comp]

/-- An isomorphism of schemes induces a `ZMod N`-linear equivalence on `N`-torsion Picard subgroups.
-/
def pullbackTorsionLinearEquiv (e : X ≅ Y) (N : ℕ) :
    AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ) ≃ₗ[ZMod N]
      AddSubgroup.torsionBy (Additive (LineBundleClass X)) (N : ℤ) :=
  LinearEquiv.ofLinearMap (pullbackTorsionLinearMap e.hom N) (pullbackTorsionLinearMap e.inv N)
    (by rw [← pullbackTorsionLinearMap_comp, e.hom_inv_id, pullbackTorsionLinearMap_id])
    (by rw [← pullbackTorsionLinearMap_comp, e.inv_hom_id, pullbackTorsionLinearMap_id])

/-- The underlying `ZMod N`-linear map of `pullbackTorsionLinearEquiv e N` is
`pullbackTorsionLinearMap e.hom N`. -/
lemma toLinearMap_pullbackTorsionLinearEquiv (e : X ≅ Y) (N : ℕ) :
    (pullbackTorsionLinearEquiv e N).toLinearMap = pullbackTorsionLinearMap e.hom N := by
  ext a
  simp [pullbackTorsionLinearEquiv]

/-- Applying `pullbackTorsionLinearEquiv e N` agrees with `pullbackTorsionLinearMap e.hom N`. -/
@[simp]
lemma pullbackTorsionLinearEquiv_apply (e : X ≅ Y) (N : ℕ)
    (a : AddSubgroup.torsionBy (Additive (LineBundleClass Y)) (N : ℤ)) :
    pullbackTorsionLinearEquiv e N a = pullbackTorsionLinearMap e.hom N a := by
  ext
  simp [pullbackTorsionLinearEquiv]

/-- The inverse of `pullbackTorsionLinearEquiv e N` is `pullbackTorsionLinearEquiv e.symm N`. -/
@[simp]
lemma pullbackTorsionLinearEquiv_symm (e : X ≅ Y) (N : ℕ) :
    (pullbackTorsionLinearEquiv e N).symm = pullbackTorsionLinearEquiv e.symm N := by
  ext a
  simp [pullbackTorsionLinearEquiv]

end TauCeti.AlgebraicGeometry.LineBundleClass

end
