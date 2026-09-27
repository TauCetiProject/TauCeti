/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic

/-!
# Tensor products and duals of finite projective modules

The full subcategory of `ModuleCat R` on finite projective modules inherits its symmetric
monoidal structure: the tensor product and the unit module remain finite projective. Linear
dualization is a contravariant endofunctor of this subcategory, and the evaluation map identifies
each module with its double dual. These constructions provide the affine tensor and dual
operations to be compared with finite locally free sheaves on a scheme.

The object property `finiteProjectiveModules` is defined in the Cartan-map development. This
file uses that same property, so the affine vector-bundle category and the category used for
algebraic `K₀` have the same objects and morphisms.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u

variable (R : Type u) [CommRing R]

/-- Finite projective modules contain the tensor unit and are closed under tensor products. -/
instance finiteProjectiveModules_isMonoidal : (finiteProjectiveModules R).IsMonoidal where
  prop_unit := finiteProjectiveModules_iff.mpr
    ⟨Module.Finite.self R, Module.Projective.of_free⟩
  prop_tensor M N hM hN := by
    have : Module.Finite R M := (finiteProjectiveModules_iff.mp hM).1
    have : Module.Finite R N := (finiteProjectiveModules_iff.mp hN).1
    have : Module.Projective R M := (finiteProjectiveModules_iff.mp hM).2
    have : Module.Projective R N := (finiteProjectiveModules_iff.mp hN).2
    exact finiteProjectiveModules_iff.mpr
      ⟨Module.Finite.tensorProduct R M N, Module.Projective.tensorProduct⟩

/-- The symmetric monoidal structure on finite projective modules is inherited from
`ModuleCat R`. -/
instance finiteProjectiveModulesSymmetricCategory :
    SymmetricCategory (finiteProjectiveModules R).FullSubcategory :=
  ObjectProperty.fullSymmetricSubcategory _

namespace FiniteProjectiveModules

/-- The linear dual of a finite projective module is finite projective. -/
@[expose] def dual (M : (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Module.Dual R M.obj),
    finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

@[simp]
theorem dual_obj (M : (finiteProjectiveModules R).FullSubcategory) :
    (dual R M).obj = ModuleCat.of R (Module.Dual R M.obj) :=
  rfl

/-- A map of finite projective modules induces the transpose map between their duals. -/
def dualMap {M N : (finiteProjectiveModules R).FullSubcategory} (f : M ⟶ N) :
    dual R N ⟶ dual R M :=
  ObjectProperty.homMk (ModuleCat.ofHom f.hom.hom.dualMap)

@[simp]
theorem dualMap_hom {M N : (finiteProjectiveModules R).FullSubcategory} (f : M ⟶ N) :
    (dualMap R f).hom = ModuleCat.ofHom f.hom.hom.dualMap := by
  rfl

/-- Linear dualization reverses arrows in the category of finite projective modules. -/
@[expose] def dualFunctor : ((finiteProjectiveModules R).FullSubcategory)ᵒᵖ ⥤
    (finiteProjectiveModules R).FullSubcategory where
  obj M := dual R M.unop
  map f := dualMap R f.unop
  map_id M := by
    apply ObjectProperty.hom_ext
    ext φ
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext φ
    rfl

@[simp]
theorem dualFunctor_obj (M : ((finiteProjectiveModules R).FullSubcategory)ᵒᵖ) :
    (dualFunctor R).obj M = dual R M.unop :=
  rfl

@[simp]
theorem dualFunctor_map {M N : ((finiteProjectiveModules R).FullSubcategory)ᵒᵖ}
    (f : M ⟶ N) : (dualFunctor R).map f = dualMap R f.unop :=
  rfl

/-- A finite projective module is naturally isomorphic to its double dual. -/
noncomputable def evalIso (M : (finiteProjectiveModules R).FullSubcategory) :
    M ≅ dual R (dual R M) :=
  ObjectProperty.isoMk (finiteProjectiveModules R)
    (Module.evalEquiv R M.obj).toModuleIso

/-- The underlying module isomorphism of the double-dual map is the evaluation equivalence. -/
@[simp]
theorem evalIso_hom_hom (M : (finiteProjectiveModules R).FullSubcategory) :
    (evalIso R M).hom.hom = (Module.evalEquiv R M.obj).toModuleIso.hom := by
  rfl

/-- The double-dual identification commutes with maps of finite projective modules. -/
@[reassoc]
theorem evalIso_naturality {M N : (finiteProjectiveModules R).FullSubcategory} (f : M ⟶ N) :
    f ≫ (evalIso R N).hom = (evalIso R M).hom ≫ dualMap R (dualMap R f) := by
  apply ObjectProperty.hom_ext
  ext m
  rfl

/-- Double-dual evaluation as a natural isomorphism on finite projective modules. -/
@[expose] noncomputable def evalNatIso :
    𝟭 (finiteProjectiveModules R).FullSubcategory ≅
      (dualFunctor R).rightOp ⋙ dualFunctor R :=
  NatIso.ofComponents (evalIso R) fun f => evalIso_naturality R f

/-- The forward component of `evalNatIso` is double-dual evaluation. -/
@[simp]
theorem evalNatIso_hom_app (M : (finiteProjectiveModules R).FullSubcategory) :
    (evalNatIso R).hom.app M = (evalIso R M).hom :=
  rfl

/-- The inverse component of `evalNatIso` is inverse double-dual evaluation. -/
@[simp]
theorem evalNatIso_inv_app (M : (finiteProjectiveModules R).FullSubcategory) :
    (evalNatIso R).inv.app M = (evalIso R M).inv :=
  rfl

end FiniteProjectiveModules

end TauCeti
