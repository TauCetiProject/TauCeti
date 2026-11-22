/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.AlgCat.Limits
public import TauCeti.Algebra.Category.SemimoduleCat.Sections

/-!
# Algebra sections and their underlying linear sections

Forgetting a diagram of algebras to modules and then to semimodules preserves its
matching sections component by component. Natural transformations transport algebra
sections by algebra homomorphisms, using Mathlib's section functor on underlying types.
-/

public section

open CategoryTheory

namespace AlgCat

universe u v w t

variable {R : Type u} [CommRing R] {J : Type v} [Category.{w} J]

/-- An algebra family is a matching section exactly when it commutes with every diagram map. -/
@[simp]
theorem mem_sectionsSubalgebra {F : J ⥤ AlgCat.{t} R} {s : ∀ j, F.obj j} :
    s ∈ sectionsSubalgebra F ↔ ∀ {j j'} (f : j ⟶ j'), (F.map f).hom (s j) = s j' := Iff.rfl

private theorem forgotten_map_apply {A B : AlgCat.{t} R} (f : A ⟶ B) (x : A) :
    (((forget₂ (AlgCat R) (ModuleCat R) ⋙
      ModuleCat.equivalenceSemimoduleCat.functor).map f).hom x) = f.hom x :=
  -- Both standard functors retain the carrier; their only computation is isolated here.
  rfl

/-- Forgetting algebra structure preserves matching sections as a linear equivalence.
The underlying diagram uses the existing forgetful functor to modules and the canonical
module-to-semimodule equivalence. -/
def sectionsLinearEquiv (F : J ⥤ AlgCat.{t} R) :
    sectionsSubalgebra F ≃ₗ[R] SemimoduleCat.sectionsSubmodule
      (F ⋙ forget₂ (AlgCat R) (ModuleCat R) ⋙ ModuleCat.equivalenceSemimoduleCat.functor) where
  toFun s := ⟨s.val, SemimoduleCat.mem_sectionsSubmodule.mpr fun f =>
    (forgotten_map_apply (F.map f) _).trans ((mem_sectionsSubalgebra.mp s.property) f)⟩
  invFun s := ⟨s.val, mem_sectionsSubalgebra.mpr fun f =>
    (forgotten_map_apply (F.map f) _).symm.trans
      ((SemimoduleCat.mem_sectionsSubmodule.mp s.property) f)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Forgetting algebra structure leaves every section component unchanged. -/
@[simp]
theorem sectionsLinearEquiv_apply (F : J ⥤ AlgCat.{t} R) (s : sectionsSubalgebra F) (j : J) :
    (sectionsLinearEquiv F s).val j = s.val j := (rfl)

/-- Recovering algebra sections from the underlying linear section preserves components. -/
@[simp]
theorem sectionsLinearEquiv_symm_apply (F : J ⥤ AlgCat.{t} R)
    (s : SemimoduleCat.sectionsSubmodule
      (F ⋙ forget₂ (AlgCat R) (ModuleCat R) ⋙ ModuleCat.equivalenceSemimoduleCat.functor)) (j : J) :
    ((sectionsLinearEquiv F).symm s).val j = s.val j := (rfl)

variable {F G H : J ⥤ AlgCat.{t} R}

/-- A natural transformation transports algebra sections by an algebra homomorphism.
Its underlying map is Mathlib's section transport. -/
def sectionsMap (α : F ⟶ G) : sectionsSubalgebra F →ₐ[R] sectionsSubalgebra G where
  toFun := (Functor.sectionsFunctor J).map (Functor.whiskerRight α (forget _))
  map_zero' := by ext j; exact map_zero (α.app j).hom
  map_one' := by ext j; exact map_one (α.app j).hom
  map_add' x y := by ext j; exact map_add (α.app j).hom _ _
  map_mul' x y := by ext j; exact map_mul (α.app j).hom _ _
  commutes' r := by ext j; exact (α.app j).hom.commutes r

/-- Section transport applies the coefficient map at each object. -/
@[simp]
theorem sectionsMap_apply (α : F ⟶ G) (s : sectionsSubalgebra F) (j : J) :
    (sectionsMap α s).val j = (α.app j).hom (s.val j) := (rfl)

/-- Identity coefficient changes fix algebra sections. -/
@[simp]
theorem sectionsMap_id : sectionsMap (𝟙 F) = AlgHom.id R _ := by
  ext s j
  simp only [sectionsMap_apply, NatTrans.id_app, AlgCat.hom_id, AlgHom.id_apply]

/-- Successive coefficient changes compose on algebra sections. -/
@[simp]
theorem sectionsMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    sectionsMap (α ≫ β) = (sectionsMap β).comp (sectionsMap α) := by
  ext s j
  simp only [AlgHom.comp_apply, sectionsMap_apply, NatTrans.comp_app,
    AlgCat.hom_comp]

/-- Forgetting algebra structure commutes with coefficient transport as bundled linear maps. -/
theorem sectionsLinearEquiv_naturality (α : F ⟶ G) :
    (sectionsLinearEquiv G).toLinearMap.comp (sectionsMap α).toLinearMap =
      (SemimoduleCat.sectionsMap (Functor.whiskerRight α
        (forget₂ (AlgCat R) (ModuleCat R) ⋙ ModuleCat.equivalenceSemimoduleCat.functor))).comp
          (sectionsLinearEquiv F).toLinearMap := by
  ext s j
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, AlgHom.toLinearMap_apply,
    sectionsLinearEquiv_apply, sectionsMap_apply, SemimoduleCat.sectionsMap_apply,
    Functor.whiskerRight_app]
  exact (forgotten_map_apply (α.app j) (s.val j)).symm

end AlgCat
