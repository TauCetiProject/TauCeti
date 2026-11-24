/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Condensed.Light.Functors
public import Mathlib.Condensed.Light.Module

import TauCeti.CategoryTheory.Sites.FreeYoneda

/-!
# Free light condensed modules on test spaces

The free-forgetful adjunction and the sheaf Yoneda equivalence identify maps out
of a free test object with sections on the test space.
-/

public section

universe u

open CategoryTheory LightCondensed

namespace LightProfinite

variable {R : Type u} [Ring R] {M : LightCondMod R}

/-- Maps from the free light condensed module on a test space correspond to sections there. -/
noncomputable def freeModuleHomEquiv (S : LightProfinite.{u}) :
    ((free R).obj S.toCondensed ⟶ M) ≃+ M.obj.obj (Opposite.op S) :=
  (ModuleCat.adj R).freeYonedaSectionsAddEquiv
    (A := forget₂ (ModuleCat R) AddCommGrpCat) (coherentTopology LightProfinite) S M

/-- The underlying natural transformation of the free-forgetful adjunction is the
coefficient adjunction after the sheafification adjunction. -/
private lemma freeForgetAdjunction_homEquiv_hom (S : LightProfinite.{u})
    (g : (free R).obj S.toCondensed ⟶ M) :
    ((freeForgetAdjunction R).homEquiv _ _ g).hom =
      ((ModuleCat.adj R).whiskerRight LightProfiniteᵒᵖ).homEquiv _ _
        ((sheafificationAdjunction (coherentTopology LightProfinite)
          (ModuleCat R)).homEquiv _ _ g) := by
  rfl

/-- The free-section comparison agrees with the free-forgetful adjunction and sheaf Yoneda. -/
lemma freeModuleHomEquiv_apply (S : LightProfinite.{u})
    (g : (free R).obj S.toCondensed ⟶ M) :
    S.freeModuleHomEquiv g = (coherentTopology LightProfinite).yonedaEquiv
      ((freeForgetAdjunction R).homEquiv _ _ g) := by
  trans (ModuleCat.adj R).freeYonedaSectionsEquiv
    (coherentTopology LightProfinite) S M g
  · exact (ModuleCat.adj R).freeYonedaSectionsAddEquiv_apply
      (A := forget₂ (ModuleCat R) AddCommGrpCat) _ S M g
  -- Free on the Yoneda sheaf is definitionally sheafification of the free representable.
  erw [Adjunction.freeYonedaSectionsEquiv_apply]
  rw [GrothendieckTopology.yonedaEquiv_apply, yonedaEquiv_apply]
  exact congrArg (fun f => f.app (Opposite.op S) (𝟙 S))
    (freeForgetAdjunction_homEquiv_hom S g).symm

/-- Precomposing with the free map induced by `f : S ⟶ T` restricts a section on `T`
to `S` along `f`. -/
@[simp↓] -- Prefer restriction to coefficient naturality on this composite.
lemma freeModuleHomEquiv_comp {S T : LightProfinite.{u}} (f : S ⟶ T)
    (g : (free R).obj T.toCondensed ⟶ M) :
    S.freeModuleHomEquiv ((free R).map (lightProfiniteToLightCondSet.map f) ≫ g) =
      M.obj.map f.op (T.freeModuleHomEquiv g) := by
  exact (ModuleCat.adj R).freeYonedaSectionsAddEquiv_naturality_left
    (A := forget₂ (ModuleCat R) AddCommGrpCat) (coherentTopology LightProfinite) f M g

/-- Postcomposition by a module morphism applies its section map to the corresponding section. -/
@[simp]
lemma freeModuleHomEquiv_postcomp {S : LightProfinite.{u}} {N : LightCondMod R}
    (g : (free R).obj S.toCondensed ⟶ M) (f : M ⟶ N) :
    S.freeModuleHomEquiv (g ≫ f) = f.hom.app (Opposite.op S) (S.freeModuleHomEquiv g) := by
  exact (ModuleCat.adj R).freeYonedaSectionsAddEquiv_naturality_right
    (A := forget₂ (ModuleCat R) AddCommGrpCat) (coherentTopology LightProfinite) g f

/-- Postcomposing the map corresponding to a section applies the coefficient morphism. -/
@[simp]
lemma freeModuleHomEquiv_symm_postcomp {S : LightProfinite.{u}} {N : LightCondMod R}
    (s : M.obj.obj (Opposite.op S)) (f : M ⟶ N) :
    S.freeModuleHomEquiv.symm (f.hom.app (Opposite.op S) s) =
      S.freeModuleHomEquiv.symm s ≫ f := by
  rw [AddEquiv.symm_apply_eq, freeModuleHomEquiv_postcomp, AddEquiv.apply_symm_apply]

/-- Free test-object evaluation is linear in the coefficient module. -/
lemma freeModuleHomEquiv_smul {R : Type u} [CommRing R] {M : LightCondMod R}
    (S : LightProfinite.{u}) (r : R) (g : (free R).obj S.toCondensed ⟶ M) :
    S.freeModuleHomEquiv (r • g) = r • S.freeModuleHomEquiv g := by
  -- Sheaf morphisms inherit scalar multiplication from the underlying natural
  -- transformations, where both scalar multiplication and identity are pointwise.
  have h : (r • 𝟙 M).hom.app (Opposite.op S) = r • 𝟙 (M.obj.obj (Opposite.op S)) := rfl
  simpa only [Linear.comp_smul, Category.comp_id, h, ModuleCat.hom_smul,
    LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply] using
    (freeModuleHomEquiv_postcomp g (r • 𝟙 M))

/-- The free test-object equivalence as a linear equivalence over the coefficient ring. -/
noncomputable def freeModuleHomLinearEquiv {R : Type u} [CommRing R] {M : LightCondMod R}
    (S : LightProfinite.{u}) :
    ((free R).obj S.toCondensed ⟶ M) ≃ₗ[R] M.obj.obj (Opposite.op S) where
  toAddEquiv := S.freeModuleHomEquiv
  map_smul' := freeModuleHomEquiv_smul S

/-- The linear comparison retains the free-section evaluation. -/
@[simp]
lemma freeModuleHomLinearEquiv_apply {R : Type u} [CommRing R] {M : LightCondMod R}
    (S : LightProfinite.{u}) (g : (free R).obj S.toCondensed ⟶ M) :
    S.freeModuleHomLinearEquiv g = S.freeModuleHomEquiv g := by
  rfl

/-- The inverse linear comparison retains the free-section inverse. -/
@[simp]
lemma freeModuleHomLinearEquiv_symm_apply {R : Type u} [CommRing R] {M : LightCondMod R}
    (S : LightProfinite.{u}) (s : M.obj.obj (Opposite.op S)) :
    S.freeModuleHomLinearEquiv.symm s = S.freeModuleHomEquiv.symm s := by
  rfl

end LightProfinite
