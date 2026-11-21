/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import TauCeti.Condensed.Light.Free

/-!
# Reduced free light condensed modules

The free module on a pointed light profinite space, with its marked point killed,
represents sections vanishing at that point. The canonical quotient splits.
-/

public section

universe u

open CategoryTheory Category Limits LightCondensed

namespace TauCeti

variable (R : Type u) [Ring R]

/-- The free light condensed module functor on light profinite spaces, reduced at the
specified point. A pointed map induces the map on cokernels of the free marked inclusions. -/
noncomputable def reducedLightFree :
    Under (LightProfinite.of PUnit.{u + 1}) ⥤ LightCondMod R where
  obj X := cokernel ((lightProfiniteToLightCondSet ⋙ free R).map X.hom)
  map {X Y} f := cokernel.map _ _ (𝟙 _)
    ((lightProfiniteToLightCondSet ⋙ free R).map f.right) (by
      rw [id_comp, ← Functor.map_comp, Under.w])
  map_id X := by
    apply (cancel_epi (cokernel.π _)).mp
    simp
  map_comp f g := by
    apply (cancel_epi (cokernel.π _)).mp
    simp

lemma reducedLightFree_obj (X : Under (LightProfinite.of PUnit.{u + 1})) :
    (reducedLightFree R).obj X =
      cokernel ((lightProfiniteToLightCondSet ⋙ free R).map X.hom) := (rfl)

/-- The reduced free module on the marked singleton is zero. -/
lemma isZero_reducedLightFree_id :
    IsZero ((reducedLightFree R).obj (Under.mk (𝟙 (LightProfinite.of PUnit.{u + 1})))) := by
  rw [reducedLightFree_obj]
  exact isZero_cokernel_of_epi ((lightProfiniteToLightCondSet ⋙ free R).map
    (𝟙 (LightProfinite.of PUnit.{u + 1})))

/-- The quotient from the free module to the reduced free module, natural in pointed
light profinite spaces. -/
noncomputable def toReducedLightFree :
    Under.forget (LightProfinite.of PUnit.{u + 1}) ⋙ lightProfiniteToLightCondSet ⋙ free R ⟶
      reducedLightFree R where
  app X := cokernel.π _
  naturality _ _ _ := by
    simp [reducedLightFree]

@[reassoc (attr := simp)]
lemma free_map_comp_toReducedLightFree (X : Under (LightProfinite.of PUnit.{u + 1})) :
    (free R).map (lightProfiniteToLightCondSet.map X.hom) ≫
      (toReducedLightFree R).app X = 0 :=
  cokernel.condition _

/-- The canonical quotient is a cokernel of the free marked inclusion. -/
noncomputable def toReducedLightFreeIsCokernel
    (X : Under (LightProfinite.of PUnit.{u + 1})) :
    IsColimit (CokernelCofork.ofπ ((toReducedLightFree R).app X)
      (free_map_comp_toReducedLightFree R X)) :=
  cokernelIsCokernel ((lightProfiniteToLightCondSet ⋙ free R).map X.hom)

/-- Morphisms out of the reduced free module correspond to sections that vanish at the
marked point. -/
noncomputable def reducedLightFreeHomEquiv
    (X : Under (LightProfinite.of PUnit.{u + 1})) (M : LightCondMod R) :
    ((reducedLightFree R).obj X ⟶ M) ≃+
      (M.obj.map X.hom.op).hom.toAddMonoidHom.ker := by
  dsimp only [reducedLightFree]
  let F := lightProfiniteToLightCondSet ⋙ free R
  refine
    { toFun := fun g ↦ ⟨X.right.freeModuleHomEquiv (cokernel.π (F.map X.hom) ≫ g), ?_⟩
      invFun := fun s ↦ cokernel.desc (F.map X.hom) (X.right.freeModuleHomEquiv.symm s.val) ?_
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · change M.obj.map X.hom.op _ = 0
    dsimp only [F, Functor.comp_map]
    rw [← LightProfinite.freeModuleHomEquiv_comp, cokernel.condition_assoc, zero_comp,
      map_zero]
  · have hs : M.obj.map X.hom.op s.val = 0 := s.property
    dsimp only [F, Functor.comp_map]
    apply ((LightProfinite.of PUnit.{u + 1}).freeModuleHomEquiv (M := M)).injective
    rw [LightProfinite.freeModuleHomEquiv_comp, AddEquiv.apply_symm_apply, hs, map_zero]
  · intro g
    apply (cancel_epi (cokernel.π (F.map X.hom))).mp
    simp
  · intro s
    apply Subtype.ext
    simp
  · intro f g
    apply Subtype.ext
    change X.right.freeModuleHomEquiv (cokernel.π (F.map X.hom) ≫ (f + g)) =
      X.right.freeModuleHomEquiv (cokernel.π (F.map X.hom) ≫ f) +
        X.right.freeModuleHomEquiv (cokernel.π (F.map X.hom) ≫ g)
    rw [Preadditive.comp_add, map_add]

/-- The underlying section is the free-section comparison after the canonical quotient. -/
lemma reducedLightFreeHomEquiv_apply_val
    (X : Under (LightProfinite.of PUnit.{u + 1})) {M : LightCondMod R}
    (g : (reducedLightFree R).obj X ⟶ M) :
    (reducedLightFreeHomEquiv R X M g).val =
      X.right.freeModuleHomEquiv ((toReducedLightFree R).app X ≫ g) := (rfl)

/-- Precomposition with a pointed map restricts the corresponding section. -/
@[simp]
lemma reducedLightFreeHomEquiv_comp_val
    {X Y : Under (LightProfinite.of PUnit.{u + 1})} (f : X ⟶ Y)
    {M : LightCondMod R} (g : (reducedLightFree R).obj Y ⟶ M) :
    (reducedLightFreeHomEquiv R X M ((reducedLightFree R).map f ≫ g)).val =
      M.obj.map f.right.op (reducedLightFreeHomEquiv R Y M g).val := by
  rw [reducedLightFreeHomEquiv_apply_val,
    ← (toReducedLightFree R).naturality_assoc]
  exact LightProfinite.freeModuleHomEquiv_comp f.right
    ((toReducedLightFree R).app Y ≫ g)

/-- Postcomposition maps the values of the section by the coefficient-module morphism. -/
lemma reducedLightFreeHomEquiv_postcomp_val
    (X : Under (LightProfinite.of PUnit.{u + 1})) {M N : LightCondMod R}
    (g : (reducedLightFree R).obj X ⟶ M) (h : M ⟶ N) :
    (reducedLightFreeHomEquiv R X N (g ≫ h)).val =
      h.hom.app (Opposite.op X.right) (reducedLightFreeHomEquiv R X M g).val := by
  rw [reducedLightFreeHomEquiv_apply_val, ← Category.assoc,
    LightProfinite.freeModuleHomEquiv_postcomp, reducedLightFreeHomEquiv_apply_val]

/-- Killing the marked point exhibits the reduced free module as a retract of the ordinary
free module. The section uses the terminal map to remove the summand generated by the mark. -/
noncomputable def reducedLightFreeRetract (X : Under (LightProfinite.of PUnit.{u + 1})) :
    Retract ((reducedLightFree R).obj X)
      ((lightProfiniteToLightCondSet ⋙ free R).obj X.right) := by
  let F := lightProfiniteToLightCondSet ⋙ free R
  let t := CompHausLike.isTerminalPUnit (P := fun S ↦
    TotallyDisconnectedSpace S ∧ SecondCountableTopology S)
  change Retract (cokernel (F.map X.hom)) (F.obj X.right)
  have ht : F.map X.hom ≫ F.map (t.from X.right) = 𝟙 _ := by
    rw [← F.map_comp, t.hom_ext (X.hom ≫ t.from X.right) (𝟙 _), F.map_id]
  -- The generic split-mono bicone chooses a retraction from an existence proof.
  -- The cokernel descends the projector built from the specified terminal retraction.
  refine ⟨cokernel.desc (F.map X.hom) (𝟙 _ - F.map (t.from X.right) ≫ F.map X.hom) ?_,
    cokernel.π _, ?_⟩
  · simp [Preadditive.comp_sub, ← Category.assoc, ht]
  · apply (cancel_epi (cokernel.π (F.map X.hom))).mp
    rw [cokernel.π_desc_assoc]
    simp [Preadditive.sub_comp, F]

@[simp]
lemma reducedLightFreeRetract_r (X : Under (LightProfinite.of PUnit.{u + 1})) :
    (reducedLightFreeRetract R X).r = (toReducedLightFree R).app X := (rfl)

/-- The chosen section projects away the free summand generated by the marked point. -/
@[reassoc]
lemma toReducedLightFree_comp_reducedLightFreeRetract_i
    (X : Under (LightProfinite.of PUnit.{u + 1})) :
    (toReducedLightFree R).app X ≫ (reducedLightFreeRetract R X).i =
      𝟙 _ - (lightProfiniteToLightCondSet ⋙ free R).map
        ((CompHausLike.isTerminalPUnit (P := fun S ↦
          TotallyDisconnectedSpace S ∧ SecondCountableTopology S)).from X.right) ≫
          (lightProfiniteToLightCondSet ⋙ free R).map X.hom := by
  exact cokernel.π_desc _ _ _

end TauCeti
