/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Extension by zero along a fully faithful functor with downward closed image

Let `G : C ⥤ D` be fully faithful, and suppose that every object of `D` admitting a morphism to an
object `G.obj c` lies in the essential image of `G`. This is the situation of the localization
`Over U ⥤ C` at a subterminal object `U`, for instance the small étale site of an open subscheme
inside the small étale site of a scheme.

Then the left Kan extension along `G.op` of a presheaf `F` on `C` with values in a category with
an initial object exists pointwise: at an object `G.obj c` it is `F.obj (op c)`, and at an object
admitting no morphism to the image of `G` it is the initial object. When the values form a
category with a zero object, this extension by zero preserves finite limits. Consequently, for
continuous `G` between sites, the left adjoint `G.sheafPullback` of restriction of sheaves is
exact on the left. The extension by zero on a lower interval of a preorder,
`TauCeti.CategoryTheory.SheafExtensionByZero`, is the case `G = Over.forget U`.

## Main declarations

* `CategoryTheory.Functor.hasPointwiseLeftKanExtension_op_of_fullyFaithful`: existence of the
  pointwise extension by zero.
* `CategoryTheory.Functor.isZero_lan_obj_obj_of_not_essImage`: its values off the essential
  image; on the essential image they are given by `CategoryTheory.Functor.lanCompEvaluationIsoOfIso`
  from `TauCeti.CategoryTheory.Functor.KanExtension.Adjunction`.
* `CategoryTheory.Functor.preservesFiniteLimits_lan_op_of_fullyFaithful` and
  `CategoryTheory.Functor.preservesFiniteLimits_sheafPullback_of_fullyFaithful`: exactness.

## References

* The Stacks Project, Lemma 18.19.3 (tag 03DJ), and Section 7.25, Localization.
-/

public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {G : C ⥤ D}

variable (hG : G.FullyFaithful) (hG' : ∀ ⦃d : D⦄ ⦃c : C⦄, (d ⟶ G.obj c) → G.essImage d)
  {A : Type*} [Category* A]

include hG hG' in
/-- If `G` is fully faithful with downward closed essential image, presheaves with values in a
category with an initial object have pointwise left Kan extensions along `G.op`. -/
lemma hasPointwiseLeftKanExtension_op_of_fullyFaithful [HasInitial A] (F : Cᵒᵖ ⥤ A) :
    G.op.HasPointwiseLeftKanExtension F := by
  intro d
  by_cases hd : G.essImage d.unop
  · obtain ⟨c, ⟨e⟩⟩ := hd
    have := hG.full
    have := hG.faithful
    exact (hasPointwiseLeftKanExtensionAt_iff_of_iso G.op F e.op.symm).mp
      (HasColimit.mk ⟨_, colimitOfDiagramTerminal
        (CostructuredArrow.mkIdTerminal (S := G.op) (Y := op c)) _⟩)
  · have : IsEmpty (CostructuredArrow G.op d) := ⟨fun f ↦ hd (hG' f.hom.unop)⟩
    let c : Cocone (CostructuredArrow.proj G.op d ⋙ F) :=
      ⟨⊥_ A, { app := fun f ↦ isEmptyElim f, naturality := fun f ↦ isEmptyElim f }⟩
    exact HasColimit.mk ⟨c, (isColimitEquivIsInitialOfIsEmpty (c := c)).symm initialIsInitial⟩

include hG hG' in
/-- If `G` is fully faithful with downward closed essential image, presheaves with values in a
category with an initial object have left Kan extensions along `G.op`. -/
lemma hasLeftKanExtension_op_of_fullyFaithful [HasInitial A] (F : Cᵒᵖ ⥤ A) :
    G.op.HasLeftKanExtension F :=
  have := hasPointwiseLeftKanExtension_op_of_fullyFaithful hG hG' F
  inferInstance

variable [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F]

include hG' in
/-- The left Kan extension along `G.op` vanishes at an object admitting no morphism to an object
of the essential image of `G`, when it is computed pointwise. -/
lemma isZero_lan_obj_obj_of_not_essImage [HasZeroObject A]
    (F : Cᵒᵖ ⥤ A) [G.op.HasPointwiseLeftKanExtension F] {d : D} (hd : ¬ G.essImage d) :
    IsZero ((G.op.lan.obj F).obj (op d)) := by
  have : IsEmpty (CostructuredArrow G.op (op d)) := ⟨fun f ↦ hd (hG' f.hom.unop)⟩
  have h := (isColimitEquivIsInitialOfIsEmpty (c := colimit.cocone (CostructuredArrow.proj G.op
    (op d) ⋙ F))) (colimit.isColimit _)
  exact (isZero_zero A).of_iso ((G.op.leftKanExtensionObjIsoColimit F (op d)) ≪≫
    h.uniqueUpToIso HasZeroObject.zeroIsInitial)

include hG hG' in
/-- Extension by zero along a fully faithful functor with downward closed essential image
preserves finite limits. -/
lemma preservesFiniteLimits_lan_op_of_fullyFaithful [HasZeroObject A] [HasFiniteLimits A] :
    PreservesFiniteLimits (G.op.lan : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) := by
  have := hG.full
  have := hG.faithful
  have := hasPointwiseLeftKanExtension_op_of_fullyFaithful hG hG' (A := A)
  refine preservesFiniteLimits_of_evaluation _ fun d ↦ ?_
  by_cases hd : G.essImage d.unop
  · obtain ⟨c, ⟨e⟩⟩ := hd
    have : PreservesFiniteLimits ((evaluation Cᵒᵖ A).obj (op c)) := ⟨fun _ _ _ ↦ inferInstance⟩
    exact preservesFiniteLimits_of_natIso (lanCompEvaluationIsoOfIso e).symm
  · let := HasZeroObject.zeroMorphismsOfZeroObject (C := A)
    refine ⟨fun J _ _ ↦ preservesLimitsOfShape_of_isZero _ ?_ J⟩
    exact Functor.isZero _ fun F ↦ isZero_lan_obj_obj_of_not_essImage hG' F hd

include hG hG' in
omit [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F] in
/-- For a continuous fully faithful functor `G` with downward closed essential image, the left
adjoint `G.sheafPullback` of restriction of sheaves (extension by zero) preserves finite limits. -/
lemma preservesFiniteLimits_sheafPullback_of_fullyFaithful [HasZeroObject A] [HasFiniteLimits A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
    [HasSheafify K A] [(G.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    PreservesFiniteLimits (G.sheafPullback A J K) := by
  have := hasLeftKanExtension_op_of_fullyFaithful hG hG' (A := A)
  have := preservesFiniteLimits_lan_op_of_fullyFaithful hG hG' (A := A)
  have : PreservesFiniteLimits (sheafPullbackConstruction.sheafPullback G A J K) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (sheafPullbackConstruction.sheafPullbackIso G A J K).symm

end CategoryTheory.Functor
