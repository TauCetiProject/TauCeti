/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Topology.Category.LightProfinite.Sequence
public import TauCeti.Condensed.Light.Free

import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The marked convergent sequence in light condensed modules

The reduced free module of a pointed light profinite space is the cokernel of the free
map on its marked point. Applied to the convergent sequence, marked at infinity, it
represents null sequences. The successor map induces an endomorphism of this module
whose precomposition drops the first term of a null sequence.

The marked sequence and its shift follow Rodríguez Camargo, *Notes on Solid Geometry*,
Definition 3.2.1, and Wagner, *q-de Rham cohomology and topological Hochschild homology
over ku*, §2.1.
-/

public section

universe u

open CategoryTheory Category Limits LightCondensed OnePoint Filter

namespace TauCeti

/-- The convergent sequence, with carrier lifted to the universe of the light profinite site. -/
@[expose]
def liftedSequence : LightProfinite.{u} :=
  let e : ULift.{u} (OnePoint ℕ) ≃ₜ OnePoint ℕ := Homeomorph.ulift
  haveI := e.secondCountableTopology
  haveI := e.symm.totallyDisconnectedSpace
  LightProfinite.of (ULift.{u} (OnePoint ℕ))

/-- The lifted sequence is also the one-point compactification of the lifted natural numbers. -/
def liftedSequenceHomeomorph : liftedSequence.{u} ≃ₜ OnePoint (ULift.{u} ℕ) :=
  (Homeomorph.ulift : ULift.{u} (OnePoint ℕ) ≃ₜ OnePoint ℕ).trans
    ((Homeomorph.ulift : ULift.{u} ℕ ≃ₜ ℕ).symm.onePointCongr)

@[simp↓]
lemma liftedSequenceHomeomorph_apply_coe (n : ℕ) :
    liftedSequenceHomeomorph (ULift.up (n : OnePoint ℕ) : liftedSequence.{u}) =
      (ULift.up n : ULift.{u} ℕ) := (rfl)

@[simp↓]
lemma liftedSequenceHomeomorph_apply_infty :
    liftedSequenceHomeomorph (ULift.up (∞ : OnePoint ℕ) : liftedSequence.{u}) = ∞ := (rfl)

/-- Successor on the finite terms of the lifted sequence, fixing infinity. -/
def natShift : liftedSequence.{u} ⟶ liftedSequence.{u} :=
  ConcreteCategory.ofHom ⟨ULift.map (OnePoint.map Nat.succ), continuous_uliftMap _ (by
    rw [OnePoint.continuous_iff_from_nat]
    have h :=
      (OnePoint.continuous_iff_from_nat (id : OnePoint ℕ → OnePoint ℕ)).mp continuous_id
    simpa [Function.comp_def] using h.comp (tendsto_add_atTop_nat 1))⟩

@[simp↓]
lemma natShift_apply_coe (n : ℕ) :
    natShift (ULift.up (n : OnePoint ℕ) : liftedSequence.{u}) =
      ULift.up ((n + 1 : ℕ) : OnePoint ℕ) := (rfl)

@[simp↓]
lemma natShift_apply_infty :
    natShift (ULift.up (∞ : OnePoint ℕ) : liftedSequence.{u}) = ULift.up ∞ := (rfl)

/-- The inclusion of the point at infinity in the lifted sequence. -/
def inftyPoint : LightProfinite.of PUnit.{u + 1} ⟶ liftedSequence.{u} :=
  CompHausLike.const _ (ULift.up ∞)

@[simp↓]
lemma inftyPoint_apply (x : LightProfinite.of PUnit.{u + 1}) :
    inftyPoint x = (ULift.up (∞ : OnePoint ℕ) : liftedSequence.{u}) := (rfl)

@[reassoc (attr := simp)]
lemma inftyPoint_comp_natShift : inftyPoint.{u} ≫ natShift = inftyPoint := by
  ext x
  rfl

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

/-- Morphisms out of the reduced free module correspond to sections that vanish at the
marked point. -/
noncomputable def reducedLightFreeHomEquiv
    (X : Under (LightProfinite.of PUnit.{u + 1})) (M : LightCondMod R) :
    ((reducedLightFree R).obj X ⟶ M) ≃
      {s : M.obj.obj (Opposite.op X.right) // M.obj.map X.hom.op s = 0} := by
  dsimp only [reducedLightFree]
  let F := lightProfiniteToLightCondSet ⋙ free R
  refine
    { toFun := fun g ↦ ⟨X.right.freeModuleHomEquiv (cokernel.π (F.map X.hom) ≫ g), ?_⟩
      invFun := fun s ↦ cokernel.desc (F.map X.hom) (X.right.freeModuleHomEquiv.symm s.val) ?_
      left_inv := ?_
      right_inv := ?_ }
  · rw [← LightProfinite.freeModuleHomEquiv_comp, cokernel.condition_assoc, zero_comp,
      map_zero]
  · apply ((LightProfinite.of PUnit.{u + 1}).freeModuleHomEquiv (M := M)).injective
    rw [LightProfinite.freeModuleHomEquiv_comp, AddEquiv.apply_symm_apply, s.property, map_zero]
  · intro g
    apply (cancel_epi (cokernel.π (F.map X.hom))).mp
    simp
  · intro s
    apply Subtype.ext
    simp

lemma reducedLightFreeHomEquiv_apply
    (X : Under (LightProfinite.of PUnit.{u + 1})) {M : LightCondMod R}
    (g : (reducedLightFree R).obj X ⟶ M) :
    (reducedLightFreeHomEquiv R X M g).val =
      X.right.freeModuleHomEquiv ((toReducedLightFree R).app X ≫ g) := (rfl)

/-- The reduced free light condensed module representing null sequences. -/
noncomputable abbrev nullSeq : LightCondMod R :=
  (reducedLightFree R).obj (Under.mk inftyPoint.{u})

/-- The endomorphism of the null-sequence module induced by successor on the sequence. -/
noncomputable def nullShift : nullSeq R ⟶ nullSeq R :=
  (reducedLightFree R).map (Under.homMk natShift.{u} inftyPoint_comp_natShift.{u})

@[reassoc]
lemma toReducedLightFree_app_comp_map {X Y : Under (LightProfinite.of PUnit.{u + 1})}
    (f : X ⟶ Y) :
    (toReducedLightFree R).app X ≫ (reducedLightFree R).map f =
      (lightProfiniteToLightCondSet ⋙ free R).map f.right ≫ (toReducedLightFree R).app Y := by
  dsimp only [toReducedLightFree, reducedLightFree]
  simp

@[reassoc]
lemma toReducedLightFree_app_inftyPoint_comp_nullShift :
    (toReducedLightFree R).app (Under.mk inftyPoint.{u}) ≫ nullShift R =
      (lightProfiniteToLightCondSet ⋙ free R).map natShift.{u} ≫
        (toReducedLightFree R).app (Under.mk inftyPoint.{u}) := by
  rw [nullShift, toReducedLightFree_app_comp_map]
  rfl

/-- Precomposition by the null shift restricts a section along successor. -/
lemma reducedLightFreeHomEquiv_nullShift
    {M : LightCondMod R} (g : nullSeq R ⟶ M) :
    (reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) M (nullShift R ≫ g)).val =
      M.obj.map natShift.op ((reducedLightFreeHomEquiv R (Under.mk inftyPoint.{u}) M g).val) := by
  simp only [reducedLightFreeHomEquiv_apply, toReducedLightFree_app_inftyPoint_comp_nullShift_assoc]
  exact LightProfinite.freeModuleHomEquiv_comp natShift
    ((toReducedLightFree R).app (Under.mk inftyPoint) ≫ g)

/-- Killing the marked point exhibits the reduced free module as a retract of the ordinary
free module. The retraction is the canonical quotient map. -/
noncomputable def reducedLightFreeRetract (X : Under (LightProfinite.of PUnit.{u + 1})) :
    Retract ((reducedLightFree R).obj X)
      ((lightProfiniteToLightCondSet ⋙ free R).obj X.right) := by
  let F := lightProfiniteToLightCondSet ⋙ free R
  let t := CompHausLike.isTerminalPUnit (P := fun S ↦
    TotallyDisconnectedSpace S ∧ SecondCountableTopology S)
  letI : IsSplitMono (F.map X.hom) :=
    ⟨⟨⟨F.map (t.from X.right), by
      rw [← F.map_comp, t.hom_ext (X.hom ≫ t.from X.right) (𝟙 _), F.map_id]⟩⟩⟩
  let b := binaryBiconeOfIsSplitMonoOfCokernel (cokernelIsCokernel (F.map X.hom))
  exact ⟨b.inr, b.snd, b.inr_snd⟩

@[simp]
lemma reducedLightFreeRetract_r (X : Under (LightProfinite.of PUnit.{u + 1})) :
    (reducedLightFreeRetract R X).r = (toReducedLightFree R).app X := (rfl)

end TauCeti
