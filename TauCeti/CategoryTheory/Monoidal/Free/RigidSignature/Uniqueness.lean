/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.RigidSignature.Basic

/-!
# Uniqueness for the free rigid monoidal category on a rigid signature

This file proves the uniqueness half of the universal property of `RigidSignature.FreeRigid S`:
strong monoidal functors out of `S.FreeRigid` into an arbitrary monoidal category `D` (not
required to be rigid) are determined up to unique monoidal natural isomorphism by their action on
the generating objects and coupons.

Because a strong monoidal functor carries every exact pairing in `S.FreeRigid` to an exact
pairing in `D`, and duals are unique up to unique isomorphism, any family of isomorphisms
`e : ∀ a, F.obj (of a) ≅ G.obj (of a)` at the generating objects extends canonically to all
formal rigid objects (`FreeRigid.wordIso`). When `e` is compatible with every coupon, these
components assemble into a monoidal natural isomorphism `FreeRigid.monoidalNatIso`. Moreover,
any two monoidal natural transformations between strong monoidal functors out of `S.FreeRigid`
that agree on the generating objects are equal (`FreeRigid.natTrans_ext`).

## Main definitions and results

* `TauCeti.RigidSignature.FreeRigid.natTrans_ext`: monoidal natural transformations between
  strong monoidal functors out of `S.FreeRigid` into any monoidal category are determined by
  their components at the generating objects.
* `TauCeti.RigidSignature.FreeRigid.wordIso`: canonical extension of generating-object
  isomorphisms `e` to all objects of `S.FreeRigid`.
* `TauCeti.RigidSignature.FreeRigid.map_comp_wordIso_hom` and
  `TauCeti.RigidSignature.FreeRigid.monoidalNatIso`: naturality of `wordIso` whenever it respects
  the coupons, assembling into a monoidal natural isomorphism `F ≅ G`.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
* A. Joyal and R. Street, *Planar diagrams and tensor algebra* (1988), §2.
* P. Selinger, *A survey of graphical languages for monoidal categories*, Lecture Notes in Physics
  813 (2011), §4.1.
-/

public section

universe u v u' v'

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.RigidSignature.FreeRigid

variable {S : RigidSignature.{u, v}} {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal natural transformation between strong monoidal functors out of the free rigid
monoidal category on `S` (into any monoidal category `D`, not required to be rigid) is determined
by its components at the generating objects. -/
theorem natTrans_ext {F G : S.FreeRigid ⥤ D} [F.Monoidal] [G.Monoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β] (h : ∀ a, α.app (of a) = β.app (of a)) :
    α = β := by
  ext ⟨X⟩
  induction X with
  | of a => exact h a
  | unit =>
    rw [← cancel_epi (ε F)]
    exact (NatTrans.IsMonoidal.unit (τ := α)).trans (NatTrans.IsMonoidal.unit (τ := β)).symm
  | tensor X Y hX hY =>
    rw [← cancel_epi (μ F ⟨X⟩ ⟨Y⟩)]
    refine (NatTrans.IsMonoidal.tensor (τ := α) ⟨X⟩ ⟨Y⟩).trans ?_
    refine Eq.trans ?_ (NatTrans.IsMonoidal.tensor (τ := β) ⟨X⟩ ⟨Y⟩).symm
    rw [hX, hY]
  | rightDual X hX =>
    let : ExactPairing (⟨X⟩ : S.FreeRigid) (⟨X.rightDual⟩ : S.FreeRigid) :=
      (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
    exact NatTrans.app_right_eq_of_exactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩ hX
  | leftDual X hX =>
    let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) (⟨X⟩ : S.FreeRigid) :=
      (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
    exact NatTrans.app_left_eq_of_exactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩ hX

variable (F G : S.FreeRigid ⥤ D) [F.Monoidal] [G.Monoidal] (e : ∀ a, F.obj (of a) ≅ G.obj (of a))

/-- The isomorphism between the images of a formal rigid object expression under two strong
monoidal functors out of `S.FreeRigid` (into any monoidal category `D`), induced by isomorphisms
`e` at the generating objects, the monoidal comparisons of `F` and `G`, and the uniqueness of
right and left duals for the image exact pairings. -/
noncomputable def wordIso : ∀ X : RigidObject S.Obj, F.obj ⟨X⟩ ≅ G.obj ⟨X⟩
  | .of a => e a
  | .unit => (Functor.Monoidal.εIso F).symm ≪≫ Functor.Monoidal.εIso G
  | .tensor X Y =>
    (Functor.Monoidal.μIso F ⟨X⟩ ⟨Y⟩).symm ≪≫ (wordIso X ⊗ᵢ wordIso Y) ≪≫
      Functor.Monoidal.μIso G ⟨X⟩ ⟨Y⟩
  | .rightDual X =>
    letI : ExactPairing (⟨X⟩ : S.FreeRigid) (⟨X.rightDual⟩ : S.FreeRigid) :=
      (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
    rightDualIso (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩)
      (@exactPairingCongrLeft D _ _ _ _ _
        (G.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩) (wordIso X))
  | .leftDual X =>
    letI : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) (⟨X⟩ : S.FreeRigid) :=
      (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
    leftDualIso (F.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩)
      (@exactPairingCongrRight D _ _ _ _ _
        (G.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩) (wordIso X))

@[simp]
theorem wordIso_of (a : S.Obj) : wordIso F G e (of a).as = e a := by rfl

@[simp]
theorem wordIso_tensorUnit_hom : (wordIso F G e (𝟙_ S.FreeRigid).as).hom = η F ≫ ε G := by rfl

@[simp]
theorem wordIso_tensor_hom (X Y : S.FreeRigid) :
    (wordIso F G e (X ⊗ Y).as).hom =
      δ F X Y ≫ ((wordIso F G e X.as).hom ⊗ₘ (wordIso F G e Y.as).hom) ≫ μ G X Y := by rfl

theorem wordIso_rightDual (X : RigidObject S.Obj) :
    wordIso F G e X.rightDual =
      let : ExactPairing (⟨X⟩ : S.FreeRigid) (⟨X.rightDual⟩ : S.FreeRigid) :=
        (RightRigidCategory.rightDual (⟨X⟩ : S.FreeRigid)).exact
      rightDualIso (F.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩)
        (@exactPairingCongrLeft D _ _ _ _ _
          (G.mapExactPairing (⟨X⟩ : S.FreeRigid) ⟨X.rightDual⟩) (wordIso F G e X)) := by
  rfl

theorem wordIso_leftDual (X : RigidObject S.Obj) :
    wordIso F G e X.leftDual =
      let : ExactPairing (⟨X.leftDual⟩ : S.FreeRigid) (⟨X⟩ : S.FreeRigid) :=
        (LeftRigidCategory.leftDual (⟨X⟩ : S.FreeRigid)).exact
      leftDualIso (F.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩)
        (@exactPairingCongrRight D _ _ _ _ _
          (G.mapExactPairing (⟨X.leftDual⟩ : S.FreeRigid) ⟨X⟩) (wordIso F G e X)) := by
  rfl

variable {F G e}

private theorem wordIso_naturality_ε_right (X : S.FreeRigid) :
    F.map (@ExactPairing.evaluation S.FreeRigid _ _ X _ (RightRigidCategory.rightDual X).exact) ≫
        (wordIso F G e (𝟙_ S.FreeRigid).as).hom =
      (wordIso F G e ((RightRigidCategory.rightDual X).rightDual ⊗ X).as).hom ≫
        G.map (@ExactPairing.evaluation S.FreeRigid _ _ X _
          (RightRigidCategory.rightDual X).exact) := by
  let : ExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid) := (RightRigidCategory.rightDual X).exact
  let pF := F.mapExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid)
  let pG := G.mapExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid)
  let pG' := @exactPairingCongrLeft D _ _ _ _ _ pG (wordIso F G e X.as)
  have h := ExactPairing.rightDualIso_hom_whiskerRight_evaluation pF pG'
  rw [← congrArg Iso.hom (wordIso_rightDual F G e X.as),
    @exactPairingCongrLeft_evaluation D _ _ _ _ _ pG (wordIso F G e X.as),
    ← tensorHom_def_assoc, Functor.mapExactPairing_evaluation,
    Functor.mapExactPairing_evaluation] at h
  rw [wordIso_tensorUnit_hom, wordIso_tensor_hom, ← cancel_epi (μ F ⟨X.as.rightDual⟩ X),
    ← cancel_mono (η G)]
  simpa [rightDual_eq, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    Functor.Monoidal.ε_η] using h.symm

private theorem wordIso_naturality_η_right (X : S.FreeRigid) :
    F.map (@ExactPairing.coevaluation S.FreeRigid _ _ X _
          (RightRigidCategory.rightDual X).exact) ≫
        (wordIso F G e (X ⊗ (RightRigidCategory.rightDual X).rightDual).as).hom =
      (wordIso F G e (𝟙_ S.FreeRigid).as).hom ≫
        G.map (@ExactPairing.coevaluation S.FreeRigid _ _ X _
          (RightRigidCategory.rightDual X).exact) := by
  let : ExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid) := (RightRigidCategory.rightDual X).exact
  let pF := F.mapExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid)
  let pG := G.mapExactPairing X (⟨X.as.rightDual⟩ : S.FreeRigid)
  let pG' := @exactPairingCongrLeft D _ _ _ _ _ pG (wordIso F G e X.as)
  have h := ExactPairing.coevaluation_comp_rightMate pG' pF (𝟙 (F.obj X))
  rw [← ExactPairing.rightDualIso_hom pF pG', id_whiskerRight, Category.comp_id,
    ← congrArg Iso.hom (wordIso_rightDual F G e X.as),
    @exactPairingCongrLeft_coevaluation D _ _ _ _ _ pG (wordIso F G e X.as)] at h
  have h' := congrArg (· ≫ (wordIso F G e X.as).hom ▷ G.obj ⟨X.as.rightDual⟩) h
  rw [Category.assoc, Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight,
    Category.comp_id, ← tensorHom_def', Functor.mapExactPairing_coevaluation,
    Functor.mapExactPairing_coevaluation] at h'
  rw [wordIso_tensorUnit_hom, wordIso_tensor_hom, ← cancel_epi (ε F),
    ← cancel_mono (δ G X ⟨X.as.rightDual⟩)]
  simpa [rightDual_eq, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    Functor.Monoidal.ε_η_assoc] using h'

private theorem wordIso_naturality_ε_left (X : S.FreeRigid) :
    F.map (@ExactPairing.evaluation S.FreeRigid _ _ _ X (LeftRigidCategory.leftDual X).exact) ≫
        (wordIso F G e (𝟙_ S.FreeRigid).as).hom =
      (wordIso F G e (X ⊗ (LeftRigidCategory.leftDual X).leftDual).as).hom ≫
        G.map (@ExactPairing.evaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) := by
  let : ExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X := (LeftRigidCategory.leftDual X).exact
  let pF := F.mapExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X
  let pG := G.mapExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X
  let pG' := @exactPairingCongrRight D _ _ _ _ _ pG (wordIso F G e X.as)
  have h := ExactPairing.leftMate_comp_evaluation pG' pF (𝟙 (F.obj X))
  rw [← ExactPairing.leftDualIso_hom pF pG', id_whiskerRight, Category.id_comp,
    ← congrArg Iso.hom (wordIso_leftDual F G e X.as),
    @exactPairingCongrRight_evaluation D _ _ _ _ _ pG (wordIso F G e X.as),
    ← tensorHom_def'_assoc, Functor.mapExactPairing_evaluation,
    Functor.mapExactPairing_evaluation] at h
  rw [wordIso_tensorUnit_hom, wordIso_tensor_hom, ← cancel_epi (μ F X ⟨X.as.leftDual⟩),
    ← cancel_mono (η G)]
  simpa [leftDual_eq, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    Functor.Monoidal.ε_η] using h.symm

private theorem wordIso_naturality_η_left (X : S.FreeRigid) :
    F.map (@ExactPairing.coevaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) ≫
        (wordIso F G e ((LeftRigidCategory.leftDual X).leftDual ⊗ X).as).hom =
      (wordIso F G e (𝟙_ S.FreeRigid).as).hom ≫
        G.map (@ExactPairing.coevaluation S.FreeRigid _ _ _ X
          (LeftRigidCategory.leftDual X).exact) := by
  let : ExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X := (LeftRigidCategory.leftDual X).exact
  let pF := F.mapExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X
  let pG := G.mapExactPairing (⟨X.as.leftDual⟩ : S.FreeRigid) X
  let pG' := @exactPairingCongrRight D _ _ _ _ _ pG (wordIso F G e X.as)
  have h := ExactPairing.coevaluation_comp_leftMate pG' pF (𝟙 (F.obj X))
  rw [← ExactPairing.leftDualIso_hom pF pG', MonoidalCategory.whiskerLeft_id, Category.comp_id,
    ← congrArg Iso.hom (wordIso_leftDual F G e X.as),
    @exactPairingCongrRight_coevaluation D _ _ _ _ _ pG (wordIso F G e X.as)] at h
  have h' := congrArg (· ≫ G.obj ⟨X.as.leftDual⟩ ◁ (wordIso F G e X.as).hom) h
  rw [Category.assoc, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id, ← tensorHom_def,
    Functor.mapExactPairing_coevaluation, Functor.mapExactPairing_coevaluation] at h'
  rw [wordIso_tensorUnit_hom, wordIso_tensor_hom, ← cancel_epi (ε F),
    ← cancel_mono (δ G ⟨X.as.leftDual⟩ X)]
  simpa [leftDual_eq, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    Functor.Monoidal.ε_η_assoc] using h'

/- Composites with tensors of morphisms are folded into a single tensor of composites, so that
the tensorators cancel inside each tensor factor. -/
attribute [local simp] whiskerLeft_comp_tensorHom whiskerLeft_comp_tensorHom_assoc
  whiskerRight_comp_tensorHom whiskerRight_comp_tensorHom_assoc tensorHom_comp_whiskerLeft
  tensorHom_comp_whiskerLeft_assoc tensorHom_comp_whiskerRight tensorHom_comp_whiskerRight_assoc

/-- The isomorphisms `wordIso F G e` are natural as soon as they are natural with respect to
the coupons. -/
theorem map_comp_wordIso_hom
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))
    {X Y : S.FreeRigid} (f : X ⟶ Y) :
    F.map f ≫ (wordIso F G e Y.as).hom = (wordIso F G e X.as).hom ≫ G.map f := by
  induction f using Hom.inductionOn with
  | id X => simp
  | α_hom X Y Z =>
    rw [← cancel_epi (μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z),
      ← cancel_mono (δ G X (Y ⊗ Z) ≫ G.obj X ◁ δ G Y Z)]
    simp [← Functor.OplaxMonoidal.associativity]
  | α_inv X Y Z =>
    rw [← cancel_epi (F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z)),
      ← cancel_mono (δ G (X ⊗ Y) Z ≫ δ G X Y ▷ G.obj Z)]
    simp [← Functor.OplaxMonoidal.associativity_inv]
  | l_hom X =>
    rw [← cancel_epi (ε F ▷ F.obj X ≫ μ F (𝟙_ _) X)]
    simp
    simp [tensorHom_def']
  | l_inv X =>
    rw [← cancel_mono (δ G (𝟙_ _) X ≫ η G ▷ G.obj X)]
    simp
    simp [MonoidalCategory.tensorHom_def, ← Functor.OplaxMonoidal.left_unitality]
  | ρ_hom X =>
    rw [← cancel_epi (F.obj X ◁ ε F ≫ μ F X (𝟙_ _))]
    simp
    simp [MonoidalCategory.tensorHom_def]
  | ρ_inv X =>
    rw [← cancel_mono (δ G X (𝟙_ _) ≫ G.obj X ◁ η G)]
    simp
    simp [tensorHom_def', ← Functor.OplaxMonoidal.right_unitality]
  | η_right X => exact wordIso_naturality_η_right X
  | ε_right X => exact wordIso_naturality_ε_right X
  | η_left X => exact wordIso_naturality_η_left X
  | ε_left X => exact wordIso_naturality_ε_left X
  | coupon g => exact he g
  | comp f g hf hg =>
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg, reassoc_of% hf]
  | whiskerLeft X f hf =>
    simp only [wordIso_tensor_hom, Functor.Monoidal.map_whiskerLeft, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerLeft_comp_tensorHom_assoc,
      tensorHom_comp_whiskerLeft_assoc, hf]
  | whiskerRight f X hf =>
    simp only [wordIso_tensor_hom, Functor.Monoidal.map_whiskerRight, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, whiskerRight_comp_tensorHom_assoc,
      tensorHom_comp_whiskerRight_assoc, hf]

/-- Two strong monoidal functors out of the free rigid monoidal category on `S` (into an arbitrary
monoidal category `D`) that agree up to isomorphisms `e` on the generating objects, compatibly
with every coupon, are isomorphic by a monoidal natural isomorphism extending `e`. -/
noncomputable def monoidalNatIso
    (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
      (wordIso F G e (S.src g)).hom ≫ G.map (coupon g)) :
    F ≅ G :=
  NatIso.ofComponents (fun X ↦ wordIso F G e X.as) fun f ↦ map_comp_wordIso_hom he f

variable (he : ∀ g, F.map (coupon g) ≫ (wordIso F G e (S.tgt g)).hom =
  (wordIso F G e (S.src g)).hom ≫ G.map (coupon g))

@[simp]
theorem monoidalNatIso_hom_app (X : S.FreeRigid) :
    (monoidalNatIso he).hom.app X = (wordIso F G e X.as).hom := by rfl

theorem monoidalNatIso_hom_app_of (a : S.Obj) :
    (monoidalNatIso he).hom.app (of a) = (e a).hom := by rfl

@[simp]
theorem monoidalNatIso_inv_app (X : S.FreeRigid) :
    (monoidalNatIso he).inv.app X = (wordIso F G e X.as).inv := by rfl

theorem monoidalNatIso_inv_app_of (a : S.Obj) :
    (monoidalNatIso he).inv.app (of a) = (e a).inv := by rfl

instance : NatTrans.IsMonoidal (monoidalNatIso he).hom where
  unit := by
    rw [monoidalNatIso_hom_app, wordIso_tensorUnit_hom, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by
    rw [monoidalNatIso_hom_app, wordIso_tensor_hom, Functor.Monoidal.μ_δ_assoc,
      monoidalNatIso_hom_app, monoidalNatIso_hom_app]

end TauCeti.RigidSignature.FreeRigid
