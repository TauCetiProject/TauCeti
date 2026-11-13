/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Mod.Free.Basic
public import TauCeti.CategoryTheory.Monoidal.Mod.Closed
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Free modules and closed tensor products

Balanced tensoring with a free module agrees with tensoring the underlying generating
object with the other module. The comparison is natural in the generating object and is
characterized by its value on the free generators. Internal linear maps out of a free
module similarly agree with maps out of its generators. These comparisons use the
existing free-module adjunction `TauCeti.freeModAdjunction`, the internal-hom adjunctions,
and Mathlib's uniqueness isomorphisms for adjoints.
-/

public section

universe v u

namespace CategoryTheory.Mod

open MonoidalCategory BraidedCategory MonObj MonoidalClosed Limits
open TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

/-- Tensoring a free module with an object is free on the tensor of generators. -/
def tensorLeftFreeIso (V : C) :
    Mod.tensorLeft ((freeMod A).obj V) ≅
      MonoidalCategory.tensorLeft V ⋙ freeMod A :=
  NatIso.ofComponents (fun K ↦
    { hom := Hom.mk' (M := (Mod.tensorLeft ((freeMod A).obj V)).obj K)
        (N := (freeMod A).obj (V ⊗ K)) (α_ A V K).hom (by
        rw [tensorLeft_smul, freeMod_smul A (V ⊗ K), freeMod_smul A V]
        simp only [selfLeftAction_actionHomRight, Category.assoc, comp_whiskerRight]
        rw [associator_naturality_left]
        monoidal)
      inv := Hom.mk' (M := (freeMod A).obj (V ⊗ K))
        (N := (Mod.tensorLeft ((freeMod A).obj V)).obj K) (α_ A V K).inv (by
        rw [tensorLeft_smul, freeMod_smul A (V ⊗ K), freeMod_smul A V]
        simp only [selfLeftAction_actionHomRight, Category.assoc, comp_whiskerRight]
        rw [associator_inv_naturality_left]
        monoidal) })
    (by intro K L f; ext; simp)

/-- The free tensor comparison is the ambient associator. -/
@[simp]
lemma tensorLeftFreeIso_hom_app_hom (V K : C) :
    ((tensorLeftFreeIso (A := A) V).hom.app K).hom = (α_ A V K).hom := by rfl

/-- The inverse free tensor comparison is the inverse ambient associator. -/
@[simp]
lemma tensorLeftFreeIso_inv_app_hom (V K : C) :
    ((tensorLeftFreeIso (A := A) V).inv.app K).hom = (α_ A V K).inv := by rfl

variable [MonoidalClosed C] [HasEqualizers C]

/-- Internal linear maps from a free module are all maps from its generating object. -/
noncomputable def ihomFreeIso (V : C) :
    Mod.ihom ((freeMod A).obj V) ≅ Mod.forget A ⋙ CategoryTheory.ihom V :=
  (ihomAdjunction ((freeMod A).obj V)).rightAdjointUniq
    (((CategoryTheory.ihom.adjunction V).comp (freeModAdjunction A)).ofNatIsoLeft
      (tensorLeftFreeIso (A := A) V).symm)

/-- The free internal-hom comparison restricts an `A`-linear map to its generators. -/
lemma ihomFreeIso_hom_app (V : C) (N : Mod C A) :
    (ihomFreeIso (A := A) V).hom.app N =
      ihomι ((freeMod A).obj V) N ≫ (MonoidalClosed.pre (freeModι A V)).app N.X := by
  let adj := ((CategoryTheory.ihom.adjunction V).comp (freeModAdjunction A)).ofNatIsoLeft
    (tensorLeftFreeIso (A := A) V).symm
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (ihomAdjunction ((freeMod A).obj V)) adj N
  have h' : (ihomFreeIso (A := A) V).hom.app N =
      (CategoryTheory.ihom.adjunction V).homEquiv _ _
        (freeModHomEquiv A _ N ((tensorLeftFreeIso (A := A) V).inv.app _ ≫
          (ihomAdjunction ((freeMod A).obj V)).counit.app N)) := by
    have hh := congrArg (adj.homEquiv ((Mod.ihom ((freeMod A).obj V)).obj N) N) h
    rw [Equiv.apply_symm_apply] at hh
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv] at hh
    simp only [freeModAdjunction_homEquiv] at hh
    exact hh
  calc
    _ = (CategoryTheory.ihom.adjunction V).homEquiv _ _
        (freeModHomEquiv A _ N ((tensorLeftFreeIso (A := A) V).inv.app _ ≫
          (ihomAdjunction ((freeMod A).obj V)).counit.app N)) := h'
    _ = _ := by
      rw [freeModHomEquiv_apply]
      simp only [comp_hom', tensorLeftFreeIso_inv_app_hom,
        ihomAdjunction_counit_app_hom, curriedTensor_obj_obj]
      rw [← Category.assoc, freeModι_tensor, homEquiv_apply_eq,
        ← curry_pre_app, curry_uncurry]

variable [BraidedCategory C] [IsCommMonObj A] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- Restriction from free-module maps commutes with precomposition on generators. -/
@[reassoc]
lemma ihomFreeIso_hom_naturality_left {V W : C} (f : V ⟶ W) (N : Mod C A) :
    ((MonoidalClosed.pre ((freeMod A).map f)).app N).hom ≫
        (ihomFreeIso (A := A) V).hom.app N =
      (ihomFreeIso (A := A) W).hom.app N ≫ (MonoidalClosed.pre f).app N.X := by
  let p : (internalHom ((freeMod A).obj W)).obj N ⟶
      (internalHom ((freeMod A).obj V)).obj N := (MonoidalClosed.pre ((freeMod A).map f)).app N
  let cV : (Mod.ihom ((freeMod A).obj V)).obj N ⟶ (CategoryTheory.ihom V).obj N.X :=
    (ihomFreeIso (A := A) V).hom.app N
  let cW : (Mod.ihom ((freeMod A).obj W)).obj N ⟶ (CategoryTheory.ihom W).obj N.X :=
    (ihomFreeIso (A := A) W).hom.app N
  have hcV : cV = ihomι ((freeMod A).obj V) N ≫
      (MonoidalClosed.pre (freeModι A V)).app N.X := ihomFreeIso_hom_app V N
  have hcW : cW = ihomι ((freeMod A).obj W) N ≫
      (MonoidalClosed.pre (freeModι A W)).app N.X := ihomFreeIso_hom_app W N
  have hp : p.hom ≫ ihomι ((freeMod A).obj V) N =
      ihomι ((freeMod A).obj W) N ≫
        (MonoidalClosed.pre ((freeMod A).map f).hom).app N.X :=
    pre_app_hom_comp_ihomι ((freeMod A).map f) N
  -- Name the ambient carriers before composing module and base internal homs.
  change p.hom ≫ cV = cW ≫ _
  rw [hcV, hcW, ← Category.assoc, hp, Category.assoc, Category.assoc]
  have h := congrArg (fun g ↦ (MonoidalClosed.pre g).app N.X) (freeModι_naturality A f)
  rw [pre_map, pre_map, NatTrans.comp_app, NatTrans.comp_app] at h
  exact congrArg (fun g ↦ ihomι ((freeMod A).obj W) N ≫ g) h.symm

/-- Balanced tensoring with a free module is tensoring with its generating object,
naturally in that object. -/
noncomputable def tensorFreeIso (M : Mod C A) :
    freeMod A ⋙ MonoidalCategory.tensorLeft M ≅ Mod.tensorLeft M :=
  ((freeModAdjunction A).comp (internalHomAdjunction M)).leftAdjointUniq
    (ihomAdjunction M)

/-- The comparison identifies the two currying bijections after restriction to free generators. -/
private lemma tensorFreeIso_hom_homEquiv (M : Mod C A) (V : C) :
    freeModι A V ≫ (tensorHomEquiv M ((freeMod A).obj V) ((Mod.tensorLeft M).obj V)
      ((tensorFreeIso M).hom.app V)).hom =
      ihomHomEquiv M V ((Mod.tensorLeft M).obj V) (𝟙 _) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((freeModAdjunction A).comp (internalHomAdjunction M)) (ihomAdjunction M) V
  rw [Adjunction.comp_homEquiv] at h
  simp only [Equiv.trans_apply] at h
  rw [freeModAdjunction_homEquiv, internalHomAdjunction_homEquiv,
    ← Adjunction.homEquiv_id, ihomAdjunction_homEquiv] at h
  -- The composite adjunction retains the forgetful functor's hom-type and EquivLike
  -- instances; normalize both so the generator-restriction equation matches.
  dsimp +instances only [Mod.forget] at h
  rw [freeModHomEquiv_apply] at h
  exact h

/-- On generators, the free balanced tensor comparison is the identity on `M.X ⊗ V`. -/
@[simp↓, reassoc (attr := simp↓)]
lemma freeModι_tensorπ_tensorFreeIso_hom (M : Mod C A) (V : C) :
    M.X ◁ freeModι A V ≫ tensorπ M ((freeMod A).obj V) ≫
      ((tensorFreeIso M).hom.app V).hom = 𝟙 (M.X ⊗ V) := by
  apply curry_injective
  rw [curry_natural_left]
  have h := tensorFreeIso_hom_homEquiv M V
  have h' : freeModι A V ≫
      (tensorHomEquiv M ((freeMod A).obj V) ((Mod.tensorLeft M).obj V)
        ((tensorFreeIso M).hom.app V)).hom ≫ ihomι M ((Mod.tensorLeft M).obj V) =
      ihomHomEquiv M V ((Mod.tensorLeft M).obj V) (𝟙 _) ≫
        ihomι M ((Mod.tensorLeft M).obj V) :=
    by simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ ihomι M ((Mod.tensorLeft M).obj V)) h
  have h₁ := tensorHomEquiv_apply_hom_comp_ihomι M ((freeMod A).obj V)
    ((Mod.tensorLeft M).obj V) ((tensorFreeIso M).hom.app V)
  have h₂ := ihomHomEquiv_apply_comp_ihomι M (𝟙 ((Mod.tensorLeft M).obj V))
  simpa only [id_hom'] using
    (congrArg (fun f ↦ freeModι A V ≫ f) h₁).symm.trans (h'.trans h₂)

/-- The inverse balanced comparison inserts the free generators and takes their balanced class. -/
@[simp]
lemma tensorFreeIso_inv_app_hom (M : Mod C A) (V : C) :
    ((tensorFreeIso M).inv.app V).hom =
      M.X ◁ freeModι A V ≫ tensorπ M ((freeMod A).obj V) := by
  have h : ((tensorFreeIso M).hom.app V).hom ≫
      ((tensorFreeIso M).inv.app V).hom = 𝟙 _ := by
    simpa only [comp_hom', id_hom'] using
      congrArg Hom.hom ((tensorFreeIso M).hom_inv_id_app V)
  calc
    _ = (M.X ◁ freeModι A V ≫ tensorπ M ((freeMod A).obj V) ≫
        ((tensorFreeIso M).hom.app V).hom) ≫
        ((tensorFreeIso M).inv.app V).hom := by
      rw [freeModι_tensorπ_tensorFreeIso_hom, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, Category.assoc, h]
      simp only [Functor.comp_obj, curriedTensor_obj_obj, Category.comp_id]

/-- The balanced free comparison is natural in the other module as well. -/
noncomputable def tensorRightFreeIso (V : C) :
    MonoidalCategory.tensorRight ((freeMod A).obj V) ≅ Mod.tensorRight (A := A) V :=
  NatIso.ofComponents (fun M ↦ (tensorFreeIso M).app V) (by
    intro M N f
    rw [← cancel_epi ((tensorFreeIso M).inv.app V)]
    apply Hom.ext
    simp only [comp_hom', tensorFreeIso_inv_app_hom, Functor.flip_obj_map,
      curriedTensor_map_app, Category.assoc, tensorπ_whiskerRight_hom_assoc,
      Hom.mk'_hom, Iso.app_hom]
    rw [whisker_exchange_assoc, freeModι_tensorπ_tensorFreeIso_hom,
      freeModι_tensorπ_tensorFreeIso_hom_assoc]
    simp)

/-- The forward free comparison in the module variable is the forward comparison
constructed by fixing the module. -/
@[simp]
lemma tensorRightFreeIso_hom_app (V : C) (M : Mod C A) :
    (tensorRightFreeIso (A := A) V).hom.app M = (tensorFreeIso M).hom.app V := by rfl

/-- The inverse free comparison in the module variable is the inverse comparison
constructed by fixing the module. -/
@[simp]
lemma tensorRightFreeIso_inv_app (V : C) (M : Mod C A) :
    (tensorRightFreeIso (A := A) V).inv.app M = (tensorFreeIso M).inv.app V := by rfl

end CategoryTheory.Mod
