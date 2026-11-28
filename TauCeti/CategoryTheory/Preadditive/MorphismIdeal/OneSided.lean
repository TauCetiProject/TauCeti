/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Bimod.Submodule
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Opposite

/-!
# One-sided ideals of a preadditive category

A left ideal is a family of submodules of the left slices of the regular bimodule.
A right ideal is a family of submodules of its right slices. Thus left ideals are
closed under precomposition and right ideals under postcomposition. Taking opposites
exchanges the two operations.

A two-sided ideal is a submodule of the regular bimodule itself. Forgetting either
action gives its corresponding one-sided ideal.

An ideal of a single representable can be inserted into the corresponding family by
extending it by zero. In particular, the principal right ideal of `f : X ⟶ Y` at `X`
has components consisting of the composites `f ≫ g`.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §3, p. 18.
* U. Oberst and H. Röhrl, *Flat and coherent functors*, J. Algebra 14 (1970),
  91–105, §1, pp. 93–94.
-/

public section

open CategoryTheory Opposite

universe u v

namespace TauCeti

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- A left ideal of `C` is a submodule of `Hom(-, Y)` for each `Y`. -/
abbrev LeftMorphismIdeal := ModCat.Bimod.LeftSubmodule (ModCat.regularBimod C)

/-- A right ideal of `C` is a submodule of `Hom(X, -)` for each `X`. -/
abbrev RightMorphismIdeal := ModCat.Bimod.RightSubmodule (ModCat.regularBimod C)

variable {C}

namespace LeftMorphismIdeal

/-- The subgroup of maps `X ⟶ Y` belonging to a left ideal. -/
abbrev hom (I : LeftMorphismIdeal C) (X Y : C) : AddSubgroup (X ⟶ Y) :=
  (I Y).carrier (op X)

/-- Construct a left ideal from a family of subgroups closed under precomposition. -/
def ofHom (S : ∀ X Y : C, AddSubgroup (X ⟶ Y))
    (hS : ∀ {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z}, g ∈ S Y Z → f ≫ g ∈ S X Z) :
    LeftMorphismIdeal C :=
  fun Y ↦
    { carrier X := S X.unop Y
      map_mem := fun f g hg ↦
        (ModCat.linearRegularBimod_sliceLeft_obj_map_apply ℤ C Y f g).symm ▸ hS f.unop hg }

@[simp]
theorem hom_ofHom (S : ∀ X Y : C, AddSubgroup (X ⟶ Y)) (hS) (X Y : C) :
    (ofHom S hS).hom X Y = S X Y := (rfl)

/-- Left ideals are closed under precomposition. -/
theorem comp_mem (I : LeftMorphismIdeal C) {X Y Z : C} (f : X ⟶ Y)
    {g : Y ⟶ Z} (hg : g ∈ I.hom Y Z) : f ≫ g ∈ I.hom X Z :=
  ModCat.linearRegularBimod_sliceLeft_obj_map_apply ℤ C Z f.op g ▸ (I Z).map_mem f.op hg

/-- Inclusion of left ideals is pointwise inclusion of their subgroups. -/
theorem le_def {I J : LeftMorphismIdeal C} :
    I ≤ J ↔ ∀ X Y : C, I.hom X Y ≤ J.hom X Y :=
  ⟨fun h X Y ↦ ModCat.Submodule.le_def.mp (h Y) (op X),
    fun h Y ↦ ModCat.Submodule.le_def.mpr fun X ↦ h X.unop Y⟩

/-- Two left ideals with the same members are equal. -/
@[ext]
theorem ext {I J : LeftMorphismIdeal C}
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), f ∈ I.hom X Y ↔ f ∈ J.hom X Y) : I = J :=
  le_antisymm (le_def.mpr fun _ _ _ hf ↦ (h _).mp hf) (le_def.mpr fun _ _ _ hf ↦ (h _).mpr hf)

@[simp]
theorem top_hom (X Y : C) : (⊤ : LeftMorphismIdeal C).hom X Y = ⊤ :=
  ModCat.Submodule.carrier_top (op X)

@[simp]
theorem bot_hom (X Y : C) : (⊥ : LeftMorphismIdeal C).hom X Y = ⊥ :=
  ModCat.Submodule.carrier_bot (op X)

end LeftMorphismIdeal

namespace RightMorphismIdeal

/-- The subgroup of maps `X ⟶ Y` belonging to a right ideal. -/
abbrev hom (I : RightMorphismIdeal C) (X Y : C) : AddSubgroup (X ⟶ Y) :=
  (I X).carrier (op (op Y))

/-- Construct a right ideal from a family of subgroups closed under postcomposition. -/
def ofHom (S : ∀ X Y : C, AddSubgroup (X ⟶ Y))
    (hS : ∀ {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z), f ∈ S X Y → f ≫ g ∈ S X Z) :
    RightMorphismIdeal C :=
  fun X ↦
    { carrier Y := S X Y.unop.unop
      map_mem := fun g f hf ↦
        (ModCat.linearRegularBimod_sliceRight_obj_map_apply ℤ C X g f).symm ▸ hS g.unop.unop hf }

@[simp]
theorem hom_ofHom (S : ∀ X Y : C, AddSubgroup (X ⟶ Y)) (hS) (X Y : C) :
    (ofHom S hS).hom X Y = S X Y := (rfl)

/-- Right ideals are closed under postcomposition. -/
theorem comp_mem (I : RightMorphismIdeal C) {X Y Z : C} {f : X ⟶ Y}
    (g : Y ⟶ Z) (hf : f ∈ I.hom X Y) : f ≫ g ∈ I.hom X Z :=
  ModCat.linearRegularBimod_sliceRight_obj_map_apply ℤ C X g.op.op f ▸ (I X).map_mem g.op.op hf

/-- Inclusion of right ideals is pointwise inclusion of their subgroups. -/
theorem le_def {I J : RightMorphismIdeal C} :
    I ≤ J ↔ ∀ X Y : C, I.hom X Y ≤ J.hom X Y :=
  ⟨fun h X Y ↦ ModCat.Submodule.le_def.mp (h X) (op (op Y)),
    fun h X ↦ ModCat.Submodule.le_def.mpr fun Y ↦ h X Y.unop.unop⟩

/-- Two right ideals with the same members are equal. -/
@[ext]
theorem ext {I J : RightMorphismIdeal C}
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), f ∈ I.hom X Y ↔ f ∈ J.hom X Y) : I = J :=
  le_antisymm (le_def.mpr fun _ _ _ hf ↦ (h _).mp hf) (le_def.mpr fun _ _ _ hf ↦ (h _).mpr hf)

@[simp]
theorem top_hom (X Y : C) : (⊤ : RightMorphismIdeal C).hom X Y = ⊤ :=
  ModCat.Submodule.carrier_top (op (op Y))

@[simp]
theorem bot_hom (X Y : C) : (⊥ : RightMorphismIdeal C).hom X Y = ⊥ :=
  ModCat.Submodule.carrier_bot (op (op Y))

/-- Taking opposites sends a right ideal of `C` to a left ideal of `Cᵒᵖ`. -/
def op (I : RightMorphismIdeal C) : LeftMorphismIdeal Cᵒᵖ :=
  LeftMorphismIdeal.ofHom (fun X Y ↦ (I.hom Y.unop X.unop).comap (unopHom X Y))
    (by
      intro X Y Z f g hg
      exact I.comp_mem f.unop hg)

@[simp]
theorem mem_op_hom (I : RightMorphismIdeal C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f ∈ I.op.hom X Y ↔ f.unop ∈ I.hom Y.unop X.unop := Iff.rfl

end RightMorphismIdeal

namespace LeftMorphismIdeal

/-- Taking unopposites sends a left ideal of `Cᵒᵖ` to a right ideal of `C`. -/
def unop (I : LeftMorphismIdeal Cᵒᵖ) : RightMorphismIdeal C :=
  RightMorphismIdeal.ofHom (fun X Y ↦ (I.hom (op Y) (op X)).comap (opHom X Y))
    (by
      intro X Y Z f g hf
      exact I.comp_mem g.op hf)

@[simp]
theorem mem_unop_hom (I : LeftMorphismIdeal Cᵒᵖ) {X Y : C} (f : X ⟶ Y) :
    f ∈ I.unop.hom X Y ↔ f.op ∈ I.hom (op Y) (op X) := Iff.rfl

end LeftMorphismIdeal

namespace RightMorphismIdeal

/-- Reversing morphisms identifies right ideals of `C` with left ideals of `Cᵒᵖ`. -/
def opOrderIso (C : Type u) [Category.{v} C] [Preadditive C] :
    RightMorphismIdeal C ≃o LeftMorphismIdeal Cᵒᵖ where
  toFun := op
  invFun := LeftMorphismIdeal.unop
  left_inv I := RightMorphismIdeal.ext fun f ↦ by simp
  right_inv I := LeftMorphismIdeal.ext fun f ↦ by simp
  map_rel_iff' := by
    intro I J
    rw [LeftMorphismIdeal.le_def, RightMorphismIdeal.le_def]
    exact ⟨fun h X Y f hf ↦ (J.mem_op_hom f.op).mp
      (h (Opposite.op Y) (Opposite.op X) ((I.mem_op_hom f.op).mpr hf)),
      fun h X Y f hf ↦ (J.mem_op_hom f).mpr (h Y.unop X.unop ((I.mem_op_hom f).mp hf))⟩

@[simp]
theorem opOrderIso_apply (I : RightMorphismIdeal C) : opOrderIso C I = I.op :=
  (rfl)

@[simp]
theorem opOrderIso_symm_apply (I : LeftMorphismIdeal Cᵒᵖ) :
    (opOrderIso C).symm I = I.unop := (rfl)

@[simp]
theorem unop_op (I : RightMorphismIdeal C) : I.op.unop = I :=
  (opOrderIso C).symm_apply_apply I

/-- Extend a submodule of `Hom(X, -)` by zero at every source other than `X`. -/
noncomputable def ofSubmodule {X : C}
    (S : ModCat.Submodule ((ModCat.regularBimod C).sliceRight X)) : RightMorphismIdeal C := by
  classical
  exact Function.update ⊥ X S

@[simp]
theorem ofSubmodule_apply_self {X : C}
    (S : ModCat.Submodule ((ModCat.regularBimod C).sliceRight X)) : ofSubmodule S X = S := by
  classical
  simp [ofSubmodule]

@[simp]
theorem ofSubmodule_apply_ne {X Y : C}
    (S : ModCat.Submodule ((ModCat.regularBimod C).sliceRight X)) (h : Y ≠ X) :
    ofSubmodule S Y = ⊥ := by
  classical
  simp [ofSubmodule, h]

/-- Extension by zero is left adjoint, in the order sense, to taking the slice at `X`. -/
theorem ofSubmodule_le_iff {X : C} {S : ModCat.Submodule ((ModCat.regularBimod C).sliceRight X)}
    {I : RightMorphismIdeal C} : ofSubmodule S ≤ I ↔ S ≤ I X := by
  classical
  simp [ofSubmodule, update_le_iff]

/-- The right ideal generated by `f : X ⟶ Y` in the right slice at `X`. -/
noncomputable def principal {X Y : C} (f : X ⟶ Y) : RightMorphismIdeal C :=
  ofSubmodule
    { carrier Z := (Preadditive.leftComp Z.unop.unop f).range
      map_mem := by
        intro Z W k g hg
        obtain ⟨h, rfl⟩ := hg
        refine ⟨h ≫ k.unop.unop, ?_⟩
        simp [Preadditive.leftComp, Category.assoc] }

/-- The components at the source of the generator consist of its right multiples. -/
@[simp]
theorem mem_principal_hom {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    g ∈ (principal f).hom X Z ↔ ∃ h : Y ⟶ Z, f ≫ h = g := by
  simp only [principal, hom, ofSubmodule_apply_self, AddMonoidHom.mem_range]
  rfl

/-- The components at sources other than the source of the generator are zero. -/
@[simp]
theorem principal_hom_of_ne {X X' Y Z : C} (f : X ⟶ Y) (h : X' ≠ X) :
    (principal f).hom X' Z = ⊥ := by
  simp only [principal, hom, ofSubmodule_apply_ne _ h]
  exact ModCat.Submodule.carrier_bot (Opposite.op (Opposite.op Z))

/-- The principal right ideal is the least right ideal containing its generator. -/
@[simp]
theorem principal_le_iff {X Y : C} {f : X ⟶ Y} {I : RightMorphismIdeal C} :
    principal f ≤ I ↔ f ∈ I.hom X Y := by
  refine ⟨fun h ↦ le_def.mp h X Y ((mem_principal_hom f f).2 ⟨𝟙 Y, Category.comp_id f⟩), ?_⟩
  intro hf
  apply le_def.mpr
  intro X' Z g hg
  by_cases h : X' = X
  · subst X'
    obtain ⟨k, rfl⟩ := (mem_principal_hom f g).mp hg
    exact I.comp_mem k hf
  · rw [principal_hom_of_ne f h, AddSubgroup.mem_bot] at hg
    exact hg.symm ▸ (I.hom X' Z).zero_mem

end RightMorphismIdeal

@[simp]
theorem LeftMorphismIdeal.op_unop (I : LeftMorphismIdeal Cᵒᵖ) : I.unop.op = I :=
  (RightMorphismIdeal.opOrderIso C).apply_symm_apply I

namespace MorphismIdeal

/-- Two-sided ideals are the submodules of the regular bimodule, ordered by inclusion. -/
def orderIsoSubmoduleRegularBimod (C : Type u) [Category.{v} C] [Preadditive C] :
    MorphismIdeal C ≃o ModCat.Submodule (ModCat.regularBimod C) where
  toFun I :=
    { carrier P := I.hom P.unop.fst P.unop.snd.unop
      map_mem := by
        rintro ⟨⟨X', Y'⟩⟩ ⟨⟨X, Y⟩⟩ t h hh
        -- Induct on the tensor morphism before taking its opposite.
        let P : LinearTensor ℤ C Cᵒᵖ := ⟨X, Y⟩
        let Q : LinearTensor ℤ C Cᵒᵖ := ⟨X', Y'⟩
        suffices ∀ k : P ⟶ Q, (ModCat.regularBimod C).obj.map k.op h ∈ I.hom X Y.unop from
          this t.unop
        intro k
        induction k using LinearTensor.hom_induction_on with
        | tmul f g =>
          exact (ModCat.linearRegularBimod_obj_map_tmul_apply ℤ C f g.unop h).symm ▸
            I.comp_mem_left f (I.comp_mem_right g.unop hh)
        | add k l hk hl =>
          have hmap : (ModCat.regularBimod C).obj.map (k + l).op h =
              (ModCat.regularBimod C).obj.map k.op h + (ModCat.regularBimod C).obj.map l.op h := by
            rw [op_add, Functor.map_add, AddCommGrpCat.hom_add_apply]
          exact hmap.symm ▸ (I.hom X Y.unop).add_mem hk hl }
  invFun S :=
    { hom X Y := S.carrier (Opposite.op ⟨X, Opposite.op Y⟩)
      comp_mem_left := by
        intro X Y Z f g hg
        have h := ModCat.linearRegularBimod_obj_map_tmul_apply ℤ C f (𝟙 Z) g
        rw [Category.comp_id] at h
        exact h ▸ S.map_mem (LinearTensor.tmul f (𝟙 (Opposite.op Z))).op hg
      comp_mem_right := by
        intro X Y Z f g hf
        have h := ModCat.linearRegularBimod_obj_map_tmul_apply ℤ C (𝟙 X) g f
        rw [Category.id_comp] at h
        exact h ▸ S.map_mem (LinearTensor.tmul (𝟙 X) g.op).op hf }
  left_inv I := MorphismIdeal.hom_injective rfl
  right_inv S := ModCat.Submodule.carrier_injective rfl
  map_rel_iff' := by
    intro I J
    rw [MorphismIdeal.le_def, ModCat.Submodule.le_def]
    exact ⟨fun h X Y f hf ↦ h (Opposite.op ⟨X, Opposite.op Y⟩) hf,
      fun h P _ hf ↦ h _ hf⟩

@[simp]
theorem orderIsoSubmoduleRegularBimod_apply_carrier (I : MorphismIdeal C)
    (P : (LinearTensor ℤ C Cᵒᵖ)ᵒᵖ) :
    (orderIsoSubmoduleRegularBimod C I).carrier P = I.hom P.unop.fst P.unop.snd.unop := (rfl)

@[simp]
theorem orderIsoSubmoduleRegularBimod_symm_apply_hom
    (S : ModCat.Submodule (ModCat.regularBimod C)) (X Y : C) :
    ((orderIsoSubmoduleRegularBimod C).symm S).hom X Y =
      S.carrier (Opposite.op ⟨X, Opposite.op Y⟩) := (rfl)

/-- Forget postcomposition closure of a two-sided ideal. -/
def toLeftMorphismIdeal (I : MorphismIdeal C) : LeftMorphismIdeal C :=
  LeftMorphismIdeal.ofHom I.hom I.comp_mem_left

/-- Forget precomposition closure of a two-sided ideal. -/
def toRightMorphismIdeal (I : MorphismIdeal C) : RightMorphismIdeal C :=
  RightMorphismIdeal.ofHom I.hom I.comp_mem_right

instance : Coe (MorphismIdeal C) (LeftMorphismIdeal C) := ⟨toLeftMorphismIdeal⟩
instance : Coe (MorphismIdeal C) (RightMorphismIdeal C) := ⟨toRightMorphismIdeal⟩

@[simp]
theorem toLeftMorphismIdeal_hom (I : MorphismIdeal C) (X Y : C) :
    (I : LeftMorphismIdeal C).hom X Y = I.hom X Y := (rfl)

@[simp]
theorem toRightMorphismIdeal_hom (I : MorphismIdeal C) (X Y : C) :
    (I : RightMorphismIdeal C).hom X Y = I.hom X Y := (rfl)

/-- Taking opposites of a two-sided ideal exchanges its two one-sided forms. -/
@[simp]
theorem op_toRightMorphismIdeal (I : MorphismIdeal C) :
    (I : RightMorphismIdeal C).op = (I.op : LeftMorphismIdeal Cᵒᵖ) := by
  apply LeftMorphismIdeal.ext
  intro X Y f
  simp

end MorphismIdeal

end TauCeti
