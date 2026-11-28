/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Path.Adjunction.Basic

/-!
# Composition of adjunctions between singleton paths

Transferring adjunctions to singleton paths commutes with composition after inserting the
canonical evaluation comparisons. These comparisons identify the full specified adjunctions:
both their units and their counits, as well as their left and right adjoints.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651, Proposition 2.7 and
  comparisons 2.9–2.10.
-/

public section

open CategoryTheory CategoryTheory.Bicategory Quiver
open TauCeti.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.Adjunction

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}
  {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- The composite unit between singleton paths evaluates to the two original units,
with the right unitor and inverse associator accounting for their parenthesization. -/
lemma compUnit_toPaths (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (Adjunction.compUnit adj₁.toPaths adj₂.toPaths : 𝟙 a ⟶ ((f₁ ≫ f₂) ≫ g₂) ≫ g₁) =
      (adj₁.unit : 𝟙 a ⟶ f₁ ≫ g₁) ≫ (ρ_ f₁).inv ▷ g₁ ≫ (f₁ ◁ adj₂.unit) ▷ g₁ ≫
        (α_ f₁ f₂ g₂).inv ▷ g₁ := by
  -- Expand the structural comparisons, then evaluate the path hom-category operations.
  rw [Adjunction.compUnit]
  dsimp only [bicategoricalComp, BicategoricalCoherence.assoc,
    BicategoricalCoherence.assoc', BicategoricalCoherence.refl, BicategoricalCoherence.iso]
  simp only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, whiskerLeftIso_hom,
    whiskerRightIso_hom, id_whiskerRight, Category.comp_id]
  simp only [Strict.associator_eqToIso (B := Paths B),
    Strict.leftUnitor_eqToIso (B := Paths B),
    eqToIso.hom, eqToIso.inv]
  simp only [Paths.comp₂_def (a := (⟨a⟩ : Paths B)) (b := ⟨a⟩),
    Paths.id₂_def (a := (⟨b⟩ : Paths B)) (b := ⟨a⟩),
    Paths.comp₂_def (a := (⟨b⟩ : Paths B)) (b := ⟨a⟩),
    Paths.eqToHom_def (a := (⟨a⟩ : Paths B)) (b := ⟨a⟩),
    Paths.eqToHom_def (a := (⟨b⟩ : Paths B)) (b := ⟨a⟩),
    Paths.whiskerLeft_def (a := (⟨a⟩ : Paths B)) (b := ⟨b⟩) (c := ⟨a⟩),
    Paths.whiskerRight_def (a := (⟨b⟩ : Paths B)) (b := ⟨b⟩) (c := ⟨a⟩)]
  simp only [Category.id_comp, Path.whiskerLeftEval_eqToHom]
  erw [Path.whiskerLeftEval_whiskerRightEval_toPath f₁.toPath adj₂.toPaths.unit g₁]
  erw [eqToHom_refl, eqToHom_refl, eqToHom_refl]
  erw [Path.whiskerLeftEval_id f₁.toPath ((f₂.toPath.comp g₂.toPath).comp g₁.toPath)]
  simp only [Paths.comp_def, Paths.id_def, Path.comp_toPath_eq_cons, Path.comp_cons,
    Path.comp_nil, Path.eval_nil, Path.eval_cons_cons, Path.eval_toPath,
    toPaths_unit, Path.evalComp_nil, Iso.symm_hom,
    Path.evalCons_cons, Iso.refl_inv]
  simp only [Quiver.Hom.toPath, Path.eval_cons_cons, Path.eval_cons_nil,
    Path.evalCons_cons, Iso.refl_hom]
  erw [Path.evalComp_cons_toPath_cons Path.nil f₁ f₂ g₂]
  bicategory

/-- The composite counit between singleton paths evaluates to the two original counits,
with the associator and right unitor accounting for their parenthesization. -/
lemma compCounit_toPaths (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    Adjunction.compCounit adj₁.toPaths adj₂.toPaths =
      (α_ g₂ g₁ f₁).hom ▷ f₂ ≫ (g₂ ◁ adj₁.counit) ▷ f₂ ≫
        (ρ_ g₂).hom ▷ f₂ ≫ adj₂.counit := by
  -- Expand the structural comparisons, then evaluate the path hom-category operations.
  rw [Adjunction.compCounit]
  dsimp only [bicategoricalComp, BicategoricalCoherence.assoc,
    BicategoricalCoherence.assoc', BicategoricalCoherence.refl, BicategoricalCoherence.iso]
  simp only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, whiskerLeftIso_hom,
    whiskerRightIso_hom, id_whiskerRight, Category.comp_id]
  simp only [Strict.associator_eqToIso (B := Paths B),
    Strict.leftUnitor_eqToIso (B := Paths B),
    eqToIso.hom, eqToIso.inv]
  simp only [Paths.comp₂_def (a := (⟨c⟩ : Paths B)) (b := ⟨c⟩),
    Paths.id₂_def (a := (⟨c⟩ : Paths B)) (b := ⟨c⟩),
    Paths.id₂_def (a := (⟨b⟩ : Paths B)) (b := ⟨c⟩),
    Paths.comp₂_def (a := (⟨b⟩ : Paths B)) (b := ⟨c⟩),
    Paths.eqToHom_def (a := (⟨c⟩ : Paths B)) (b := ⟨c⟩),
    Paths.eqToHom_def (a := (⟨b⟩ : Paths B)) (b := ⟨c⟩),
    Paths.whiskerLeft_def (a := (⟨c⟩ : Paths B)) (b := ⟨b⟩) (c := ⟨c⟩),
    Paths.whiskerRight_def (a := (⟨b⟩ : Paths B)) (b := ⟨b⟩) (c := ⟨c⟩)]
  simp only [Category.id_comp, Path.whiskerLeftEval_eqToHom]
  erw [Path.whiskerLeftEval_whiskerRightEval_toPath g₂.toPath adj₁.toPaths.counit f₂]
  erw [eqToHom_refl, eqToHom_refl, eqToHom_refl]
  erw [Path.whiskerLeftEval_id g₂.toPath ((g₁.toPath.comp f₁.toPath).comp f₂.toPath)]
  simp only [Paths.comp_def, Paths.id_def, Path.comp_toPath_eq_cons, Path.comp_cons,
    Path.comp_nil, Path.eval_nil, Path.eval_cons_cons, Path.eval_toPath,
    toPaths_counit, Path.evalComp_nil, Iso.symm_inv,
    Path.evalCons_cons, Iso.refl_hom]
  simp only [Quiver.Hom.toPath, Path.eval_cons_cons, Path.eval_cons_nil,
    Path.evalCons_cons, Iso.refl_inv]
  erw [Path.evalComp_cons_toPath_cons Path.nil g₂ g₁ f₁]
  bicategory

/-- The unit of the composite of two singleton-path adjunctions evaluates to the original
composite unit, after the concatenation comparison. -/
lemma toPaths_comp_unit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (adj₁.toPaths.comp adj₂.toPaths).unit =
      (adj₁.comp adj₂).unit ≫
        (Path.evalComp (f₁.toPath.comp f₂.toPath) (g₂.toPath.comp g₁.toPath)).inv := by
  refine (Iso.eq_comp_inv
    (Path.evalComp (f₁.toPath.comp f₂.toPath) (g₂.toPath.comp g₁.toPath))).2 ?_
  erw [comp_unit, compUnit_toPaths]
  rw [comp_unit]
  dsimp only [compUnit]
  simp only [Path.comp_toPath_eq_cons, Path.evalComp_cons_toPath_cons]
  bicategory

/-- The counit of the composite of two singleton-path adjunctions evaluates to the original
composite counit, after the inverse concatenation comparison. -/
lemma toPaths_comp_counit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (adj₁.toPaths.comp adj₂.toPaths).counit =
      (Path.evalComp (g₂.toPath.comp g₁.toPath) (f₁.toPath.comp f₂.toPath)).hom ≫
        (adj₁.comp adj₂).counit := by
  refine (Iso.inv_comp_eq
    (Path.evalComp (g₂.toPath.comp g₁.toPath) (f₁.toPath.comp f₂.toPath))).1 ?_
  erw [comp_counit, compCounit_toPaths]
  rw [comp_counit]
  dsimp only [compCounit]
  simp only [Path.comp_toPath_eq_cons, Path.evalComp_cons_toPath_cons]
  bicategory

end CategoryTheory.Bicategory.Adjunction

namespace TauCeti.Bicategory.Paths

variable {B : Type u} [Bicategory.{w, v} B]

/-- The unit of the identity adjunction on the empty path is the identity 2-cell in `B`.
The evaluation comparison with two empty paths supplies the original identity unit. -/
@[simp]
lemma idAdjunction_unit (a : B) :
    (Adjunction.id (⟨a⟩ : Paths B)).unit = (𝟙 (𝟙 a) : 𝟙 a ⟶ 𝟙 a) := by
  dsimp only [Adjunction.id]
  rw [Strict.rightUnitor_eqToIso (B := Paths B)]
  rfl

/-- The counit of the identity adjunction on the empty path is the identity 2-cell in `B`.
The inverse evaluation comparison supplies the original identity counit. -/
@[simp]
lemma idAdjunction_counit (a : B) :
    (Adjunction.id (⟨a⟩ : Paths B)).counit = (𝟙 (𝟙 a) : 𝟙 a ⟶ 𝟙 a) := by
  dsimp only [Adjunction.id]
  rw [Strict.rightUnitor_eqToIso (B := Paths B)]
  rfl

end TauCeti.Bicategory.Paths
