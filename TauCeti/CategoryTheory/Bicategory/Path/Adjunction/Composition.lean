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

/-- The unit of the composite of two singleton-path adjunctions evaluates to the original
composite unit, after the concatenation comparison. -/
lemma toPaths_comp_unit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (adj₁.toPaths.comp adj₂.toPaths).unit =
      (adj₁.comp adj₂).unit ≫
        (Path.evalComp (f₁.toPath.comp f₂.toPath) (g₂.toPath.comp g₁.toPath)).inv := by
  refine (Iso.eq_comp_inv
    (Path.evalComp (f₁.toPath.comp f₂.toPath) (g₂.toPath.comp g₁.toPath))).2 ?_
  -- The path hom-categories compute by evaluation; `erw` reduces their projections.
  erw [comp_unit, comp_unit, compUnit, compUnit]
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
  erw [Path.whiskerLeftEval_def f₁.toPath
    (q := Path.nil.comp g₁.toPath) (q' := (f₂.toPath.comp g₂.toPath).comp g₁.toPath)]
  erw [Path.whiskerRightEval_def (p := Path.nil) (p' := f₂.toPath.comp g₂.toPath)
    adj₂.toPaths.unit g₁.toPath]
  simp only [Paths.comp_def, Paths.id_def, toPaths_unit,
    Quiver.Hom.toPath, Path.comp_cons, Path.comp_nil, Path.evalComp_cons, Path.evalComp_nil,
    Path.evalCons_cons, Path.evalCons_nil, Path.eval_cons_cons, Path.eval_cons_nil,
    Path.eval_nil, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    whiskerRightIso_hom, whiskerRightIso_inv, whiskerLeftIso_hom, whiskerLeftIso_inv,
    Iso.refl_hom, Iso.refl_inv]
  erw [eqToHom_refl, eqToHom_refl, eqToHom_refl]
  erw [Path.whiskerLeftEval_id f₁.toPath ((f₂.toPath.comp g₂.toPath).comp g₁.toPath)]
  bicategory

/-- The counit of the composite of two singleton-path adjunctions evaluates to the original
composite counit, after the inverse concatenation comparison. -/
lemma toPaths_comp_counit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    (adj₁.toPaths.comp adj₂.toPaths).counit =
      (Path.evalComp (g₂.toPath.comp g₁.toPath) (f₁.toPath.comp f₂.toPath)).hom ≫
        (adj₁.comp adj₂).counit := by
  refine (Iso.inv_comp_eq
    (Path.evalComp (g₂.toPath.comp g₁.toPath) (f₁.toPath.comp f₂.toPath))).1 ?_
  -- The path hom-categories compute by evaluation; `erw` reduces their projections.
  erw [comp_counit, comp_counit, compCounit, compCounit]
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
  erw [Path.whiskerLeftEval_def g₂.toPath
    (q := (g₁.toPath.comp f₁.toPath).comp f₂.toPath) (q' := Path.nil.comp f₂.toPath)]
  erw [Path.whiskerRightEval_def (p := g₁.toPath.comp f₁.toPath) (p' := Path.nil)
    adj₁.toPaths.counit f₂.toPath]
  simp only [Paths.comp_def, Paths.id_def, toPaths_counit,
    Quiver.Hom.toPath, Path.comp_cons, Path.comp_nil, Path.evalComp_cons, Path.evalComp_nil,
    Path.evalCons_cons, Path.evalCons_nil, Path.eval_cons_cons, Path.eval_cons_nil,
    Path.eval_nil, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    whiskerRightIso_hom, whiskerRightIso_inv, whiskerLeftIso_hom, whiskerLeftIso_inv,
    Iso.refl_hom, Iso.refl_inv]
  erw [eqToHom_refl, eqToHom_refl, eqToHom_refl]
  erw [Path.whiskerLeftEval_id g₂.toPath ((g₁.toPath.comp f₁.toPath).comp f₂.toPath)]
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
