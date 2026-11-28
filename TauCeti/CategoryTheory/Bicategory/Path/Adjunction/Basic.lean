/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Path.Strict
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Adjunctions between singleton paths

A specified adjunction in a bicategory `B` gives an adjunction between the corresponding
singleton paths in `TauCeti.Bicategory.Paths B`, and conversely. The unit and counit are
unchanged: evaluation sends the empty path to the identity and a two-arrow path to the
composite of its arrows. The triangle composites, however, include the whiskering
comparisons of the path bicategory. We compute both composites explicitly before
constructing the transfers.

`TauCeti.Bicategory.Paths.singletonAdjunctionEquiv` packages the correspondence as an
equivalence of full specified adjunction data, including the unit and counit.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651, Proposition 2.5 and the adjunction
  comparison of Proposition 2.7.
-/

public section

open CategoryTheory CategoryTheory.Bicategory Quiver

universe w v u

namespace TauCeti.Bicategory.Paths

variable {B : Type u} [Bicategory.{w, v} B] {a b : Paths B}
  {f : a.as ⟶ b.as} {g : b.as ⟶ a.as}

/-- The left triangle composite on singleton paths is the original zigzag conjugated by
the left and right unitors. -/
lemma leftZigzag_toPath (η : 𝟙 a.as ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b.as) :
    leftZigzag (B := Paths B) (f := f.toPath) (g := g.toPath) η ε =
      (λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom := by
  dsimp only [leftZigzag, bicategoricalComp, BicategoricalCoherence.assoc,
    BicategoricalCoherence.assoc', BicategoricalCoherence.refl, BicategoricalCoherence.iso]
  simp only [Iso.trans_hom, whiskerRightIso_hom, Iso.refl_hom,
    id_whiskerRight, Category.comp_id]
  erw [comp₂_def (a := a) (b := b), comp₂_def (a := a) (b := b),
    whiskerRight_def (a := a) (b := a) (c := b),
    whiskerLeft_def (a := a) (b := b) (c := b)]
  erw [Path.whiskerRightEval_def (p := Path.nil) (p' := f.toPath.cons g) η f.toPath,
    Path.whiskerLeftEval_def f.toPath (q := g.toPath.cons f) (q' := Path.nil) ε]
  erw [Strict.associator_eqToIso (B := Paths B)]
  erw [eqToIso.hom, eqToHom_def, eqToHom_refl]
  erw [Path.evalComp_cons_toPath_cons Path.nil f g f]
  simp only [Path.comp_toPath_eq_cons, Path.eval_cons_nil, Path.eval_nil, Path.eval_toPath,
    Path.eval_cons_cons, Path.evalComp_toPath, Path.evalCons_nil_hom, Path.evalCons_cons,
    Iso.refl_inv, Category.comp_id, Path.comp_cons, Path.comp_nil,
    Path.evalComp_nil, Iso.symm_inv, Category.assoc]
  -- Normalize the evaluated path endpoints before applying category laws in `B`.
  change ((λ_ f).inv ≫ η ▷ f) ≫ 𝟙 ((f ≫ g) ≫ f) ≫
    (α_ f g f).hom ≫ f ◁ ε ≫ (ρ_ f).hom = _
  simp [Category.assoc]

/-- The right triangle composite on singleton paths is the original zigzag conjugated by
the right and left unitors. -/
lemma rightZigzag_toPath (η : 𝟙 a.as ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b.as) :
    rightZigzag (B := Paths B) (f := f.toPath) (g := g.toPath) η ε =
      (ρ_ g).inv ≫ rightZigzag η ε ≫ (λ_ g).hom := by
  dsimp only [rightZigzag, bicategoricalComp, BicategoricalCoherence.assoc,
    BicategoricalCoherence.assoc', BicategoricalCoherence.refl, BicategoricalCoherence.iso]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Iso.refl_hom,
    id_whiskerRight, Category.id_comp]
  erw [comp₂_def (a := b) (b := a), comp₂_def (a := b) (b := a),
    whiskerLeft_def (a := b) (b := a) (c := a),
    whiskerRight_def (a := b) (b := b) (c := a)]
  erw [Path.whiskerLeftEval_def g.toPath (q := Path.nil) (q' := f.toPath.cons g) η,
    Path.whiskerRightEval_def (p := g.toPath.cons f) (p' := Path.nil) ε g.toPath]
  erw [Strict.associator_eqToIso (B := Paths B)]
  erw [eqToIso.inv, eqToHom_def, eqToHom_refl]
  erw [Path.evalComp_cons_toPath_cons Path.nil g f g]
  simp only [Path.comp_nil, Path.eval_toPath, Path.eval_nil, Path.comp_cons,
    Path.comp_toPath_eq_cons, Path.eval_cons_cons, Path.evalComp_nil, Iso.symm_hom,
    Path.eval_cons_nil, Path.evalComp_toPath, Path.evalCons_cons,
    Iso.refl_hom, Path.evalCons_nil_inv, Category.id_comp, Category.assoc]
  -- Normalize the evaluated path endpoints before applying category laws in `B`.
  change ((ρ_ g).inv ≫ g ◁ η ≫ (α_ g f g).inv) ≫ 𝟙 ((g ≫ f) ≫ g) ≫
    ε ▷ g ≫ (λ_ g).hom = _
  simp [Category.assoc]

/-- The left triangle identity for two singleton paths holds exactly when the original
unit and counit satisfy the left triangle identity in `B`. -/
lemma left_triangle_toPath_iff (η : 𝟙 a.as ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b.as) :
    leftZigzag (B := Paths B) (f := f.toPath) (g := g.toPath) η ε =
        (leftUnitor (B := Paths B) (a := a) (b := b) f.toPath).hom ≫
          (rightUnitor (B := Paths B) (a := a) (b := b) f.toPath).inv ↔
      leftZigzag η ε = (λ_ f).hom ≫ (ρ_ f).inv := by
  erw [leftZigzag_toPath (a := a) (b := b),
    Strict.leftUnitor_eqToIso (B := Paths B),
    Strict.rightUnitor_eqToIso (B := Paths B), eqToIso_refl]
  simp only [Iso.refl_hom, Iso.refl_inv]
  erw [comp₂_def, id₂_def]
  -- Express the remaining path identity as the identity 2-cell of `f` in `B`.
  change (λ_ f).inv ≫ leftZigzag η ε ≫ (ρ_ f).hom = 𝟙 f ≫ 𝟙 f ↔ _
  rw [Category.id_comp, Iso.inv_comp_eq, Category.comp_id, ← Iso.eq_comp_inv]

/-- The right triangle identity for two singleton paths holds exactly when the original
unit and counit satisfy the right triangle identity in `B`. -/
lemma right_triangle_toPath_iff (η : 𝟙 a.as ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b.as) :
    rightZigzag (B := Paths B) (f := f.toPath) (g := g.toPath) η ε =
        (rightUnitor (B := Paths B) (a := b) (b := a) g.toPath).hom ≫
          (leftUnitor (B := Paths B) (a := b) (b := a) g.toPath).inv ↔
      rightZigzag η ε = (ρ_ g).hom ≫ (λ_ g).inv := by
  erw [rightZigzag_toPath (a := a) (b := b),
    Strict.rightUnitor_eqToIso (B := Paths B),
    Strict.leftUnitor_eqToIso (B := Paths B), eqToIso_refl]
  simp only [Iso.refl_hom, Iso.refl_inv]
  erw [comp₂_def, id₂_def]
  -- Express the remaining path identity as the identity 2-cell of `g` in `B`.
  change (ρ_ g).inv ≫ rightZigzag η ε ≫ (λ_ g).hom = 𝟙 g ≫ 𝟙 g ↔ _
  rw [Category.id_comp, Iso.inv_comp_eq, Category.comp_id, ← Iso.eq_comp_inv]

end TauCeti.Bicategory.Paths

namespace CategoryTheory.Bicategory.Adjunction

open TauCeti.Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {a b : B}
  {f : a ⟶ b} {g : b ⟶ a}

/-- Transfer a specified adjunction to the singleton paths of its left and right adjoints.
The unit and counit are unchanged as 2-cells in `B`. -/
def toPaths (adj : f ⊣ g) :
    Adjunction (B := Paths B) (a := ⟨a⟩) (b := ⟨b⟩) f.toPath g.toPath where
  unit := adj.unit
  counit := adj.counit
  left_triangle := (Paths.left_triangle_toPath_iff adj.unit adj.counit).2 adj.left_triangle
  right_triangle := (Paths.right_triangle_toPath_iff adj.unit adj.counit).2 adj.right_triangle

@[simp]
lemma toPaths_unit (adj : f ⊣ g) : adj.toPaths.unit = adj.unit := (rfl)

@[simp]
lemma toPaths_counit (adj : f ⊣ g) : adj.toPaths.counit = adj.counit := (rfl)

/-- Recover a specified adjunction in `B` from an adjunction between singleton paths.
The unit and counit are unchanged as 2-cells in `B`. -/
def ofPaths (adj : Adjunction (B := Paths B) (a := ⟨a⟩) (b := ⟨b⟩)
    f.toPath g.toPath) : f ⊣ g where
  unit := adj.unit
  counit := adj.counit
  left_triangle := (Paths.left_triangle_toPath_iff adj.unit adj.counit).1 adj.left_triangle
  right_triangle := (Paths.right_triangle_toPath_iff adj.unit adj.counit).1 adj.right_triangle

@[simp]
lemma ofPaths_unit (adj : Adjunction (B := Paths B) (a := ⟨a⟩) (b := ⟨b⟩)
    f.toPath g.toPath) : adj.ofPaths.unit = adj.unit := (rfl)

@[simp]
lemma ofPaths_counit (adj : Adjunction (B := Paths B) (a := ⟨a⟩) (b := ⟨b⟩)
    f.toPath g.toPath) : adj.ofPaths.counit = adj.counit := (rfl)

/-- Transferring to singleton paths and back recovers the full specified adjunction. -/
@[simp]
lemma ofPaths_toPaths (adj : f ⊣ g) : adj.toPaths.ofPaths = adj := by
  ext <;> rfl

/-- Transferring from singleton paths and back recovers the full specified adjunction. -/
@[simp]
lemma toPaths_ofPaths (adj : Adjunction (B := Paths B) (a := ⟨a⟩) (b := ⟨b⟩)
    f.toPath g.toPath) : adj.ofPaths.toPaths = adj := by
  ext <;> rfl

end CategoryTheory.Bicategory.Adjunction

namespace TauCeti.Bicategory.Paths

variable {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}

/-- Specified adjunctions in `B` correspond to specified adjunctions between singleton
paths, preserving the full unit and counit data in both directions. -/
def singletonAdjunctionEquiv :
    (f ⊣ g) ≃ Adjunction (B := Paths B) (a := ⟨a⟩) (b := ⟨b⟩) f.toPath g.toPath where
  toFun := Adjunction.toPaths
  invFun := Adjunction.ofPaths
  left_inv := Adjunction.ofPaths_toPaths
  right_inv := Adjunction.toPaths_ofPaths

@[simp]
lemma singletonAdjunctionEquiv_apply (adj : f ⊣ g) :
    singletonAdjunctionEquiv adj = adj.toPaths := (rfl)

@[simp]
lemma singletonAdjunctionEquiv_symm_apply
    (adj : Adjunction (B := Paths B) (a := ⟨a⟩) (b := ⟨b⟩) f.toPath g.toPath) :
    singletonAdjunctionEquiv.symm adj = adj.ofPaths := (rfl)

end TauCeti.Bicategory.Paths
