/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Path.Strict
public import TauCeti.CategoryTheory.Bicategory.Adjunction.Basic

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
  -- Give the cells their path types before mapping them to `B` with `homEval`.
  let η' : (𝟙 a : a ⟶ a) ⟶ f.toPath ≫ g.toPath := η
  let ε' : g.toPath ≫ f.toPath ⟶ (𝟙 b : b ⟶ b) := ε
  have h := congrArg (homEval a b).map
    (leftZigzag_eq (B := Paths B) (f := f.toPath) (g := g.toPath) η' ε')
  simp only [Functor.map_comp] at h
  simp only [homEval_map_whiskerRight, homEval_map_whiskerLeft,
    Strict.associator_eqToIso, eqToIso.hom, eqToHom_map, homEval_obj] at h
  simp only [homEval_map] at h
  simp [η', ε', id_def, comp_def, Path.evalComp_toPath, Path.evalCons_cons,
    Path.comp_toPath_eq_cons, Path.evalComp_toPath_cons, Category.assoc] at h
  have hB := congrArg (fun θ => (λ_ f).inv ≫ θ ≫ (ρ_ f).hom)
    (leftZigzag_eq (B := B) η ε)
  simp only [Category.assoc] at hB
  exact h.trans hB.symm

/-- The right triangle composite on singleton paths is the original zigzag conjugated by
the right and left unitors. -/
lemma rightZigzag_toPath (η : 𝟙 a.as ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b.as) :
    rightZigzag (B := Paths B) (f := f.toPath) (g := g.toPath) η ε =
      (ρ_ g).inv ≫ rightZigzag η ε ≫ (λ_ g).hom := by
  -- Give the cells their path types before mapping them to `B` with `homEval`.
  let η' : (𝟙 a : a ⟶ a) ⟶ f.toPath ≫ g.toPath := η
  let ε' : g.toPath ≫ f.toPath ⟶ (𝟙 b : b ⟶ b) := ε
  have h := congrArg (homEval b a).map
    (rightZigzag_eq (B := Paths B) (f := f.toPath) (g := g.toPath) η' ε')
  simp only [Functor.map_comp] at h
  simp only [homEval_map_whiskerRight, homEval_map_whiskerLeft,
    Strict.associator_eqToIso, eqToIso.inv, eqToHom_map, homEval_obj] at h
  simp only [homEval_map] at h
  simp [η', ε', id_def, comp_def, Path.evalComp_toPath, Path.evalCons_cons,
    Path.comp_toPath_eq_cons, Path.evalComp_toPath_cons, Category.assoc] at h
  have hB := congrArg (fun θ => (ρ_ g).inv ≫ θ ≫ (λ_ g).hom)
    (rightZigzag_eq (B := B) η ε)
  simp only [Category.assoc] at hB
  exact h.trans hB.symm

/-- The left triangle identity for two singleton paths holds exactly when the original
unit and counit satisfy the left triangle identity in `B`. -/
lemma left_triangle_toPath_iff (η : 𝟙 a.as ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b.as) :
    leftZigzag (B := Paths B) (f := f.toPath) (g := g.toPath) η ε =
        (leftUnitor (B := Paths B) (a := a) (b := b) f.toPath).hom ≫
          (rightUnitor (B := Paths B) (a := a) (b := b) f.toPath).inv ↔
      leftZigzag η ε = (λ_ f).hom ≫ (ρ_ f).inv := by
  have h := congrArg₂ (fun θ θ' : f ⟶ f => θ = θ')
    (leftZigzag_toPath (a := a) (b := b) η ε)
    (leftUnitor_hom_comp_rightUnitor_inv_toPath (a := a) (b := b) f)
  exact h.to_iff.trans (by
    rw [Iso.inv_comp_eq, Category.comp_id, ← Iso.eq_comp_inv])

/-- The right triangle identity for two singleton paths holds exactly when the original
unit and counit satisfy the right triangle identity in `B`. -/
lemma right_triangle_toPath_iff (η : 𝟙 a.as ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b.as) :
    rightZigzag (B := Paths B) (f := f.toPath) (g := g.toPath) η ε =
        (rightUnitor (B := Paths B) (a := b) (b := a) g.toPath).hom ≫
          (leftUnitor (B := Paths B) (a := b) (b := a) g.toPath).inv ↔
      rightZigzag η ε = (ρ_ g).hom ≫ (λ_ g).inv := by
  have h := congrArg₂ (fun θ θ' : g ⟶ g => θ = θ')
    (rightZigzag_toPath (a := a) (b := b) η ε)
    (rightUnitor_hom_comp_leftUnitor_inv_toPath (a := b) (b := a) g)
  exact h.to_iff.trans (by
    rw [Iso.inv_comp_eq, Category.comp_id, ← Iso.eq_comp_inv])

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
