/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import TauCeti.CategoryTheory.Monoidal.Scalar
public import TauCeti.Combinatorics.PlanarMatching.Category
public import TauCeti.Combinatorics.PlanarMatching.Tensor

/-!
# The monoidal structure on the Temperley–Lieb diagram category

The Temperley–Lieb diagram category `TauCeti.TLDiagCat` is a monoidal category under horizontal
juxtaposition: on objects `TLDiagCat.of n ⊗ TLDiagCat.of m = TLDiagCat.of (n + m)`, with unit
`𝟙_ TLDiagCat = TLDiagCat.of 0`, and on morphisms `f ⊗ₘ g` is `TauCeti.TLDiagram.tensor f.diagram
g.diagram`. The associator and unitors are the equality-induced isomorphisms from `Nat.add_assoc`,
`Nat.zero_add` and `Nat.add_zero`, so the category is strict up to arithmetic equalities on `ℕ`.

Every endomorphism `a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` of the unit is a collection of closed circles,
and tensoring it on the left or on the right of any object `X` adds the same number of circles to
`𝟙 X`. In particular, every scalar — including `TLDiagCat.circle` and `TLDiagCat.cup ≫
TLDiagCat.cap` — is central at every object (`TauCeti.TLDiagCat.circlesCommuteAt_scalar`).

## Main definitions

* `MonoidalCategoryStruct TauCeti.TLDiagCat`, `MonoidalCategory TauCeti.TLDiagCat`: the monoidal
  structure by horizontal juxtaposition of diagrams.

## Main results

* `TauCeti.TLDiagCat.diagram_tensorHom`, `TauCeti.TLDiagCat.diagram_whiskerLeft`,
  `TauCeti.TLDiagCat.diagram_whiskerRight`: the underlying diagrams of tensor products and
  whiskerings.
* `TauCeti.TLDiagCat.diagram_comp_eqToHom`, `TauCeti.TLDiagCat.diagram_eqToHom_comp`: composing
  with `eqToHom` casts the corresponding boundary of the underlying diagram.
* `TauCeti.TLDiagCat.circlesCommuteAt_scalar`, `TauCeti.TLDiagCat.circlesCommuteAt_circle`: every
  scalar, and in particular the closed circle, acts equally on the left and right of every object.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace TLDiagCat

/-! ### Casting morphisms along object equalities -/

variable {X Y Z : TLDiagCat}

/-- The diagram of an equality-induced morphism `eqToHom h` is the identity diagram cast along
`congrArg as h`. -/
@[simp]
theorem diagram_eqToHom (h : X = Y) :
    (eqToHom h).diagram = TLDiagram.cast rfl (congrArg as h) (TLDiagram.id X.as) := by
  subst h; simp

/-- Postcomposing with `eqToHom h` casts the top boundary of the underlying diagram. -/
theorem diagram_comp_eqToHom (f : X ⟶ Y) (h : Y = Z) :
    (f ≫ eqToHom h).diagram = TLDiagram.cast rfl (congrArg as h) f.diagram := by
  subst h; simp

/-- Precomposing with `eqToHom h` casts the bottom boundary of the underlying diagram. -/
theorem diagram_eqToHom_comp (h : X = Y) (f : Y ⟶ Z) :
    (eqToHom h ≫ f).diagram = TLDiagram.cast (congrArg as h).symm rfl f.diagram := by
  subst h; simp

/-! ### Monoidal structure -/

/-- The horizontal juxtaposition monoidal structure on `TLDiagCat`, with `of n ⊗ of m = of (n + m)`
and unit `of 0`. -/
instance : MonoidalCategoryStruct TLDiagCat where
  tensorObj X Y := of (X.as + Y.as)
  whiskerLeft X _ _ g := Hom.mk ((TLDiagram.id X.as).tensor g.diagram)
  whiskerRight f Y := Hom.mk (f.diagram.tensor (TLDiagram.id Y.as))
  tensorHom f g := Hom.mk (f.diagram.tensor g.diagram)
  tensorUnit := of 0
  associator X Y Z := eqToIso (congrArg of (Nat.add_assoc X.as Y.as Z.as))
  leftUnitor X := eqToIso (congrArg of (Nat.zero_add X.as))
  rightUnitor X := eqToIso (congrArg of (Nat.add_zero X.as))

/-! ### Computation lemmas for the monoidal structure -/

@[simp]
theorem tensorObj_as (X Y : TLDiagCat) : (X ⊗ Y).as = X.as + Y.as := (rfl)

theorem tensorUnit_as : (𝟙_ TLDiagCat).as = 0 := (rfl)

@[simp]
theorem of_tensor_of (n m : ℕ) : of n ⊗ of m = of (n + m) := (rfl)

@[simp]
theorem tensorUnit_eq : (𝟙_ TLDiagCat) = of 0 := (rfl)

@[simp]
theorem diagram_tensorHom {X₁ Y₁ X₂ Y₂ : TLDiagCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).diagram = f.diagram.tensor g.diagram := (rfl)

@[simp]
theorem diagram_whiskerLeft (X : TLDiagCat) {Y₁ Y₂ : TLDiagCat} (g : Y₁ ⟶ Y₂) :
    (X ◁ g).diagram = (TLDiagram.id X.as).tensor g.diagram := (rfl)

@[simp]
theorem diagram_whiskerRight {X₁ X₂ : TLDiagCat} (f : X₁ ⟶ X₂) (Y : TLDiagCat) :
    (f ▷ Y).diagram = f.diagram.tensor (TLDiagram.id Y.as) := (rfl)

theorem associator_hom_eq (X Y Z : TLDiagCat) :
    (α_ X Y Z).hom = eqToHom (congrArg of (Nat.add_assoc X.as Y.as Z.as)) := (rfl)

theorem associator_inv_eq (X Y Z : TLDiagCat) :
    (α_ X Y Z).inv = eqToHom (congrArg of (Nat.add_assoc X.as Y.as Z.as).symm) := (rfl)

theorem leftUnitor_hom_eq (X : TLDiagCat) :
    (λ_ X).hom = eqToHom (congrArg of (Nat.zero_add X.as)) := (rfl)

theorem leftUnitor_inv_eq (X : TLDiagCat) :
    (λ_ X).inv = eqToHom (congrArg of (Nat.zero_add X.as).symm) := (rfl)

theorem rightUnitor_hom_eq (X : TLDiagCat) :
    (ρ_ X).hom = eqToHom (congrArg of (Nat.add_zero X.as)) := (rfl)

theorem rightUnitor_inv_eq (X : TLDiagCat) :
    (ρ_ X).inv = eqToHom (congrArg of (Nat.add_zero X.as).symm) := (rfl)

private theorem eqToHom_tensorHom_id {X₁ Y₁ : TLDiagCat} (h : X₁ = Y₁) (Z : TLDiagCat) :
    eqToHom h ⊗ₘ 𝟙 Z = eqToHom (congrArg (· ⊗ Z) h) := by
  subst h
  exact hom_ext (TLDiagram.tensor_id_id _ _)

private theorem id_tensorHom_eqToHom (X : TLDiagCat) {Y₁ Z₁ : TLDiagCat} (h : Y₁ = Z₁) :
    𝟙 X ⊗ₘ eqToHom h = eqToHom (congrArg (X ⊗ ·) h) := by
  subst h
  exact hom_ext (TLDiagram.tensor_id_id _ _)

/-- `TLDiagCat` is a monoidal category under horizontal juxtaposition of diagrams. -/
instance : MonoidalCategory TLDiagCat :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X₁ X₂ => hom_ext (TLDiagram.tensor_id_id X₁.as X₂.as))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      hom_ext (TLDiagram.tensor_comp f₁.diagram f₂.diagram g₁.diagram g₂.diagram))
    (associator_naturality := fun f₁ f₂ f₃ => by
      refine hom_ext ?_
      rw [associator_hom_eq, associator_hom_eq, diagram_comp_eqToHom, diagram_eqToHom_comp,
        diagram_tensorHom, diagram_tensorHom, diagram_tensorHom, diagram_tensorHom]
      have h := congrArg (TLDiagram.cast (Nat.add_assoc _ _ _).symm rfl)
        (TLDiagram.tensor_assoc f₁.diagram f₂.diagram f₃.diagram)
      rw [TLDiagram.cast_cast] at h
      exact h)
    (leftUnitor_naturality := fun f => by
      refine hom_ext ?_
      rw [leftUnitor_hom_eq, leftUnitor_hom_eq, diagram_comp_eqToHom, diagram_eqToHom_comp,
        diagram_tensorHom, diagram_id]
      have h := congrArg (TLDiagram.cast (Nat.zero_add _).symm rfl)
        (TLDiagram.id_zero_tensor f.diagram)
      rw [TLDiagram.cast_cast] at h
      exact h)
    (rightUnitor_naturality := fun f => by
      refine hom_ext ?_
      rw [rightUnitor_hom_eq, rightUnitor_hom_eq, diagram_comp_eqToHom, diagram_eqToHom_comp,
        diagram_tensorHom, diagram_id, TLDiagram.cast_refl, Equiv.refl_apply]
      exact TLDiagram.tensor_id_zero f.diagram)
    (pentagon := fun W X Y Z => by
      simp only [associator_hom_eq, eqToHom_tensorHom_id, id_tensorHom_eqToHom, eqToHom_trans])
    (triangle := fun X Y => by
      simp only [associator_hom_eq, leftUnitor_hom_eq, rightUnitor_hom_eq,
        eqToHom_tensorHom_id, id_tensorHom_eqToHom, eqToHom_trans])

/-! ### Centrality of scalars and closed circles -/

/-- Acting on the right of `X` by a scalar `a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` keeps the identity
matching on `X.as` strands and adds the circles of `a`. -/
theorem diagram_rightUnitor_inv_whiskerLeft_rightUnitor_hom
    (a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat) (X : TLDiagCat) :
    ((ρ_ X).inv ≫ X ◁ a ≫ (ρ_ X).hom).diagram =
      ⟨(TLDiagram.id X.as).matching, a.diagram.circles⟩ := by
  have ha : a.diagram = ⟨PlanarMatching.nested 0, a.diagram.circles⟩ :=
    TLDiagram.ext (Subsingleton.elim (α := PlanarMatching 0) _ _) rfl
  rw [rightUnitor_inv_eq, rightUnitor_hom_eq, diagram_eqToHom_comp, diagram_comp_eqToHom,
    diagram_whiskerLeft, TLDiagram.cast_cast, TLDiagram.cast_refl, Equiv.refl_apply, ha,
    TLDiagram.tensor_mk_nested_zero]
  ext <;> simp

/-- Acting on the left of `X` by a scalar `a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` keeps the identity
matching on `X.as` strands and adds the circles of `a`. -/
theorem diagram_leftUnitor_inv_whiskerRight_leftUnitor_hom
    (a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat) (X : TLDiagCat) :
    ((λ_ X).inv ≫ a ▷ X ≫ (λ_ X).hom).diagram =
      ⟨(TLDiagram.id X.as).matching, a.diagram.circles⟩ := by
  have ha : a.diagram = ⟨PlanarMatching.nested 0, a.diagram.circles⟩ :=
    TLDiagram.ext (Subsingleton.elim (α := PlanarMatching 0) _ _) rfl
  rw [leftUnitor_inv_eq, leftUnitor_hom_eq, diagram_eqToHom_comp, diagram_comp_eqToHom,
    diagram_whiskerRight, TLDiagram.cast_cast, ha, TLDiagram.mk_nested_zero_tensor]
  ext <;> simp

/-- **Every scalar is central in `TLDiagCat`**: tensoring any endomorphism of `𝟙_ TLDiagCat` on
the left or on the right of an object `X` produces the same endomorphism of `X`. -/
theorem circlesCommuteAt_scalar (a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat) (X : TLDiagCat) :
    CirclesCommuteAt a X := by
  rw [circlesCommuteAt_iff]
  exact hom_ext <| (diagram_rightUnitor_inv_whiskerLeft_rightUnitor_hom a X).trans
    (diagram_leftUnitor_inv_whiskerRight_leftUnitor_hom a X).symm

/-- The closed circle acts identically on the left and right of every object of `TLDiagCat`. -/
theorem circlesCommuteAt_circle (X : TLDiagCat) : CirclesCommuteAt circle X :=
  circlesCommuteAt_scalar circle X

/-- The composite `cup ≫ cap` acts identically on the left and right of every object of
`TLDiagCat`. -/
theorem circlesCommuteAt_cup_comp_cap (X : TLDiagCat) : CirclesCommuteAt (cup ≫ cap) X :=
  circlesCommuteAt_scalar (cup ≫ cap) X

end TLDiagCat

/-- Tensoring in `TLDiagCat` is noncommutative: `(cap ▷ of 1)` and `(of 1 ◁ cap)` are distinct
morphisms `of 3 ⟶ of 1` (up to the unitors on `of 1`). -/
example :
    TLDiagCat.cap ▷ TLDiagCat.of 1 ≫ (λ_ (TLDiagCat.of 1)).hom ≠
      eqToHom (by simp : TLDiagCat.of 2 ⊗ TLDiagCat.of 1 = TLDiagCat.of 1 ⊗ TLDiagCat.of 2) ≫
        TLDiagCat.of 1 ◁ TLDiagCat.cap ≫ (ρ_ (TLDiagCat.of 1)).hom := by
  intro h
  have h0 := congrArg (fun f : TLDiagCat.of 2 ⊗ TLDiagCat.of 1 ⟶ TLDiagCat.of 1 =>
    (f.diagram.matching.1.val ⟨0, by simp⟩ : ℕ)) h
  simp only [TLDiagCat.leftUnitor_hom_eq, TLDiagCat.rightUnitor_hom_eq,
    TLDiagCat.diagram_comp_eqToHom, TLDiagCat.diagram_eqToHom_comp,
    TLDiagCat.diagram_whiskerRight, TLDiagCat.diagram_whiskerLeft, TLDiagCat.diagram_cap,
    TLDiagram.cast_cast, TLDiagram.matching_cast, TLDiagram.matching_tensor,
    TLDiagram.matching_id, PlanarMatching.cast_cast, PlanarMatching.coe_cast_apply,
    PerfectMatching.congr_val, Equiv.permCongr_apply, finCongr_symm, finCongr_apply,
    Fin.val_cast, Fin.cast_mk] at h0
  have hL := PlanarMatching.coe_insert_val_of_lt 2 (Nat.le_add_right 2 0)
    TLDiagram.cap.matching (PlanarMatching.nested 1) (q := 0) (by omega)
  have hR := PlanarMatching.coe_insert_val_of_lt 1 (Nat.le_add_right 1 1)
    (PlanarMatching.nested 1) TLDiagram.cap.matching (q := 0) (by omega)
  simp only [TLDiagram.cap_matching_val, PlanarMatching.nested_val,
    Fin.revPerm_apply, Fin.val_rev] at hL hR
  rw [hL, hR] at h0
  exact absurd h0 (by decide)

end TauCeti
