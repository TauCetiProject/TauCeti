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

Horizontal juxtaposition of Temperley–Lieb diagrams (`TauCeti.TLDiagram.tensor`) makes the
Temperley–Lieb diagram category `TauCeti.TLDiagCat` into a monoidal category:

* On objects, `of n ⊗ of m = of (n + m)` and the tensor unit is `𝟙_ TLDiagCat = of 0`.
* On morphisms, `f ⊗ₘ g` juxtaposes the underlying diagrams side by side.
* The right unitor is `Iso.refl X` (since `n + 0 = n` definitionally), while the associator and
  left unitor are `eqToIso` induced by `Nat.add_assoc` and `Nat.zero_add`.
* The interchange law `TauCeti.TLDiagram.tensor_comp` supplies `tensorHom_comp_tensorHom`.

Every scalar `d : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` acts identically on the left and on the right of
every object `X` (`TauCeti.TLDiagCat.circlesCommuteAt`): juxtaposing a closed circle on either
side of a diagram adds one to its circle count without altering the boundary matching.

## Main definitions

* `TauCeti.TLDiagCat.instMonoidalCategoryStruct`: the monoidal data on `TLDiagCat`.
* `TauCeti.TLDiagCat.instMonoidalCategory`: the `CategoryTheory.MonoidalCategory` instance on
  `TLDiagCat`.

## Main results

* `TauCeti.TLDiagCat.circlesCommuteAt`: every scalar `d : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` is central
  at every object `X`, in the sense of `TauCeti.CirclesCommuteAt`.
* `TauCeti.TLDiagCat.circlesCommuteAt_circle`: in particular, `TLDiagCat.circle` commutes past
  every object.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace TLDiagCat

@[expose] section MonoidalStruct

instance instMonoidalCategoryStruct : MonoidalCategoryStruct TLDiagCat where
  tensorObj X Y := of (X.as + Y.as)
  whiskerLeft X {_ _} f := Hom.mk ((TLDiagram.id X.as).tensor f.diagram)
  whiskerRight {_ _} f Y := Hom.mk (f.diagram.tensor (TLDiagram.id Y.as))
  tensorHom f g := Hom.mk (f.diagram.tensor g.diagram)
  tensorUnit := of 0
  associator X Y Z := eqToIso (congrArg of (Nat.add_assoc X.as Y.as Z.as))
  leftUnitor X := eqToIso (congrArg of (Nat.zero_add X.as))
  rightUnitor X := Iso.refl X

end MonoidalStruct

variable {X Y Z X₁ Y₁ X₂ Y₂ : TLDiagCat}

@[simp]
theorem tensorObj_as (X Y : TLDiagCat) : (X ⊗ Y).as = X.as + Y.as :=
  (rfl)

theorem tensorObj_of (n m : ℕ) : of n ⊗ of m = of (n + m) :=
  (rfl)

theorem tensorUnit_eq : (𝟙_ TLDiagCat : TLDiagCat) = of 0 :=
  (rfl)

@[simp]
theorem tensorUnit_as : (𝟙_ TLDiagCat : TLDiagCat).as = 0 :=
  (rfl)

@[simp]
theorem diagram_tensorHom (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).diagram = f.diagram.tensor g.diagram :=
  (rfl)

@[simp]
theorem diagram_whiskerLeft (X : TLDiagCat) (f : Y₁ ⟶ Y₂) :
    (X ◁ f).diagram = (TLDiagram.id X.as).tensor f.diagram :=
  (rfl)

@[simp]
theorem diagram_whiskerRight (f : X₁ ⟶ X₂) (Y : TLDiagCat) :
    (f ▷ Y).diagram = f.diagram.tensor (TLDiagram.id Y.as) :=
  (rfl)

theorem associator_eq (X Y Z : TLDiagCat) :
    α_ X Y Z = eqToIso (congrArg of (Nat.add_assoc X.as Y.as Z.as)) :=
  (rfl)

theorem leftUnitor_eq (X : TLDiagCat) :
    λ_ X = eqToIso (congrArg of (Nat.zero_add X.as)) :=
  (rfl)

theorem rightUnitor_eq (X : TLDiagCat) : ρ_ X = Iso.refl X :=
  (rfl)

theorem rightUnitor_hom (X : TLDiagCat) : (ρ_ X).hom = 𝟙 X :=
  (rfl)

theorem rightUnitor_inv (X : TLDiagCat) : (ρ_ X).inv = 𝟙 X :=
  (rfl)

/-! ### Effect of `eqToHom` on underlying diagrams -/

theorem matching_comp_eqToHom (f : X ⟶ Y) (h : Y = Z) :
    (f ≫ eqToHom h).diagram.matching =
      PlanarMatching.cast (by cases h; rfl) f.diagram.matching := by
  cases h
  simp

theorem circles_comp_eqToHom (f : X ⟶ Y) (h : Y = Z) :
    (f ≫ eqToHom h).diagram.circles = f.diagram.circles := by
  cases h
  simp

theorem matching_eqToHom_comp (h : X = Y) (f : Y ⟶ Z) :
    (eqToHom h ≫ f).diagram.matching =
      PlanarMatching.cast (by cases h; rfl) f.diagram.matching := by
  cases h
  simp

theorem circles_eqToHom_comp (h : X = Y) (f : Y ⟶ Z) :
    (eqToHom h ≫ f).diagram.circles = f.diagram.circles := by
  cases h
  simp

@[simp]
theorem circles_eqToHom (h : X = Y) : (eqToHom h).diagram.circles = 0 := by
  cases h
  simp

private theorem tensorHom_eqToHom (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂) :
    eqToHom h₁ ⊗ₘ eqToHom h₂ = eqToHom (by rw [h₁, h₂]) := by
  cases h₁
  cases h₂
  exact hom_ext (TLDiagram.tensor_id_id X₁.as X₂.as)

/-! ### The `MonoidalCategory` instance -/

instance instMonoidalCategory : MonoidalCategory TLDiagCat :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X₁ X₂ => hom_ext (TLDiagram.tensor_id_id X₁.as X₂.as))
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun {_ _} _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      hom_ext (TLDiagram.tensor_comp f₁.diagram g₁.diagram f₂.diagram g₂.diagram))
    (associator_naturality := fun f₁ f₂ f₃ => by
      apply hom_ext
      ext : 1
      · simp only [associator_eq, eqToIso.hom, matching_comp_eqToHom, matching_eqToHom_comp,
          diagram_tensorHom]
        rw [← Equiv.symm_apply_eq, PlanarMatching.cast_symm, PlanarMatching.cast_cast]
        exact TLDiagram.matching_tensor_assoc f₁.diagram f₂.diagram f₃.diagram
      · simp only [associator_eq, eqToIso.hom, circles_comp_eqToHom, circles_eqToHom_comp,
          diagram_tensorHom, TLDiagram.circles_tensor, add_assoc])
    (leftUnitor_naturality := fun f => by
      apply hom_ext
      ext : 1
      · simp only [leftUnitor_eq, eqToIso.hom, matching_comp_eqToHom, matching_eqToHom_comp,
          diagram_tensorHom, diagram_id]
        rw [← Equiv.symm_apply_eq, PlanarMatching.cast_symm, PlanarMatching.cast_cast]
        exact TLDiagram.matching_zero_tensor (TLDiagram.id 0) f.diagram
      · simp only [leftUnitor_eq, eqToIso.hom, circles_comp_eqToHom, circles_eqToHom_comp,
          diagram_tensorHom, diagram_id, TLDiagram.circles_tensor, TLDiagram.circles_id, zero_add])
    (rightUnitor_naturality := fun f => hom_ext <| by
      simp only [rightUnitor_hom, diagram_comp, diagram_tensorHom, diagram_id]
      exact (TLDiagram.comp_id _).trans
        ((TLDiagram.tensor_id_zero f.diagram).trans (TLDiagram.id_comp _).symm))
    (pentagon := fun W X Y Z => by
      simp only [associator_eq, eqToIso.hom, ← eqToHom_refl, tensorHom_eqToHom, eqToHom_trans])
    (triangle := fun X Y => by
      simp only [associator_eq, leftUnitor_eq, rightUnitor_hom, eqToIso.hom, ← eqToHom_refl,
        tensorHom_eqToHom, eqToHom_trans])

/-! ### Circle centrality -/

/-- Every scalar `d : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` acts identically on the right and on the left
of every object `X`: juxtaposing closed circles on either side preserves the boundary matching and
adds `d.diagram.circles` to the circle count. -/
theorem circlesCommuteAt (d : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat) (X : TLDiagCat) :
    CirclesCommuteAt d X := by
  rw [circlesCommuteAt_iff, rightUnitor_inv, rightUnitor_hom, Category.id_comp]
  have hcomp : X ◁ d ≫ 𝟙 X = X ◁ d := Category.comp_id (X ◁ d)
  rw [hcomp]
  apply hom_ext
  ext : 1
  · simp only [leftUnitor_eq, eqToIso.inv, eqToIso.hom, matching_eqToHom_comp,
      matching_comp_eqToHom, diagram_whiskerLeft, diagram_whiskerRight, PlanarMatching.cast_cast]
    rw [TLDiagram.matching_tensor_zero, TLDiagram.matching_zero_tensor]
  · simp only [leftUnitor_eq, eqToIso.inv, eqToIso.hom, circles_eqToHom_comp,
      circles_comp_eqToHom, diagram_whiskerLeft, diagram_whiskerRight, TLDiagram.circles_tensor,
      TLDiagram.circles_id, zero_add, add_zero]

/-- The closed circle `TLDiagCat.circle` commutes past every object of `TLDiagCat`. -/
theorem circlesCommuteAt_circle (X : TLDiagCat) : CirclesCommuteAt circle X :=
  circlesCommuteAt circle X

end TLDiagCat

end TauCeti
