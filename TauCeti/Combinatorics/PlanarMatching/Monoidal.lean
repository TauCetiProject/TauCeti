/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import TauCeti.Combinatorics.PlanarMatching.Category
public import TauCeti.Combinatorics.PlanarMatching.Tensor

/-!
# The monoidal structure of the Temperley–Lieb diagram category

The Temperley–Lieb diagram category `TauCeti.TLDiagCat` is a strict monoidal category under
juxtaposition. The tensor product of objects adds the numbers of boundary points,
`TLDiagCat.of n ⊗ TLDiagCat.of m = TLDiagCat.of (n + m)`, the unit is the empty boundary
`TLDiagCat.of 0`, and the tensor product `f ⊗ₘ g` of two morphisms places the diagram of `g` to the
right of that of `f` (`TauCeti.TLDiagram.tensor`). The associators and unitors are the transports
`eqToHom` along the equalities `n + m + k = n + (m + k)`, `0 + n = n` and `n + 0 = n`.

The axioms of a monoidal category come from the laws of `TauCeti.TLDiagram.tensor`: the interchange
law `TauCeti.TLDiagram.tensor_comp_tensor` makes the tensor product a functor, and associativity and
unitality of the tensor product of diagrams give the naturality of the associators and unitors.

## Main definitions

* `TauCeti.TLDiagCat.instMonoidalCategory`: the monoidal structure on `TLDiagCat`.

## Main results

* `TauCeti.TLDiagCat.diagram_tensorHom`, `TauCeti.TLDiagCat.diagram_whiskerLeft`,
  `TauCeti.TLDiagCat.diagram_whiskerRight`: the diagrams of tensor products and whiskerings.
* `TauCeti.TLDiagCat.associator_hom`, `TauCeti.TLDiagCat.leftUnitor_hom`,
  `TauCeti.TLDiagCat.rightUnitor_hom` and their inverses: the structure isomorphisms are transports
  along equalities of objects, so the monoidal structure is strict.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace TLDiagCat

instance : MonoidalCategoryStruct TLDiagCat where
  tensorObj X Y := of (X.as + Y.as)
  whiskerLeft X _ _ f := Hom.mk ((TLDiagram.id X.as).tensor f.diagram)
  whiskerRight f Y := Hom.mk (f.diagram.tensor (TLDiagram.id Y.as))
  tensorHom f g := Hom.mk (f.diagram.tensor g.diagram)
  tensorUnit := of 0
  associator X Y Z := eqToIso (TLDiagCat.ext (Nat.add_assoc X.as Y.as Z.as))
  leftUnitor X := eqToIso (TLDiagCat.ext (Nat.zero_add X.as))
  rightUnitor X := eqToIso (TLDiagCat.ext (Nat.add_zero X.as))

variable {X Y Z X' Y' : TLDiagCat}

/-! The next two lemmas are proved by `rfl`, not `(rfl)`, so that `dsimp` and `simp` can rewrite
the numbers of points inside the indices of diagram types, where a propositional rewrite would not
typecheck. -/

/-- The tensor product of objects adds the numbers of boundary points. -/
@[simp]
theorem tensorObj_as (X Y : TLDiagCat) : (X ⊗ Y).as = X.as + Y.as := rfl

/-- The monoidal unit is the empty boundary. -/
@[simp]
theorem tensorUnit_as : (𝟙_ TLDiagCat).as = 0 := rfl

/-- The diagram of a tensor product of morphisms is the tensor product of their diagrams. -/
@[simp]
theorem diagram_tensorHom (f : X ⟶ Y) (g : X' ⟶ Y') :
    (f ⊗ₘ g).diagram = f.diagram.tensor g.diagram := (rfl)

/-- The diagram of a left whiskering `X ◁ f` is the diagram of `f` with `X.as` straight strands on
its left. -/
@[simp]
theorem diagram_whiskerLeft (X : TLDiagCat) (f : Y ⟶ Z) :
    (X ◁ f).diagram = (TLDiagram.id X.as).tensor f.diagram := (rfl)

/-- The diagram of a right whiskering `f ▷ Z` is the diagram of `f` with `Z.as` straight strands on
its right. -/
@[simp]
theorem diagram_whiskerRight (f : X ⟶ Y) (Z : TLDiagCat) :
    (f ▷ Z).diagram = f.diagram.tensor (TLDiagram.id Z.as) := (rfl)

/-- The associator is the transport along `X.as + Y.as + Z.as = X.as + (Y.as + Z.as)`. -/
theorem associator_hom (X Y Z : TLDiagCat) :
    (α_ X Y Z).hom = eqToHom (TLDiagCat.ext (Nat.add_assoc X.as Y.as Z.as)) := (rfl)

theorem associator_inv (X Y Z : TLDiagCat) :
    (α_ X Y Z).inv = eqToHom (TLDiagCat.ext (Nat.add_assoc X.as Y.as Z.as).symm) := (rfl)

/-- The left unitor is the transport along `0 + X.as = X.as`. -/
theorem leftUnitor_hom (X : TLDiagCat) :
    (λ_ X).hom = eqToHom (TLDiagCat.ext (Nat.zero_add X.as)) := (rfl)

theorem leftUnitor_inv (X : TLDiagCat) :
    (λ_ X).inv = eqToHom (TLDiagCat.ext (Nat.zero_add X.as).symm) := (rfl)

/-- The right unitor is the transport along `X.as + 0 = X.as`. -/
theorem rightUnitor_hom (X : TLDiagCat) :
    (ρ_ X).hom = eqToHom (TLDiagCat.ext (Nat.add_zero X.as)) := (rfl)

theorem rightUnitor_inv (X : TLDiagCat) :
    (ρ_ X).inv = eqToHom (TLDiagCat.ext (Nat.add_zero X.as).symm) := (rfl)

/-- **The Temperley–Lieb diagram category is monoidal** under juxtaposition of diagrams. The
monoidal structure is strict: the tensor product of objects adds the numbers of points, and the
associators and unitors are transports along equalities of objects. -/
instance instMonoidalCategory : MonoidalCategory TLDiagCat :=
  .ofTensorHom
    (id_tensorHom_id := fun X Y => hom_ext (TLDiagram.id_tensor_id X.as Y.as))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      hom_ext (TLDiagram.tensor_comp_tensor f₁.diagram f₂.diagram g₁.diagram g₂.diagram))
    (associator_naturality := fun _ _ _ => hom_ext <| by
      simp [associator_hom, TLDiagram.tensor_assoc])
    (leftUnitor_naturality := fun _ => hom_ext <| by simp [leftUnitor_hom])
    (rightUnitor_naturality := fun _ => hom_ext <| by simp [rightUnitor_hom])
    (pentagon := fun _ _ _ _ => hom_ext <| by simp [associator_hom])
    (triangle := fun _ _ => hom_ext <| by simp [associator_hom, leftUnitor_hom, rightUnitor_hom])

end TLDiagCat

/-- Juxtaposition is not symmetric: the cap on the two left points of three, `cap ▷ of 1`, differs
from the cap on the two right points, `of 1 ◁ cap`. In the first the bottom-left point is joined
to its neighbour, in the second to the top point. -/
example : TLDiagCat.cap ▷ TLDiagCat.of 1 ≠ TLDiagCat.of 1 ◁ TLDiagCat.cap := by
  intro h
  have := congrArg (fun f => (f.diagram.matching.val.val 0 : ℕ)) h
  have e₁ := PlanarMatching.coe_insertBlock_val_castAdd_castAdd TLDiagram.cap.matching
    (PlanarMatching.nested 1) (0 : Fin 2)
  have e₂ := PlanarMatching.coe_insertBlock_val_castAdd_castAdd (PlanarMatching.nested 1)
    TLDiagram.cap.matching (0 : Fin 1)
  simp [TLDiagram.cap_matching_val, PlanarMatching.nested_val] at this e₁ e₂
  omega

end TauCeti
