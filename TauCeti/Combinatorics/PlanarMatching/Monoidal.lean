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

Every endomorphism `a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` of the unit is a collection of closed circles,
and tensoring it on the left or on the right of any object `X` adds the same number of circles to
`𝟙 X`. In particular, every scalar — including `TLDiagCat.circle` and `TLDiagCat.cup ≫
TLDiagCat.cap` — is central at every object (`TauCeti.TLDiagCat.circlesCommuteAt_scalar`).

## Main definitions

* `TauCeti.TLDiagCat.instMonoidalCategory`: the monoidal structure on `TLDiagCat`.

## Main results

* `TauCeti.TLDiagCat.diagram_tensorHom`, `TauCeti.TLDiagCat.diagram_whiskerLeft`,
  `TauCeti.TLDiagCat.diagram_whiskerRight`: the diagrams of tensor products and whiskerings.
* `TauCeti.TLDiagCat.associator_hom`, `TauCeti.TLDiagCat.leftUnitor_hom`,
  `TauCeti.TLDiagCat.rightUnitor_hom` and their inverses: the structure isomorphisms are transports
  along equalities of objects, so the monoidal structure is strict.
* `TauCeti.TLDiagCat.circlesCommuteAt_scalar`, `TauCeti.TLDiagCat.circlesCommuteAt_circle`: every
  scalar, and in particular the closed circle, acts equally on the left and right of every object.

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

/-- Postcomposing with `eqToHom h` casts the top boundary of the underlying diagram. -/
theorem diagram_comp_eqToHom (f : X ⟶ Y) (h : Y = Z) :
    (f ≫ eqToHom h).diagram = TLDiagram.cast rfl (congrArg as h) f.diagram := by
  subst h; simp

/-- Precomposing with `eqToHom h` casts the bottom boundary of the underlying diagram. -/
theorem diagram_eqToHom_comp (h : X = Y) (f : Y ⟶ Z) :
    (eqToHom h ≫ f).diagram = TLDiagram.cast (congrArg as h).symm rfl f.diagram := by
  subst h; simp

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

/-! ### Centrality of scalars and closed circles -/

/-- Acting on the right of `X` by a scalar `a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` keeps the identity
matching on `X.as` strands and adds the circles of `a`. -/
theorem diagram_rightUnitor_inv_whiskerLeft_rightUnitor_hom
    (a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat) (X : TLDiagCat) :
    ((ρ_ X).inv ≫ X ◁ a ≫ (ρ_ X).hom).diagram =
      ⟨(TLDiagram.id X.as).matching, a.diagram.circles⟩ := by
  have hm : a.diagram.matching = (TLDiagram.id 0).matching :=
    PlanarMatching.ext fun i => i.elim0
  have ht := congrArg TLDiagram.matching (TLDiagram.tensor_id_zero (TLDiagram.id X.as))
  rw [TLDiagram.matching_tensor, TLDiagram.matching_id] at ht
  rw [rightUnitor_inv, rightUnitor_hom, diagram_eqToHom_comp, diagram_comp_eqToHom,
    diagram_whiskerLeft, TLDiagram.cast_cast]
  ext : 1
  · simp only [TLDiagram.matching_cast, TLDiagram.matching_tensor, TLDiagram.matching_id, hm]
    simpa [PlanarMatching.cast_cast] using ht
  · simp

/-- Acting on the left of `X` by a scalar `a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat` keeps the identity
matching on `X.as` strands and adds the circles of `a`. -/
theorem diagram_leftUnitor_inv_whiskerRight_leftUnitor_hom
    (a : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat) (X : TLDiagCat) :
    ((λ_ X).inv ≫ a ▷ X ≫ (λ_ X).hom).diagram =
      ⟨(TLDiagram.id X.as).matching, a.diagram.circles⟩ := by
  have hm : a.diagram.matching = (TLDiagram.id 0).matching :=
    PlanarMatching.ext fun i => i.elim0
  have ht := congrArg (PlanarMatching.cast (by omega : 0 + X.as + (0 + X.as) = X.as + X.as))
    (congrArg TLDiagram.matching (TLDiagram.id_zero_tensor (TLDiagram.id X.as)))
  rw [TLDiagram.matching_tensor, TLDiagram.matching_cast, TLDiagram.matching_id,
    PlanarMatching.cast_cast, PlanarMatching.cast_cast, PlanarMatching.cast_refl,
    Equiv.refl_apply] at ht
  rw [leftUnitor_inv, leftUnitor_hom, diagram_eqToHom_comp, diagram_comp_eqToHom,
    diagram_whiskerRight, TLDiagram.cast_cast]
  ext : 1
  · simp only [TLDiagram.matching_cast, TLDiagram.matching_tensor, TLDiagram.matching_id, hm,
      PlanarMatching.cast_cast] at ht ⊢
    exact ht
  · simp

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
