/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.Combinatorics.PlanarMatching.Associativity

/-!
# The Temperley–Lieb diagram category

The **Temperley–Lieb diagram category** `TauCeti.TLDiagCat` has one object `TLDiagCat.of n` for
each number `n` of boundary points, and its morphisms `of n ⟶ of m` are the Temperley–Lieb
diagrams `n → m` (`TauCeti.TLDiagram n m`): planar matchings of the `n + m` boundary points of a
rectangle together with a number of closed circles. Composition `f ≫ g` stacks `g` on top of `f`
and glues along the middle boundary, keeping the circles of both diagrams and adding those closed
in the middle (`TauCeti.TLDiagram.comp`); the identities are the diagrams with straight strands.
The category axioms are `TauCeti.TLDiagram.id_comp`, `TauCeti.TLDiagram.comp_id` and the
associativity of gluing, `TauCeti.TLDiagram.comp_assoc`.

The circles are kept as data rather than evaluated: a closed circle is the nontrivial endomorphism
`TLDiagCat.circle` of the empty boundary `of 0`, and `TLDiagCat.cup ≫ TLDiagCat.cap` is that
circle. Keeping the count, rather than evaluating each circle at a loop value `δ`, is what lets
the linearization at every `δ` factor through this one category.

## Main definitions

* `TauCeti.TLDiagCat`: the Temperley–Lieb diagram category, with objects `TLDiagCat.of n`.
* `TauCeti.TLDiagCat.homEquiv`: morphisms `X ⟶ Y` are Temperley–Lieb diagrams `X.as → Y.as`.
* `TauCeti.TLDiagCat.cup`, `TauCeti.TLDiagCat.cap`, `TauCeti.TLDiagCat.circle`: the cup
  `of 0 ⟶ of 2`, the cap `of 2 ⟶ of 0` and the closed circle `of 0 ⟶ of 0`.
* `TauCeti.TLDiagCat.endZeroMulEquiv`: the endomorphism monoid of `of 0` is the free monoid on
  the circle, `End (of 0) ≃* Multiplicative ℕ`, by counting circles.

## Main results

* `TauCeti.TLDiagCat.cup_comp_cap`: a cup followed by a cap is the closed circle.
* `TauCeti.TLDiagCat.endZeroMulEquiv_circle`: the circle corresponds to the generator of
  `Multiplicative ℕ`, so its powers are pairwise distinct.
* `TauCeti.TLDiagCat.end_zero_eq_circle_pow`: every endomorphism of `of 0` is a power of the
  circle.
* `TauCeti.TLDiagCat.nonempty_hom_iff`: there is a morphism `X ⟶ Y` exactly when the total
  number of boundary points of `X` and `Y` is even.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory

namespace TauCeti

/-- The **Temperley–Lieb diagram category**. An object is a number of boundary points, wrapped in
a one-field structure (with constructor `TLDiagCat.of`) so that the category structure lives on a
dedicated type rather than on `ℕ`. Its morphisms are the Temperley–Lieb diagrams, see
`TauCeti.TLDiagCat.homEquiv`. -/
@[ext]
structure TLDiagCat : Type where
  /-- The object of the Temperley–Lieb diagram category with `n` boundary points. -/
  of ::
  /-- The number of boundary points of an object of the Temperley–Lieb diagram category. -/
  as : ℕ
  deriving DecidableEq

namespace TLDiagCat

@[simp]
theorem of_as (X : TLDiagCat) : of X.as = X := (rfl)

/-- A morphism `X ⟶ Y` of the Temperley–Lieb diagram category: a Temperley–Lieb diagram with
`X.as` points on the bottom and `Y.as` points on the top. -/
@[ext]
structure Hom (X Y : TLDiagCat) where
  /-- The morphism of the Temperley–Lieb diagram category given by a diagram. -/
  mk ::
  /-- The Temperley–Lieb diagram underlying a morphism. -/
  diagram : TLDiagram X.as Y.as
  deriving DecidableEq

instance : Category TLDiagCat where
  Hom := Hom
  id X := ⟨TLDiagram.id X.as⟩
  comp f g := ⟨f.diagram.comp g.diagram⟩
  id_comp f := Hom.ext (TLDiagram.id_comp f.diagram)
  comp_id f := Hom.ext (TLDiagram.comp_id f.diagram)
  assoc f g h := Hom.ext (TLDiagram.comp_assoc f.diagram g.diagram h.diagram)

variable {X Y Z : TLDiagCat}

instance (X Y : TLDiagCat) : DecidableEq (X ⟶ Y) :=
  inferInstanceAs (DecidableEq (Hom X Y))

/-- Two morphisms of the Temperley–Lieb diagram category are equal if their diagrams are.

This registers extensionality for categorical morphisms `X ⟶ Y`: the generated `Hom.ext` is
indexed by `Hom X Y`, which the `ext` tactic does not find on a goal stated using `⟶`. -/
@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.diagram = g.diagram) : f = g :=
  Hom.ext h

@[simp]
theorem Hom.mk_diagram (f : X ⟶ Y) : (Hom.mk f.diagram : X ⟶ Y) = f := (rfl)

/-- The diagram of an identity morphism is the identity diagram, with straight strands and no
circles. -/
@[simp]
theorem diagram_id (X : TLDiagCat) : (𝟙 X : X ⟶ X).diagram = TLDiagram.id X.as := (rfl)

/-- The diagram of a composite `f ≫ g` is `g` stacked on top of `f`, glued along the middle. -/
@[simp]
theorem diagram_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).diagram = f.diagram.comp g.diagram :=
  (rfl)

/-- The morphisms `X ⟶ Y` of the Temperley–Lieb diagram category are the Temperley–Lieb diagrams
from `X.as` bottom points to `Y.as` top points. -/
def homEquiv (X Y : TLDiagCat) : (X ⟶ Y) ≃ TLDiagram X.as Y.as where
  toFun f := f.diagram
  invFun D := Hom.mk D
  left_inv _ := (rfl)
  right_inv _ := (rfl)

@[simp]
theorem homEquiv_apply (f : X ⟶ Y) : homEquiv X Y f = f.diagram := (rfl)

@[simp]
theorem homEquiv_symm_apply (D : TLDiagram X.as Y.as) : (homEquiv X Y).symm D = Hom.mk D := (rfl)

/-- There is a morphism `X ⟶ Y` exactly when the total number `X.as + Y.as` of boundary points is
even: an odd number of points has no planar matching, and an even number `j + j` has the nested
one. -/
theorem nonempty_hom_iff : Nonempty (X ⟶ Y) ↔ Even (X.as + Y.as) :=
  (homEquiv X Y).nonempty_congr.trans TLDiagram.nonempty_iff

/-! ### The cup, the cap and the circle -/

/-- The **cup** `of 0 ⟶ of 2`, joining the two top points. -/
def cup : of 0 ⟶ of 2 :=
  Hom.mk TLDiagram.cup

/-- The **cap** `of 2 ⟶ of 0`, joining the two bottom points. -/
def cap : of 2 ⟶ of 0 :=
  Hom.mk TLDiagram.cap

/-- The **closed circle**, the endomorphism of the empty boundary `of 0` with one circle. -/
def circle : of 0 ⟶ of 0 :=
  Hom.mk ⟨PlanarMatching.nested 0, 1⟩

@[simp]
theorem diagram_cup : cup.diagram = TLDiagram.cup := (rfl)

@[simp]
theorem diagram_cap : cap.diagram = TLDiagram.cap := (rfl)

@[simp]
theorem diagram_circle : circle.diagram = ⟨PlanarMatching.nested 0, 1⟩ := (rfl)

/-- **A cup followed by a cap is the closed circle.** -/
@[reassoc (attr := simp)]
theorem cup_comp_cap : cup ≫ cap = circle :=
  hom_ext (by simp [TLDiagram.cup_comp_cap])

/-! ### Endomorphisms of the empty boundary -/

/-- Every diagram `0 → 0` is a number of closed circles: there is only one matching of no
points. -/
private theorem diagram_eq_of_zero (f : of 0 ⟶ of 0) :
    f.diagram = ⟨PlanarMatching.nested 0, f.diagram.circles⟩ :=
  TLDiagram.ext (Subsingleton.elim (α := PlanarMatching 0) _ _) rfl

/-- **The endomorphisms of the empty boundary are freely generated by the circle**: an
endomorphism of `of 0` is determined by its number of circles, and composing two of them adds the
numbers of circles, since gluing along an empty boundary closes no new circle. -/
def endZeroMulEquiv : End (of 0) ≃* Multiplicative ℕ where
  toFun f := Multiplicative.ofAdd f.asHom.diagram.circles
  invFun k := .of (Hom.mk ⟨PlanarMatching.nested 0, k.toAdd⟩)
  left_inv f := End.ext (hom_ext (diagram_eq_of_zero f.asHom)).symm
  right_inv _ := (rfl)
  map_mul' f g := by
    rw [End.mul_asHom, diagram_comp, TLDiagram.circles_comp,
      PlanarMatching.glueMiddleCircles_zero, add_zero, add_comm, ofAdd_add]

@[simp]
theorem endZeroMulEquiv_apply (f : End (of 0)) :
    endZeroMulEquiv f = Multiplicative.ofAdd f.asHom.diagram.circles := (rfl)

/-- The circle corresponds to the generator `Multiplicative.ofAdd 1` of `Multiplicative ℕ`. -/
theorem endZeroMulEquiv_circle : endZeroMulEquiv (.of circle) = Multiplicative.ofAdd 1 := (rfl)

@[simp]
theorem endZeroMulEquiv_symm_apply (k : Multiplicative ℕ) :
    endZeroMulEquiv.symm k = .of circle ^ k.toAdd := by
  rw [MulEquiv.symm_apply_eq, map_pow, endZeroMulEquiv_circle, ← ofAdd_nsmul, smul_eq_mul,
    mul_one, ofAdd_toAdd]

/-- Every endomorphism of the empty boundary is a power of the circle, namely the power given by
its number of circles. -/
theorem end_zero_eq_circle_pow (f : End (of 0)) : f = .of circle ^ f.asHom.diagram.circles :=
  (endZeroMulEquiv.symm_apply_apply f).symm.trans (endZeroMulEquiv_symm_apply _)

/-- The `k`-th power of the circle in `End (of 0)` is the empty diagram with `k` circles. -/
@[simp]
theorem diagram_circle_pow (k : ℕ) :
    ((End.of circle) ^ k).asHom.diagram = ⟨PlanarMatching.nested 0, k⟩ := by
  rw [diagram_eq_of_zero]
  simpa using congrArg Multiplicative.toAdd (map_pow endZeroMulEquiv (.of circle) k)

end TLDiagCat

end TauCeti
