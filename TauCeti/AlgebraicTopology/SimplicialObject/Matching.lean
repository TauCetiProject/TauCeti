/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Matching maps of simplicial objects

For a simplicial object `X` in a category `C` and `n : ℕ`, the *matching map* in degree `n + 1` is
the component at `⦋n + 1⦌` of the unit `X ⟶ (cosk n).obj X` of the adjunction between
`n`-truncation and the `n`-coskeleton (`CategoryTheory.SimplicialObject.coskAdj`). Its target, the
*matching object*, is the limit of the `X _⦋k⦌` over all simplices `⦋k⦌ ⟶ ⦋n + 1⦌` with `k ≤ n`,
that is, over the boundary of the standard `(n + 1)`-simplex. The matching map sends an
`(n + 1)`-simplex to the family of its faces.

When the right Kan extensions defining the coskeleton are pointwise, this limit is realized by
the cone `CategoryTheory.SimplicialObject.matchingCone`, and the matching map is characterized by
its composites with the projections of that cone (`matchingMap_π` and `cosk_obj_hom_ext`).
Surjectivity conditions on matching maps define hypercovers.

## Main definitions

* `CategoryTheory.SimplicialObject.matchingMap`: the matching map
  `X _⦋n + 1⦌ ⟶ ((cosk n).obj X) _⦋n + 1⦌`.
* `CategoryTheory.SimplicialObject.matchingCone`: the cone over the faces of dimension at most `n`
  of `⦋n + 1⦌` with vertex the matching object.
* `CategoryTheory.SimplicialObject.isLimitMatchingCone`: it is a limit cone.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section VII.1, for matching objects and coskeleta.
-/

public section

open CategoryTheory Limits Opposite Functor

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] (n : ℕ)

section

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/-- The `n`-coskeleton of a truncated simplicial object, with the counit of the adjunction
`truncation n ⊣ Truncated.cosk n`, is a right Kan extension. This only uses the existence of the
right Kan extensions, and not of left Kan extensions. -/
instance Truncated.cosk_obj_isRightKanExtension (T : Truncated C n) :
    ((Truncated.cosk n).obj T).IsRightKanExtension ((coskAdj n).counit.app T) := by
  dsimp [coskAdj]
  rw [ranAdjunction_counit]
  infer_instance

variable (X : SimplicialObject C)

/-- The matching map of `X` in degree `n + 1`, from `X _⦋n + 1⦌` to the matching object
`((cosk n).obj X) _⦋n + 1⦌`. It sends a simplex to the family of its faces of dimension at
most `n`. -/
noncomputable def matchingMap : X _⦋n + 1⦌ ⟶ ((cosk n).obj X) _⦋n + 1⦌ :=
  ((coskAdj n).unit.app X).app (op ⦋n + 1⦌)

/-- The cone over the simplices `⦋k⦌ ⟶ ⦋n + 1⦌` with `k ≤ n` whose vertex is the matching object
`((cosk n).obj X) _⦋n + 1⦌`. It is a limit cone when the right Kan extensions defining the
coskeleton are pointwise (`isLimitMatchingCone`). -/
noncomputable abbrev matchingCone :
    Cone (StructuredArrow.proj (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op ⋙
      (truncation n).obj X) :=
  (RightExtension.mk _ ((coskAdj n).counit.app ((truncation n).obj X))).coneAt (op ⦋n + 1⦌)

/-- The projection of the matching map to the face `f` of `⦋n + 1⦌` is the action of `f`. -/
@[reassoc]
theorem matchingMap_π
    (f : StructuredArrow (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op) :
    X.matchingMap n ≫ (X.matchingCone n).π.app f = X.map f.hom := by
  have h := congr_app ((coskAdj (C := C) n).left_triangle_components X) f.right
  have h' := ((coskAdj (C := C) n).unit.app X).naturality f.hom
  dsimp [matchingMap] at h h' ⊢
  rw [← Category.assoc, ← h', Category.assoc]
  -- `h` is the triangle identity, stated with the component of the unit at the truncated object.
  exact (congrArg (X.map f.hom ≫ ·) h).trans (Category.comp_id _)

end

section

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
  (X : SimplicialObject C)

/-- When the right Kan extensions defining the `n`-coskeleton are pointwise, the matching object
is the limit of the `X _⦋k⦌` over the simplices `⦋k⦌ ⟶ ⦋n + 1⦌` with `k ≤ n`. -/
noncomputable def isLimitMatchingCone : IsLimit (X.matchingCone n) :=
  isPointwiseRightKanExtensionOfIsRightKanExtension _ _ (op ⦋n + 1⦌)

variable {X n} in
/-- Two morphisms into the matching object agree if their projections to every simplex
`⦋k⦌ ⟶ ⦋n + 1⦌` with `k ≤ n` agree. -/
theorem cosk_obj_hom_ext {Z : C} {g h : Z ⟶ ((cosk n).obj X) _⦋n + 1⦌}
    (w : ∀ f, g ≫ (X.matchingCone n).π.app f = h ≫ (X.matchingCone n).π.app f) : g = h :=
  (X.isLimitMatchingCone n).hom_ext w

end

end CategoryTheory.SimplicialObject
