/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Discrete simplicial sets

The discrete simplicial set on a type `ι` is the constant simplicial set
`(Functor.const SimplexCategoryᵒᵖ).obj ι`: its simplices in every dimension are the elements of
`ι`, and all its faces and degeneracies are identities. It is the free simplicial set on the
vertices `ι`: a map from it to a simplicial set `X` is a family `ι → X _⦋0⦌` of vertices
(`SSet.constHomEquiv`). Its only nondegenerate simplices are its vertices, so it has exactly as
many nondegenerate simplices as `ι` has elements (`SSet.constNEquiv`). Discrete simplicial sets are
therefore the test objects for statements about families of vertices that are phrased in terms of
the number of nondegenerate simplices, such as cardinal filteredness.

## Main declarations

* `SSet.constHomEquiv`: maps from the discrete simplicial set on `ι` are families of vertices.
* `SSet.constNEquiv`: the nondegenerate simplices of the discrete simplicial set on `ι` are the
  elements of `ι`.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet

variable (ι : Type u) {X : SSet.{u}}

/-- Maps from the discrete simplicial set on `ι` to `X` are families of vertices of `X` indexed by
`ι`; the map attached to a family sends `i` in every dimension to the degenerate simplex on the
vertex at `i`. This is the adjunction between constant presheaves and evaluation at the terminal
object `⦋0⦌` of `SimplexCategory`. -/
noncomputable def constHomEquiv : ((Functor.const SimplexCategoryᵒᵖ).obj ι ⟶ X) ≃ (ι → X _⦋0⦌) :=
  ((constantPresheafAdj (Type u) SimplexCategory.isTerminalZero).homEquiv ι X).trans
    TypeCat.homEquiv

@[simp]
lemma constHomEquiv_apply (f : (Functor.const SimplexCategoryᵒᵖ).obj ι ⟶ X) (i : ι) :
    constHomEquiv ι f i = f.app (op ⦋0⦌) i :=
  (rfl)

/-- The map from the discrete simplicial set given by a family of vertices sends the vertex `i`
to the vertex at `i`. The source of the component is stated as `ι`, its simp-normal form. -/
@[simp]
lemma constHomEquiv_symm_app_zero (x : ι → X _⦋0⦌) (i : ι) :
    ConcreteCategory.hom (X := ι) (Y := X _⦋0⦌) (((constHomEquiv ι).symm x).app (op ⦋0⦌)) i =
      x i :=
  congrFun ((constHomEquiv ι).apply_symm_apply x) i

/-- Every simplex of positive dimension of a discrete simplicial set is degenerate. -/
@[simp]
lemma const_degenerate_succ (n : ℕ) :
    SSet.degenerate ((Functor.const SimplexCategoryᵒᵖ).obj ι) (n + 1) = Set.univ :=
  -- Faces and degeneracies of a discrete simplicial set are identities, so `i = σ₀ i`.
  Set.eq_univ_of_forall fun i ↦
    σ_mem_degenerate (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) (n := n) 0 i

/-- The nondegenerate simplices of the discrete simplicial set on `ι` are its vertices, the
elements of `ι`. -/
def constNEquiv : SSet.N ((Functor.const SimplexCategoryᵒᵖ).obj ι) ≃ ι where
  toFun s := s.simplex
  invFun i := N.mk (n := 0) i (by simp)
  left_inv s := by
    induction s with | mk n s
    obtain ⟨s, hs⟩ := s
    obtain _ | n := n
    · rfl
    · simp [nonDegenerate, const_degenerate_succ] at hs
  right_inv _ := rfl

end SSet
