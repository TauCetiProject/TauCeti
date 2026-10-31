/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Maps to the nerve of a preorder

The nerve of a preorder `P` is thin: an `n`-simplex is a monotone chain of `n + 1` elements of
`P`, determined by its vertices. Accordingly, a map of simplicial sets `X ⟶ nerve P` is the same as
a map `g : X _⦋0⦌ → P` on vertices that is monotone along the edges of `X`, in the sense that
`g x ≤ g y` whenever `X` has an edge from `x` to `y`. A simplex of `X` is sent to the chain of the
values of `g` at its vertices.

This describes, for instance, the maps from a join to the nerve of a preorder, where a cone point
is sent to an upper bound.

## Main declarations

* `CategoryTheory.nerve.homOfVertex`: the map `X ⟶ nerve P` given by a map on vertices that is
  monotone along edges.
* `CategoryTheory.nerve.homEquivOfPreorder`: maps `X ⟶ nerve P` correspond to maps on vertices
  that are monotone along edges.
* `CategoryTheory.nerve.hom_ext_of_preorder`: maps to the nerve of a preorder agree when they agree
  on vertices.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace CategoryTheory.nerve

variable {X : SSet.{u}} {P : Type u} [Preorder P]

/-- The `i`-th vertex of the image of a simplex `s` under `X.map f` is the `f i`-th vertex
of `s`. -/
private lemma map_const_map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (s : X.obj n)
    (i : Fin (m.unop.len + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ m.unop i).op (X.map f s) =
      X.map (SimplexCategory.const ⦋0⦌ n.unop (f.unop.toOrderHom i)).op s := by
  rw [← Functor.map_comp_apply, ← Quiver.Hom.op_unop f, ← op_comp, SimplexCategory.const_comp]
  rfl

/-- A map on vertices that is monotone along edges is monotone along the vertices of each
simplex, since any two vertices of a simplex span an edge. -/
private lemma monotone_map_const (g : X _⦋0⦌ → P) (hg : ∀ ⦃x y⦄, X.Edge x y → g x ≤ g y)
    {n : SimplexCategoryᵒᵖ} (s : X.obj n) :
    Monotone fun i ↦ g (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op s) := by
  intro i j h
  refine hg (SSet.Edge.mk (X.map (SimplexCategory.mkOfLe i j h).op s) ?_ ?_) <;>
  · rw [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp]
    congr 3
    ext a
    fin_cases a
    rfl

/-- The map to the nerve of a preorder given by a map on vertices that is monotone along edges:
a simplex goes to the chain of the values at its vertices. -/
def homOfVertex (g : X _⦋0⦌ → P) (hg : ∀ ⦃x y⦄, X.Edge x y → g x ≤ g y) : X ⟶ nerve P where
  app n := ↾fun s ↦ (monotone_map_const g hg s).functor
  naturality n m f := by
    ext s i
    exact congrArg g (map_const_map f s i)

/-- The `i`-th vertex of the image of a simplex `s` under `homOfVertex g hg` is the value of `g`
at the `i`-th vertex of `s`. -/
lemma homOfVertex_app_obj (g : X _⦋0⦌ → P) (hg : ∀ ⦃x y⦄, X.Edge x y → g x ≤ g y)
    {n : SimplexCategoryᵒᵖ} (s : X.obj n) (i : Fin (n.unop.len + 1)) :
    ((homOfVertex g hg).app n s).obj i = g (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op s) :=
  (rfl)

@[simp]
lemma nerveEquiv_homOfVertex_app (g : X _⦋0⦌ → P) (hg : ∀ ⦃x y⦄, X.Edge x y → g x ≤ g y)
    (x : X _⦋0⦌) : nerveEquiv ((homOfVertex g hg).app _ x) = g x := by
  rw [nerveEquiv, Equiv.coe_fn_mk, homOfVertex_app_obj,
    Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ _) (𝟙 _), op_id]
  simp

/-- A map to the nerve of a preorder is monotone along edges on vertices. -/
lemma le_of_edge (f : X ⟶ nerve P) {x y : X _⦋0⦌} (e : X.Edge x y) :
    nerveEquiv (f.app _ x) ≤ nerveEquiv (f.app _ y) :=
  (nerve.homEquiv (e.map f)).le

/-- Maps to the nerve of a preorder agree when they agree on vertices. -/
lemma hom_ext_of_preorder {f f' : X ⟶ nerve P}
    (h : ∀ x : X _⦋0⦌, nerveEquiv (f.app _ x) = nerveEquiv (f'.app _ x)) : f = f' := by
  ext n s : 4
  apply nerve.ext_of_isThin
  funext i
  -- The `i`-th vertex of the image of `s` is the image of the `i`-th vertex of `s`.
  have hf := congrArg nerveEquiv (f.naturality_apply (SimplexCategory.const ⦋0⦌ n.unop i).op s)
  have hf' := congrArg nerveEquiv (f'.naturality_apply (SimplexCategory.const ⦋0⦌ n.unop i).op s)
  exact hf.symm.trans ((h _).trans hf')

/-- Maps from a simplicial set `X` to the nerve of a preorder `P` correspond to maps
`X _⦋0⦌ → P` on vertices that are monotone along the edges of `X`. -/
def homEquivOfPreorder :
    (X ⟶ nerve P) ≃ {g : X _⦋0⦌ → P // ∀ ⦃x y⦄, X.Edge x y → g x ≤ g y} where
  toFun f := ⟨fun x ↦ nerveEquiv (f.app _ x), fun _ _ e ↦ le_of_edge f e⟩
  invFun g := homOfVertex g.1 g.2
  left_inv _ := hom_ext_of_preorder fun x ↦ nerveEquiv_homOfVertex_app _ _ x
  right_inv g := Subtype.ext (funext fun x ↦ nerveEquiv_homOfVertex_app g.1 g.2 x)

@[simp]
lemma homEquivOfPreorder_apply_coe (f : X ⟶ nerve P) (x : X _⦋0⦌) :
    (homEquivOfPreorder f).1 x = nerveEquiv (f.app _ x) :=
  (rfl)

lemma homEquivOfPreorder_symm_apply (g : {g : X _⦋0⦌ → P // ∀ ⦃x y⦄, X.Edge x y → g x ≤ g y}) :
    homEquivOfPreorder.symm g = homOfVertex g.1 g.2 :=
  (rfl)

end CategoryTheory.nerve
