/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Edges of the nerve of a monoid

An edge of the nerve of a monoid `M`, viewed as a category with one object, is an element of `M`
(`CategoryTheory.nerve.edgeElem`), and the long edge of a `2`-simplex is the product of its two
short edges. Consequently, a homotopy `H` from `f` to `g` between maps `K ⟶ nerve (SingleObj M)`
satisfies, over each edge `e` of `K` from `x₀` to `x₁`, the relation
`H ({x₁} × Δ[1]) * f e = g e * H ({x₀} × Δ[1])` (`CategoryTheory.nerve.edgeElem_homotopy`),
obtained from the two triangles `SSet.Edge.CompStruct.ofSimplicialObjectHomotopy` and
`SSet.Edge.CompStruct.ofSimplicialObjectHomotopy'` cutting the square `e × Δ[1]` along its
diagonal. For a group, this is the obstruction showing that a map whose values around a loop do
not multiply to `1` is not homotopic to a constant map.

## Main declarations

* `CategoryTheory.nerve.edgeElem`: the element of `M` represented by an edge.
* `CategoryTheory.nerve.edgeElem_app_δ_one`: the long edge of a `2`-simplex is the product of its
  short edges.
* `CategoryTheory.nerve.edgeElem_map`, `CategoryTheory.nerve.edgeElem_const_app`: degenerate
  edges, such as the edges of a constant map, represent `1`.
* `CategoryTheory.nerve.edgeElem_homotopy`: the relation between the vertical edges of a homotopy
  over the endpoints of an edge.
-/

public section

open CategoryTheory MonoidalCategory Simplicial SSet

universe u

namespace CategoryTheory.nerve

variable {M : Type u} [Monoid M]

/-- The element of `M` represented by an edge of the nerve of `M`, viewed as a category with one
object. -/
abbrev edgeElem (x : (nerve (SingleObj M)) _⦋1⦌) : M := x.hom

/-- For a map `f` to the nerve of `M`, the long edge of the image of a `2`-simplex is the product
of its two short edges. -/
lemma edgeElem_app_δ_one {K : SSet.{u}} (f : K ⟶ nerve (SingleObj M)) (x : K _⦋2⦌) :
    edgeElem (f.app _ (K.δ 1 x)) = edgeElem (f.app _ (K.δ 0 x)) * edgeElem (f.app _ (K.δ 2 x)) := by
  simp only [δ_naturality_apply]
  obtain ⟨_, _, _, a, b, hx⟩ := ComposableArrows.mk₂_surjective (f.app _ x)
  rw [hx, δ₁_mk₂_eq, δ₀_mk₂_eq, δ₂_mk₂_eq]
  exact SingleObj.comp_as_mul _ a b

/-- The degenerate edges at a vertex of the nerve of `M` represent `1`. -/
@[simp]
lemma edgeElem_map (z : (nerve (SingleObj M)) _⦋0⦌) (φ : ⦋1⦌ ⟶ ⦋0⦌) :
    edgeElem ((nerve (SingleObj M)).map φ.op z) = 1 := by
  obtain rfl := Subsingleton.elim (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) φ
  exact (congrArg z.map (Subsingleton.elim _ _)).trans (z.map_id 0)

/-- The edges of a constant map to the nerve of `M` represent `1`. -/
lemma edgeElem_const_app {K : SSet.{u}} (z : (nerve (SingleObj M)) _⦋0⦌) (x : K _⦋1⦌) :
    edgeElem ((const z : K ⟶ _).app _ x) = 1 :=
  edgeElem_map z _

/-- Let `H` be a homotopy from `f` to `g`, with values in the nerve of `M`. Over an edge `e` of `K`
from `x₀ = K.δ 1 e` to `x₁ = K.δ 0 e`, the square `e × Δ[1]` is the union of two triangles with a
common diagonal, which shows that the vertical edges over the endpoints of `e` satisfy
`H ({x₁} × Δ[1]) * f e = g e * H ({x₀} × Δ[1])`. -/
lemma edgeElem_homotopy {K : SSet.{u}} {f g : K ⟶ nerve (SingleObj M)} (H : SSet.Homotopy f g)
    (e : K _⦋1⦌) :
    edgeElem (H.h.app _ (verticalEdge (K.δ 0 e))) * edgeElem (f.app _ e) =
      edgeElem (g.app _ e) * edgeElem (H.h.app _ (verticalEdge (K.δ 1 e))) := by
  -- Edges of the nerve of `M` are the elements of `M` they represent.
  have hE {x y : (nerve (SingleObj M)) _⦋0⦌} (e : (nerve (SingleObj M)).Edge x y) :
      homEquiv e = edgeElem e.edge :=
    (homEquiv_apply e).trans (by simp)
  -- The vertical edges of the combinatorial homotopy are the images of the vertical edges.
  have hv (v : K _⦋0⦌) : (Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy v).edge =
      H.h.app _ (verticalEdge v) := by
    refine congrArg (H.h.app _) (Prod.ext ?_ ?_)
    · exact (congrArg (fun φ : ⦋1⦌ ⟶ ⦋0⦌ ↦ K.map φ.op v) (Subsingleton.elim _ _)).trans
        (verticalEdge_fst v).symm
    · rw [verticalEdge_snd]
      exact (prodStdSimplex₁.nonDegenerateEquiv_snd 0).trans (by decide)
  -- The two triangles of the square `e × Δ[1]`, with their common diagonal.
  have h₁ := homEquiv_comp
    (Edge.CompStruct.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy (Edge.mk' e))
  have h₂ := homEquiv_comp
    (Edge.CompStruct.ofSimplicialObjectHomotopy' H.toSimplicialObjectHomotopy (Edge.mk' e))
  rw [hE, hE, hE, hv, SingleObj.comp_as_mul] at h₁ h₂
  rw [← h₁] at h₂
  exact h₂.symm

end CategoryTheory.nerve
