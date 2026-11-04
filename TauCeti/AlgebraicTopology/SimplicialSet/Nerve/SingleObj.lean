/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
obtained by cutting the square `e × Δ[1]` into two triangles along its diagonal. For a group,
this is the obstruction showing that a map whose values around a loop do not multiply to `1` is
not homotopic to a constant map.

## Main declarations

* `CategoryTheory.nerve.edgeElem`: the element of `M` represented by an edge.
* `CategoryTheory.nerve.edgeElem_app_δ_one`: the long edge of a `2`-simplex is the product of its
  short edges.
* `CategoryTheory.nerve.edgeElem_const_app`: the edges of a constant map represent `1`.
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

/-- The edges of a constant map to the nerve of `M` represent `1`. -/
lemma edgeElem_const_app {K : SSet.{u}} (z : (nerve (SingleObj M)) _⦋0⦌) (x : K _⦋1⦌) :
    edgeElem ((const z : K ⟶ _).app _ x) = 1 :=
  (congrArg z.map (Subsingleton.elim _ _)).trans (z.map_id 0)

/-- Let `H` be a homotopy from `f` to `g`, with values in the nerve of `M`. Over an edge `e` of `K`
from `x₀ = K.δ 1 e` to `x₁ = K.δ 0 e`, the square `e × Δ[1]` is the union of two triangles with a
common diagonal, which shows that the vertical edges over the endpoints of `e` satisfy
`H ({x₁} × Δ[1]) * f e = g e * H ({x₀} × Δ[1])`. -/
lemma edgeElem_homotopy {K : SSet.{u}} {f g : K ⟶ nerve (SingleObj M)} (H : SSet.Homotopy f g)
    (e : K _⦋1⦌) :
    edgeElem (H.h.app _ (verticalEdge (K.δ 0 e))) * edgeElem (f.app _ e) =
      edgeElem (g.app _ e) * edgeElem (H.h.app _ (verticalEdge (K.δ 1 e))) := by
  let y : Δ[1] _⦋1⦌ := stdSimplex.edge 1 0 1 (by decide)
  -- The triangles with vertices `(x₀, 0), (x₁, 0), (x₁, 1)` and `(x₀, 0), (x₀, 1), (x₁, 1)`.
  let P : (K ⊗ Δ[1]) _⦋2⦌ := (K.σ 1 e, Δ[1].σ 0 y)
  let Q : (K ⊗ Δ[1]) _⦋2⦌ := (K.σ 0 e, Δ[1].σ 1 y)
  have hP := edgeElem_app_δ_one H.h P
  have hQ := edgeElem_app_δ_one H.h Q
  -- The ends of the cylinder: `(ι₀ ≫ H.h).app _ e` is `H.h.app _ (ι₀.app _ e)` by definition.
  have hb : H.h.app _ (ι₀.app _ e) = f.app _ e := ConcreteCategory.congr_hom (congr_app H.h₀ _) e
  have ht : H.h.app _ (ι₁.app _ e) = g.app _ e := ConcreteCategory.congr_hom (congr_app H.h₁ _) e
  have hPQ : (K ⊗ Δ[1]).δ 1 P = (K ⊗ Δ[1]).δ 1 Q :=
    Prod.ext ((δ_comp_σ_self_apply 1 e).trans (δ_comp_σ_succ_apply 0 e).symm)
      ((δ_comp_σ_succ_apply 0 y).trans (δ_comp_σ_self_apply 1 y).symm)
  have hP₀ : (K ⊗ Δ[1]).δ 0 P = verticalEdge (K.δ 0 e) :=
    Prod.ext (δ_comp_σ_of_le_apply (i := 0) (j := 0) le_rfl e) (δ_comp_σ_self_apply 0 y)
  have hP₂ : (K ⊗ Δ[1]).δ 2 P = ι₀.app _ e :=
    Prod.ext (δ_comp_σ_succ_apply 1 e) (stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl)
  have hQ₀ : (K ⊗ Δ[1]).δ 0 Q = ι₁.app _ e :=
    Prod.ext (δ_comp_σ_self_apply 0 e) (stdSimplex.ext _ _ fun i ↦ by fin_cases i <;> rfl)
  have hQ₂ : (K ⊗ Δ[1]).δ 2 Q = verticalEdge (K.δ 1 e) :=
    Prod.ext (δ_comp_σ_of_gt_apply (i := 1) (j := 0) (by decide) e) (δ_comp_σ_succ_apply 1 y)
  rw [hPQ, hP₀, hP₂, hb] at hP
  rw [hQ₀, hQ₂, ht] at hQ
  rw [← hP, hQ]

end CategoryTheory.nerve
