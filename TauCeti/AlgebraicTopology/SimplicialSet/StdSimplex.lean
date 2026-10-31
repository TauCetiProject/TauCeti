/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
# Complements on standard simplices

A map of simplicial sets `q : Δ[m] ⟶ Δ[n]` is determined by its vertex map, the `m`-simplex
`yonedaEquiv q` of `Δ[n]`, and it acts on the simplices of `Δ[m]` by composing with it. Standard
simplices are nerves of finite linear orders, hence quasicategories. These facts let one handle
maps from horns and simplices to `Δ[n]`, for instance to `Δ[1]` when splitting a simplex into
an initial and a final segment.

## Main results

* `SSet.stdSimplex.hom_app_apply`: the vertices of the image of a simplex under a map of standard
  simplices.
* `SSet.stdSimplex.const_app_apply`: the constant map at a vertex of `Δ[n]` sends every simplex
  to the constant simplex at that vertex.
* `SSet.stdSimplex.subcomplex_hom_app_apply`: the vertices of the image of a simplex under a map
  from a subcomplex of a standard simplex to a standard simplex.
* `SSet.stdSimplex.quasicategory`: standard simplices are quasicategories.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet.stdSimplex

/-- A map of standard simplices `q : Δ[m] ⟶ Δ[n]` sends a simplex `x` of `Δ[m]` to the simplex
whose `j`-th vertex is the image of the `j`-th vertex of `x` under the vertex map of `q`. -/
lemma hom_app_apply {m n d : ℕ} (q : (Δ[m] : SSet.{u}) ⟶ Δ[n]) (x : Δ[m] _⦋d⦌)
    (j : Fin (d + 1)) : q.app _ x j = yonedaEquiv q (x j) := by
  conv_lhs => rw [← yonedaEquiv.symm_apply_apply q]
  -- The map `yonedaEquiv.symm s` acts on `x` by precomposing `s` with `x`.
  rfl

/-- The constant map at the vertex `e` of `Δ[n]` sends every simplex to a simplex all of whose
vertices are `e`. -/
lemma const_app_apply {X : SSet.{u}} {n d : ℕ} (e : Fin (n + 1)) (x : X _⦋d⦌)
    (j : Fin (d + 1)) : (SSet.const (stdSimplex.const n e _) : X ⟶ Δ[n]).app _ x j = e :=
  (rfl)

/-- The top simplex of `Δ[n]`, corresponding to its identity map, has `j` as its `j`-th vertex. -/
@[simp]
lemma yonedaEquiv_id_apply (n : ℕ) (j : Fin (n + 1)) : yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) j = j :=
  (rfl)

/-- The constant simplex at the vertex `k` of `Δ[n]` has all its vertices equal to `k`. -/
@[simp]
lemma const_apply (n : ℕ) (k : Fin (n + 1)) (d : ℕ) (t : Fin (d + 1)) :
    stdSimplex.const n k (op ⦋d⦌) t = k :=
  (rfl)

/-- The vertices of the image of a simplex `x` of `Δ[n]` under a simplicial operator `f` are the
vertices of `x` indexed through `f`. -/
@[simp]
lemma obj_map_apply {n d d' : ℕ} (f : op ⦋d⦌ ⟶ op ⦋d'⦌) (x : Δ[n] _⦋d⦌) (j : Fin (d' + 1)) :
    Δ[n].map f x j = x (f.unop.toOrderHom j) :=
  (rfl)

/-- The edge of `Δ[n]` from `a` to `b` starts at `a`. -/
@[simp]
lemma edge_apply_zero (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) : edge n a b hab 0 = a :=
  (rfl)

/-- The edge of `Δ[n]` from `a` to `b` ends at `b`. -/
@[simp]
lemma edge_apply_one (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) : edge n a b hab 1 = b :=
  (rfl)

/-- A map `g` from a subcomplex `S` of `Δ[d]` to `Δ[n]` acts on vertices: the `t`-th vertex of the
image of a simplex `x` of `S` is the image of the `t`-th vertex of `x`. -/
lemma subcomplex_hom_app_apply {d n a : ℕ} {S : (Δ[d] : SSet.{u}).Subcomplex}
    (g : (S : SSet.{u}) ⟶ Δ[n]) (x : Δ[d] _⦋a⦌) (hx : x ∈ S.obj _) (t : Fin (a + 1))
    (ht : obj₀Equiv.symm (x t) ∈ S.obj (op ⦋0⦌)) :
    g.app _ ⟨x, hx⟩ t = g.app _ ⟨obj₀Equiv.symm (x t), ht⟩ 0 := by
  have h : (⟨obj₀Equiv.symm (x t), ht⟩ : S.obj (op ⦋0⦌)) =
      (S : SSet.{u}).map (SimplexCategory.const ⦋0⦌ ⦋a⦌ t).op ⟨x, hx⟩ :=
    Subtype.ext (stdSimplex.ext _ _ fun _ ↦ by simp)
  rw [h, NatTrans.naturality_apply, obj_map_apply]
  simp

/-- Standard simplices are quasicategories, being isomorphic to nerves of linear orders. -/
instance quasicategory (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) where
  hornFilling' _ _ σ₀ h₀ hₙ := by
    obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling' (σ₀ ≫ (isoNerve n).hom) h₀ hₙ
    exact ⟨σ ≫ (isoNerve n).inv, by rw [← Category.assoc, ← hσ]; simp⟩

end SSet.stdSimplex
