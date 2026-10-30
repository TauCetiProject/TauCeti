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
* `SSet.stdSimplex.quasicategory`: standard simplices are quasicategories.
-/

public section

open CategoryTheory Simplicial

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

/-- Standard simplices are quasicategories, being isomorphic to nerves of linear orders. -/
instance quasicategory (n : ℕ) : Quasicategory (Δ[n] : SSet.{u}) where
  hornFilling' _ _ σ₀ h₀ hₙ := by
    obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling' (σ₀ ≫ (isoNerve n).hom) h₀ hₙ
    exact ⟨σ ≫ (isoNerve n).inv, by rw [← Category.assoc, ← hσ]; simp⟩

end SSet.stdSimplex
