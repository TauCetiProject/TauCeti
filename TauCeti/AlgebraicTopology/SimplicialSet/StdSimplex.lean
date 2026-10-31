/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

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
* `SSet.stdSimplex.isConnected`: standard simplices are connected.
* `SSet.stdSimplex.contraction`: the homotopy from the constant map at the initial vertex of
  `Δ[n]` to its identity.
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

/-- Standard simplices are connected: the edge from `0` to `k` joins every vertex `k` to the
initial vertex. -/
instance isConnected (n : ℕ) : (Δ[n] : SSet.{u}).IsConnected where
  allEq := π₀.rec fun x ↦ π₀.rec fun y ↦ by
    suffices h : ∀ k : Fin (n + 1), π₀.mk (obj₀Equiv.symm k) = π₀.mk (obj₀Equiv.symm 0) by
      rw [← obj₀Equiv.symm_apply_apply x, ← obj₀Equiv.symm_apply_apply y]
      exact (h _).trans (h _).symm
    intro k
    exact (π₀.sound (Edge.mk (x₀ := obj₀Equiv.symm 0) (x₁ := obj₀Equiv.symm k)
      (edge.{u} n 0 k (Fin.zero_le k)) (ext _ _ fun i ↦ by fin_cases i; rfl)
      (ext _ _ fun i ↦ by fin_cases i; rfl))).symm

/-- The contraction of the standard simplex `Δ[n]` onto its initial vertex: the homotopy from the
constant map at `0` to the identity which is `0` over the vertex `0` of `Δ[1]` and the identity
over the vertex `1`. -/
noncomputable def contraction (n : ℕ) :
    Homotopy (SSet.const (obj₀Equiv.symm 0)) (𝟙 Δ[n]) where
  h :=
    { app m := ↾fun p ↦ objMk
        ⟨fun k ↦ if asOrderHom p.2 k = 0 then 0 else asOrderHom p.1 k,
          fun k l hkl ↦ by
            dsimp only
            split_ifs with hk hl hl
            · exact le_rfl
            · exact Fin.zero_le _
            · exact absurd (Fin.le_zero_iff.1 (hl ▸ (asOrderHom p.2).monotone hkl)) hk
            · exact (asOrderHom p.1).monotone hkl⟩
      -- The formula is computed vertexwise, so it commutes with reindexing by definition.
      naturality m m' φ := by
        ext p
        rfl }
  -- Over the vertex `0` of `Δ[1]` every vertex is sent to `0`, and over `1` it is unchanged.
  h₀ := by
    ext ⟨⟨m⟩⟩ p
    rfl
  h₁ := by
    ext ⟨⟨m⟩⟩ p
    rfl
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

end SSet.stdSimplex
