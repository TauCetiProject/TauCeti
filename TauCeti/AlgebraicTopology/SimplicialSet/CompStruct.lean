/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct

/-!
# Composition triangles: initial vertex and extensionality

A composition triangle `SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂` in a simplicial set `X` is a
`2`-simplex of `X` with edges `e₀₁ : x₀ ⟶ x₁`, `e₁₂ : x₁ ⟶ x₂` and `e₀₂ : x₀ ⟶ x₂`. This file
supplements Mathlib's API for them: the initial vertex of the underlying `2`-simplex is `x₀`, and a
composition triangle together with its first and long edges is determined by its `2`-simplex.

## Main results

* `SSet.Edge.CompStruct.map_const_zero_simplex`: the vertex `0` of a composition triangle from
  `x₀` is `x₀`.
* `SSet.Edge.CompStruct.sigma_ext`: two composition triangles with the same last edge are equal,
  together with their first and long edges, when their `2`-simplices are.
-/

public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet.Edge.CompStruct

variable {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
  {e₀₂ : Edge x₀ x₂}

/-- The vertex `0` of a composition triangle from `x₀` is `x₀`. -/
lemma map_const_zero_simplex (c : CompStruct e₀₁ e₁₂ e₀₂) :
    X.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0).op c.simplex = x₀ := by
  calc X.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0).op c.simplex = X.δ 1 (X.δ 2 c.simplex) := by
        rw [SimplicialObject.δ, SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp]
        congr 3
        ext a
        fin_cases a
        rfl
    _ = x₀ := by rw [c.d₂, e₀₁.src_eq]

/-- Two composition triangles with last edge `e₁₂` are equal, together with their first and long
edges, when their `2`-simplices are. -/
lemma sigma_ext {e₀₁' : Edge x₀ x₁} {e₀₂' : Edge x₀ x₂} {c : CompStruct e₀₁ e₁₂ e₀₂}
    {c' : CompStruct e₀₁' e₁₂ e₀₂'} (e : c.simplex = c'.simplex) :
    (⟨e₀₁, e₀₂, c⟩ : Σ (f : Edge x₀ x₁) (h : Edge x₀ x₂), CompStruct f e₁₂ h) =
      ⟨e₀₁', e₀₂', c'⟩ := by
  obtain rfl : e₀₁ = e₀₁' := Edge.ext (by rw [← c.d₂, ← c'.d₂, e])
  obtain rfl : e₀₂ = e₀₂' := Edge.ext (by rw [← c.d₁, ← c'.d₁, e])
  obtain rfl : c = c' := ext e
  rfl

end SSet.Edge.CompStruct
