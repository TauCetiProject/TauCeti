/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

/-!
# Basic lemmas on the fundamental groupoid of a simplicial set

Two edges with the same underlying `1`-simplex induce morphisms in the fundamental groupoid that
agree up to `eqToHom` on their endpoints
(`SSet.Truncated.FundamentalGroupoid.homMk_comp_eqToHom`,
`SSet.FundamentalGroupoid.homMk_comp_eqToHom`).
-/

public section

open CategoryTheory Simplicial SimplicialObject.Truncated

universe u

namespace SSet

namespace Truncated.FundamentalGroupoid

/-- Two edges of a `2`-truncated simplicial set with the same underlying `1`-simplex induce
morphisms in `Truncated.FundamentalGroupoid X` that agree up to `eqToHom` on their endpoints. -/
lemma homMk_comp_eqToHom {X : SSet.Truncated.{u} 2} {x₁ y₁ x₂ y₂ : X _⦋0⦌₂}
    (e₁ : X.Edge x₁ y₁) (e₂ : X.Edge x₂ y₂) (he : e₁.edge = e₂.edge)
    (hx : mk x₁ = mk x₂ := congrArg mk (by rw [← e₁.src_eq, ← e₂.src_eq, he]))
    (hy : mk y₁ = mk y₂ := congrArg mk (by rw [← e₁.tgt_eq, ← e₂.tgt_eq, he])) :
    homMk e₁ ≫ eqToHom hy = eqToHom hx ≫ homMk e₂ := by
  obtain rfl : x₁ = x₂ := by rw [← e₁.src_eq, ← e₂.src_eq, he]
  obtain rfl : y₁ = y₂ := by rw [← e₁.tgt_eq, ← e₂.tgt_eq, he]
  obtain rfl : e₁ = e₂ := Edge.ext he
  simp

end Truncated.FundamentalGroupoid

namespace FundamentalGroupoid

/-- Two edges of a simplicial set with the same underlying `1`-simplex induce morphisms in
`SSet.FundamentalGroupoid X` that agree up to `eqToHom` on their endpoints. -/
lemma homMk_comp_eqToHom {X : SSet.{u}} {x₁ y₁ x₂ y₂ : X _⦋0⦌}
    (e₁ : X.Edge x₁ y₁) (e₂ : X.Edge x₂ y₂) (he : e₁.edge = e₂.edge)
    (hx : mk x₁ = mk x₂ := congrArg mk (by rw [← e₁.src_eq, ← e₂.src_eq, he]))
    (hy : mk y₁ = mk y₂ := congrArg mk (by rw [← e₁.tgt_eq, ← e₂.tgt_eq, he])) :
    homMk e₁ ≫ eqToHom hy = eqToHom hx ≫ homMk e₂ :=
  Truncated.FundamentalGroupoid.homMk_comp_eqToHom e₁ e₂ he hx hy

end FundamentalGroupoid

end SSet
