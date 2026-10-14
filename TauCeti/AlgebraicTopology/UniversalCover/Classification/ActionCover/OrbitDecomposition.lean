/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover.Basic
public import TauCeti.Topology.Covering.BalancedProduct.OrbitDecomposition

/-!
# Associated covers decompose over label orbits

For a discrete `π₁(X, x)`-set `A`, `BalancedProduct.orbitHomeomorph` gives the homeomorphism

`(Σ o : MulAction.orbitRel.Quotient (FundamentalGroup X x) A, ActionCover x o.orbit)
  ≃ₜ ActionCover x A`.

This file identifies its projection to `X`: on each summand it is the associated-cover
projection for that orbit. Thus the disjoint-union comparison is over `X`. Each label orbit
is nonempty and transitive, without requiring the whole action to be transitive. Empty label
sets give empty disjoint unions.
-/

public section

namespace TauCeti.UniversalCover

universe u

variable {X A : Type u} [TopologicalSpace X] (x : X)
  [MulAction (FundamentalGroup X x) A] [TopologicalSpace A] [DiscreteTopology A]

/-- The orbitwise disjoint-union comparison of associated covers commutes with projection
onto the base. -/
@[simp]
theorem actionCoverProj_orbitHomeomorph
    (o : MulAction.orbitRel.Quotient (FundamentalGroup X x) A)
    (z : ActionCover x o.orbit) :
    actionCoverProj x A (BalancedProduct.orbitHomeomorph ⟨o, z⟩) =
      actionCoverProj x o.orbit z := by
  induction z using Quotient.inductionOn with
  | h p =>
    obtain ⟨e, a⟩ := p
    rw [BalancedProduct.orbitHomeomorph_mk, actionCoverProj_mk, actionCoverProj_mk]

end TauCeti.UniversalCover
