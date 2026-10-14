/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TopRep.Subquotients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Subrepresentations and quotients of smooth discrete representations

An invariant submodule of a smooth discrete representation inherits its topology and action, and
the quotient by an invariant submodule carries the quotient topology and descended action. Both
remain smooth discrete representations. These constructions supply the subgroup and quotient
coefficient modules used with continuous cohomology.
-/

public section

namespace TauCeti

open TopRep

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {G : Type*} [Monoid G] [TopologicalSpace G] {X : TopRep R G}

/-- Smoothness is inherited by the representation on an invariant submodule. -/
theorem IsSmoothDiscrete.subrepresentation (hX : IsSmoothDiscrete R X)
    (W : Submodule R X.V) (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    IsSmoothDiscrete R (TopRep.subrepresentation X W hW) :=
  hX.of_injective (TopRep.subrepresentationι X W hW)
    (TopRep.subrepresentationι_injective X W hW)

/-- Over a group with separately continuous multiplication, the quotient of a smooth discrete
representation by an invariant submodule is smooth discrete with its quotient topology. -/
theorem IsSmoothDiscrete.quotient {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] {X : TopRep R G}
    (hX : IsSmoothDiscrete R X) (W : Submodule R X.V)
    (hW : ∀ g x, x ∈ W → X.ρ g x ∈ W) :
    IsSmoothDiscrete R (TopRep.quotient X W hW) := by
  have : DiscreteTopology X.V := hX.discreteTopology
  have : DiscreteTopology (X.V ⧸ W) :=
    QuotientAddGroup.discreteTopology (N := W.toAddSubgroup) (isOpen_discrete _)
  exact hX.of_surjective (TopRep.quotientπ X W hW) (TopRep.quotientπ_surjective X W hW)

end TauCeti
