/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange.NoetherDeuring
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic

/-!
# Noether–Deuring for continuous representations

Two jointly continuous finite-dimensional semisimple representations over a topological field,
with their module topologies, whose underlying representations become equivalent after extending
scalars are isomorphic as continuous representations. This is the algebraic
`Representation.nonempty_equiv_of_nonempty_equiv_baseChange`, transported along
`TauCeti.ContinuousRep.Iso.ofEquiv`.

## Main results

* `TauCeti.ContinuousRep.nonempty_iso_of_nonempty_equiv_baseChange`: Noether–Deuring for
  continuous representations.
-/

public section

namespace TauCeti.ContinuousRep

variable {Γ K L V W : Type*} [Monoid Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
  [CommRing L] [Nontrivial L] [Algebra K L]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
  [IsModuleTopology K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [TopologicalSpace W] [IsModuleTopology K W]

/-- **Noether–Deuring for continuous representations.** Two jointly continuous finite-dimensional
semisimple representations over a topological field `K`, with their module topologies, whose
underlying representations become equivalent after extending scalars to a nonzero commutative
`K`-algebra, are isomorphic as continuous representations. -/
theorem nonempty_iso_of_nonempty_equiv_baseChange (ρ : ContinuousRep Γ K V)
    (σ : ContinuousRep Γ K W) [ρ.toRepresentation.IsSemisimpleRepresentation]
    [σ.toRepresentation.IsSemisimpleRepresentation]
    (h : Nonempty ((ρ.toRepresentation.baseChange L).Equiv (σ.toRepresentation.baseChange L))) :
    Nonempty (Iso ρ σ) :=
  (Representation.nonempty_equiv_of_nonempty_equiv_baseChange _ _ h).map Iso.ofEquiv

end TauCeti.ContinuousRep
