/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BrauerNesbitt
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic

/-!
# The Brauer–Nesbitt theorem for continuous representations

For jointly continuous finite-dimensional semisimple representations on modules with their module
topologies, over an algebraically closed topological field, the equivalence given by Brauer–Nesbitt
(`Representation.nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation`) is automatically a
homeomorphism (`TauCeti.ContinuousRep.nonempty_iso_of_charpoly_eq`).

## Main results

* `TauCeti.ContinuousRep.nonempty_iso_of_charpoly_eq`: Brauer–Nesbitt for continuous
  representations.
-/

public section

namespace TauCeti.ContinuousRep

variable {Γ k V W : Type*} [Monoid Γ] [TopologicalSpace Γ] [Field k] [IsAlgClosed k]
  [TopologicalSpace k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [TopologicalSpace V]
  [IsModuleTopology k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [TopologicalSpace W] [IsModuleTopology k W]

/-- **Brauer–Nesbitt for continuous representations.** Over an algebraically closed topological
field, two jointly continuous finite-dimensional semisimple representations with their module
topologies and the same characteristic polynomial at every element are isomorphic as continuous
representations. -/
theorem nonempty_iso_of_charpoly_eq (ρ : ContinuousRep Γ k V) (σ : ContinuousRep Γ k W)
    [ρ.toRepresentation.IsSemisimpleRepresentation] [σ.toRepresentation.IsSemisimpleRepresentation]
    (h : ∀ g, (ρ g).charpoly = (σ g).charpoly) : Nonempty (Iso ρ σ) :=
  (Representation.nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation _ _ h).map
    Iso.ofEquiv

end TauCeti.ContinuousRep
