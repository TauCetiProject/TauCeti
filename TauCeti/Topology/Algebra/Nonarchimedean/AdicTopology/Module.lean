/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.Topology.Algebra.Nonarchimedean.SubmodulesBasis

/-!
# Neighbourhood bases for adic module topologies

The submodules `I^n M` form a neighbourhood basis of zero for `Ideal.adicModuleTopology`.
This module exposes that basis without requiring clients to unfold the topology, paralleling
Mathlib's `Ideal.hasBasis_nhds_zero_adic` for the ring itself.
-/

public section

open Filter Topology

namespace Ideal

/-- For the `I`-adic topology on a module `M`, the submodules `I^n M` form a neighbourhood
basis of zero. No finiteness assumption on the module or ideal is needed. -/
theorem hasBasis_nhds_zero_adicModuleTopology {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    (@nhds M (I.adicModuleTopology M) 0).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((I ^ n • ⊤ : Submodule R M) : Set M)) := by
  let := I.adicTopology
  -- Unfolding `adicModuleTopology` and `SubmodulesBasis.topology` gives the same
  -- `ModuleFilterBasis.topology` for the power-submodule family.
  exact (I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis M)).hasBasis_nhds_zero

end Ideal
