/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

import TauCeti.Order.Filter.Pi
import TauCeti.RingTheory.Ideal.Operations

/-!
# Adic topologies and finite module presentations

For a finite module over an `I`-adic ring, the `I`-adic topology is the natural module
topology. Consequently it is the quotient topology from any finite free presentation, with
the product topology on the source. This description makes the topology independent of the
chosen generators and allows the general `IsModuleTopology` API to be used for finite adic
modules. Neither noetherianity nor completeness nor finite generation of `I` is required.

The argument uses Mathlib's open quotient theorem for natural module topologies and the
finite-sum description of ideal multiples of a span. It parallels the spanning-lattice
argument in `TauCeti.RingTheory.Huber.ModuleTopology.Basic`, but applies to arbitrary ideals,
which need not define Huber rings.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0,
  §§7.2–7.3, especially 7.2.10 and 7.3.5–7.3.6.
-/

public section

open Filter Topology

namespace IsAdic

variable {R M : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R}
  [AddCommGroup M] [Module R M]

/-- In the natural topology on a finite module over an `I`-adic ring, the submodules
`I^n M` form a neighbourhood basis of zero. -/
theorem hasBasis_nhds_zero_pow_smul (hI : IsAdic I)
    [TopologicalSpace M] [IsModuleTopology R M] [Module.Finite R M] :
    (𝓝 (0 : M)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ ((I ^ n • ⊤ : Submodule R M) : Set M) := by
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  obtain ⟨k, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hsurj : Function.Surjective (Fintype.linearCombination R v) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination _ _).mp hv
  have hcube : (𝓝 (0 : Fin k → R)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ Set.univ.pi fun _ ↦ ((I ^ n : Ideal R) : Set R)) := by
    rw [nhds_pi]
    exact hI.hasBasis_nhds_zero.pi_self_of_finite
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hsurj
  rw [← map_zero (Fintype.linearCombination R v), ← hq.map_nhds_eq]
  simpa only [Ideal.image_fintypeLinearCombination_pi, hv] using
    hcube.map (Fintype.linearCombination R v)

/-- The adic topology on a finite module is its natural module topology. Thus the general
`IsModuleTopology` continuity and quotient-map theorems apply to finite adic modules. -/
theorem adicModuleTopology_eq_moduleTopology (hI : IsAdic I) [Module.Finite R M] :
    I.adicModuleTopology M = moduleTopology R M := by
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  let := moduleTopology R M
  have := IsModuleTopology.isTopologicalAddGroup R M
  apply IsTopologicalAddGroup.ext
  · infer_instance
  · infer_instance
  exact (I.hasBasis_nhds_zero_adicModuleTopology M).eq_of_same_basis
    (hI.hasBasis_nhds_zero_pow_smul (M := M))

/-- Any surjection from a finite free module presents the adic topology on its target as
an actual quotient of the product topology on the source. -/
theorem adicModuleTopology_eq_coinduced (hI : IsAdic I) {ι : Type*} [Finite ι]
    (f : (ι → R) →ₗ[R] M) (hf : Function.Surjective f) :
    I.adicModuleTopology M = TopologicalSpace.coinduced f inferInstance := by
  have : IsTopologicalRing R := hI ▸ I.nonarchimedean.toIsTopologicalRing
  have : Module.Finite R M := Module.Finite.of_surjective f hf
  rw [hI.adicModuleTopology_eq_moduleTopology]
  exact ModuleTopology.eq_coinduced_of_surjective hf

end IsAdic
