/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# The weak topology and the canonical bidual map

The canonical map from a seminormed space with its weak topology to its weak-star bidual is
inducing: the weak topology is the topology pulled back from the weak-star bidual. This holds
without assuming that the seminorm separates points.

When the scalar field is proper, a norm-bounded set has weakly compact closure if the
weak-star closure of its bidual image lies in the range of the canonical map. This extends Mathlib's
`NormedSpace.isCompact_closure_of_isBounded` to seminormed spaces, using the inducing property
to transfer Banach–Alaoglu compactness back to the weak topology.
-/

public section

open Bornology Set Topology

namespace NormedSpace

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The canonical bidual map induces the weak topology from the weak-star topology,
including when the seminorm on the source does not separate points. -/
theorem isInducing_inclusionInDoubleDualWeak :
    IsInducing (inclusionInDoubleDualWeak 𝕜 E) where
  -- Both topologies are induced by evaluation against the continuous dual.
  eq_induced := Eq.symm induced_compose

variable [ProperSpace 𝕜]

/-- A norm-bounded set in a seminormed space has weakly compact closure if the weak-star
closure of its canonical bidual image lies in the range of the canonical map. -/
theorem isCompact_closure_weakSpace_of_isBounded (s : Set (WeakSpace 𝕜 E))
    (hs : IsBounded ((toWeakSpace 𝕜 E) ⁻¹' s))
    (hrange : closure (inclusionInDoubleDualWeak 𝕜 E '' s) ⊆
      range (inclusionInDoubleDualWeak 𝕜 E)) :
    IsCompact (closure s) := by
  rw [(isInducing_inclusionInDoubleDualWeak 𝕜 E).closure_eq_preimage_closure_image]
  apply (isInducing_inclusionInDoubleDualWeak 𝕜 E).isCompact_preimage' _ hrange
  -- The bundled Lipschitz bound on the bidual map exceeds the default elaboration budget
  -- for these seminormed hypotheses. A direct ball bound avoids that instance comparison.
  apply WeakDual.isCompact_of_bounded_of_closed _ isClosed_closure
  apply WeakDual.isBounded_closure
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp hs
  refine (WeakDual.isBounded_closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) r).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_preimage, inclusionInDoubleDualWeak_apply, StrongDual.toStrongDual_toWeakDual,
    mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))]
  exact (double_dual_bound 𝕜 E _).trans (hr _ (by simpa using hx))

end NormedSpace
