/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Continuous sums along local homeomorphisms

Summing a continuous function along the fibers of a local homeomorphism preserves continuity
when its support is proper over the base. This is the pushforward operation used in averaging
continuous cochains on an étale groupoid. The support condition is essential: it prevents
nonzero summands from escaping to infinity above a convergent sequence in the base.
-/

public section

open Topology

namespace IsLocalHomeomorph

/-- A continuous function with support proper over a Hausdorff weakly locally compact base
has a continuous sum along the fibers of a local homeomorphism. -/
theorem continuous_finsum_mem_preimage_singleton
    {E B M : Type*} [TopologicalSpace E] [TopologicalSpace B] [T2Space E] [T2Space B]
    [WeaklyLocallyCompactSpace B] [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    {p : E → B} (hp : IsLocalHomeomorph p) {f : E → M} (hf : Continuous f)
    (hproper : ∀ ⦃K : Set B⦄, IsCompact K → IsCompact (p ⁻¹' K ∩ tsupport f)) :
    Continuous fun b ↦ ∑ᶠ e ∈ p ⁻¹' {b}, f e := by
  classical
  refine continuous_iff_continuousAt.2 fun b ↦ ?_
  obtain ⟨F, hF, hev⟩ := hp.eventually_finsum_mem_preimage_singleton_eq_sum hproper
    (σ := fun e ↦ hp.localInverseAt e)
    (fun e ↦ (hp.localInverseAt e).continuousAt hp.apply_self_mem_localInverseAt_source)
    (fun e ↦ hp.localInverseAt_apply_self)
    (fun e ↦ by
      filter_upwards [(hp.localInverseAt e).open_source.mem_nhds
        hp.apply_self_mem_localInverseAt_source] with b hb
      exact hp.apply_localInverseAt_of_mem hb) b
  have hcont : ContinuousAt (fun b ↦ ∑ e ∈ F, f (hp.localInverseAt e b)) b := by
    apply tendsto_finsetSum
    intro e he
    rw [← hF e he]
    exact hf.continuousAt.comp
      ((hp.localInverseAt e).continuousAt hp.apply_self_mem_localInverseAt_source)
  exact hcont.congr_of_eventuallyEq hev

end IsLocalHomeomorph
