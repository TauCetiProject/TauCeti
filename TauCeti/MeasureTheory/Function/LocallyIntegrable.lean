/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Separation.Regular

/-!
# Local integrability on relatively compact open subdomains

Local integrability on an open set is equivalent to local integrability on every open subdomain
whose closure is compact and contained in the original set. This form is useful when a proof can be
localized to relatively compact subdomains.

## Attribution

The characterization adapts Mathlib's `locallyIntegrableOn_iff` and
`LocallyIntegrableOn.integrableOn_compact_subset`, combined with
`exists_open_between_and_isCompact_closure` to reach relatively compact open subdomains.
-/

public section

open MeasureTheory Set TopologicalSpace

namespace TauCeti

variable {X ε : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [TopologicalSpace ε] [ContinuousENorm ε] [PseudoMetrizableSpace ε]
  [LocallyCompactSpace X] [RegularSpace X]
  {μ : Measure X} {f : X → ε} {Ω : Opens X}

/-- A function is locally integrable on an open set exactly when it is locally integrable on every
open subdomain with compact closure contained in that set. -/
theorem locallyIntegrableOn_iff_forall_isCompact_closure :
    LocallyIntegrableOn f Ω μ ↔
      ∀ V : Opens X, IsCompact (closure (V : Set X)) → closure (V : Set X) ⊆ Ω →
        LocallyIntegrableOn f V μ := by
  constructor
  · intro hf V _ hV
    exact hf.mono_set (subset_closure.trans hV)
  · intro h
    refine (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 ?_
    intro K hKΩ hK
    obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
    exact (h ⟨V, hVo⟩ hVc hVΩ).integrableOn_compact_subset hKV hK

end TauCeti
