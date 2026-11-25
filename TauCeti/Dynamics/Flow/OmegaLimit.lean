/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.OmegaLimit

/-!
# ω-limit sets of flows and maximal invariant subsets

Let `ϕ` be a flow of an additive monoid `τ`, `f` a filter on `τ` invariant under translations
(such as `atTop` for `τ = ℝ`) and `P` a closed set. The ω-limit set with respect to `f` of any set
whose images under `ϕ t` lie in `P` for `f`-eventually all `t` is contained in the maximal
invariant subset `Inv(P) = {x | ∀ t, ϕ t x ∈ P}`
(`Flow.omegaLimit_subset_setOf_forall_apply_mem`). When `P` is compact and the space is
Hausdorff, Mathlib's ω-limit absorption theorem then shows that such a set is eventually carried
into every open neighbourhood of `Inv(P)` (`Flow.eventually_mapsTo_of_isCompact_of_isOpen`).

## Main results

* `Flow.omegaLimit_subset_setOf_forall_apply_mem`: ω-limit sets of sets eventually mapped into a
  closed set `P` lie in the maximal invariant subset of `P`.
* `Flow.eventually_mapsTo_of_isCompact_of_isOpen`: for compact `P`, such sets are eventually
  carried into every open neighbourhood of the maximal invariant subset of `P`.
-/

public section

open Filter Set
open scoped omegaLimit

namespace Flow

variable {τ : Type*} [TopologicalSpace τ] [AddMonoid τ] {α : Type*} [TopologicalSpace α]
  {ϕ : Flow τ α} {f : Filter τ} {P s : Set α}

/-- The ω-limit set, with respect to a translation-invariant filter `f`, of a set whose images
eventually lie in a closed set `P` is contained in the maximal invariant subset of `P`, the set of
points whose whole orbit lies in `P`. -/
theorem omegaLimit_subset_setOf_forall_apply_mem (hf : ∀ t, Tendsto (t + ·) f f)
    (hP : IsClosed P) (hs : ∀ᶠ t in f, MapsTo (ϕ t) s P) : ω f ϕ s ⊆ {x | ∀ t, ϕ t x ∈ P} := by
  have hω : ω f ϕ s ⊆ P :=
    (omegaLimit_subset_closure_image2 _ _ _ hs).trans
      (closure_minimal (image2_subset_iff.2 fun _ ht _ hx ↦ ht hx) hP)
  exact fun y hy t ↦ hω (isInvariant_omegaLimit f ϕ s hf t hy)

/-- **Attraction to the maximal invariant subset.** If `P` is compact in a Hausdorff space and `f`
is a translation-invariant filter, a set whose images eventually lie in `P` is eventually carried
by the flow into every open neighbourhood of the maximal invariant subset of `P`. -/
theorem eventually_mapsTo_of_isCompact_of_isOpen [T2Space α] (hf : ∀ t, Tendsto (t + ·) f f)
    (hP : IsCompact P) (hs : ∀ᶠ t in f, MapsTo (ϕ t) s P) {U : Set α} (hU : IsOpen U)
    (hPU : {x | ∀ t, ϕ t x ∈ P} ⊆ U) : ∀ᶠ t in f, MapsTo (ϕ t) s U :=
  eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset _ _ _ hP hs hU
    ((omegaLimit_subset_setOf_forall_apply_mem hf hP.isClosed hs).trans hPU)

end Flow
