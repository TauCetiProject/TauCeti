/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.FunctionTopology

/-!
# Limits of convex functions

A pointwise limit, on a set `s`, of functions that are eventually convex on `s` is convex on `s`.
This is the closedness of the set of convex functions (`isClosed_setOfPred_convexOn`) applied to
functions that are only known to converge on `s`.
-/

public section

namespace TauCeti

open Set Filter

open scoped Topology

variable {𝕜 α β ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [PartialOrder β]
  [TopologicalSpace β] [OrderClosedTopology β] [AddCommMonoid α] [AddCommMonoid β]
  [SMul 𝕜 α] [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] [ContinuousAdd β]

/-- **A pointwise limit of convex functions is convex.** If the functions `F i` are eventually
convex on `s` and converge to `f` at every point of `s`, then `f` is convex on `s`. -/
theorem convexOn_of_tendsto {l : Filter ι} [l.NeBot] {F : ι → α → β} {f : α → β} {s : Set α}
    (hF : ∀ᶠ i in l, ConvexOn 𝕜 s (F i))
    (hf : ∀ x ∈ s, Tendsto (fun i => F i x) l (𝓝 (f x))) : ConvexOn 𝕜 s f := by
  classical
  -- Replace `F i` by `f` off `s`; the modified functions converge to `f` everywhere.
  have hlim : Tendsto (fun i => s.piecewise (F i) f) l (𝓝 f) := tendsto_pi_nhds.2 fun x => by
    by_cases hx : x ∈ s
    · simpa only [s.piecewise_eq_of_mem _ _ hx] using hf x hx
    · simpa only [s.piecewise_eq_of_notMem _ _ hx] using tendsto_const_nhds
  exact isClosed_setOfPred_convexOn.mem_of_tendsto hlim
    (hF.mono fun i hi => hi.congr fun x hx => (s.piecewise_eq_of_mem _ _ hx).symm)

end TauCeti
