/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function

import Mathlib.Analysis.Convex.Segment

/-!
# Monotonicity of lower truncations of convex functions

Cutting off a convex function of one variable from below at a level `d` above its value at a point
`c ∈ s` produces a nondecreasing function on `s ∩ Ici c`: for `c ≤ a ≤ b` with `b ∈ s`, convexity
on the segment `[c, b]` bounds `Φ a ≤ max (Φ c) (Φ b) ≤ max (Φ b) d` via `ConvexOn.le_on_segment`.

## Main results

* `ConvexOn.monotoneOn_max_const`: if `Φ` is convex on `s` and `c ∈ s` with `Φ c ≤ d`, then
  `x ↦ max (Φ x) d` is nondecreasing on `s ∩ Ici c`.
-/

public section

open Set

namespace ConvexOn

/-- Truncating a function convex on `s` from below at any level `d ≥ Φ c` (with `c ∈ s`) produces
a nondecreasing function on `s ∩ Ici c`. -/
theorem monotoneOn_max_const {𝕜 β : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]
    {Φ : 𝕜 → β} {s : Set 𝕜} {c : 𝕜} {d : β} (hΦ : ConvexOn 𝕜 s Φ) (hc : c ∈ s) (hd : Φ c ≤ d) :
    MonotoneOn (fun x ↦ max (Φ x) d) (s ∩ Ici c) := by
  intro a ha b hb hab
  exact max_le
    ((hΦ.le_on_segment hc hb.1 (Icc_subset_segment ⟨ha.2, hab⟩)).trans
      (max_le (hd.trans (le_max_right _ _)) (le_max_left _ _)))
    (le_max_right _ _)

end ConvexOn
