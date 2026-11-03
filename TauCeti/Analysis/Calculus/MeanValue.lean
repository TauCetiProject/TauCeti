/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Mean value estimates for two maps with nearby derivatives

If two maps on a convex set have derivatives within `ε` of a common linear map and agree at a
point `y`, then by the mean value inequality applied to their difference they stay within
`2 ε ‖x - y‖` of each other (`Convex.norm_sub_le_of_norm_hasFDerivWithin_sub_le`).

This is how a map and a model agreeing with it to first order along a set are compared before
splicing them together (`TauCeti.Analysis.Calculus.Splice`).
-/

public section

/-- **Two maps with nearby derivatives that agree at a point stay close.** If the derivatives of
`k` and `l` on a convex set `S` are within `ε` of a fixed linear map `A`, and `k` and `l` agree at
`y ∈ S`, then `‖l x - k x‖ ≤ 2 ε ‖x - y‖` for every `x ∈ S`. -/
theorem Convex.norm_sub_le_of_norm_hasFDerivWithin_sub_le {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {S : Set X} (hS : Convex ℝ S)
    {k l : X → Y} {k' l' : X → X →L[ℝ] Y} {A : X →L[ℝ] Y} {ε : ℝ}
    (hk : ∀ x ∈ S, HasFDerivWithinAt k (k' x) S x) (hl : ∀ x ∈ S, HasFDerivWithinAt l (l' x) S x)
    (hk' : ∀ x ∈ S, ‖k' x - A‖ ≤ ε) (hl' : ∀ x ∈ S, ‖l' x - A‖ ≤ ε) {x y : X} (hx : x ∈ S)
    (hy : y ∈ S) (hxy : k y = l y) : ‖l x - k x‖ ≤ 2 * ε * ‖x - y‖ := by
  have h := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun v => l v - k v)
    (f' := fun v => l' v - k' v) (C := 2 * ε) (fun v hv => (hl v hv).sub (hk v hv))
    (fun v hv => (norm_sub_le_norm_sub_add_norm_sub (l' v) A (k' v)).trans
      (by rw [norm_sub_rev A]; linarith [hl' v hv, hk' v hv])) hy hx
  rwa [hxy, sub_self, sub_zero] at h
