/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Length
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The reflection principle in geodesic spaces

Let `f` be a continuous real function on a geodesic space `X`. A geodesic segment from `x` to `y`
with `f x` and `f y` of opposite signs crosses the level set `f = 0`, at a point `m` with
`d(x, m) + d(m, y) = d(x, y)`.

Consequently, if `τ` is an isometry of `X` fixing the level set `f = 0` pointwise, as a reflection
fixes its mirror, then `d(p, τ w) ≤ d(p, w)` whenever `f p` and `f w` have opposite signs: reflect
the part of a shortest path from `p` to `w` after it crosses the mirror. For instance, rotating a
point of a surface of revolution towards `p` about the axis does not increase its distance to `p`.

## Main statements

* `TauCeti.IsGeodesicSegment.exists_apply_eq_zero`: a geodesic segment crosses the zero set of a
  continuous function changing sign along it.
* `TauCeti.dist_apply_le_of_mul_nonpos`: the reflection principle.

## References

* M. R. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*, Springer (1999),
  Chapter I.1 (geodesic spaces).
-/

public section

open Set

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- **A geodesic segment crosses the zero set of a function changing sign along it.** If `γ` is a
geodesic segment from `x` to `y` and `f` is continuous with `f x * f y ≤ 0`, then some point
`m = γ t` with `t ∈ [0, 1]` has `f m = 0` and `d(x, m) + d(m, y) = d(x, y)`. -/
theorem IsGeodesicSegment.exists_apply_eq_zero {γ : ℝ → X} {x y : X} (hγ : IsGeodesicSegment γ x y)
    {f : X → ℝ} (hf : Continuous f) (hxy : f x * f y ≤ 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, f (γ t) = 0 ∧ dist x (γ t) + dist (γ t) y = dist x y := by
  have hg : ContinuousOn (f ∘ γ) (Icc 0 1) := hf.comp_continuousOn hγ.continuousOn
  have h0 : (f ∘ γ) 0 = f x := by simp [hγ.source]
  have h1 : (f ∘ γ) 1 = f y := by simp [hγ.target]
  obtain ⟨t, ht, hft⟩ : ∃ t ∈ Icc (0 : ℝ) 1, (f ∘ γ) t = 0 := by
    rcases mul_nonpos_iff.1 hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact intermediate_value_Icc' zero_le_one hg ⟨by rwa [h1], by rwa [h0]⟩
    · exact intermediate_value_Icc zero_le_one hg ⟨by rwa [h0], by rwa [h1]⟩
  refine ⟨t, ht, hft, ?_⟩
  rw [hγ.dist_source_apply ht, hγ.dist_apply_target ht]
  ring

/-- **The reflection principle.** Let `X` be a geodesic space, `τ` an isometry of `X` and `f` a
continuous function such that `τ` fixes every zero of `f`. If `f p` and `f w` have opposite signs,
then `d(p, τ w) ≤ d(p, w)`. -/
theorem dist_apply_le_of_mul_nonpos [IsGeodesicSpace X] {τ : X → X} (hτ : Isometry τ)
    {f : X → ℝ} (hf : Continuous f) (hfix : ∀ m, f m = 0 → τ m = m) {p w : X}
    (hpw : f p * f w ≤ 0) : dist p (τ w) ≤ dist p w := by
  obtain ⟨γ, hγ⟩ := IsGeodesicSpace.exists_isGeodesicSegment p w
  obtain ⟨t, -, hft, hsum⟩ := hγ.exists_apply_eq_zero hf hpw
  calc dist p (τ w) ≤ dist p (γ t) + dist (γ t) (τ w) := dist_triangle _ _ _
    _ = dist p (γ t) + dist (τ (γ t)) (τ w) := by rw [hfix _ hft]
    _ = dist p w := by rw [hτ.dist_eq, hsum]

end TauCeti
