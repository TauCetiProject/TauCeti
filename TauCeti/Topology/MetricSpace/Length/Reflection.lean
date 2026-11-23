/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Length
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The reflection principle in length spaces

Let `f` be a continuous real function on a geodesic space `X`. A geodesic segment from `x` to `y`
with `f x` and `f y` of opposite signs crosses the level set `f = 0`, at a point `m` with
`d(x, m) + d(m, y) = d(x, y)`.

More generally, let `X` be a length space and `τ` a `1`-Lipschitz map fixing the level set `f = 0`
pointwise, as a reflection fixes its mirror. Then `d(p, τ w) ≤ d(p, w)` whenever
`f p * f w ≤ 0`: apply `τ` to the part of a joining curve after it crosses the mirror, and let
the curve's length approach the distance. For instance, rotating a point of a surface of revolution
towards `p` about the axis does not increase its distance to `p`.

## Main statements

* `TauCeti.IsCurveJoining.exists_apply_eq_zero`: a continuous joining curve crosses the zero set
  of a continuous function changing sign along it.
* `TauCeti.IsGeodesicSegment.exists_apply_eq_zero`: a geodesic segment crosses the zero set of a
  continuous function changing sign along it, with exact distance additivity at the crossing.
* `LipschitzWith.edist_apply_le_of_mul_nonpos`: the reflection principle in an extended length
  space.
* `LipschitzWith.dist_apply_le_of_mul_nonpos`: the metric form of the reflection principle.

## References

* M. R. Bridson, A. Haefliger, *Metric Spaces of Non-Positive Curvature*, Springer (1999),
  Chapter I.1 (geodesic spaces).
-/

public section

open Set

namespace TauCeti

variable {X : Type*}

/-- A continuous curve joining points where a continuous real function has opposite signs
crosses its zero set. -/
theorem IsCurveJoining.exists_apply_eq_zero [TopologicalSpace X] {γ : ℝ → X} {x y : X}
    (hγ : IsCurveJoining γ x y) {f : X → ℝ} (hf : Continuous f) (hxy : f x * f y ≤ 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, f (γ t) = 0 := by
  have hg : ContinuousOn (f ∘ γ) (Icc 0 1) := hf.comp_continuousOn hγ.continuousOn
  have h0 : (f ∘ γ) 0 = f x := by simp [hγ.source]
  have h1 : (f ∘ γ) 1 = f y := by simp [hγ.target]
  rcases mul_nonpos_iff.1 hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact intermediate_value_Icc' zero_le_one hg ⟨by rwa [h1], by rwa [h0]⟩
  · exact intermediate_value_Icc zero_le_one hg ⟨by rwa [h0], by rwa [h1]⟩

/-- **A geodesic segment crosses the zero set of a function changing sign along it.** If `γ` is a
geodesic segment from `x` to `y` and `f` is continuous with `f x * f y ≤ 0`, then some point
`m = γ t` with `t ∈ [0, 1]` has `f m = 0` and `d(x, m) + d(m, y) = d(x, y)`. -/
theorem IsGeodesicSegment.exists_apply_eq_zero [PseudoMetricSpace X] {γ : ℝ → X} {x y : X}
    (hγ : IsGeodesicSegment γ x y)
    {f : X → ℝ} (hf : Continuous f) (hxy : f x * f y ≤ 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, f (γ t) = 0 ∧ dist x (γ t) + dist (γ t) y = dist x y := by
  obtain ⟨t, ht, hft⟩ := hγ.isCurveJoining.exists_apply_eq_zero hf hxy
  refine ⟨t, ht, hft, ?_⟩
  rw [hγ.dist_source_apply ht, hγ.dist_apply_target ht]
  ring

/-- **The reflection principle in extended length spaces.** A `1`-Lipschitz map fixing the zero
set of a continuous real function cannot increase the extended distance from `p` to `w` when
`f p * f w ≤ 0`. -/
theorem _root_.LipschitzWith.edist_apply_le_of_mul_nonpos [PseudoEMetricSpace X] [IsLengthSpace X]
    {τ : X → X} (hτ : LipschitzWith 1 τ)
    {f : X → ℝ} (hf : Continuous f) (hfix : ∀ m, f m = 0 → τ m = m) {p w : X}
    (hpw : f p * f w ≤ 0) : edist p (τ w) ≤ edist p w := by
  rw [IsLengthSpace.edist_eq_iInf p w]
  refine le_iInf₂ fun γ hγ ↦ ?_
  obtain ⟨t, ht, hft⟩ := hγ.exists_apply_eq_zero hf hpw
  calc
    edist p (τ w) ≤ edist p (γ t) + edist (γ t) (τ w) := edist_triangle _ _ _
    _ = edist p (γ t) + edist (τ (γ t)) (τ w) := by rw [hfix _ hft]
    _ ≤ edist p (γ t) + edist (γ t) w :=
      add_le_add le_rfl (by simpa using hτ.edist_le_mul (γ t) w)
    _ ≤ eVariationOn γ (Icc 0 t) + eVariationOn γ (Icc t 1) := by
      rw [← hγ.source, ← hγ.target]
      exact add_le_add
        (eVariationOn.edist_le γ ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩)
        (eVariationOn.edist_le γ ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩)
    _ = eVariationOn γ (Icc 0 1) := by
      simpa only [univ_inter] using eVariationOn.Icc_add_Icc γ ht.1 ht.2 (mem_univ t)

/-- **The reflection principle.** In a length space, a `1`-Lipschitz map fixing the zero set of
a continuous real function cannot increase the distance from `p` to `w` when `f p * f w ≤ 0`. -/
theorem _root_.LipschitzWith.dist_apply_le_of_mul_nonpos [PseudoMetricSpace X] [IsLengthSpace X]
    {τ : X → X} (hτ : LipschitzWith 1 τ)
    {f : X → ℝ} (hf : Continuous f) (hfix : ∀ m, f m = 0 → τ m = m) {p w : X}
    (hpw : f p * f w ≤ 0) : dist p (τ w) ≤ dist p w := by
  simpa only [dist_edist] using
    ENNReal.toReal_mono (edist_ne_top p w) (hτ.edist_apply_le_of_mul_nonpos hf hfix hpw)

end TauCeti
