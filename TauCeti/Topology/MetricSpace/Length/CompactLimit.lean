/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Topology.MetricSpace.Length
import TauCeti.Topology.MetricSpace.Isometry.CompactLimit

/-!
# Limits of approximate geodesic segments

Compactness constructs a native minimizing segment from curves whose endpoints and
constant-speed distance formulas converge. The approximating curves need not be continuous.

## References

* D. Burago, Y. Burago and S. Ivanov, *A Course in Metric Geometry*, §7.5.
-/

public section

open Set Filter Metric
open scoped Topology

namespace TauCeti

variable {X : Type*} [MetricSpace X]

/-- A compact target contains a geodesic segment when curves with convergent endpoints have
the limiting constant-speed distance formula. Continuity of the approximating curves is
unnecessary. -/
theorem exists_isGeodesicSegment_of_tendsto_dist [CompactSpace X]
    {ι : Type*} {l : Filter ι} [l.NeBot] {x y : X} (f : ι → ℝ → X)
    (hzero : Tendsto (fun i ↦ f i 0) l (𝓝 x))
    (hone : Tendsto (fun i ↦ f i 1) l (𝓝 y))
    (hdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun i ↦ dist (f i s) (f i t)) l (𝓝 (|s - t| * dist x y))) :
    ∃ γ : ℝ → X, IsGeodesicSegment γ x y := by
  by_cases hxy : x = y
  · subst y
    exact ⟨fun _ ↦ x, isGeodesicSegment_const x⟩
  have hd : 0 < dist x y := dist_pos.mpr hxy
  let A := Icc (0 : ℝ) (dist x y)
  have hmem (s : A) : (s : ℝ) / dist x y ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg s.property.left hd.le, (div_le_one hd).mpr s.property.right⟩
  have hlim (s t : A) :
      Tendsto (fun i ↦ dist (f i ((s : ℝ) / dist x y)) (f i ((t : ℝ) / dist x y)))
        l (𝓝 (dist s t)) := by
    convert hdist _ (hmem s) _ (hmem t) using 1
    rw [Subtype.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hd,
      div_mul_cancel₀ _ hd.ne']
  obtain ⟨U, hU, e, he, hpoint⟩ :=
    exists_isometric_ultrafilter_limit (fun i (s : A) ↦ f i ((s : ℝ) / dist x y)) hlim
  have hezero : e ⟨0, by simp [A, hd.le]⟩ = x := by
    apply tendsto_nhds_unique (hpoint ⟨0, by simp [A, hd.le]⟩)
    simpa only [zero_div] using hzero.mono_left hU
  have heone : e ⟨dist x y, by simp [A, hd.le]⟩ = y := by
    apply tendsto_nhds_unique (hpoint ⟨dist x y, by simp [A, hd.le]⟩)
    simpa only [div_self hd.ne'] using hone.mono_left hU
  refine ⟨fun t ↦ IccExtend hd.le e (dist x y * t), ⟨?_, ?_, ?_⟩⟩
  · simpa only [mul_zero, IccExtend_left] using hezero
  · simpa only [mul_one, IccExtend_right] using heone
  · intro s hs t ht
    have hds : dist x y * s ∈ A :=
      ⟨mul_nonneg hd.le hs.left, mul_le_of_le_one_right hd.le hs.right⟩
    have hdt : dist x y * t ∈ A :=
      ⟨mul_nonneg hd.le ht.left, mul_le_of_le_one_right hd.le ht.right⟩
    rw [IccExtend_of_mem _ _ hds, IccExtend_of_mem _ _ hdt, he.dist_eq,
      Subtype.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hd, mul_comm]

end TauCeti
