/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Flow.Domain
public import TauCeti.MeasureTheory.MeasurableSpace.RayCutTime

/-!
# Cut times of geodesics in a compact set

Let `S` and `K` be subsets of a Riemannian manifold `M`, with `K` compact, and let `γ` be the
maximal geodesic with initial data `(p, v)`, where `p ∈ S ∩ K` and `‖v‖ ≤ 1`; the main case is a
unit vector `v`. The *cut time* of `γ` from `S` in `K`, capped at `R`, is the supremum of the times
`t ∈ [0, R]` such that `γ` is defined and lies in `K` on `[0, t]` and `γ t` is at distance `t` from
`S`, for the Riemannian distance of `M`. In the language of
`TauCeti.Topology.MetricSpace.RayCutTime` it is the cut time `TauCeti.rayCutTime γ S T R` of the
ray `γ` for the time domain `T = geodesicInterval I M p v ∩ γ ⁻¹' K`.

The manifold is not assumed to be complete, and `γ` need not be defined up to time `R`. Compactness
of `K` makes up for both: a maximal geodesic that is defined and lies in `K` on `[0, τ)` is defined
at time `τ`, where it is still in `K`. Consequently the cut time is attained. Moreover, for a
continuous family of initial vectors, the parameters whose geodesic is defined and lies in `K` on
`[0, t]` form a closed set
(`TauCeti.Manifold.isClosed_setOfPred_Icc_subset_geodesicInterval_inter_preimage`), and the cut
time is an upper semicontinuous, hence measurable, function of the parameter.

## Main results

* `TauCeti.Manifold.rayCutTime_maximalGeodesic_mem_rayMinimizingTimes`: the cut time of a geodesic
  in a compact set is attained.
* `TauCeti.Manifold.upperSemicontinuous_rayCutTime_maximalGeodesic` and
  `TauCeti.Manifold.measurable_rayCutTime_maximalGeodesic`: the cut time in a compact set is an
  upper semicontinuous, hence measurable, function of the initial vector along a continuous family.
-/

public section

open Bundle Metric Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {P : Type*} [TopologicalSpace P]

variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {S K : Set M} {R : ℝ}

/-- **The cut time of a geodesic in a compact set is attained.** Let `γ` be the maximal geodesic
with initial data `(p, v)`, where `‖v‖ ≤ 1` and `p` lies in `S` and in a compact set `K`, and take
as time domain the times at which `γ` is defined and lies in `K`. Then the cut time of `γ` from
`S`, capped at `R`, is a minimizing time: `γ` is defined and lies in `K` up to the cut time, at
which its distance to `S` is the cut time. -/
theorem rayCutTime_maximalGeodesic_mem_rayMinimizingTimes {p : M} {v : TangentSpace I p}
    (hK : IsCompact K) (hv : ‖v‖ ≤ 1) (hR : 0 ≤ R) (hpS : p ∈ S) (hpK : p ∈ K) :
    rayCutTime (maximalGeodesic I M p v) S
        (geodesicInterval I M p v ∩ maximalGeodesic I M p v ⁻¹' K) R ∈
      rayMinimizingTimes (maximalGeodesic I M p v) S
        (geodesicInterval I M p v ∩ maximalGeodesic I M p v ⁻¹' K) R := by
  set γ := maximalGeodesic I M p v
  set T := geodesicInterval I M p v ∩ γ ⁻¹' K
  have hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u) := fun u _ hu ↦
    (lipschitzOnWith_maximalGeodesic.mono (hu.trans inter_subset_left)).weaken (mod_cast hv)
  have h0 : γ 0 = p := maximalGeodesic_zero p v
  have h0T : 0 ∈ T := ⟨zero_mem_geodesicInterval, mem_preimage.2 (h0 ▸ hpK)⟩
  have h0S : γ 0 ∈ S := h0 ▸ hpS
  have hlt : Ico 0 (rayCutTime γ S T R) ⊆ T := fun t ht ↦
    (mem_rayMinimizingTimes.1 (mem_rayMinimizingTimes_of_lt_rayCutTime hγ hR h0T h0S ht.1
      ht.2)).2.1 (right_mem_Icc.2 ht.1)
  have hτ := (rayCutTime_mem_Icc hR h0T h0S).1
  have hτJ : rayCutTime γ S T R ∈ geodesicInterval I M p v :=
    mem_geodesicInterval_of_isCompact_of_mapsTo_Ico hK hτ fun t ht ↦ (hlt ht.1).2
  refine rayCutTime_mem_rayMinimizingTimes hγ hR h0T h0S ⟨hτJ, ?_⟩
  rcases hτ.eq_or_lt with hτ0 | hτ0
  · exact hτ0 ▸ h0T.2
  have hcont : ContinuousWithinAt γ (Ico 0 (rayCutTime γ S T R)) (rayCutTime γ S T R) :=
    ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.contMDiffOn.continuousOn
      _ hτJ).mono (hlt.trans inter_subset_left)
  refine hK.isClosed.closure_subset (hcont.mem_closure ?_ fun t ht ↦ (hlt ht).2)
  rw [closure_Ico hτ0.ne]
  exact right_mem_Icc.2 hτ

variable {Z : P → TangentBundle I M}

/-- **Upper semicontinuity of the cut time in a compact set.** Let `Z` be a continuous family of
tangent vectors of norm at most one, based at points of `S` and of a compact set `K`, and take as
time domain of each maximal geodesic the times at which it is defined and lies in `K`. Then the cut
time from `S`, capped at `R`, is an upper semicontinuous function of the parameter. -/
theorem upperSemicontinuous_rayCutTime_maximalGeodesic (hZ : Continuous Z) (hK : IsCompact K)
    (hv : ∀ q, ‖(Z q).2‖ ≤ 1) (hR : 0 ≤ R) (hZS : ∀ q, (Z q).proj ∈ S)
    (hZK : ∀ q, (Z q).proj ∈ K) :
    UpperSemicontinuous fun q ↦ rayCutTime (maximalGeodesic I M (Z q).proj (Z q).2) S
      (geodesicInterval I M (Z q).proj (Z q).2 ∩ maximalGeodesic I M (Z q).proj (Z q).2 ⁻¹' K)
      R := by
  have hmem (q : P) := mem_rayMinimizingTimes.1 <|
    rayCutTime_maximalGeodesic_mem_rayMinimizingTimes (v := (Z q).2) hK (hv q) hR (hZS q) (hZK q)
  refine upperSemicontinuous_rayCutTime (fun q u _ hu ↦ (lipschitzOnWith_maximalGeodesic.mono
      (hu.trans inter_subset_left)).weaken (mod_cast hv q)) hR
    (fun q ↦ (hmem q).2.1 (left_mem_Icc.2 (hmem q).1.1))
    (fun q ↦ by rw [maximalGeodesic_zero]; exact hZS q)
    (fun q ↦ (hmem q).2.1 (right_mem_Icc.2 (hmem q).1.1))
    (fun t _ ↦ isClosed_setOfPred_Icc_subset_geodesicInterval_inter_preimage hZ hK t)
    fun t ht q hq ↦ (continuousAt_maximalGeodesic_comp hZ.continuousAt continuousAt_const
      (hq (right_mem_Icc.2 ht.1)).1).continuousWithinAt

/-- The cut time in a compact set `K` of the maximal geodesics of a continuous family of tangent
vectors of norm at most one, based at points of `S` and of `K`, is a measurable function of the
parameter. -/
theorem measurable_rayCutTime_maximalGeodesic [MeasurableSpace P] [OpensMeasurableSpace P]
    (hZ : Continuous Z) (hK : IsCompact K) (hv : ∀ q, ‖(Z q).2‖ ≤ 1) (hR : 0 ≤ R)
    (hZS : ∀ q, (Z q).proj ∈ S) (hZK : ∀ q, (Z q).proj ∈ K) :
    Measurable fun q ↦ rayCutTime (maximalGeodesic I M (Z q).proj (Z q).2) S
      (geodesicInterval I M (Z q).proj (Z q).2 ∩ maximalGeodesic I M (Z q).proj (Z q).2 ⁻¹' K)
      R :=
  (upperSemicontinuous_rayCutTime_maximalGeodesic hZ hK hv hR hZS hZK).measurable

end TauCeti.Manifold
