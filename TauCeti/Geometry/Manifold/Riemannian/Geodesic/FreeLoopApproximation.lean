/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Broken
public import TauCeti.Topology.PathSpace.Moore.BrokenPath
import TauCeti.Data.Fin.Basic

/-!
# Approximating compact families of free loops by broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r > 0` be a
radius such that the tangent ball of radius `r` at every point is a normal domain. Points at
distance less than `r` are joined by the radial geodesic between them, which gives a path
interpolation `TauCeti.Manifold.geodesicInterpolation` on the pairs of points at distance less
than `r`. Run at unit speed on each arc, the broken Moore path through `q 0, …, q n` for this
interpolation is the broken geodesic through these points
(`TauCeti.Manifold.brokenGeodesic_eq_brokenMoorePath`).

Sample a free Moore loop `γ` at the `n + 1` times `i L / (n + 1)`, `L` its duration, and suppose
that every point of each of the `n + 1` arcs is at distance less than `r` from the initial vertex
of its arc. The closed broken geodesic through the sampled vertices is then defined
(`TauCeti.Manifold.sampleBrokenGeodesicLoop`), and it is homotopic to `γ`, continuously in `γ`
(`TauCeti.Manifold.sampleBrokenGeodesicLoopHomotopy`), through loops with the same base point
(`TauCeti.Manifold.basepoint_sampleBrokenGeodesicLoopHomotopy`). The homotopy runs in two stages.

* The arcs of `γ` are straightened, keeping the duration of each arc equal to `L / (n + 1)`
  (`TauCeti.MooreFreeLoopSpace.arcStraightening`). This ends at the broken path through the
  sampled vertices whose arcs all last `L / (n + 1)`.
* The duration of the `i`-th arc is moved linearly from `L / (n + 1)` to the distance between its
  end points, at which the broken path travels at unit speed and is the closed broken geodesic
  (`TauCeti.Manifold.brokenPathDurationHomotopy`).

The duration is a continuous function on the Moore loops, so no filtration by geometric length is
involved. For a compact family `K` of free loops and cut-offs bounded below by `ε > 0` and less
than `r`, every sufficiently fine sampling maps `K` into the distance cut
`𝓛ⁿM = {q | dist (q i) (q (i - 1)) ≤ δ i}`, and the composite `geoⁿ ∘ evₙ` of the sampling with
the broken geodesic map `geoⁿ : 𝓛ⁿM → 𝓛M` (`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`) is
homotopic to the inclusion of `K`
(`TauCeti.Manifold.exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic`). This is the
compact-family approximation of the free loop space by broken geodesics, the first of the two
hypotheses under which the colimit of the finite-dimensional approximations `𝓛ⁿM` computes the
homology of the free loop space.

## Main definitions

* `TauCeti.Manifold.sampleBrokenGeodesicLoop`: the closed broken geodesic through the sampled
  vertices of a free Moore loop with arcs of radius less than `r`.
* `TauCeti.Manifold.brokenPathDurationHomotopy`: the linear change of the arc durations, from the
  broken path with equal arc durations to the closed broken geodesic.
* `TauCeti.Manifold.sampleBrokenGeodesicLoopHomotopy`: the homotopy from the inclusion to the
  closed broken geodesic through the sampled vertices.

## Main results

* `TauCeti.Manifold.basepoint_sampleBrokenGeodesicLoopHomotopy`: the homotopy keeps the base point.
* `TauCeti.Manifold.exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic`: on a compact family of
  free loops, every sufficiently fine `geoⁿ ∘ evₙ` is homotopic to the inclusion.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public section

open Bundle Manifold Metric Set
open scoped ContDiff Manifold NNReal Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ} (hr : ∀ q : M, IsNormalDomain I M q (ball 0 r))

/-! ### Changing the durations of the arcs -/

section Duration

variable (n : ℕ)

/-- The duration of the `i`-th arc at time `s` of the homotopy from equal durations to unit
speed: `(1 - s) L / (n + 1) + s d`, for a free loop of duration `L` whose `i`-th and `(i + 1)`-st
sampled vertices are at distance `d`. -/
private def arcDuration (s : unitInterval) (γ : MooreFreeLoopSpace M) (i : Fin (n + 1)) : ℝ≥0 :=
  unitInterval.toNNReal (unitInterval.symm s) * (γ.length / (n + 1)) +
    unitInterval.toNNReal s *
      nndist (γ.closedSample (n + 1) i.castSucc) (γ.closedSample (n + 1) i.succ)

omit [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- At the start of the homotopy every arc lasts `L / (n + 1)`. -/
private theorem arcDuration_zero (γ : MooreFreeLoopSpace M) (i : Fin (n + 1)) :
    arcDuration n 0 γ i = γ.length / (n + 1) := by
  simp [arcDuration]

omit [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- At the end of the homotopy every arc lasts the distance between its vertices. -/
private theorem arcDuration_one (γ : MooreFreeLoopSpace M) (i : Fin (n + 1)) :
    arcDuration n 1 γ i =
      nndist (γ.closedSample (n + 1) i.castSucc) (γ.closedSample (n + 1) i.succ) := by
  simp [arcDuration]

omit [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- An arc of duration zero joins equal vertices. -/
private theorem eq_of_arcDuration_eq_zero {s : unitInterval} {γ : MooreFreeLoopSpace M}
    {i : Fin (n + 1)} (h : arcDuration n s γ i = 0) :
    γ.closedSample (n + 1) i.castSucc = γ.closedSample (n + 1) i.succ := by
  rcases mul_eq_zero.1 (add_eq_zero.1 h).2 with hs | hd
  · -- At `s = 0` the duration is `L / (n + 1)`, which only vanishes for a loop of length zero.
    obtain rfl : s = 0 := Subtype.ext (by simpa using congrArg NNReal.toReal hs)
    rw [arcDuration_zero, div_eq_zero_iff] at h
    have hγ := h.resolve_right (by exact_mod_cast n.succ_ne_zero)
    rw [MooreFreeLoopSpace.closedSample_of_length_eq_zero hγ,
      MooreFreeLoopSpace.closedSample_of_length_eq_zero hγ]
  · exact nndist_eq_zero.1 hd

include hr

/-- The broken Moore paths of the homotopy changing the durations of the arcs. -/
private def arcDurationMap :
    C(unitInterval × MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1),
      MooreFreeLoopSpace M) where
  toFun p := ⟨brokenMoorePath (isPathInterpolation_geodesicInterpolation hr) (n + 1)
      ((p.2 : MooreFreeLoopSpace M).closedSample (n + 1))
      (arcDuration n p.1 (p.2 : MooreFreeLoopSpace M)) fun i ↦
        ⟨MooreFreeLoopSpace.closedSample_mem_of_mem_arcsWithin p.2.property i,
          eq_of_arcDuration_eq_zero n⟩, by
    rw [target_brokenMoorePath, source_brokenMoorePath, MooreFreeLoopSpace.closedSample_last,
      MooreFreeLoopSpace.closedSample_zero]⟩
  continuous_toFun := by
    refine MooreFreeLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 ?_
    have hq : Continuous fun p : unitInterval ×
        MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) ↦
        (p.2 : MooreFreeLoopSpace M).closedSample (n + 1) :=
      (MooreFreeLoopSpace.continuous_closedSample _).comp
        (continuous_subtypeVal.comp continuous_snd)
    refine continuous_brokenMoorePath _ (n + 1) hq
      (L := fun (p : unitInterval ×
        MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) i ↦
          arcDuration n p.1 (p.2 : MooreFreeLoopSpace M) i) (continuous_pi fun i ↦ ?_) _
    simp only [arcDuration]
    have hL : Continuous fun p : unitInterval ×
        MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) ↦
        (p.2 : MooreFreeLoopSpace M).length :=
      MooreFreeLoopSpace.continuous_length.comp (continuous_subtypeVal.comp continuous_snd)
    refine ((unitInterval.toNNReal_continuous.comp
      (unitInterval.continuous_symm.comp continuous_fst)).mul (hL.div_const _)).add
      ((unitInterval.toNNReal_continuous.comp continuous_fst).mul ?_)
    exact ((continuous_apply _).comp hq).nndist ((continuous_apply _).comp hq)

/-- At the end of the homotopy changing the durations, the arcs travel at unit speed, so the
broken Moore path is the closed broken geodesic through the sampled vertices. -/
private theorem arcDurationMap_one
    (γ : MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    arcDurationMap hr n (1, γ) =
      brokenGeodesicLoop hr n ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1))
        (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin γ.property) := by
  refine MooreFreeLoopSpace.ext ?_
  simp only [arcDurationMap, ContinuousMap.coe_mk]
  rw [toMoorePath_brokenGeodesicLoop hr n _ _ fun i ↦ by
      rw [← MooreFreeLoopSpace.closedSample_eq_snoc]
      exact MooreFreeLoopSpace.closedSample_mem_of_mem_arcsWithin γ.property i,
    brokenGeodesic_eq_brokenMoorePath hr]
  exact brokenMoorePath_congr _ _ _ (MooreFreeLoopSpace.closedSample_eq_snoc _ _)
    (funext fun i ↦ by simp [arcDuration_one, MooreFreeLoopSpace.closedSample_eq_snoc])

/-- **The closed broken geodesic through the sampled vertices** of a free Moore loop whose `n + 1`
arcs lie within distance `r` of their initial vertices, as a continuous map. -/
def sampleBrokenGeodesicLoop :
    C(MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1),
      MooreFreeLoopSpace M) where
  toFun γ := brokenGeodesicLoop hr n ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1))
    (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin γ.property)
  continuous_toFun :=
    ((arcDurationMap hr n).continuous.comp (Continuous.prodMk_right 1)).congr
      (arcDurationMap_one hr n)

/-- The closed broken geodesic through the sampled vertices, for any proof that consecutive
vertices are at distance less than `r`. -/
theorem sampleBrokenGeodesicLoop_apply
    (γ : MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1))
    (h : ∀ i, dist ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) i)
      ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) (i - 1)) < r) :
    sampleBrokenGeodesicLoop hr n γ =
      brokenGeodesicLoop hr n ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1)) h :=
  (rfl)

/-- The broken geodesic through the samples of a free loop is based at the base point of the loop,
its first sampled vertex. -/
@[simp]
theorem basepoint_sampleBrokenGeodesicLoop
    (γ : MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    (sampleBrokenGeodesicLoop hr n γ).basepoint = (γ : MooreFreeLoopSpace M).basepoint := by
  rw [sampleBrokenGeodesicLoop_apply hr n γ
      (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin γ.property),
    basepoint_brokenGeodesicLoop, MoorePath.sample_zero, MooreFreeLoopSpace.source_toMoorePath]

/-- The length of the broken geodesic through the samples is the sum of the distances between
consecutive samples, the last one followed by the first one. -/
theorem length_sampleBrokenGeodesicLoop
    (γ : MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    (sampleBrokenGeodesicLoop hr n γ).length =
      ∑ k, nndist ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) k)
        ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) (k + 1)) := by
  rw [sampleBrokenGeodesicLoop_apply hr n γ
      (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin γ.property),
    length_brokenGeodesicLoop_eq_partialSum, Fin.partialSum_last]

/-- The length of the broken geodesic through the samples varies continuously with the loop. -/
theorem continuous_length_sampleBrokenGeodesicLoop :
    Continuous fun γ : MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) ↦
      (sampleBrokenGeodesicLoop hr n γ).length :=
  MooreFreeLoopSpace.continuous_length.comp (sampleBrokenGeodesicLoop hr n).continuous

/-- **Changing the durations of the arcs.** On the free Moore loops whose `n + 1` arcs lie within
distance `r` of their initial vertices, a homotopy from the broken loops through the sampled
vertices with arcs of equal durations, at the end of the arc-straightening homotopy, to the closed
broken geodesics through the same vertices. At time `s` the `i`-th arc runs along the geodesic
between its vertices in time `(1 - s) L / (n + 1) + s d`, for a loop of duration `L` and vertices
at distance `d`. -/
def brokenPathDurationHomotopy :
    (MooreFreeLoopSpace.brokenPathMap (isPathInterpolation_geodesicInterpolation hr)
      n.succ_pos).Homotopy (sampleBrokenGeodesicLoop hr n) where
  toContinuousMap := arcDurationMap hr n
  map_zero_left γ := by
    refine MooreFreeLoopSpace.ext ?_
    simp only [arcDurationMap, MooreFreeLoopSpace.toMoorePath_brokenPathMap]
    rw [MoorePath.brokenPathMap_eq_brokenMoorePath _ _ (fun i ↦ by
      rw [MooreFreeLoopSpace.coe_toArcsWithin]
      exact MooreFreeLoopSpace.closedSample_eq_toUnitPath (γ : MooreFreeLoopSpace M) n.succ_pos i)
      fun i ↦ ⟨MooreFreeLoopSpace.closedSample_mem_of_mem_arcsWithin γ.property i, fun h ↦
        eq_of_arcDuration_eq_zero n (s := 0) (by simpa [arcDuration_zero] using h)⟩]
    exact brokenMoorePath_congr _ _ _ rfl (funext fun i ↦ by simp [arcDuration_zero])
  map_one_left := arcDurationMap_one hr n

/-- At time `s` of the homotopy changing the durations, the `i`-th arc runs along the geodesic
between the `i`-th and `(i + 1)`-st closed sampled vertices in time `(1 - s) L / (n + 1) + s d`,
for a loop of duration `L` and vertices at distance `d`. -/
theorem toMoorePath_brokenPathDurationHomotopy (s : unitInterval)
    (γ : MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1))
    (h : ∀ i : Fin (n + 1), ((γ : MooreFreeLoopSpace M).closedSample (n + 1) i.castSucc,
        (γ : MooreFreeLoopSpace M).closedSample (n + 1) i.succ) ∈ {p : M × M | dist p.1 p.2 < r} ∧
      (unitInterval.toNNReal (unitInterval.symm s) * ((γ : MooreFreeLoopSpace M).length / (n + 1)) +
          unitInterval.toNNReal s * nndist ((γ : MooreFreeLoopSpace M).closedSample (n + 1)
            i.castSucc) ((γ : MooreFreeLoopSpace M).closedSample (n + 1) i.succ) = 0 →
        (γ : MooreFreeLoopSpace M).closedSample (n + 1) i.castSucc =
          (γ : MooreFreeLoopSpace M).closedSample (n + 1) i.succ)) :
    (brokenPathDurationHomotopy hr n (s, γ)).toMoorePath =
      brokenMoorePath (isPathInterpolation_geodesicInterpolation hr) (n + 1)
        ((γ : MooreFreeLoopSpace M).closedSample (n + 1))
        (fun i ↦ unitInterval.toNNReal (unitInterval.symm s) *
            ((γ : MooreFreeLoopSpace M).length / (n + 1)) +
          unitInterval.toNNReal s * nndist ((γ : MooreFreeLoopSpace M).closedSample (n + 1)
            i.castSucc) ((γ : MooreFreeLoopSpace M).closedSample (n + 1) i.succ)) h :=
  (rfl)

/-- **Free loops are homotopic to the broken geodesics through their sampled vertices.** On the
free Moore loops whose `n + 1` arcs lie within distance `r` of their initial vertices, a homotopy
from the inclusion to the closed broken geodesic through the sampled vertices: the arcs are first
straightened into geodesics run in equal times, and then run at unit speed. -/
def sampleBrokenGeodesicLoopHomotopy :
    (ContinuousMap.subtypeVal _).Homotopy (sampleBrokenGeodesicLoop hr n) :=
  (MooreFreeLoopSpace.arcStraightening (isPathInterpolation_geodesicInterpolation hr)
    n.succ_pos).trans (brokenPathDurationHomotopy hr n)

/-- The homotopy changing the durations of the arcs keeps the base point: every broken loop of the
homotopy starts at the first sampled vertex. -/
@[simp]
theorem basepoint_brokenPathDurationHomotopy (p : unitInterval ×
    MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    (brokenPathDurationHomotopy hr n p).basepoint = (p.2 : MooreFreeLoopSpace M).basepoint := by
  rw [← MooreFreeLoopSpace.source_toMoorePath, ← MooreFreeLoopSpace.closedSample_zero _ (n + 1)]
  -- the broken loop of the homotopy is a broken Moore path through the closed sampled vertices
  exact source_brokenMoorePath _ _ _ _ _

/-- **The homotopy from a free loop to the broken geodesic through its sampled vertices keeps the
base point.** So it restricts to the loops based at a point. -/
@[simp]
theorem basepoint_sampleBrokenGeodesicLoopHomotopy (p : unitInterval ×
    MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :
    (sampleBrokenGeodesicLoopHomotopy hr n p).basepoint =
      (p.2 : MooreFreeLoopSpace M).basepoint := by
  rw [sampleBrokenGeodesicLoopHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> simp

end Duration

/-! ### Compact families -/

section Compact

include hr

/-- **The compact-family approximation of the free loop space by broken geodesics.** For a compact
family `K` of free Moore loops and `ε > 0` there is `N` such that for every `n ≥ N` and all
cut-offs `ε ≤ δ i < r`, the sampling `evₙ` at `n + 1` times maps `K` into the distance cut
`𝓛ⁿM = {q | dist (q i) (q (i - 1)) ≤ δ i}`, and `geoⁿ ∘ evₙ : K → 𝓛M`, with `geoⁿ` the closed
broken geodesic map, is homotopic to the inclusion of `K`. -/
theorem exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic {K : Set (MooreFreeLoopSpace M)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ δ : Fin (n + 1) → ℝ, (∀ i, ε ≤ δ i) → ∀ hδ : ∀ i, δ i < r,
      ∃ e : C(K, cyclicDistanceCut (X := M) δ),
        (∀ γ, (e γ : Fin (n + 1) → M) = (γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1)) ∧
        ((cyclicDistanceCutBrokenGeodesic hr hδ).comp e).Homotopic
          (ContinuousMap.subtypeVal K) := by
  by_cases hr0 : 0 < r
  swap
  · exact ⟨0, fun n _ δ hεδ hδ ↦ absurd ((hε.trans_le (hεδ 0)).trans (hδ 0)) hr0⟩
  obtain ⟨N₁, -, hN₁⟩ := MoorePath.exists_subset_arcsWithin
    (hK.image MooreFreeLoopSpace.continuous_toMoorePath) (Metric.dist_mem_uniformity hr0)
  obtain ⟨N₂, hN₂⟩ := MooreFreeLoopSpace.exists_mapsTo_sample_cyclicDistanceCut hK hε
  refine ⟨max N₁ N₂, fun n hn δ hεδ hδ ↦ ?_⟩
  have hKA (γ : K) : (γ : MooreFreeLoopSpace M) ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) :=
    MooreFreeLoopSpace.mem_arcsWithin.2
      (MoorePath.mem_arcsWithin.1 (hN₁ (n + 1) (by omega) ⟨γ, γ.property, rfl⟩))
  have hmaps := hN₂ n (le_of_max_le_right hn) δ hεδ
  let ι : C(K, MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :=
    ⟨fun γ ↦ ⟨γ, hKA γ⟩, continuous_subtypeVal.subtype_mk _⟩
  let e : C(K, cyclicDistanceCut (X := M) δ) :=
    ⟨fun γ ↦ ⟨_, hmaps γ.property⟩, ((MooreFreeLoopSpace.continuous_sample _).comp
      continuous_subtypeVal).subtype_mk _⟩
  refine ⟨e, fun γ ↦ rfl, ?_⟩
  -- On `K`, `geoⁿ ∘ evₙ` is the closed broken geodesic through the sampled vertices.
  have he : (cyclicDistanceCutBrokenGeodesic hr hδ).comp e =
      (sampleBrokenGeodesicLoop hr n).comp ι :=
    ContinuousMap.ext fun γ ↦ by
      simp only [ContinuousMap.comp_apply, cyclicDistanceCutBrokenGeodesic_apply, e, ι,
        ContinuousMap.coe_mk, sampleBrokenGeodesicLoop_apply hr n ⟨γ, hKA γ⟩
          (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin (hKA γ))]
  rw [he]
  exact ⟨((sampleBrokenGeodesicLoopHomotopy hr n).compContinuousMap ι).symm⟩

end Compact

end TauCeti.Manifold
