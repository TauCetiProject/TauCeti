/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Broken
public import TauCeti.Topology.PathSpace.Moore.BrokenPath
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Approximating compact families of free loops by broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r > 0` be a
radius such that the tangent ball of radius `r` at every point is a normal domain. Points at
distance less than `r` are joined by the radial geodesic between them, which gives a path
interpolation `TauCeti.Manifold.geodesicInterpolation` on the pairs of points at distance less
than `r` (`TauCeti.Manifold.isPathInterpolation_geodesicInterpolation`). Run at unit speed on
each arc, the broken Moore path through `q 0, …, q n` for this interpolation is the broken
geodesic through these points
(`TauCeti.Manifold.brokenGeodesic_eq_brokenMoorePath`).

Sample a free Moore loop `γ` at the `n + 1` times `i L / (n + 1)`, `L` its duration, and suppose
that every point of each of the `n + 1` arcs is at distance less than `r` from the initial vertex
of its arc. The closed broken geodesic through the sampled vertices is then defined
(`TauCeti.Manifold.sampleBrokenGeodesicLoop`), and it is homotopic to `γ`, continuously in `γ`
(`TauCeti.Manifold.sampleBrokenGeodesicLoopHomotopy`). The homotopy runs in two stages.

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
compact-family approximation of the free loop space by broken geodesics, which makes the colimit of
the finite-dimensional approximations `𝓛ⁿM` compute the homology of the free loop space.

## Main definitions

* `TauCeti.Manifold.geodesicInterpolation`: the radial geodesics between points closer than `r`,
  on the unit interval.
* `TauCeti.Manifold.sampleBrokenGeodesicLoop`: the closed broken geodesic through the sampled
  vertices of a free Moore loop with arcs of radius less than `r`.
* `TauCeti.Manifold.brokenPathDurationHomotopy`: the linear change of the arc durations, from the
  broken path with equal arc durations to the closed broken geodesic.
* `TauCeti.Manifold.sampleBrokenGeodesicLoopHomotopy`: the homotopy from the inclusion to the
  closed broken geodesic through the sampled vertices.

## Main results

* `TauCeti.Manifold.brokenGeodesic_eq_brokenMoorePath`: broken geodesics are the broken Moore paths
  of the geodesic interpolation with the distances as durations.
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

/-! ### Geodesic interpolation -/

section Interpolation

include hr

/-- **Geodesic interpolation**: for points `x`, `y` at distance less than `r`, the radial geodesic
`s ↦ exp_x (s • log_x y)` from `x` to `y` on the unit interval, and the constant path at `x`
otherwise. -/
def geodesicInterpolation (p : M × M) : C(unitInterval, M) :=
  if h : dist p.1 p.2 < r then geodesicSegmentUnitPath hr ⟨p, h⟩ else ContinuousMap.const _ p.1

theorem geodesicInterpolation_of_dist_lt (p : M × M) (h : dist p.1 p.2 < r) :
    geodesicInterpolation hr p = geodesicSegmentUnitPath hr ⟨p, h⟩ := by
  simp only [geodesicInterpolation, h, ↓reduceDIte]

/-- **The radial geodesics interpolate** between the points at distance less than `r`. -/
theorem isPathInterpolation_geodesicInterpolation :
    IsPathInterpolation (geodesicInterpolation hr) {p : M × M | dist p.1 p.2 < r} where
  continuousOn := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact ((geodesicSegmentUnitPath hr).continuous.comp
      (continuous_subtype_val.subtype_mk fun p : {p : M × M | dist p.1 p.2 < r} ↦ p.2)).congr
      fun p ↦ (geodesicInterpolation_of_dist_lt hr p.1 p.2).symm
  apply_zero p hp := by
    rw [geodesicInterpolation_of_dist_lt hr p hp, geodesicSegmentUnitPath_zero]
  apply_one p hp := by
    rw [geodesicInterpolation_of_dist_lt hr p hp, geodesicSegmentUnitPath_one]
  apply_diag x hx := by
    ext s
    rw [geodesicInterpolation_of_dist_lt hr _ hx, geodesicSegmentUnitPath_of_eq hr _ rfl]
    rfl

/-- Broken geodesics are the broken Moore paths of the geodesic interpolation in which each arc
lasts the distance between its end points. -/
theorem brokenGeodesic_eq_brokenMoorePath (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    brokenGeodesic hr n q h = brokenMoorePath (isPathInterpolation_geodesicInterpolation hr) n q
      (fun i ↦ nndist (q i.castSucc) (q i.succ)) fun i ↦ ⟨h i, nndist_eq_zero.1⟩ := by
  induction n with
  | zero => rw [brokenGeodesic_zero, brokenMoorePath_zero]
  | succ n ih =>
    have htail : ∀ i : Fin n, dist (Fin.tail q i.castSucc) (Fin.tail q i.succ) < r := fun i ↦ by
      simpa only [Fin.tail, Fin.succ_castSucc] using h i.succ
    rw [brokenGeodesic_succ hr n q h htail, brokenMoorePath_succ _ n q _ _ fun i ↦
      ⟨htail i, nndist_eq_zero.1⟩]
    congr 1
    · rw [geodesicSegment_def, geodesicInterpolation_of_dist_lt hr _ (h 0)]
    · rw [ih _ htail]
      exact brokenMoorePath_congr _ _ _ rfl (funext fun i ↦ by
        simp only [Fin.tail, Fin.succ_castSucc])

end Interpolation

/-! ### Sampled vertices of free loops -/

section Sample

omit [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The vertices `q 0, …, q n, q 0` of a free Moore loop sampled at `n + 1` times are the points
`i / (n + 1)` of its reparametrization to the unit interval. -/
private theorem snoc_sample_eq_toUnitPath {n : ℕ} (γ : MooreFreeLoopSpace M) (i : Fin (n + 2)) :
    (Fin.snoc (γ.toMoorePath.sample (n + 1)) (γ.toMoorePath.sample (n + 1) 0) :
      Fin (n + 2) → M) i = γ.toMoorePath.toUnitPath (unitInterval.arcPoint (n + 1) i 0) := by
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, MoorePath.sample_zero, Fin.val_last,
      unitInterval.arcPoint_self_zero n.succ_pos, MoorePath.toUnitPath_one,
      γ.target_eq_source]
  | cast j =>
    rw [Fin.snoc_castSucc, MoorePath.sample_eq_toUnitPath_arcPoint, Fin.val_castSucc]

omit [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The consecutive sampled vertices of a free Moore loop whose arcs lie within distance `r` of
their initial vertices are at distance less than `r`. -/
private theorem snoc_sample_mem {n : ℕ}
    (γ : MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) (i : Fin (n + 1)) :
    ((Fin.snoc ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1))
        ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) 0) : Fin (n + 2) → M) i.castSucc,
      (Fin.snoc ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1))
        ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) 0) : Fin (n + 2) → M) i.succ) ∈
      {p : M × M | dist p.1 p.2 < r} := by
  rw [snoc_sample_eq_toUnitPath, snoc_sample_eq_toUnitPath, Fin.val_castSucc, Fin.val_succ,
    ← unitInterval.arcPoint_one]
  exact MooreFreeLoopSpace.mem_arcsWithin.1 γ.2 i i.2 1

omit [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- All the sampled vertices of a free Moore loop of length zero are equal. -/
private theorem snoc_sample_eq_of_length_eq_zero {n : ℕ} {γ : MooreFreeLoopSpace M}
    (hγ : γ.length = 0) (i j : Fin (n + 2)) :
    (Fin.snoc (γ.toMoorePath.sample (n + 1)) (γ.toMoorePath.sample (n + 1) 0) :
      Fin (n + 2) → M) i =
      (Fin.snoc (γ.toMoorePath.sample (n + 1)) (γ.toMoorePath.sample (n + 1) 0) :
        Fin (n + 2) → M) j := by
  rw [snoc_sample_eq_toUnitPath, snoc_sample_eq_toUnitPath, MoorePath.toUnitPath_apply,
    MoorePath.toUnitPath_apply, MooreFreeLoopSpace.length_toMoorePath, hγ, zero_mul, zero_mul]

omit [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Each sampled vertex of a free Moore loop whose arcs lie within distance `r` of their initial
vertices is at distance less than `r` from the preceding one. -/
private theorem dist_sample_lt {n : ℕ}
    (γ : MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) (i : Fin (n + 1)) :
    dist ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) i)
      ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) (i - 1)) < r := by
  have h := snoc_sample_mem γ (i - 1)
  rw [mem_ofPred_eq, Fin.snoc_castSucc, Fin.snoc_self_zero_succ, sub_add_cancel] at h
  rwa [dist_comm]

end Sample

/-! ### Changing the durations of the arcs -/

section Duration

variable (n : ℕ)

/-- The duration of the `i`-th arc at time `s` of the homotopy from equal durations to unit
speed: `(1 - s) L / (n + 1) + s d`, for a free loop of duration `L` whose `i`-th and `(i + 1)`-st
sampled vertices are at distance `d`. -/
private def arcDuration (s : unitInterval) (γ : MooreFreeLoopSpace M) (i : Fin (n + 1)) : ℝ≥0 :=
  unitInterval.toNNReal (unitInterval.symm s) * (γ.length / (n + 1)) +
    unitInterval.toNNReal s *
      nndist ((Fin.snoc (γ.toMoorePath.sample (n + 1)) (γ.toMoorePath.sample (n + 1) 0) :
          Fin (n + 2) → M) i.castSucc)
        ((Fin.snoc (γ.toMoorePath.sample (n + 1)) (γ.toMoorePath.sample (n + 1) 0) :
          Fin (n + 2) → M) i.succ)

omit [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- An arc of duration zero joins equal vertices. -/
private theorem eq_of_arcDuration_eq_zero {s : unitInterval} {γ : MooreFreeLoopSpace M}
    {i : Fin (n + 1)} (h : arcDuration n s γ i = 0) :
    (Fin.snoc (γ.toMoorePath.sample (n + 1)) (γ.toMoorePath.sample (n + 1) 0) :
      Fin (n + 2) → M) i.castSucc =
      (Fin.snoc (γ.toMoorePath.sample (n + 1)) (γ.toMoorePath.sample (n + 1) 0) :
        Fin (n + 2) → M) i.succ := by
  obtain ⟨h₁, h₂⟩ := add_eq_zero.1 h
  rcases mul_eq_zero.1 h₂ with hs | hd
  · -- At `s = 0` the duration is `L / (n + 1)`, which only vanishes for a loop of length zero.
    have hs : s = 0 := Subtype.ext (congrArg NNReal.toReal hs)
    rw [hs, unitInterval.symm_zero, unitInterval.toNNReal_one, one_mul,
      div_eq_zero_iff] at h₁
    exact snoc_sample_eq_of_length_eq_zero
      (h₁.resolve_right (by exact_mod_cast n.succ_ne_zero)) _ _
  · exact nndist_eq_zero.1 hd

include hr

/-- The broken Moore paths of the homotopy changing the durations of the arcs. -/
private def arcDurationMap :
    C(unitInterval × MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1),
      MooreFreeLoopSpace M) where
  toFun p := ⟨brokenMoorePath (isPathInterpolation_geodesicInterpolation hr) (n + 1)
      (Fin.snoc ((p.2 : MooreFreeLoopSpace M).toMoorePath.sample (n + 1))
        ((p.2 : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) 0))
      (arcDuration n p.1 (p.2 : MooreFreeLoopSpace M))
      fun i ↦ ⟨snoc_sample_mem p.2 i, eq_of_arcDuration_eq_zero n⟩, by
    rw [target_brokenMoorePath, source_brokenMoorePath, Fin.snoc_last, Fin.snoc_apply_zero]⟩
  continuous_toFun := by
    refine MooreFreeLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 ?_
    have hγ : Continuous fun p : unitInterval ×
        MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) ↦
        (p.2 : MooreFreeLoopSpace M).toMoorePath.sample (n + 1) :=
      (MoorePath.continuous_sample _).comp
        (MooreFreeLoopSpace.continuous_toMoorePath.comp
          (continuous_subtype_val.comp continuous_snd))
    have hq := Continuous.finSnoc (A := fun _ ↦ M) hγ ((continuous_apply 0).comp hγ)
    refine continuous_brokenMoorePath _ (n + 1) hq
      (L := fun (p : unitInterval ×
        MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) i ↦
          arcDuration n p.1 (p.2 : MooreFreeLoopSpace M) i) (continuous_pi fun i ↦ ?_) _
    simp only [arcDuration]
    have hL : Continuous fun p : unitInterval ×
        MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) ↦
        (p.2 : MooreFreeLoopSpace M).length :=
      MooreFreeLoopSpace.continuous_length.comp (continuous_subtype_val.comp continuous_snd)
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
        (dist_sample_lt γ) := by
  refine MooreFreeLoopSpace.ext ?_
  simp only [arcDurationMap, ContinuousMap.coe_mk]
  rw [toMoorePath_brokenGeodesicLoop hr n _ _ fun i ↦ snoc_sample_mem γ i,
    brokenGeodesic_eq_brokenMoorePath hr]
  exact brokenMoorePath_congr _ _ _ rfl (funext fun i ↦ by simp [arcDuration])

/-- **The closed broken geodesic through the sampled vertices** of a free Moore loop whose `n + 1`
arcs lie within distance `r` of their initial vertices, as a continuous map. -/
def sampleBrokenGeodesicLoop :
    C(MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1),
      MooreFreeLoopSpace M) where
  toFun γ := brokenGeodesicLoop hr n ((γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1))
    (dist_sample_lt γ)
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
      exact snoc_sample_eq_toUnitPath (γ : MooreFreeLoopSpace M) i) fun i ↦
        ⟨snoc_sample_mem γ i, fun h ↦ snoc_sample_eq_of_length_eq_zero (by
          rw [MooreFreeLoopSpace.coe_toArcsWithin, MooreFreeLoopSpace.length_toMoorePath] at h
          exact (div_eq_zero_iff.1 h).resolve_right (by positivity)) _ _⟩]
    exact brokenMoorePath_congr _ _ _ rfl (funext fun i ↦ by simp [arcDuration])
  map_one_left := arcDurationMap_one hr n

/-- **Free loops are homotopic to the broken geodesics through their sampled vertices.** On the
free Moore loops whose `n + 1` arcs lie within distance `r` of their initial vertices, a homotopy
from the inclusion to the closed broken geodesic through the sampled vertices: the arcs are first
straightened into geodesics run in equal times, and then run at unit speed. -/
def sampleBrokenGeodesicLoopHomotopy :
    (ContinuousMap.subtypeVal _).Homotopy (sampleBrokenGeodesicLoop hr n) :=
  (MooreFreeLoopSpace.arcStraightening (isPathInterpolation_geodesicInterpolation hr)
    n.succ_pos).trans (brokenPathDurationHomotopy hr n)

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
      (MoorePath.mem_arcsWithin.1 (hN₁ (n + 1) (by omega) ⟨γ, γ.2, rfl⟩))
  have hmaps := hN₂ n (le_of_max_le_right hn) δ hεδ
  let ι : C(K, MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :=
    ⟨fun γ ↦ ⟨γ, hKA γ⟩, continuous_subtype_val.subtype_mk _⟩
  let e : C(K, cyclicDistanceCut (X := M) δ) :=
    ⟨fun γ ↦ ⟨_, hmaps γ.2⟩, ((MoorePath.continuous_sample _).comp
      (MooreFreeLoopSpace.continuous_toMoorePath.comp continuous_subtype_val)).subtype_mk _⟩
  refine ⟨e, fun γ ↦ rfl, ?_⟩
  -- On `K`, `geoⁿ ∘ evₙ` is the closed broken geodesic through the sampled vertices.
  have he : (cyclicDistanceCutBrokenGeodesic hr hδ).comp e =
      (sampleBrokenGeodesicLoop hr n).comp ι :=
    ContinuousMap.ext fun γ ↦ by
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply,
        cyclicDistanceCutBrokenGeodesic_apply,
        sampleBrokenGeodesicLoop_apply hr n _ (dist_sample_lt (ι γ))]
      rfl
  rw [he]
  exact ⟨((sampleBrokenGeodesicLoopHomotopy hr n).compContinuousMap ι).symm⟩

end Compact

end TauCeti.Manifold
