/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment.Basic
public import TauCeti.Topology.MetricSpace.CyclicDistanceCut
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.FreeLoop
public import TauCeti.Topology.PathSpace.Moore.Lipschitz
import TauCeti.Data.Fin.Basic
public import TauCeti.Topology.PathSpace.Moore.BrokenPath
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing

/-!
# Broken geodesics as Moore loops

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r > 0` be a
radius such that the tangent ball of radius `r` at every point is a normal domain; on a compact
manifold such a radius exists
(`TauCeti.Manifold.exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog`).
Two points `x`, `y` at distance less than `r` are joined by the radial geodesic
`s ↦ exp_x (s • log_x y)`, `s ∈ [0, 1]`, which is minimizing and depends continuously on
`(x, y)`. Travelled at unit speed it is a Moore path of length `dist x y`, the
**geodesic segment** from `x` to `y` (`TauCeti.Manifold.geodesicSegment`): at time `t` it is at
`exp_x (min (t / dist x y) 1 • log_x y)`, and it is an isometry from `[0, dist x y]` onto its
image. The segment from a point to itself is the constant Moore path of length zero, which is a
strict unit for concatenation; this is why the segment is parametrized by arc length rather than
on the unit interval. On the unit interval, the radial geodesics form a path interpolation
`TauCeti.Manifold.geodesicInterpolation` on the pairs of points at distance less than `r`
(`TauCeti.Manifold.isPathInterpolation_geodesicInterpolation`).

Concatenating the segments through points `q 0, …, q n` whose consecutive distances are less
than `r` gives the **broken geodesic** `TauCeti.Manifold.brokenGeodesic` through them, of length
the sum of the consecutive distances. It is the broken Moore path `TauCeti.brokenMoorePath` of
the geodesic interpolation in which each arc lasts the distance between its end points
(`TauCeti.Manifold.brokenGeodesic_eq_brokenMoorePath`). It is `1`-Lipschitz in its time
(`TauCeti.Manifold.lipschitzWith_brokenGeodesic`) and passes through `q i` at the partial sum of
the first `i` consecutive distances (`TauCeti.Manifold.brokenGeodesic_apply_partialSum`).
Closing it up with the segment from `q n` back to `q 0` gives the closed broken geodesic, a free
Moore loop (`TauCeti.Manifold.brokenGeodesicLoop`). On the tuples of a cyclic distance cut
`𝓛ⁿM = {q | dist (q i) (q (i - 1)) ≤ δ i}` with all cut-offs below `r`, this is a continuous map

`geoⁿ : 𝓛ⁿM → 𝓛M`

(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`), the map of the finite-dimensional
approximation of the free loop space by broken geodesics. It sends constant tuples to constant
loops of length zero, and because the segment of length zero is a strict unit, it is strictly
compatible with the embedding `ιⁿ : 𝓛ⁿM → 𝓛ⁿ⁺¹M` repeating the first vertex
(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirst`):
`geoⁿ⁺¹ ∘ ιⁿ = geoⁿ`.

## Main definitions

* `TauCeti.Manifold.geodesicInterpolation`: the radial geodesics between points closer than `r`,
  on the unit interval.
* `TauCeti.Manifold.geodesicSegment`: the unit-speed geodesic segment between points at distance
  less than `r`, as a Moore path, continuous in its endpoints.
* `TauCeti.Manifold.brokenGeodesic`: the broken geodesic through a tuple of points.
* `TauCeti.Manifold.brokenGeodesicLoop`: the closed broken geodesic through a cyclic tuple.
* `TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`: the map `geoⁿ` on a distance cut.

## Main results

* `TauCeti.Manifold.dist_geodesicSegment_apply`: the geodesic segment travels at unit speed.
* `TauCeti.Manifold.lipschitzWith_geodesicSegment`, `TauCeti.Manifold.lipschitzWith_brokenGeodesic`,
  `TauCeti.Manifold.lipschitzWith_brokenGeodesicLoop`: broken geodesics are `1`-Lipschitz.
* `TauCeti.Manifold.geodesicSegment_self`: the segment from a point to itself is the constant
  path of length zero.
* `TauCeti.Manifold.length_brokenGeodesic`, `TauCeti.Manifold.length_brokenGeodesicLoop`: the
  length of a broken geodesic is the sum of the distances between consecutive vertices.
* `TauCeti.Manifold.brokenGeodesic_apply_partialSum`,
  `TauCeti.Manifold.brokenGeodesicLoop_apply_partialSum`: a broken geodesic passes through its
  vertices at the partial sums of the distances between consecutive vertices.
* `TauCeti.Manifold.brokenGeodesicLoop_const`: a constant tuple gives the constant loop.
* `TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirst`:
  `geoⁿ⁺¹ ∘ ιⁿ = geoⁿ`.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2.
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

/-! ### Geodesic segments -/

section Segment

include hr

/-- The radial geodesic from `x` to `y` on the unit interval, as a continuous function of the
pair `(x, y)` of points at distance less than `r`. -/
def geodesicSegmentUnitPath : C({p : M × M // dist p.1 p.2 < r}, C(unitInterval, M)) :=
  ContinuousMap.curry
    ⟨fun x : {p : M × M // dist p.1 p.2 < r} × unitInterval ↦
        riemannianExp I M x.1.val.1 ((x.2 : ℝ) • riemannianLog I M x.1.val.1 (ball 0 r) x.1.val.2),
      (contMDiffOn_riemannianExp_smul_riemannianLog_of_forall_isNormalDomain
        hr).continuousOn.comp_continuous
        (f := fun x : {p : M × M // dist p.1 p.2 < r} × unitInterval ↦ ((x.1 : M × M), (x.2 : ℝ)))
        (by fun_prop) fun x ↦ ⟨edist_lt_ofReal.2 x.1.property, x.2.property⟩⟩

theorem geodesicSegmentUnitPath_apply (p : {p : M × M // dist p.1 p.2 < r}) (s : unitInterval) :
    geodesicSegmentUnitPath hr p s =
      riemannianExp I M p.val.1 ((s : ℝ) • riemannianLog I M p.val.1 (ball 0 r) p.val.2) :=
  (rfl)

@[simp]
theorem geodesicSegmentUnitPath_zero (p : {p : M × M // dist p.1 p.2 < r}) :
    geodesicSegmentUnitPath hr p 0 = p.val.1 := by
  simp [geodesicSegmentUnitPath_apply]

@[simp]
theorem geodesicSegmentUnitPath_one (p : {p : M × M // dist p.1 p.2 < r}) :
    geodesicSegmentUnitPath hr p 1 = p.val.2 := by
  rw [geodesicSegmentUnitPath_apply, Set.Icc.coe_one, one_smul]
  exact riemannianExp_riemannianLog ((hr p.val.1).mem_image_riemannianExp_ball subset_rfl
      p.property)

theorem geodesicSegmentUnitPath_of_eq (p : {p : M × M // dist p.1 p.2 < r}) (hp : p.val.1 = p.val.2)
    (s : unitInterval) : geodesicSegmentUnitPath hr p s = p.val.1 := by
  rw [geodesicSegmentUnitPath_apply, ← hp, (hr _).riemannianLog_self, smul_zero,
    riemannianExp_zero]

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
      (continuous_subtypeVal.subtype_mk fun p : {p : M × M | dist p.1 p.2 < r} ↦ p.property)).congr
      fun p ↦ (geodesicInterpolation_of_dist_lt hr p.val p.property).symm
  apply_zero p hp := by
    rw [geodesicInterpolation_of_dist_lt hr p hp, geodesicSegmentUnitPath_zero]
  apply_one p hp := by
    rw [geodesicInterpolation_of_dist_lt hr p hp, geodesicSegmentUnitPath_one]
  apply_diag x hx := by
    ext s
    rw [geodesicInterpolation_of_dist_lt hr _ hx, geodesicSegmentUnitPath_of_eq hr _ rfl,
      ContinuousMap.const_apply]

/-- **The geodesic segment** from `x` to `y`, for points at distance less than `r`: the Moore path
of length `dist x y` running along the radial geodesic `s ↦ exp_x (s • log_x y)` at unit speed,
so that it is at `exp_x (min (t / dist x y) 1 • log_x y)` at time `t`
(`TauCeti.Manifold.geodesicSegment_apply`). It depends continuously on the pair `(x, y)`, and the
segment from a point to itself is the constant path of length zero
(`TauCeti.Manifold.geodesicSegment_self`). -/
def geodesicSegment : C({p : M × M // dist p.1 p.2 < r}, MoorePath M) where
  toFun p := (MoorePath.ofUnitPath (geodesicSegmentUnitPath hr p)).rescale (nndist p.val.1 p.val.2)
  continuous_toFun :=
    (continuous_rescale_ofUnitPath (isPathInterpolation_geodesicInterpolation hr)
      continuous_subtypeVal (by fun_prop) (fun p ↦ p.property) fun _ ↦ nndist_eq_zero.1).congr
      fun p ↦ congrArg (fun f ↦ (MoorePath.ofUnitPath f).rescale (nndist p.val.1 p.val.2))
        (geodesicInterpolation_of_dist_lt hr p.val p.property)

theorem geodesicSegment_def (p : {p : M × M // dist p.1 p.2 < r}) :
    geodesicSegment hr p =
      (MoorePath.ofUnitPath (geodesicSegmentUnitPath hr p)).rescale (nndist p.val.1 p.val.2) :=
  (rfl)

@[simp]
theorem length_geodesicSegment (p : {p : M × M // dist p.1 p.2 < r}) :
    (geodesicSegment hr p).length = nndist p.val.1 p.val.2 := by
  rw [geodesicSegment_def, MoorePath.length_rescale]

/-- The geodesic segment from `x` to `y` is at `exp_x (min (t / dist x y) 1 • log_x y)` at time
`t`. -/
theorem geodesicSegment_apply (p : {p : M × M // dist p.1 p.2 < r}) (t : ℝ≥0) :
    geodesicSegment hr p t = riemannianExp I M p.val.1
      (min ((t : ℝ) / dist p.val.1 p.val.2) 1 • riemannianLog I M p.val.1 (ball 0 r) p.val.2) := by
  rw [geodesicSegment_def, MoorePath.rescale_apply, MoorePath.ofUnitPath_apply,
    geodesicSegmentUnitPath_apply, Set.coe_projIcc]
  simp [min_comm, div_nonneg]

@[simp]
theorem source_geodesicSegment (p : {p : M × M // dist p.1 p.2 < r}) :
    (geodesicSegment hr p).source = p.val.1 := by
  rw [geodesicSegment_def, MoorePath.source_rescale, MoorePath.source_ofUnitPath,
    geodesicSegmentUnitPath_zero]

@[simp]
theorem target_geodesicSegment (p : {p : M × M // dist p.1 p.2 < r}) :
    (geodesicSegment hr p).target = p.val.2 := by
  rcases eq_or_ne (nndist p.val.1 p.val.2) 0 with hp | hp
  · rw [geodesicSegment_def, hp, MoorePath.rescale_zero, MoorePath.target_refl,
      MoorePath.source_ofUnitPath, geodesicSegmentUnitPath_zero, nndist_eq_zero.1 hp]
  · rw [geodesicSegment_def, MoorePath.target_rescale _ hp, MoorePath.target_ofUnitPath,
      geodesicSegmentUnitPath_one]

/-- The geodesic segment between equal points is the constant Moore path of length zero. -/
theorem geodesicSegment_of_eq (p : {p : M × M // dist p.1 p.2 < r}) (hp : p.val.1 = p.val.2) :
    geodesicSegment hr p = MoorePath.refl p.val.1 := by
  rw [geodesicSegment_def, nndist_eq_zero.2 hp, MoorePath.rescale_zero,
    MoorePath.source_ofUnitPath, geodesicSegmentUnitPath_zero]

/-- The geodesic segment from a point to itself is the constant Moore path of length zero. -/
@[simp]
theorem geodesicSegment_self (x : M) (hx : dist x x < r) :
    geodesicSegment hr ⟨(x, x), hx⟩ = MoorePath.refl x :=
  geodesicSegment_of_eq hr _ rfl

/-- **The geodesic segment travels at unit speed:** two of its points at times `s` and `t` up to
its length `dist x y` are at distance `|s - t|`. -/
theorem dist_geodesicSegment_apply (p : {p : M × M // dist p.1 p.2 < r}) {s t : ℝ≥0}
    (hs : s ≤ (geodesicSegment hr p).length) (ht : t ≤ (geodesicSegment hr p).length) :
    dist (geodesicSegment hr p s) (geodesicSegment hr p t) = |(s : ℝ) - t| := by
  obtain ⟨⟨x, y⟩, hxy⟩ := p
  rw [length_geodesicSegment] at hs ht
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist x y) with h0 | hpos
  · have hd : nndist x y = 0 := by rw [← NNReal.coe_eq_zero, coe_nndist, ← h0]
    rw [hd, nonpos_iff_eq_zero] at hs ht
    simp [hs, ht]
  have hy := (hr x).mem_image_riemannianExp_ball subset_rfl hxy
  -- The logarithm `v = log_x y` has norm `dist x y`, and the segment is `exp_x ((t / ‖v‖) • v)`.
  have hnorm := (hr x).dist_eq_norm_riemannianLog_of_mem_ball subset_rfl
    (by rwa [mem_ball, dist_comm])
  have hmin : ‖riemannianLog I M x (ball 0 r) y‖ ≤
      dist x (riemannianExp I M x (riemannianLog I M x (ball 0 r) y)) := by
    rw [riemannianExp_riemannianLog hy, hnorm]
  have hs' : (s : ℝ) / dist x y ≤ 1 := (div_le_one hpos).2 (by exact_mod_cast hs)
  have ht' : (t : ℝ) / dist x y ≤ 1 := (div_le_one hpos).2 (by exact_mod_cast ht)
  rw [geodesicSegment_apply, geodesicSegment_apply, min_eq_left hs', min_eq_left ht',
    dist_riemannianExp_smul_riemannianExp_smul hmin ⟨by positivity, hs'⟩ ⟨by positivity, ht'⟩,
    ← hnorm, ← sub_div, abs_div, abs_of_pos hpos]
  field_simp

/-- The geodesic segment is `1`-Lipschitz in its time: it travels at unit speed up to its length,
and stops there. -/
theorem lipschitzWith_geodesicSegment (p : {p : M × M // dist p.1 p.2 < r}) :
    LipschitzWith 1 (geodesicSegment hr p) := by
  refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
  rw [← MoorePath.apply_min_length (geodesicSegment hr p) s,
    ← MoorePath.apply_min_length (geodesicSegment hr p) t,
    dist_geodesicSegment_apply hr p (min_le_right _ _) (min_le_right _ _), NNReal.coe_one, one_mul,
    NNReal.dist_eq, NNReal.coe_min, NNReal.coe_min]
  simpa using abs_min_sub_min_le_max (s : ℝ) (geodesicSegment hr p).length t
    (geodesicSegment hr p).length

end Segment

/-! ### Broken geodesics -/

section Broken

/-- If consecutive points of `q 0, …, q (n + 1)` are at distance less than `r`, so are those of
`q 1, …, q (n + 1)`. -/
private theorem forall_dist_tail_lt {n : ℕ} {q : Fin (n + 2) → M}
    (h : ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r) (i : Fin n) :
    dist (Fin.tail q i.castSucc) (Fin.tail q i.succ) < r := by
  simpa only [Fin.tail, Fin.succ_castSucc] using h i.succ

/-- The distances between consecutive vertices of `q 0, …, q (n + 1)`, after the first one, are
those of `q 1, …, q (n + 1)`. -/
private theorem tail_nndist_castSucc_succ {n : ℕ} (q : Fin (n + 2) → M) :
    Fin.tail (fun k : Fin (n + 1) ↦ nndist (q k.castSucc) (q k.succ)) =
      fun k : Fin n ↦ nndist (Fin.tail q k.castSucc) (Fin.tail q k.succ) := by
  funext k
  simp only [Fin.tail, Fin.succ_castSucc]

include hr

/-- **The broken geodesic** through points `q 0, …, q n` whose consecutive distances are less than
`r`: the concatenation of the geodesic segments from `q i` to `q (i + 1)`, that is, the broken
Moore path of the geodesic interpolation in which each arc lasts the distance between its end
points. -/
def brokenGeodesic (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) : MoorePath M :=
  brokenMoorePath (isPathInterpolation_geodesicInterpolation hr) n q
    (fun i ↦ nndist (q i.castSucc) (q i.succ)) fun i ↦ ⟨h i, nndist_eq_zero.1⟩

/-- Broken geodesics are the broken Moore paths of the geodesic interpolation in which each arc
lasts the distance between its end points. -/
theorem brokenGeodesic_eq_brokenMoorePath (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    brokenGeodesic hr n q h = brokenMoorePath (isPathInterpolation_geodesicInterpolation hr) n q
      (fun i ↦ nndist (q i.castSucc) (q i.succ)) fun i ↦ ⟨h i, nndist_eq_zero.1⟩ :=
  (rfl)

@[simp]
theorem brokenGeodesic_zero (q : Fin 1 → M) (h : ∀ i : Fin 0, dist (q i.castSucc) (q i.succ) < r) :
    brokenGeodesic hr 0 q h = MoorePath.refl (q 0) :=
  brokenMoorePath_zero _ _ _ _

@[simp]
theorem source_brokenGeodesic (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    (brokenGeodesic hr n q h).source = q 0 :=
  source_brokenMoorePath _ _ _ _ _

@[simp]
theorem target_brokenGeodesic (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    (brokenGeodesic hr n q h).target = q (Fin.last n) :=
  target_brokenMoorePath _ _ _ _ _

/-- The broken geodesic through `q 0, …, q (n + 1)` is the geodesic segment from `q 0` to `q 1`
followed by the broken geodesic through `q 1, …, q (n + 1)`. -/
theorem brokenGeodesic_succ (n : ℕ) (q : Fin (n + 2) → M)
    (h : ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r)
    (h' : ∀ i : Fin n, dist (Fin.tail q i.castSucc) (Fin.tail q i.succ) < r) :
    brokenGeodesic hr (n + 1) q h =
      (geodesicSegment hr ⟨(q (Fin.castSucc 0), q (Fin.succ 0)), h 0⟩).trans
        (brokenGeodesic hr n (Fin.tail q) h')
        (by
          rw [target_geodesicSegment]
          exact (source_brokenGeodesic hr n (Fin.tail q) h').symm) := by
  rw [brokenGeodesic, brokenMoorePath_succ _ n q _ _ fun i ↦ ⟨h' i, nndist_eq_zero.1⟩]
  congr 1
  rw [geodesicSegment_def, geodesicInterpolation_of_dist_lt hr _ (h 0)]

/-- The broken geodesic only depends on its vertices. -/
theorem brokenGeodesic_congr {n : ℕ} {q q' : Fin (n + 1) → M}
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r)
    (h' : ∀ i : Fin n, dist (q' i.castSucc) (q' i.succ) < r) (hq : q = q') :
    brokenGeodesic hr n q h = brokenGeodesic hr n q' h' := by
  subst hq
  rfl

/-- The length of a broken geodesic is the sum of the distances between consecutive vertices. -/
@[simp]
theorem length_brokenGeodesic (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    (brokenGeodesic hr n q h).length = ∑ i : Fin n, nndist (q i.castSucc) (q i.succ) :=
  length_brokenMoorePath _ _ _ _ _

/-- The broken geodesic through a constant tuple is the constant path of length zero. -/
@[simp]
theorem brokenGeodesic_const (n : ℕ) (x : M)
    (h : ∀ i : Fin n, dist ((fun _ ↦ x : Fin (n + 1) → M) i.castSucc)
      ((fun _ ↦ x : Fin (n + 1) → M) i.succ) < r) :
    brokenGeodesic hr n (fun _ ↦ x) h = MoorePath.refl x := by
  induction n with
  | zero => exact brokenGeodesic_zero hr _ h
  | succ n ih =>
    rw [brokenGeodesic_succ hr n (fun _ ↦ x) h fun _ ↦ h 0]
    simp only [geodesicSegment_self, MoorePath.refl_trans]
    exact ih _

/-- The broken geodesics through the tuples whose consecutive distances are less than `r` depend
continuously on the tuple. -/
theorem continuous_brokenGeodesic (n : ℕ) :
    Continuous fun q : {q : Fin (n + 1) → M // ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r} ↦
      brokenGeodesic hr n q.val q.property :=
  continuous_brokenMoorePath _ n continuous_subtypeVal
    (continuous_pi fun _ ↦ ((continuous_apply _).comp continuous_subtypeVal).nndist
      ((continuous_apply _).comp continuous_subtypeVal)) _

/-- Repeating the first vertex does not change the broken geodesic: the geodesic segment from
`q 0` to itself is the constant path of length zero, a strict unit for concatenation. -/
theorem brokenGeodesic_cons_of_eq (n : ℕ) {x : M} {q : Fin (n + 1) → M} (hx : x = q 0)
    (h : ∀ i : Fin (n + 1), dist ((Fin.cons x q : Fin (n + 2) → M) i.castSucc)
      ((Fin.cons x q : Fin (n + 2) → M) i.succ) < r)
    (h' : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    brokenGeodesic hr (n + 1) (Fin.cons x q) h = brokenGeodesic hr n q h' := by
  rw [brokenGeodesic_succ hr n _ h (by simpa only [Fin.tail_cons] using h')]
  have hseg : geodesicSegment hr ⟨((Fin.cons x q : Fin (n + 2) → M) (Fin.castSucc 0),
      (Fin.cons x q : Fin (n + 2) → M) (Fin.succ 0)), h 0⟩ = MoorePath.refl x :=
    geodesicSegment_of_eq hr _ (by simp [hx])
  simp only [hseg, MoorePath.refl_trans]
  exact brokenGeodesic_congr hr _ _ (Fin.tail_cons _ _)

/-- A broken geodesic is `1`-Lipschitz in its time. -/
theorem lipschitzWith_brokenGeodesic (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    LipschitzWith 1 (brokenGeodesic hr n q h) := by
  induction n with
  | zero =>
    rw [brokenGeodesic_zero]
    exact MoorePath.lipschitzWith_refl _ _
  | succ n ih =>
    rw [brokenGeodesic_succ hr n q h (forall_dist_tail_lt h)]
    exact MoorePath.lipschitzWith_trans _ (lipschitzWith_geodesicSegment hr _) (ih _ _)

/-- **The broken geodesic passes through its vertices at the partial sums of the distances:** it is
at `q i` at the time `d(q 0, q 1) + ⋯ + d(q (i - 1), q i)`. -/
theorem brokenGeodesic_apply_partialSum (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) (i : Fin (n + 1)) :
    brokenGeodesic hr n q h
      (Fin.partialSum (fun k : Fin n ↦ nndist (q k.castSucc) (q k.succ)) i) = q i := by
  induction n with
  | zero =>
    rw [Fin.fin_one_eq_zero i, Fin.partialSum_zero, brokenGeodesic_zero, MoorePath.refl_apply]
  | succ n ih =>
    rw [brokenGeodesic_succ hr n q h (forall_dist_tail_lt h)]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [Fin.partialSum_zero, ← MoorePath.source_def, MoorePath.source_trans,
        source_geodesicSegment]
      exact congrArg q Fin.castSucc_zero
    · rw [Fin.partialSum_succ', tail_nndist_castSucc_succ,
        ← length_geodesicSegment hr ⟨(q (Fin.castSucc 0), q (Fin.succ 0)), h 0⟩,
        MoorePath.trans_apply_length_add]
      exact ih (Fin.tail q) (forall_dist_tail_lt h) j

/-- The length of a broken geodesic is the last partial sum of the distances between consecutive
vertices: the broken geodesic reaches its last vertex at its length. -/
theorem length_brokenGeodesic_eq_partialSum (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    (brokenGeodesic hr n q h).length =
      Fin.partialSum (fun k : Fin n ↦ nndist (q k.castSucc) (q k.succ)) (Fin.last n) := by
  rw [length_brokenGeodesic, Fin.partialSum_last]

end Broken

/-! ### Closed broken geodesics -/

section Loop

/-- If every point of a cyclic tuple `q 0, …, q n` is at distance less than `r` from the preceding
one, `q n` preceding `q 0`, then consecutive points of `q 0, …, q n, q 0` are at distance less than
`r`. -/
private theorem forall_dist_snoc_lt {n : ℕ} {q : Fin (n + 1) → M}
    (h : ∀ i, dist (q i) (q (i - 1)) < r) (i : Fin (n + 1)) :
    dist ((Fin.snoc q (q 0) : Fin (n + 2) → M) i.castSucc)
      ((Fin.snoc q (q 0) : Fin (n + 2) → M) i.succ) < r := by
  rw [Fin.snoc_castSucc, Fin.snoc_self_zero_succ, dist_comm]
  simpa only [add_sub_cancel_right] using h (i + 1)

/-- The edges of `q 0, …, q n, q 0` are the cyclic edges of `q`. -/
private theorem nndist_snoc_castSucc_succ {n : ℕ} (q : Fin (n + 1) → M) :
    (fun k : Fin (n + 1) ↦ nndist ((Fin.snoc q (q 0) : Fin (n + 2) → M) k.castSucc)
      ((Fin.snoc q (q 0) : Fin (n + 2) → M) k.succ)) = fun k ↦ nndist (q k) (q (k + 1)) :=
  funext fun k ↦ by rw [Fin.snoc_castSucc, Fin.snoc_self_zero_succ]

include hr

/-- **The closed broken geodesic** through a cyclic tuple `q 0, …, q n` in which every point is at
distance less than `r` from the preceding one, `q n` preceding `q 0`: the free Moore loop at `q 0`
concatenating the geodesic segments from `q 0` to `q 1`, …, from `q (n - 1)` to `q n`, and from
`q n` back to `q 0`. -/
def brokenGeodesicLoop (n : ℕ) (q : Fin (n + 1) → M) (h : ∀ i, dist (q i) (q (i - 1)) < r) :
    MooreFreeLoopSpace M where
  toMoorePath := brokenGeodesic hr (n + 1) (Fin.snoc q (q 0)) (forall_dist_snoc_lt h)
  target_eq_source := by
    rw [target_brokenGeodesic, source_brokenGeodesic, Fin.snoc_last, Fin.snoc_apply_zero]

/-- The closed broken geodesic through `q 0, …, q n` is the broken geodesic through
`q 0, …, q n, q 0`. -/
theorem toMoorePath_brokenGeodesicLoop (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i, dist (q i) (q (i - 1)) < r)
    (h' : ∀ i : Fin (n + 1), dist ((Fin.snoc q (q 0) : Fin (n + 2) → M) i.castSucc)
      ((Fin.snoc q (q 0) : Fin (n + 2) → M) i.succ) < r) :
    (brokenGeodesicLoop hr n q h).toMoorePath = brokenGeodesic hr (n + 1) (Fin.snoc q (q 0)) h' :=
  (rfl)

@[simp]
theorem basepoint_brokenGeodesicLoop (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i, dist (q i) (q (i - 1)) < r) :
    (brokenGeodesicLoop hr n q h).basepoint = q 0 := by
  rw [← MooreFreeLoopSpace.source_toMoorePath,
    toMoorePath_brokenGeodesicLoop hr n q h (forall_dist_snoc_lt h), source_brokenGeodesic,
    Fin.snoc_apply_zero]

/-- The length of the closed broken geodesic through a cyclic tuple is the sum of the distances
from each point to the preceding one. -/
@[simp]
theorem length_brokenGeodesicLoop (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i, dist (q i) (q (i - 1)) < r) :
    (brokenGeodesicLoop hr n q h).length = ∑ i, nndist (q i) (q (i - 1)) := by
  rw [← MooreFreeLoopSpace.length_toMoorePath,
    toMoorePath_brokenGeodesicLoop hr n q h (forall_dist_snoc_lt h), length_brokenGeodesic,
    ← Equiv.sum_comp (Equiv.addRight 1) fun i ↦ nndist (q i) (q (i - 1))]
  simp only [Fin.snoc_castSucc, Fin.snoc_self_zero_succ, Equiv.coe_addRight, add_sub_cancel_right,
    nndist_comm]

/-- The closed broken geodesic through a constant tuple is the constant loop of length zero. -/
@[simp]
theorem brokenGeodesicLoop_const (n : ℕ) (x : M)
    (h : ∀ i : Fin (n + 1), dist ((fun _ ↦ x : Fin (n + 1) → M) i)
      ((fun _ ↦ x : Fin (n + 1) → M) (i - 1)) < r) :
    brokenGeodesicLoop hr n (fun _ ↦ x) h = MooreFreeLoopSpace.const x := by
  ext1
  rw [toMoorePath_brokenGeodesicLoop hr n _ h (forall_dist_snoc_lt h),
    MooreFreeLoopSpace.toMoorePath_const, ← brokenGeodesic_const hr (n + 1) x (fun _ ↦ h 0)]
  refine brokenGeodesic_congr hr _ _ (funext fun i ↦ ?_)
  induction i using Fin.cases with
  | zero => rw [Fin.snoc_apply_zero]
  | succ j => rw [Fin.snoc_self_zero_succ]

/-- Repeating the first vertex of a cyclic tuple does not change its closed broken geodesic. -/
theorem brokenGeodesicLoop_cons (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i, dist (q i) (q (i - 1)) < r)
    (h' : ∀ i, dist ((Fin.cons (q 0) q : Fin (n + 2) → M) i)
      ((Fin.cons (q 0) q : Fin (n + 2) → M) (i - 1)) < r) :
    brokenGeodesicLoop hr (n + 1) (Fin.cons (q 0) q) h' = brokenGeodesicLoop hr n q h := by
  ext1
  rw [toMoorePath_brokenGeodesicLoop hr _ _ h' (forall_dist_snoc_lt h'),
    toMoorePath_brokenGeodesicLoop hr n q h (forall_dist_snoc_lt h)]
  have hq : (Fin.snoc (Fin.cons (q 0) q : Fin (n + 2) → M) ((Fin.cons (q 0) q : Fin (n + 2) → M) 0)
      : Fin (n + 3) → M) = Fin.cons (q 0) (Fin.snoc q (q 0) : Fin (n + 2) → M) := by
    rw [Fin.cons_zero, Fin.cons_snoc_eq_snoc_cons]
  rw [brokenGeodesic_congr hr _ (hq ▸ forall_dist_snoc_lt h') hq]
  exact brokenGeodesic_cons_of_eq hr (n + 1)
    (by rw [Fin.snoc_apply_zero]) _ _

/-- A closed broken geodesic is `1`-Lipschitz in its time. -/
theorem lipschitzWith_brokenGeodesicLoop (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i, dist (q i) (q (i - 1)) < r) :
    LipschitzWith 1 (brokenGeodesicLoop hr n q h).toMoorePath := by
  rw [toMoorePath_brokenGeodesicLoop hr n q h (forall_dist_snoc_lt h)]
  exact lipschitzWith_brokenGeodesic hr _ _ _

/-- **The closed broken geodesic passes through its vertices at the partial sums of the distances:**
it is at `q i` at the time `d(q 0, q 1) + ⋯ + d(q (i - 1), q i)`. -/
theorem brokenGeodesicLoop_apply_partialSum (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i, dist (q i) (q (i - 1)) < r) (i : Fin (n + 1)) :
    (brokenGeodesicLoop hr n q h).toMoorePath
      (Fin.partialSum (fun k ↦ nndist (q k) (q (k + 1))) i.castSucc) = q i := by
  rw [toMoorePath_brokenGeodesicLoop hr n q h (forall_dist_snoc_lt h),
    ← nndist_snoc_castSucc_succ q,
    brokenGeodesic_apply_partialSum, Fin.snoc_castSucc]

/-- The length of the closed broken geodesic through `q 0, …, q n` is the last partial sum
`d(q 0, q 1) + ⋯ + d(q (n - 1), q n) + d(q n, q 0)` of its cyclic edges. -/
theorem length_brokenGeodesicLoop_eq_partialSum (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i, dist (q i) (q (i - 1)) < r) :
    (brokenGeodesicLoop hr n q h).length =
      Fin.partialSum (fun k ↦ nndist (q k) (q (k + 1))) (Fin.last (n + 1)) := by
  rw [← MooreFreeLoopSpace.length_toMoorePath,
    toMoorePath_brokenGeodesicLoop hr n q h (forall_dist_snoc_lt h), ← nndist_snoc_castSucc_succ q,
    length_brokenGeodesic_eq_partialSum]

end Loop

/-! ### Broken geodesics on a distance cut -/

section Cut

include hr

/-- **The broken geodesics through the tuples of a distance cut**, `geoⁿ : 𝓛ⁿM → 𝓛M`: for cut-offs
`δ i < r`, the closed broken geodesic through each cyclic tuple of the distance cut
`{q | dist (q i) (q (i - 1)) ≤ δ i}`, as a continuous map to the free Moore loop space. -/
def cyclicDistanceCutBrokenGeodesic {n : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r) :
    C(cyclicDistanceCut (X := M) δ, MooreFreeLoopSpace M) where
  toFun q := brokenGeodesicLoop hr n q.val fun i ↦ (mem_cyclicDistanceCut.1 q.property i).trans_lt
      (hδ i)
  continuous_toFun := by
    refine MooreFreeLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 ?_
    have hsnoc : Continuous fun q : cyclicDistanceCut (X := M) δ ↦
        (⟨Fin.snoc q.val (q.val 0),
          forall_dist_snoc_lt fun i ↦ (mem_cyclicDistanceCut.1 q.property i).trans_lt (hδ i)⟩ :
          {q : Fin (n + 2) → M // ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r}) :=
      (Continuous.finSnoc (A := fun _ ↦ M) continuous_subtypeVal
        ((continuous_apply 0).comp continuous_subtypeVal)).subtype_mk _
    exact (continuous_brokenGeodesic hr (n + 1)).comp hsnoc

@[simp]
theorem cyclicDistanceCutBrokenGeodesic_apply {n : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (q : cyclicDistanceCut (X := M) δ) :
    cyclicDistanceCutBrokenGeodesic hr hδ q =
      brokenGeodesicLoop hr n q.val fun i ↦ (mem_cyclicDistanceCut.1 q.property i).trans_lt (hδ i)
          :=
  (rfl)

/-- **`geoⁿ⁺¹ ∘ ιⁿ = geoⁿ`.** The broken geodesics through a tuple of a distance cut and through
the tuple obtained by repeating its first vertex (`TauCeti.cyclicDistanceCutRepeatFirst`) are equal
free Moore loops. -/
theorem cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirst {n : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + 2) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ i, δ' i < r) (h₀ : δ 0 ≤ δ' 0)
    (h₁ : 0 ≤ δ' 1) (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ)
    (q : cyclicDistanceCut (X := M) δ) :
    cyclicDistanceCutBrokenGeodesic hr hδ' (cyclicDistanceCutRepeatFirst h₀ h₁ h q) =
      cyclicDistanceCutBrokenGeodesic hr hδ q := by
  simp only [cyclicDistanceCutBrokenGeodesic_apply, coe_cyclicDistanceCutRepeatFirst_apply]
  exact brokenGeodesicLoop_cons hr n q.val _ _

/-- The length of the closed broken geodesic through a tuple of a distance cut is at most the sum of
the cut-offs. -/
theorem length_cyclicDistanceCutBrokenGeodesic_le {n : ℕ} {δ : Fin (n + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (q : cyclicDistanceCut (X := M) δ) :
    ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) ≤ ∑ i, δ i := by
  rw [cyclicDistanceCutBrokenGeodesic_apply, length_brokenGeodesicLoop, NNReal.coe_sum]
  exact Finset.sum_le_sum fun i _ ↦ by
    rw [coe_nndist]
    exact mem_cyclicDistanceCut.1 q.property i

end Cut

end TauCeti.Manifold
