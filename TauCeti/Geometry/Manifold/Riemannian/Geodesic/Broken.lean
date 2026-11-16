/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment
public import TauCeti.Topology.MetricSpace.CyclicDistanceCut
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.FreeLoop
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
on the unit interval.

Concatenating the segments through points `q 0, …, q n` whose consecutive distances are less
than `r` gives the **broken geodesic** `TauCeti.Manifold.brokenGeodesic` through them, of length
the sum of the consecutive distances. Closing it up with the segment from `q n` back to `q 0`
gives the closed broken geodesic, a free Moore loop
(`TauCeti.Manifold.brokenGeodesicLoop`). On the tuples of a cyclic distance cut
`𝓛ⁿM = {q | dist (q i) (q (i - 1)) ≤ δ i}` with all cut-offs below `r`, this is a continuous map

`geoⁿ : 𝓛ⁿM → 𝓛M`

(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`), the map of the finite-dimensional
approximation of the free loop space by broken geodesics. It sends constant tuples to constant
loops of length zero, and because the segment of length zero is a strict unit, it is strictly
compatible with the embedding `ιⁿ : 𝓛ⁿM → 𝓛ⁿ⁺¹M` repeating the first vertex
(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic_repeatFirst`): `geoⁿ⁺¹ ∘ ιⁿ = geoⁿ`.

## Main definitions

* `TauCeti.Manifold.geodesicSegment`: the unit-speed geodesic segment between points at distance
  less than `r`, as a Moore path, continuous in its endpoints.
* `TauCeti.Manifold.brokenGeodesic`: the broken geodesic through a tuple of points.
* `TauCeti.Manifold.brokenGeodesicLoop`: the closed broken geodesic through a cyclic tuple.
* `TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`: the map `geoⁿ` on a distance cut.

## Main results

* `TauCeti.Manifold.dist_geodesicSegment_apply`: the geodesic segment travels at unit speed.
* `TauCeti.Manifold.geodesicSegment_self`: the segment from a point to itself is the constant
  path of length zero.
* `TauCeti.Manifold.length_brokenGeodesic`, `TauCeti.Manifold.length_brokenGeodesicLoop`: the
  length of a broken geodesic is the sum of the distances between consecutive vertices.
* `TauCeti.Manifold.brokenGeodesicLoop_const`: a constant tuple gives the constant loop.
* `TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic_repeatFirst`: `geoⁿ⁺¹ ∘ ιⁿ = geoⁿ`.

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
        riemannianExp I M x.1.1.1 ((x.2 : ℝ) • riemannianLog I M x.1.1.1 (ball 0 r) x.1.1.2),
      (contMDiffOn_riemannianExp_smul_riemannianLog_of_edist_lt hr).continuousOn.comp_continuous
        (f := fun x : {p : M × M // dist p.1 p.2 < r} × unitInterval ↦ ((x.1 : M × M), (x.2 : ℝ)))
        (by fun_prop) fun x ↦ ⟨edist_lt_ofReal.2 x.1.2, x.2.2⟩⟩

theorem geodesicSegmentUnitPath_apply (p : {p : M × M // dist p.1 p.2 < r}) (s : unitInterval) :
    geodesicSegmentUnitPath hr p s =
      riemannianExp I M p.1.1 ((s : ℝ) • riemannianLog I M p.1.1 (ball 0 r) p.1.2) :=
  (rfl)

@[simp]
theorem geodesicSegmentUnitPath_zero (p : {p : M × M // dist p.1 p.2 < r}) :
    geodesicSegmentUnitPath hr p 0 = p.1.1 := by
  simp [geodesicSegmentUnitPath_apply]

@[simp]
theorem geodesicSegmentUnitPath_one (p : {p : M × M // dist p.1 p.2 < r}) :
    geodesicSegmentUnitPath hr p 1 = p.1.2 := by
  rw [geodesicSegmentUnitPath_apply, Set.Icc.coe_one, one_smul]
  exact riemannianExp_riemannianLog ((hr p.1.1).mem_image_riemannianExp_ball subset_rfl p.2)

theorem geodesicSegmentUnitPath_of_eq (p : {p : M × M // dist p.1 p.2 < r}) (hp : p.1.1 = p.1.2)
    (s : unitInterval) : geodesicSegmentUnitPath hr p s = p.1.1 := by
  rw [geodesicSegmentUnitPath_apply, ← hp, (hr _).riemannianLog_self, smul_zero,
    riemannianExp_zero]

/-- **The geodesic segment** from `x` to `y`, for points at distance less than `r`: the Moore path
of length `dist x y` running along the radial geodesic `s ↦ exp_x (s • log_x y)` at unit speed,
so that it is at `exp_x (min (t / dist x y) 1 • log_x y)` at time `t`
(`TauCeti.Manifold.geodesicSegment_apply`). It depends continuously on the pair `(x, y)`, and the
segment from a point to itself is the constant path of length zero
(`TauCeti.Manifold.geodesicSegment_self`). -/
def geodesicSegment : C({p : M × M // dist p.1 p.2 < r}, MoorePath M) where
  toFun p := (MoorePath.ofUnitPath (geodesicSegmentUnitPath hr p)).rescale (nndist p.1.1 p.1.2)
  continuous_toFun := by
    refine (MoorePath.continuous_ofUnitPath.comp
      (geodesicSegmentUnitPath hr).continuous).moorePath_rescale_of_forall_eq_source
      (by fun_prop) fun p hp t ↦ ?_
    have hxy := nndist_eq_zero.1 hp
    simp only [Function.comp_apply, MoorePath.ofUnitPath_apply, MoorePath.source_ofUnitPath,
      geodesicSegmentUnitPath_of_eq hr p hxy]

theorem geodesicSegment_eq (p : {p : M × M // dist p.1 p.2 < r}) :
    geodesicSegment hr p =
      (MoorePath.ofUnitPath (geodesicSegmentUnitPath hr p)).rescale (nndist p.1.1 p.1.2) :=
  (rfl)

@[simp]
theorem length_geodesicSegment (p : {p : M × M // dist p.1 p.2 < r}) :
    (geodesicSegment hr p).length = nndist p.1.1 p.1.2 := by
  rw [geodesicSegment_eq, MoorePath.length_rescale]

/-- The geodesic segment from `x` to `y` is at `exp_x (min (t / dist x y) 1 • log_x y)` at time
`t`. -/
theorem geodesicSegment_apply (p : {p : M × M // dist p.1 p.2 < r}) (t : ℝ≥0) :
    geodesicSegment hr p t = riemannianExp I M p.1.1
      (min ((t : ℝ) / dist p.1.1 p.1.2) 1 • riemannianLog I M p.1.1 (ball 0 r) p.1.2) := by
  rw [geodesicSegment_eq, MoorePath.rescale_apply, MoorePath.ofUnitPath_apply,
    geodesicSegmentUnitPath_apply, Set.coe_projIcc]
  simp [min_comm, div_nonneg]

@[simp]
theorem source_geodesicSegment (p : {p : M × M // dist p.1 p.2 < r}) :
    (geodesicSegment hr p).source = p.1.1 := by
  rw [geodesicSegment_eq, MoorePath.source_rescale, MoorePath.source_ofUnitPath,
    geodesicSegmentUnitPath_zero]

@[simp]
theorem target_geodesicSegment (p : {p : M × M // dist p.1 p.2 < r}) :
    (geodesicSegment hr p).target = p.1.2 := by
  rcases eq_or_ne (nndist p.1.1 p.1.2) 0 with hp | hp
  · rw [geodesicSegment_eq, hp, MoorePath.rescale_zero, MoorePath.target_refl,
      MoorePath.source_ofUnitPath, geodesicSegmentUnitPath_zero, nndist_eq_zero.1 hp]
  · rw [geodesicSegment_eq, MoorePath.target_rescale _ hp, MoorePath.target_ofUnitPath,
      geodesicSegmentUnitPath_one]

/-- The geodesic segment between equal points is the constant Moore path of length zero. -/
theorem geodesicSegment_of_eq (p : {p : M × M // dist p.1 p.2 < r}) (hp : p.1.1 = p.1.2) :
    geodesicSegment hr p = MoorePath.refl p.1.1 := by
  rw [geodesicSegment_eq, nndist_eq_zero.2 hp, MoorePath.rescale_zero,
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

end Segment

/-! ### Broken geodesics -/

section Broken

/-- If consecutive points of `q 0, …, q (n + 1)` are at distance less than `r`, so are those of
`q 1, …, q (n + 1)`. -/
private theorem forall_dist_tail_lt {n : ℕ} {q : Fin (n + 2) → M}
    (h : ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r) (i : Fin n) :
    dist (Fin.tail q i.castSucc) (Fin.tail q i.succ) < r := by
  simpa only [Fin.tail, Fin.succ_castSucc] using h i.succ

include hr

/-- The broken geodesic through `q 0, …, q n`, together with its end points. -/
private def brokenGeodesicAux : (n : ℕ) → (q : Fin (n + 1) → M) →
    (∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) →
    {γ : MoorePath M // γ.source = q 0 ∧ γ.target = q (Fin.last n)}
  | 0, q, _ => ⟨MoorePath.refl (q 0), MoorePath.source_refl _, MoorePath.target_refl _⟩
  | n + 1, q, h =>
    let γ := brokenGeodesicAux n (Fin.tail q) (forall_dist_tail_lt h)
    ⟨(geodesicSegment hr ⟨(q (Fin.castSucc 0), q (Fin.succ 0)), h 0⟩).trans γ.1
        (by rw [target_geodesicSegment, γ.2.1, Fin.tail]),
      by rw [MoorePath.source_trans, source_geodesicSegment]; exact congrArg q Fin.castSucc_zero,
      by rw [MoorePath.target_trans, γ.2.2, Fin.tail, Fin.succ_last]⟩

/-- **The broken geodesic** through points `q 0, …, q n` whose consecutive distances are less than
`r`: the concatenation of the geodesic segments from `q i` to `q (i + 1)`. -/
def brokenGeodesic (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) : MoorePath M :=
  (brokenGeodesicAux hr n q h).1

@[simp]
theorem brokenGeodesic_zero (q : Fin 1 → M) (h : ∀ i : Fin 0, dist (q i.castSucc) (q i.succ) < r) :
    brokenGeodesic hr 0 q h = MoorePath.refl (q 0) := by
  simp only [brokenGeodesic, brokenGeodesicAux]

@[simp]
theorem source_brokenGeodesic (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    (brokenGeodesic hr n q h).source = q 0 :=
  (brokenGeodesicAux hr n q h).2.1

@[simp]
theorem target_brokenGeodesic (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    (brokenGeodesic hr n q h).target = q (Fin.last n) :=
  (brokenGeodesicAux hr n q h).2.2

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
  simp only [brokenGeodesic, brokenGeodesicAux]

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
    (brokenGeodesic hr n q h).length = ∑ i : Fin n, nndist (q i.castSucc) (q i.succ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [brokenGeodesic_succ hr n q h (forall_dist_tail_lt h), MoorePath.length_trans,
      length_geodesicSegment, ih, Fin.sum_univ_succ]
    simp only [Fin.tail, Fin.succ_castSucc]

/-- The broken geodesic through a constant tuple is the constant path of length zero. -/
@[simp]
theorem brokenGeodesic_const (n : ℕ) (x : M)
    (h : ∀ i : Fin n, dist ((fun _ ↦ x : Fin (n + 1) → M) i.castSucc)
      ((fun _ ↦ x : Fin (n + 1) → M) i.succ) < r) :
    brokenGeodesic hr n (fun _ ↦ x) h = MoorePath.refl x := by
  induction n with
  | zero => exact brokenGeodesic_zero hr _ h
  | succ n ih =>
    rw [brokenGeodesic_succ hr n _ h (forall_dist_tail_lt h)]
    simp only [geodesicSegment_self, MoorePath.refl_trans]
    exact ih _

/-- The broken geodesics through the tuples whose consecutive distances are less than `r` depend
continuously on the tuple. -/
theorem continuous_brokenGeodesic (n : ℕ) :
    Continuous fun q : {q : Fin (n + 1) → M // ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r} ↦
      brokenGeodesic hr n q.1 q.2 := by
  induction n with
  | zero =>
    simp only [brokenGeodesic_zero]
    exact MoorePath.continuous_refl.comp ((continuous_apply 0).comp continuous_subtype_val)
  | succ n ih =>
    simp only [fun q : {q : Fin (n + 2) → M //
        ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r} ↦
      brokenGeodesic_succ hr n q.1 q.2 (forall_dist_tail_lt q.2)]
    have hseg : Continuous fun q : {q : Fin (n + 2) → M //
        ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r} ↦
        (⟨(q.1 (Fin.castSucc 0), q.1 (Fin.succ 0)), q.2 0⟩ : {p : M × M // dist p.1 p.2 < r}) :=
      (((continuous_apply _).comp continuous_subtype_val).prodMk
        ((continuous_apply _).comp continuous_subtype_val)).subtype_mk _
    have htail : Continuous fun q : {q : Fin (n + 2) → M //
        ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r} ↦
        (⟨Fin.tail q.1, forall_dist_tail_lt q.2⟩ :
          {q : Fin (n + 1) → M // ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r}) :=
      continuous_subtype_val.finTail.subtype_mk _
    exact ((geodesicSegment hr).continuous.comp hseg).moorePath_trans (ih.comp htail) _

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

end Loop

/-! ### Broken geodesics on a distance cut -/

section Cut

include hr

/-- **The broken geodesics through the tuples of a distance cut**, `geoⁿ : 𝓛ⁿM → 𝓛M`: for cut-offs
`δ i < r`, the closed broken geodesic through each cyclic tuple of the distance cut
`{q | dist (q i) (q (i - 1)) ≤ δ i}`, as a continuous map to the free Moore loop space. -/
def cyclicDistanceCutBrokenGeodesic {n : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r) :
    C(cyclicDistanceCut (X := M) δ, MooreFreeLoopSpace M) where
  toFun q := brokenGeodesicLoop hr n q.1 fun i ↦ (mem_cyclicDistanceCut.1 q.2 i).trans_lt (hδ i)
  continuous_toFun := by
    refine MooreFreeLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 ?_
    have hsnoc : Continuous fun q : cyclicDistanceCut (X := M) δ ↦
        (⟨Fin.snoc q.1 (q.1 0),
          forall_dist_snoc_lt fun i ↦ (mem_cyclicDistanceCut.1 q.2 i).trans_lt (hδ i)⟩ :
          {q : Fin (n + 2) → M // ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r}) :=
      (Continuous.finSnoc (A := fun _ ↦ M) continuous_subtype_val
        ((continuous_apply 0).comp continuous_subtype_val)).subtype_mk _
    exact (continuous_brokenGeodesic hr (n + 1)).comp hsnoc

@[simp]
theorem cyclicDistanceCutBrokenGeodesic_apply {n : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (q : cyclicDistanceCut (X := M) δ) :
    cyclicDistanceCutBrokenGeodesic hr hδ q =
      brokenGeodesicLoop hr n q.1 fun i ↦ (mem_cyclicDistanceCut.1 q.2 i).trans_lt (hδ i) :=
  (rfl)

/-- **`geoⁿ⁺¹ ∘ ιⁿ = geoⁿ`.** The broken geodesics through a tuple of a distance cut and through
the tuple obtained by repeating its first vertex (`TauCeti.cyclicDistanceCutRepeatFirst`) are equal
free Moore loops. -/
theorem cyclicDistanceCutBrokenGeodesic_repeatFirst {n : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + 2) → ℝ} (hδ : ∀ i, δ i < r) (hδ' : ∀ i, δ' i < r) (h₀ : δ 0 ≤ δ' 0)
    (h₁ : 0 ≤ δ' 1) (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ)
    (q : cyclicDistanceCut (X := M) δ) :
    cyclicDistanceCutBrokenGeodesic hr hδ' (cyclicDistanceCutRepeatFirst h₀ h₁ h q) =
      cyclicDistanceCutBrokenGeodesic hr hδ q := by
  simp only [cyclicDistanceCutBrokenGeodesic_apply, coe_cyclicDistanceCutRepeatFirst_apply]
  exact brokenGeodesicLoop_cons hr n q.1 _ _

end Cut

end TauCeti.Manifold
