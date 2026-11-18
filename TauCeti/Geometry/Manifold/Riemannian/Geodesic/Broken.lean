/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Segment
public import TauCeti.Topology.MetricSpace.CyclicDistanceCut
public import TauCeti.Topology.PathSpace.Moore.Between.Concat
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic
public import TauCeti.Topology.PathSpace.Moore.FreeLoop

import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing

/-!
# Broken geodesics as Moore paths

Let `M` be a Riemannian manifold and `r > 0` a radius such that the tangent ball of radius `r` at
every point is a normal domain; on a compact manifold such a radius exists by
`TauCeti.Manifold.exists_pos_contMDiffAt_riemannianExp_smul_riemannianLog`. Two points `x, y` at
distance less than `r` are joined by the short geodesic `t ↦ exp_x (t • log_x y)`, `t ∈ [0, 1]`,
which depends continuously, indeed smoothly, on `(x, y, t)`.

Parametrized by arc length, this geodesic is a Moore path of duration `dist x y`
(`TauCeti.Manifold.shortGeodesic`): its points at times `s, t ≤ dist x y` are at distance
`|s - t|` (`TauCeti.Manifold.dist_shortGeodesic_apply`), so it is a minimizing segment travelled at
unit speed. It varies continuously with the pair of points, also where the two points come
together, where it shrinks to the constant path of length zero
(`TauCeti.Manifold.continuous_shortGeodesic`, `TauCeti.Manifold.shortGeodesic_self`).

A tuple `q 0, …, q n` of points with consecutive distances less than `r` is the vertex tuple of a
**broken geodesic**, the concatenation of the short geodesics from each vertex to the next
(`TauCeti.Manifold.brokenGeodesic`); its duration is the sum of the consecutive distances. A
cyclic tuple whose consecutive distances, including the closing one from `q n` back to `q 0`, are
bounded by cut-offs below `r` is the vertex tuple of a closed broken geodesic. On Abouzaid's
distance cut `𝓛ⁿM = {q | d(q i, q (i - 1)) ≤ δ i}` (`TauCeti.cyclicDistanceCut`) this gives the
continuous map to the free Moore loops (`TauCeti.Manifold.brokenGeodesicLoop`)

`geoⁿ : 𝓛ⁿM → 𝓛M`

sending a tuple to the closed broken geodesic through it, based at `q 0` and parametrized at unit
speed. Repeating the first vertex adds a segment of length zero, which concatenation drops on
the nose, so `geoⁿ⁺¹ ∘ ιⁿ = geoⁿ` for the embeddings `ιⁿ : 𝓛ⁿM → 𝓛ⁿ⁺¹M` repeating the first
vertex (`TauCeti.Manifold.brokenGeodesicLoop_cyclicDistanceCutRepeatFirst`), and the maps `geoⁿ`
induce a map out of the colimit of the distance cuts along the `ιⁿ`. These are the maps through
which Abouzaid compares the free loop space with its finite-dimensional approximations by broken
geodesics. A constant tuple goes to the constant loop of length zero
(`TauCeti.Manifold.brokenGeodesicLoop_const`).

## Main definitions

* `TauCeti.Manifold.shortGeodesic`: the unit-speed short geodesic from `x` to `y` as a Moore path.
* `TauCeti.Manifold.brokenGeodesic`: the broken geodesic through a tuple of nearby points.
* `TauCeti.Manifold.brokenGeodesicLoop`: the closed broken geodesic through the vertices of a
  tuple of the distance cut, as a continuous map to the free Moore loops.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24, EMS, 2015, §11.2.
-/

public noncomputable section

open Bundle Set Function Topology
open scoped NNReal Manifold ContDiff

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ}

/-! ### Short geodesics -/

/-- The radial geodesic `exp_x (t • log_x y)` from `x` towards `y`. -/
private abbrev segment (r : ℝ) (p : (M × M) × ℝ) : M :=
  riemannianExp I M p.1.1 (p.2 • riemannianLog I M p.1.1 (Metric.ball 0 r) p.1.2)

/-- The radial geodesics from `x` towards points `y` at distance less than `r` are jointly
continuous in `(x, y, t)` for `t ∈ [0, 1]`. -/
private theorem continuousOn_segment (hr : ∀ q : M, IsNormalDomain I M q (Metric.ball 0 r)) :
    ContinuousOn (segment (I := I) r) ({p : M × M | dist p.1 p.2 < r} ×ˢ Icc 0 1) := by
  have h := (contMDiffOn_riemannianExp_smul_riemannianLog (I := I) (M := M) isOpen_univ
    fun q _ ↦ hr q).continuousOn
  refine h.mono fun p hp ↦ ⟨⟨mem_univ _, ?_⟩, hp.2⟩
  rw [(hr p.1.1).image_riemannianExp_ball_eq_ball subset_rfl, Metric.mem_ball']
  exact hp.1

omit [IsRiemannianManifold I M] in
private theorem segment_zero (x y : M) : segment (I := I) r ((x, y), 0) = x := by
  simp [segment]

omit [IsRiemannianManifold I M] in
private theorem segment_self (hr : ∀ q : M, IsNormalDomain I M q (Metric.ball 0 r)) (x : M)
    (t : ℝ) : segment (I := I) r ((x, x), t) = x := by
  simp [segment, (hr x).riemannianLog_self]

private theorem segment_one (hr : ∀ q : M, IsNormalDomain I M q (Metric.ball 0 r)) {x y : M}
    (h : dist x y < r) : segment (I := I) r ((x, y), 1) = y := by
  rw [segment, one_smul, riemannianExp_riemannianLog]
  rw [(hr x).image_riemannianExp_ball_eq_ball subset_rfl, Metric.mem_ball']
  exact h

/-- The short geodesic from `x` to `y` on the unit interval. -/
private def segmentUnitPath (hr : ∀ q : M, IsNormalDomain I M q (Metric.ball 0 r)) {x y : M}
    (h : dist x y < r) : C(unitInterval, M) :=
  ⟨fun t ↦ segment (I := I) r ((x, y), t), (continuousOn_segment hr).comp_continuous
    (by fun_prop) fun t ↦ ⟨h, t.2⟩⟩

private theorem continuous_segmentUnitPath
    (hr : ∀ q : M, IsNormalDomain I M q (Metric.ball 0 r)) :
    Continuous fun p : {p : M × M // dist p.1 p.2 < r} ↦ segmentUnitPath hr p.2 :=
  ContinuousMap.continuous_of_continuous_uncurry _ <| (continuousOn_segment hr).comp_continuous
    (by fun_prop) fun p ↦ ⟨p.1.2, p.2.2⟩

variable (hr : ∀ q : M, IsNormalDomain I M q (Metric.ball 0 r))

/-- The **short geodesic** from `x` to `y`, for points at distance less than `r`: the radial
geodesic `exp_x (t • log_x y)` parametrized by arc length, as a Moore path of duration
`dist x y`. -/
def shortGeodesic (x y : M) (h : dist x y < r) : MoorePathBetween M x y :=
  ⟨(MoorePath.ofUnitPath (segmentUnitPath hr h)).rescale (nndist x y),
    by simp [segmentUnitPath, segment_zero],
    by
      rcases eq_or_ne (nndist x y) 0 with h0 | h0
      · rw [nndist_eq_zero] at h0
        subst h0
        simp [segmentUnitPath, segment_zero]
      · simp [h0, segmentUnitPath, segment_one hr h]⟩

theorem shortGeodesic_apply {x y : M} (h : dist x y < r) (t : ℝ≥0) :
    (shortGeodesic hr x y h).toMoorePath t = riemannianExp I M x
      ((projIcc 0 1 zero_le_one ((t : ℝ) / dist x y) : ℝ) •
        riemannianLog I M x (Metric.ball 0 r) y) := by
  simp [shortGeodesic, segmentUnitPath, MoorePath.ofUnitPath_apply, segment]

@[simp]
theorem length_shortGeodesic {x y : M} (h : dist x y < r) :
    (shortGeodesic hr x y h).toMoorePath.length = nndist x y := by
  simp [shortGeodesic]

/-- The short geodesic from a point to itself is the constant path of length zero. -/
@[simp]
theorem shortGeodesic_self (x : M) (h : dist x x < r) :
    (shortGeodesic hr x x h).toMoorePath = MoorePath.refl x := by
  simpa using MoorePath.eq_refl_of_length_eq_zero (length_shortGeodesic hr h |>.trans (by simp))

/-- **Short geodesics travel at unit speed**: the points of the short geodesic from `x` to `y` at
times `s, t ≤ dist x y` are at distance `|s - t|`. In particular the short geodesic is a
minimizing segment, of length `dist x y`. -/
theorem dist_shortGeodesic_apply {x y : M} (h : dist x y < r) {s t : ℝ≥0}
    (hs : (s : ℝ) ≤ dist x y) (ht : (t : ℝ) ≤ dist x y) :
    dist ((shortGeodesic hr x y h).toMoorePath s) ((shortGeodesic hr x y h).toMoorePath t) =
      |(s : ℝ) - t| := by
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist x y) with h0 | h0
  · have hs0 : (s : ℝ) = 0 := le_antisymm (h0 ▸ hs) s.2
    have ht0 : (t : ℝ) = 0 := le_antisymm (h0 ▸ ht) t.2
    simp [shortGeodesic_apply, hs0, ht0]
  have hlog : dist x y = ‖riemannianLog I M x (Metric.ball 0 r) y‖ :=
    (hr x).dist_eq_norm_riemannianLog_of_mem_ball subset_rfl (Metric.mem_ball'.2 h)
  have hmin : ‖riemannianLog I M x (Metric.ball 0 r) y‖ ≤
      dist x (riemannianExp I M x (riemannianLog I M x (Metric.ball 0 r) y)) := by
    rw [riemannianExp_riemannianLog, ← hlog]
    rw [(hr x).image_riemannianExp_ball_eq_ball subset_rfl, Metric.mem_ball']
    exact h
  have hmem : ∀ u : ℝ≥0, (u : ℝ) ≤ dist x y → (u : ℝ) / dist x y ∈ Icc (0 : ℝ) 1 :=
    fun u hu ↦ ⟨div_nonneg u.2 h0.le, (div_le_one h0).2 hu⟩
  rw [shortGeodesic_apply, shortGeodesic_apply, projIcc_of_mem _ (hmem s hs),
    projIcc_of_mem _ (hmem t ht),
    dist_riemannianExp_smul_riemannianExp_smul hmin (hmem s hs) (hmem t ht), ← hlog,
    ← sub_div, abs_div, abs_of_pos h0, div_mul_cancel₀ _ h0.ne']

/-- **Short geodesics depend continuously on their endpoints**, as Moore paths, also where the two
endpoints come together. -/
theorem continuous_shortGeodesic :
    Continuous fun p : {p : M × M // dist p.1 p.2 < r} ↦
      (shortGeodesic hr p.1.1 p.1.2 p.2).toMoorePath := by
  simp only [shortGeodesic, MoorePathBetween.toMoorePath_mk]
  refine (MoorePath.continuous_ofUnitPath.comp
    (continuous_segmentUnitPath hr)).moorePath_rescale_of_forall_eq_source (by fun_prop)
    fun p hp t ↦ ?_
  rw [nndist_eq_zero] at hp
  obtain ⟨⟨x, y⟩, hxy⟩ := p
  simp only at hp
  subst hp
  simp [MoorePath.ofUnitPath_apply, segmentUnitPath, segment_self hr]

/-! ### Broken geodesics -/

/-- The **broken geodesic** through points `q 0, …, q n` at consecutive distances less than `r`:
the concatenation of the short geodesics from each `q i` to the next, a Moore path from `q 0` to
`q n` of duration the sum of the consecutive distances. -/
def brokenGeodesic {n : ℕ} (q : Fin (n + 1) → M)
    (hq : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    MoorePathBetween M (q 0) (q (Fin.last n)) :=
  MoorePathBetween.concat q (fun i : Fin n ↦ (shortGeodesic hr _ _ (hq i)).toMoorePath)
    fun _ ↦ ⟨MoorePathBetween.source _, MoorePathBetween.target _⟩

/-- The broken geodesic through `q 0, q 1, …` runs along the short geodesic from `q 0` to `q 1`
and then along the broken geodesic through `q 1, q 2, …`. -/
theorem toMoorePath_brokenGeodesic_succ {n : ℕ} (q : Fin (n + 2) → M)
    (hq : ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r) :
    (brokenGeodesic hr q hq).toMoorePath = (shortGeodesic hr _ _ (hq 0)).toMoorePath.trans
      (brokenGeodesic hr (Fin.tail q) fun i ↦ by simpa [Fin.tail] using hq i.succ).toMoorePath
      (by rw [MoorePathBetween.target, MoorePathBetween.source]; rfl) := by
  simp only [brokenGeodesic, MoorePathBetween.toMoorePath_concat_succ]
  -- The pieces of the remaining concatenation are the short geodesics between the vertices of
  -- `Fin.tail q`, indexed through `Fin.tail` on one side and evaluated on `Fin.tail q` on the
  -- other; the two agree by unfolding `Fin.tail`.
  rfl

/-- The duration of a broken geodesic is the sum of the distances between consecutive vertices. -/
@[simp]
theorem length_brokenGeodesic {n : ℕ} (q : Fin (n + 1) → M)
    (hq : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r) :
    (brokenGeodesic hr q hq).toMoorePath.length =
      ∑ i : Fin n, nndist (q i.castSucc) (q i.succ) := by
  simp [brokenGeodesic]

/-- A repeated first vertex can be dropped: if `q 0 = q 1`, the broken geodesic through
`q 0, q 1, …` is the broken geodesic through `q 1, q 2, …`, as a Moore path. -/
theorem toMoorePath_brokenGeodesic_succ_of_eq {n : ℕ} (q : Fin (n + 2) → M)
    (hq : ∀ i : Fin (n + 1), dist (q i.castSucc) (q i.succ) < r) (h01 : q 0 = q 1) :
    (brokenGeodesic hr q hq).toMoorePath =
      (brokenGeodesic hr (Fin.tail q) fun i ↦ by simpa [Fin.tail] using hq i.succ).toMoorePath :=
  MoorePathBetween.toMoorePath_concat_succ_of_length_eq_zero _ (by
    simp only [length_shortGeodesic, nndist_eq_zero]
    exact h01)

private theorem toMoorePath_brokenGeodesic_congr {n : ℕ} {q q' : Fin (n + 1) → M}
    (hq : ∀ i : Fin n, dist (q i.castSucc) (q i.succ) < r)
    (hq' : ∀ i : Fin n, dist (q' i.castSucc) (q' i.succ) < r) (h : q = q') :
    (brokenGeodesic hr q hq).toMoorePath = (brokenGeodesic hr q' hq').toMoorePath := by
  subst h
  rfl

/-- **Broken geodesics depend continuously on their vertices.** -/
theorem continuous_brokenGeodesic {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    {q : Y → Fin (n + 1) → M} (hq : Continuous q)
    (hqr : ∀ y, ∀ i : Fin n, dist (q y i.castSucc) (q y i.succ) < r) :
    Continuous fun y ↦ (brokenGeodesic hr (q y) (hqr y)).toMoorePath :=
  MoorePathBetween.continuous_concat _ (by fun_prop) fun i ↦
    (continuous_shortGeodesic hr).comp (f := fun y ↦ ⟨(q y i.castSucc, q y i.succ), hqr y i⟩)
      (by fun_prop)

/-! ### Closed broken geodesics on the distance cut -/

variable {n : ℕ} {δ : Fin (n + 1) → ℝ}

/-- **The closed broken geodesics through the tuples of the distance cut**, `geoⁿ : 𝓛ⁿM → 𝓛M`:
for cut-offs below `r`, the map sending `(q 0, …, q n)` to the closed broken geodesic through
`q 0, …, q n` and back to `q 0`, based at `q 0` and parametrized at unit speed. -/
def brokenGeodesicLoop (hδ : ∀ i, δ i < r) :
    C(cyclicDistanceCut (X := M) δ, MooreFreeLoopSpace M) where
  toFun q := ⟨(brokenGeodesic hr (Fin.snoc q.1 (q.1 0))
    fun i ↦ (dist_snoc_le_of_mem_cyclicDistanceCut q.2 i).trans_lt (hδ _)).toMoorePath, by simp⟩
  continuous_toFun := by
    have hc : Continuous fun q : cyclicDistanceCut (X := M) δ ↦
        (Fin.snoc q.1 (q.1 0) : Fin (n + 2) → M) :=
      Continuous.finSnoc (A := fun _ : Fin (n + 2) ↦ M) continuous_subtype_val
        ((continuous_apply 0).comp continuous_subtype_val)
    exact MooreFreeLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
      continuous_brokenGeodesic hr hc _

variable {hr}

theorem toMoorePath_brokenGeodesicLoop (hδ : ∀ i, δ i < r) (q : cyclicDistanceCut (X := M) δ) :
    (brokenGeodesicLoop hr hδ q).toMoorePath =
      (brokenGeodesic hr (Fin.snoc q.1 (q.1 0))
        fun i ↦ (dist_snoc_le_of_mem_cyclicDistanceCut q.2 i).trans_lt (hδ _)).toMoorePath :=
  (rfl)

@[simp]
theorem basepoint_brokenGeodesicLoop (hδ : ∀ i, δ i < r) (q : cyclicDistanceCut (X := M) δ) :
    (brokenGeodesicLoop hr hδ q).basepoint = q.1 0 := by
  rw [← MooreFreeLoopSpace.source_toMoorePath, toMoorePath_brokenGeodesicLoop,
    MoorePathBetween.source]
  exact Fin.snoc_castSucc (α := fun _ ↦ M) _ _ 0

/-- The duration of the closed broken geodesic through a cyclic tuple is the sum of the distances
from each vertex to the cyclically next one. -/
@[simp]
theorem length_brokenGeodesicLoop (hδ : ∀ i, δ i < r) (q : cyclicDistanceCut (X := M) δ) :
    (brokenGeodesicLoop hr hδ q).length = ∑ i, nndist (q.1 i) (q.1 (i + 1)) := by
  simp [← MooreFreeLoopSpace.length_toMoorePath, toMoorePath_brokenGeodesicLoop,
    length_brokenGeodesic, Fin.snoc_self_zero_succ]

/-- **Repeating the first vertex does not change the closed broken geodesic**:
`geoⁿ⁺¹ ∘ ιⁿ = geoⁿ`. The repeated vertex adds a segment of length zero, which concatenation of
Moore paths drops on the nose. -/
theorem brokenGeodesicLoop_cyclicDistanceCutRepeatFirst {δ' : Fin (n + 2) → ℝ}
    (hδ : ∀ i, δ i < r) (hδ' : ∀ i, δ' i < r) (h₀ : δ 0 ≤ δ' 0) (h₁ : 0 ≤ δ' 1)
    (h : ∀ i : Fin n, δ i.succ ≤ δ' i.succ.succ) (q : cyclicDistanceCut (X := M) δ) :
    brokenGeodesicLoop hr hδ' (cyclicDistanceCutRepeatFirst h₀ h₁ h q) =
      brokenGeodesicLoop hr hδ q := by
  ext1
  rw [toMoorePath_brokenGeodesicLoop, toMoorePath_brokenGeodesicLoop,
    toMoorePath_brokenGeodesic_succ_of_eq]
  · refine toMoorePath_brokenGeodesic_congr hr _ _ ?_
    rw [coe_cyclicDistanceCutRepeatFirst_apply, Fin.cons_zero, ← Fin.cons_snoc_eq_snoc_cons,
      Fin.tail_cons]
  · rw [coe_cyclicDistanceCutRepeatFirst_apply, Fin.cons_zero, ← Fin.cons_snoc_eq_snoc_cons,
      Fin.cons_one, Fin.cons_zero]
    exact (Fin.snoc_castSucc (α := fun _ ↦ M) _ _ 0).symm

/-- A constant tuple goes to the constant loop of length zero. -/
@[simp]
theorem brokenGeodesicLoop_const (hδ : ∀ i, δ i < r) (x : M)
    (hx : (fun _ ↦ x) ∈ cyclicDistanceCut (X := M) δ) :
    brokenGeodesicLoop hr hδ ⟨fun _ ↦ x, hx⟩ = MooreFreeLoopSpace.const x := by
  ext1
  rw [toMoorePath_brokenGeodesicLoop, brokenGeodesic,
    MoorePathBetween.toMoorePath_concat_of_length_eq_zero _ fun i ↦ by
      simp [Fin.snoc_self_zero_succ]]
  simp

end TauCeti.Manifold
