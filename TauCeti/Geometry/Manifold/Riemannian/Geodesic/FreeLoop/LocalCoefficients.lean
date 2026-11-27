/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.CompactApproximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.Homology
public import TauCeti.Topology.Homotopy.Path
public import TauCeti.Topology.PathSpace.Moore.Reparametrization
import TauCeti.Data.Fin.Basic

/-!
# The homology of the free loop space with local coefficients from broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r` be a radius
such that the tangent ball of radius `r` at every point is a normal domain. The closed broken
geodesics through the tuples of the distance cuts `𝓛ⁿM` form a cocone `geoⁿ : 𝓛ⁿM → 𝓛M` over
the sequence of distance cuts (`TauCeti.Manifold.cyclicDistanceCutCocone`), and singular homology
with constant coefficients turns it into a colimit cocone
(`TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`). This file proves
the same with local coefficients: for every local system `L` on the free loop space,

`Hₖ(𝓛M; L) = colimₙ Hₖ(𝓛ⁿM; (geoⁿ)^* L)`

(`TauCeti.Manifold.isColimitWhiskerOverTwistedHomologyCyclicDistanceCutCocone`).

It is the compact-approximation criterion with local coefficients,
`TauCeti.LocalCoefficientSystem.isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox`. Its new
hypothesis is a coherence of the two homotopies of the approximation: at a late stage `𝓛ᵐM`, the
homotopy `G` from the broken geodesics through the samples of a loop to the loop itself, and the
homotopy `H` sliding the vertices of a tuple `q` of `𝓛ᵐM` along its broken geodesic `γ` to the
samples of `γ`, must agree over `𝓛M`: the path traced by `geoᵐ ∘ H` from `γ` must be homotopic,
with fixed end points, to the path traced by `G` at `γ`
(`TauCeti.Manifold.homotopic_map_evalAt_cyclicDistanceCutSampleBrokenGeodesicHomotopy`).

The proof reparametrizes `γ` by time maps (`TauCeti.MooreFreeLoopSpace.reparam`), the paths
`g : I → ℝ` from `0` to the length `L` of `γ`, which form a convex and hence simply connected set.

* Read on the unit interval, a tuple of times `τ₀ ≤ ⋯ ≤ τₘ` is a time map with arcs of equal
  duration, and the reparametrization of `γ` by it has the samples `γ(τⱼ)`. Along the segment of
  time maps from the vertex times of `q` to the time map `s ↦ L s`, the samples of the
  reparametrized loops are exactly the slid vertices.
* At the vertex times, `γ` is reparametrized into the closed broken geodesic through `q` with arcs
  of equal duration. Straightening its arcs only reparametrizes it, since the radial geodesic from
  a vertex to a point of its arc runs along that arc
  (`TauCeti.Manifold.geodesicInterpolation_brokenGeodesicLoop_apply`), and changing the durations
  of the arcs only reparametrizes it too. So `G` at this loop runs along reparametrizations of `γ`.
* The square of `G` along the path of reparametrized loops
  (`Path.Homotopic.map_trans_evalAt`) has these two paths of reparametrizations as one pair of
  sides, which are homotopic because the time maps are simply connected, and `geoᵐ ∘ H` and the
  path of `G` at `γ` as the other pair.

## Main results

* `TauCeti.Manifold.homotopic_map_evalAt_cyclicDistanceCutSampleBrokenGeodesicHomotopy`: sliding
  the vertices and straightening the arcs agree up to homotopy.
* `TauCeti.Manifold.isColimitWhiskerOverTwistedHomologyCyclicDistanceCutCocone`: the homology of
  the free loop space with local coefficients is the colimit of the homology of the distance cuts.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §13.2, Propositions 13.2.2 and
  13.2.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients.
-/

public section

open AlgebraicTopology Bundle CategoryTheory Limits Manifold Metric Set
open scoped ContDiff Manifold NNReal

noncomputable section

namespace TauCeti.Manifold

universe u w

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ} (hr : ∀ q : M, IsNormalDomain I M q (ball 0 r))

/-! ### The vertex times of a closed broken geodesic as a time map -/

section TimeMap

variable {m : ℕ} {δ : Fin (m + 1) → ℝ} (hδ : ∀ i, δ i < r) (q : cyclicDistanceCut (X := M) δ)

include hδ in
/-- Consecutive vertices of `q` are less than `r` apart. -/
private theorem dist_val_sub_one_lt (i : Fin (m + 1)) : dist (q.val i) (q.val (i - 1)) < r :=
  (mem_cyclicDistanceCut.1 q.property i).trans_lt (hδ i)

include hδ in
/-- Consecutive vertices of `q` are less than `r` apart, read forwards. -/
private theorem dist_val_add_one_lt (i : Fin (m + 1)) : dist (q.val i) (q.val (i + 1)) < r :=
  dist_add_one_lt_of_forall_dist_sub_one_lt (dist_val_sub_one_lt hδ q) i

/-- The time `d(q 0, q 1) + ⋯ + d(q (j - 1), q j)` at which the closed broken geodesic through `q`
passes through its `j`-th vertex, the last one being `q 0` again at the length of the loop. -/
private def vertexTime (j : Fin (m + 2)) : ℝ :=
  (Fin.partialSum (fun k ↦ nndist (q.val k) (q.val (k + 1))) j : ℝ≥0)

private theorem vertexTime_succ (i : Fin (m + 1)) :
    vertexTime q i.succ = vertexTime q i.castSucc + nndist (q.val i) (q.val (i + 1)) := by
  rw [vertexTime, vertexTime, Fin.partialSum_succ, NNReal.coe_add]

private theorem vertexTime_zero : vertexTime q 0 = 0 := by
  simp [vertexTime]

private theorem vertexTime_last :
    vertexTime q (Fin.last (m + 1)) = (cyclicDistanceCutBrokenGeodesic hr hδ q).length := by
  rw [vertexTime, cyclicDistanceCutBrokenGeodesic_apply, length_brokenGeodesicLoop_eq_partialSum]

/-- An edge of the broken geodesic through `q` is at most its length. -/
private theorem nndist_le_length (i : Fin (m + 1)) :
    nndist (q.val i) (q.val (i + 1)) ≤ (cyclicDistanceCutBrokenGeodesic hr hδ q).length := by
  rw [cyclicDistanceCutBrokenGeodesic_apply, length_brokenGeodesicLoop_eq_partialSum,
    Fin.partialSum_last]
  exact Finset.single_le_sum (f := fun k ↦ nndist (q.val k) (q.val (k + 1)))
    (fun _ _ ↦ by positivity) (Finset.mem_univ i)

/-- If the loop through `q` has length zero, consecutive vertex times agree. -/
private theorem vertexTime_succ_of_length_eq_zero (i : Fin (m + 1))
    (h : (cyclicDistanceCutBrokenGeodesic hr hδ q).length / (m + 1) = 0) :
    vertexTime q i.castSucc = vertexTime q i.succ := by
  have hL : (cyclicDistanceCutBrokenGeodesic hr hδ q).length = 0 := by
    simpa [div_eq_zero_iff] using h
  rw [vertexTime_succ, nonpos_iff_eq_zero.1 ((nndist_le_length hr hδ q i).trans hL.le),
    NNReal.coe_zero, add_zero]

/-- The vertex times, with arcs of equal duration, as a broken Moore path in `ℝ`. -/
private def vertexTimePath : MoorePath ℝ :=
  brokenMoorePath isPathInterpolation_segment (m + 1) (vertexTime q)
    (fun _ ↦ (cyclicDistanceCutBrokenGeodesic hr hδ q).length / (m + 1)) fun i ↦
      ⟨trivial, vertexTime_succ_of_length_eq_zero hr hδ q i⟩

private theorem length_vertexTimePath :
    (vertexTimePath hr hδ q).length = (cyclicDistanceCutBrokenGeodesic hr hδ q).length := by
  rw [vertexTimePath, length_brokenMoorePath, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_succ, mul_div_cancel₀ _ (by positivity)]

/-- The vertex time path passes through the `j`-th vertex time at `j / (m + 1)`. -/
private theorem toUnitPath_vertexTimePath_arcPoint (j : Fin (m + 2)) :
    (vertexTimePath hr hδ q).toUnitPath (unitInterval.arcPoint (m + 1) j 0) = vertexTime q j := by
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.val_last, unitInterval.arcPoint_self_zero m.succ_pos, MoorePath.toUnitPath_one,
      vertexTimePath, target_brokenMoorePath]
  | cast i =>
    rw [MoorePath.toUnitPath_apply, length_vertexTimePath]
    have ht : (cyclicDistanceCutBrokenGeodesic hr hδ q).length *
        unitInterval.toNNReal (unitInterval.arcPoint (m + 1) (i.castSucc : ℕ) 0) =
        (i : ℕ) * ((cyclicDistanceCutBrokenGeodesic hr hδ q).length / (m + 1)) + 0 := by
      apply NNReal.coe_injective
      rw [NNReal.coe_mul, unitInterval.coe_toNNReal, Fin.val_castSucc,
        unitInterval.coe_arcPoint (by omega)]
      push_cast
      ring
    rw [ht, vertexTimePath, brokenMoorePath_apply_mul_add _ _ _ _ i zero_le,
      MoorePath.rescale_apply, mul_zero, zero_div, MoorePath.ofUnitPath_apply]
    simp

/-- The vertex times of the closed broken geodesic through `q`, run with arcs of equal duration on
the unit interval, as a time map of its duration. -/
private def vertexTimeMap :
    MooreFreeLoopSpace.timeMaps (cyclicDistanceCutBrokenGeodesic hr hδ q).length :=
  ⟨(vertexTimePath hr hδ q).toUnitPath, MooreFreeLoopSpace.mem_timeMaps.2 ⟨by
    rw [MoorePath.toUnitPath_zero, vertexTimePath, source_brokenMoorePath, vertexTime_zero], by
    rw [MoorePath.toUnitPath_one, vertexTimePath, target_brokenMoorePath, vertexTime_last hr hδ q]⟩⟩

private theorem coe_vertexTimeMap :
    (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) = (vertexTimePath hr hδ q).toUnitPath :=
  (rfl)

private theorem vertexTimeMap_arcPoint_zero (j : Fin (m + 2)) :
    (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) j 0) =
      vertexTime q j := by
  rw [coe_vertexTimeMap, toUnitPath_vertexTimePath_arcPoint]

/-- The broken path of the segments through the vertices of the vertex time map is itself. -/
private theorem brokenPath_vertexTimeMap :
    brokenPath (fun p : ℝ × ℝ ↦ (Path.segment p.1 p.2 : C(unitInterval, ℝ))) (m + 1)
      (vertexTimeMap hr hδ q) = vertexTimeMap hr hδ q := by
  have hA : vertexTimePath hr hδ q ∈ MoorePath.arcsWithin univ (m + 1) :=
    MoorePath.mem_arcsWithin.2 fun _ _ _ ↦ trivial
  have hB := MoorePath.brokenPathMap_eq_brokenMoorePath isPathInterpolation_segment (n := m)
    ⟨vertexTimePath hr hδ q, hA⟩ (q := vertexTime q)
    (fun j ↦ (toUnitPath_vertexTimePath_arcPoint hr hδ q j).symm) fun i ↦ ⟨trivial, fun h ↦ by
      rw [length_vertexTimePath] at h
      exact vertexTime_succ_of_length_eq_zero hr hδ q i h⟩
  rw [coe_vertexTimeMap]
  funext s
  have hs := MoorePath.toUnitPath_brokenPathMap isPathInterpolation_segment m.succ_pos
    ⟨vertexTimePath hr hδ q, hA⟩ s
  rw [hB] at hs
  rw [← hs]
  congr 2
  exact brokenMoorePath_congr _ _ _ rfl (funext fun _ ↦ by rw [length_vertexTimePath])

/-- On its `i`-th arc the vertex time map runs at constant speed from the `i`-th vertex time to
the next one. -/
private theorem vertexTimeMap_arcPoint (i : Fin (m + 1)) (a : unitInterval) :
    (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) i a) =
      vertexTime q i.castSucc + a * nndist (q.val i) (q.val (i + 1)) := by
  rw [← congrFun (brokenPath_vertexTimeMap hr hδ q),
    brokenPath_arcPoint_of_arcsWithin isPathInterpolation_segment (fun _ _ _ ↦ trivial) i.isLt a]
  have h₀ := vertexTimeMap_arcPoint_zero hr hδ q i.castSucc
  have h₁ := vertexTimeMap_arcPoint_zero hr hδ q i.succ
  rw [Fin.val_castSucc] at h₀
  rw [Fin.val_succ] at h₁
  rw [h₀, h₁, vertexTime_succ]
  simp only [coe_nndist, ContinuousMap.coe_mk, Path.segment_apply, AffineMap.lineMap_apply_module,
    smul_eq_mul]
  ring

/-- **The arcs of the vertex time map are carried to radial geodesics.** Along the closed broken
geodesic `γ` through `q`, the segment from the `i`-th vertex time to any time of the `i`-th arc of
the vertex time map is carried to the radial geodesic between the corresponding points of `γ`. -/
private theorem geodesicInterpolation_extend_vertexTimeMap {i : ℕ} (hi : i < m + 1)
    (a : unitInterval) :
    geodesicInterpolation hr
        ((cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend
          ((vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) i 0)),
        (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend
          ((vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) i a))) =
      (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend.comp
        (Path.segment ((vertexTimeMap hr hδ q : C(unitInterval, ℝ))
            (unitInterval.arcPoint (m + 1) i 0))
          ((vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) i a)) :
            C(unitInterval, ℝ)) := by
  set i' : Fin (m + 1) := ⟨i, hi⟩ with hi'
  set P := Fin.partialSum (fun k ↦ nndist (q.val k) (q.val (k + 1))) i'.castSucc with hP
  set d := nndist (q.val i') (q.val (i' + 1))
  have h₀ : (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) i 0) =
      ((P : ℝ≥0) : ℝ) := by
    have h := vertexTimeMap_arcPoint_zero hr hδ q i'.castSucc
    rwa [Fin.val_castSucc, hi', Fin.val_mk, vertexTime, ← hP] at h
  have hval : ∀ b : unitInterval,
      ((P : ℝ) + b * d : ℝ) = ((P + d * unitInterval.toNNReal b : ℝ≥0) : ℝ) := fun b ↦ by
    rw [NNReal.coe_add, NNReal.coe_mul, unitInterval.coe_toNNReal, mul_comm]
  have ha : (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) i a) =
      ((P + d * unitInterval.toNNReal a : ℝ≥0) : ℝ) := by
    rw [← hval]
    exact vertexTimeMap_arcPoint hr hδ q i' a
  rw [h₀, ha, MoorePath.extend_coe, MoorePath.extend_coe, cyclicDistanceCutBrokenGeodesic_apply]
  ext u
  rw [geodesicInterpolation_brokenGeodesicLoop_apply hr m q.val _ i' a u,
    ContinuousMap.comp_apply, ← cyclicDistanceCutBrokenGeodesic_apply hr hδ q]
  have hu : (Path.segment ((P : ℝ≥0) : ℝ) ((P + d * unitInterval.toNNReal a : ℝ≥0) : ℝ) :
      C(unitInterval, ℝ)) u = ((P + d * unitInterval.toNNReal (u * a) : ℝ≥0) : ℝ) := by
    rw [← hval, ← hval, Set.Icc.coe_mul]
    simp only [ContinuousMap.coe_mk, Path.segment_apply, AffineMap.lineMap_apply_module,
      smul_eq_mul]
    ring
  rw [hu, MoorePath.extend_coe, cyclicDistanceCutBrokenGeodesic_apply]

/-- The closed broken geodesic through `q` is at `q i` at the `i`-th vertex time. -/
private theorem extend_vertexTime_castSucc (i : Fin (m + 1)) :
    (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend (vertexTime q i.castSucc) =
      q.val i := by
  rw [vertexTime, MoorePath.extend_coe, cyclicDistanceCutBrokenGeodesic_apply,
    brokenGeodesicLoop_apply_partialSum]

/-- The closed broken geodesic through `q` is at `q (i + 1)` at the `(i + 1)`-st vertex time, the
last one being `q 0`. -/
private theorem extend_vertexTime_succ (i : Fin (m + 1)) :
    (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend (vertexTime q i.succ) =
      q.val (i + 1) := by
  rw [vertexTime_succ, vertexTime, ← NNReal.coe_add, MoorePath.extend_coe,
    cyclicDistanceCutBrokenGeodesic_apply, brokenGeodesicLoop_apply_partialSum_add hr m q.val _ i
      le_rfl]
  have h := target_geodesicSegment hr
    ⟨(q.val i, q.val (i + 1)), dist_val_add_one_lt hδ q i⟩
  rwa [MoorePath.target_def, length_geodesicSegment] at h

/-- The closed sampled vertices of the reparametrization of `γ` by the vertex time map are the
points of `γ` at the vertex times. -/
private theorem closedSample_reparam_vertexTimeMap (j : Fin (m + 2)) :
    ((cyclicDistanceCutBrokenGeodesic hr hδ q).reparam (vertexTimeMap hr hδ q)).closedSample
      (m + 1) j =
      (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend (vertexTime q j) := by
  rw [MooreFreeLoopSpace.closedSample_eq_toUnitPath _ m.succ_pos,
    MooreFreeLoopSpace.toUnitPath_reparam, ContinuousMap.comp_apply,
    vertexTimeMap_arcPoint_zero]

/-! #### Straightening the arcs of the reparametrization by the vertex time map -/

/-- The straightening homotopy of the vertex time map, jointly in the time and the parameter. -/
private def straightenVertexTimeMap : C(unitInterval × unitInterval, ℝ) :=
  ⟨fun p ↦ straightenArcs (fun p : ℝ × ℝ ↦ (Path.segment p.1 p.2 : C(unitInterval, ℝ))) (m + 1)
    (vertexTimeMap hr hδ q) p.1 p.2,
    (continuous_straightenArcs (Y := Unit) isPathInterpolation_segment m.succ_pos continuous_const
      fun _ _ _ _ ↦ trivial).comp (by fun_prop : Continuous fun p : unitInterval × unitInterval ↦
        ((), p.1, p.2))⟩

/-- The straightened vertex time map at time `t`, a time map. -/
private def straightenedTimeMap (t : unitInterval) :
    MooreFreeLoopSpace.timeMaps (cyclicDistanceCutBrokenGeodesic hr hδ q).length :=
  ⟨(straightenVertexTimeMap hr hδ q).curry t, MooreFreeLoopSpace.mem_timeMaps.2
    ⟨(straightenArcs_source isPathInterpolation_segment m.succ_pos (fun _ _ _ ↦ trivial) t).trans
      (MooreFreeLoopSpace.mem_timeMaps.1 (vertexTimeMap hr hδ q).property).1,
    (straightenArcs_target isPathInterpolation_segment m.succ_pos (fun _ _ _ ↦ trivial) t).trans
      (MooreFreeLoopSpace.mem_timeMaps.1 (vertexTimeMap hr hδ q).property).2⟩⟩

private theorem coe_straightenedTimeMap_apply (t s : unitInterval) :
    (straightenedTimeMap hr hδ q t : C(unitInterval, ℝ)) s =
      straightenArcs (fun p : ℝ × ℝ ↦ (Path.segment p.1 p.2 : C(unitInterval, ℝ))) (m + 1)
        (vertexTimeMap hr hδ q) t s :=
  (rfl)

/-- The straightening of the vertex time map, a loop of time maps at the vertex time map. -/
private def straightenTimeMapPath : Path (vertexTimeMap hr hδ q) (vertexTimeMap hr hδ q) where
  toFun := straightenedTimeMap hr hδ q
  continuous_toFun := (straightenVertexTimeMap hr hδ q).curry.continuous.subtype_mk _
  source' := Subtype.ext <| ContinuousMap.ext fun s ↦ by
    rw [coe_straightenedTimeMap_apply,
      straightenArcs_zero isPathInterpolation_segment m.succ_pos (fun _ _ _ ↦ trivial) s]
  target' := Subtype.ext <| ContinuousMap.ext fun s ↦ by
    rw [coe_straightenedTimeMap_apply, straightenArcs_one,
      congrFun (brokenPath_vertexTimeMap hr hδ q) s]

private theorem straightenTimeMapPath_apply (t : unitInterval) :
    straightenTimeMapPath hr hδ q t = straightenedTimeMap hr hδ q t :=
  (rfl)

/-- **Straightening the reparametrization by the vertex time map** is reparametrizing by the
straightened vertex time map. -/
private theorem arcStraighteningMap_reparam_vertexTimeMap
    (hA : (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam (vertexTimeMap hr hδ q) ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (m + 1)) (t : unitInterval) :
    MooreFreeLoopSpace.arcStraighteningMap (isPathInterpolation_geodesicInterpolation hr)
        m.succ_pos (t, ⟨_, hA⟩) =
      (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam (straightenedTimeMap hr hδ q t) := by
  ext1
  rw [MooreFreeLoopSpace.toMoorePath_arcStraighteningMap,
    ← MoorePath.ofUnitPath_toUnitPath_rescale_length (MoorePath.arcStraighteningMap _ _ _),
    MoorePath.length_arcStraighteningMap, MooreFreeLoopSpace.toMoorePath_reparam,
    MooreFreeLoopSpace.coe_toArcsWithin, MooreFreeLoopSpace.length_toMoorePath,
    MooreFreeLoopSpace.length_reparam]
  congr 2
  ext s
  rw [MoorePath.toUnitPath_arcStraighteningMap, MooreFreeLoopSpace.coe_toArcsWithin,
    MooreFreeLoopSpace.toUnitPath_reparam, ContinuousMap.comp_apply,
    straightenArcs_comp (ρ := fun p : ℝ × ℝ ↦ (Path.segment p.1 p.2 : C(unitInterval, ℝ))) _
      m.succ_pos fun i hi a ↦ geodesicInterpolation_extend_vertexTimeMap hr hδ q hi a,
    coe_straightenedTimeMap_apply]

/-! #### Changing the durations of the arcs of the reparametrization -/

/-- The sum of the edges of `q` is the length of the closed broken geodesic through it. -/
private theorem sum_nndist_eq_length :
    ∑ i, nndist (q.val i) (q.val (i + 1)) = (cyclicDistanceCutBrokenGeodesic hr hδ q).length := by
  rw [cyclicDistanceCutBrokenGeodesic_apply, length_brokenGeodesicLoop_eq_partialSum,
    Fin.partialSum_last]

/-- The durations of the arcs at the time `s` of the homotopy changing the durations of the
reparametrization by the vertex time map: `(1 - s) L / (m + 1) + s d(q i, q (i + 1))`. -/
private def durationTime (s : unitInterval) (i : Fin (m + 1)) : ℝ≥0 :=
  unitInterval.toNNReal (unitInterval.symm s) *
      ((cyclicDistanceCutBrokenGeodesic hr hδ q).length / (m + 1)) +
    unitInterval.toNNReal s * nndist (q.val i) (q.val (i + 1))

private theorem nndist_eq_zero_of_durationTime_eq_zero {s : unitInterval} {i : Fin (m + 1)}
    (h : durationTime hr hδ q s i = 0) : nndist (q.val i) (q.val (i + 1)) = 0 := by
  obtain ⟨h₁, h₂⟩ := add_eq_zero.1 h
  rcases mul_eq_zero.1 h₂ with hs | hd
  · -- At `s = 0` the duration is `L / (m + 1)`, which only vanishes for a loop of length zero.
    rw [unitInterval.toNNReal_symm, hs, tsub_zero, one_mul, div_eq_zero_iff] at h₁
    have hL := h₁.resolve_right (by positivity)
    exact nonpos_iff_eq_zero.1 ((nndist_le_length hr hδ q i).trans hL.le)
  · exact hd

private theorem durationTime_one (i : Fin (m + 1)) :
    durationTime hr hδ q 1 i = nndist (q.val i) (q.val (i + 1)) := by
  simp [durationTime]

/-- The vertex times run with the durations of the arcs at the time `s`. -/
private def durationPath (s : unitInterval) : MoorePath ℝ :=
  brokenMoorePath isPathInterpolation_segment (m + 1) (vertexTime q) (durationTime hr hδ q s)
    fun i ↦ ⟨trivial, fun h ↦ by
      rw [vertexTime_succ, nndist_eq_zero_of_durationTime_eq_zero hr hδ q h, NNReal.coe_zero,
        add_zero]⟩

private theorem length_durationPath (s : unitInterval) :
    (durationPath hr hδ q s).length = (cyclicDistanceCutBrokenGeodesic hr hδ q).length := by
  rw [durationPath, length_brokenMoorePath]
  simp only [durationTime, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sum_nndist_eq_length hr hδ q]
  rw [Nat.cast_succ, mul_div_cancel₀ _ (by positivity), ← add_mul, add_comm,
    unitInterval.toNNReal_add_toNNReal_symm, one_mul]

/-- The durations at the time `s`, as a time map. -/
private def durationTimeMap (s : unitInterval) :
    MooreFreeLoopSpace.timeMaps (cyclicDistanceCutBrokenGeodesic hr hδ q).length :=
  ⟨(durationPath hr hδ q s).toUnitPath, MooreFreeLoopSpace.mem_timeMaps.2 ⟨by
    rw [MoorePath.toUnitPath_zero, durationPath, source_brokenMoorePath, vertexTime_zero], by
    rw [MoorePath.toUnitPath_one, durationPath, target_brokenMoorePath,
      vertexTime_last hr hδ q]⟩⟩

private theorem coe_durationTimeMap (s : unitInterval) :
    (durationTimeMap hr hδ q s : C(unitInterval, ℝ)) = (durationPath hr hδ q s).toUnitPath :=
  (rfl)

/-- The homotopy changing the durations of the arcs, as a path of time maps from the vertex time
map to the time map `s ↦ L s`. -/
private def durationTimeMapPath :
    Path (vertexTimeMap hr hδ q)
      (MooreFreeLoopSpace.mulTimeMap (cyclicDistanceCutBrokenGeodesic hr hδ q).length) where
  toFun := durationTimeMap hr hδ q
  continuous_toFun := by
    refine (MoorePath.continuous_toUnitPath.comp (continuous_brokenMoorePath _ (m + 1)
      continuous_const (continuous_pi fun i ↦ ?_) _)).subtype_mk _
    simp only [durationTime]
    fun_prop
  -- At time zero every arc lasts `L / (m + 1)`.
  source' := by
    refine Subtype.ext ?_
    rw [coe_durationTimeMap, coe_vertexTimeMap]
    exact congrArg MoorePath.toUnitPath <|
      brokenMoorePath_congr _ _ _ rfl (funext fun i ↦ by simp [durationTime])
  target' := by
    refine Subtype.ext (ContinuousMap.ext fun t ↦ ?_)
    rw [coe_durationTimeMap, MoorePath.toUnitPath_apply]
    -- At time one every arc lasts the distance between its end points, so the time map runs at
    -- unit speed.
    rw [MooreFreeLoopSpace.coe_mulTimeMap_apply, length_durationPath,
      durationPath, brokenMoorePath_segment_apply _ _ _ fun i ↦ by
        rw [durationTime_one]
        exact vertexTime_succ q i]
    simp only [durationTime_one, sum_nndist_eq_length hr hδ q]
    rw [vertexTime_zero, zero_add, NNReal.coe_mul, unitInterval.coe_toNNReal,
      min_eq_left (mul_le_of_le_one_right (NNReal.coe_nonneg _) t.property.2)]

private theorem durationTimeMapPath_apply (s : unitInterval) :
    durationTimeMapPath hr hδ q s = durationTimeMap hr hδ q s :=
  (rfl)

/-- **Changing the durations of the arcs of the reparametrization by the vertex time map** is
reparametrizing by the time maps of the durations. -/
private theorem brokenPathDurationHomotopy_reparam_vertexTimeMap
    (hA : (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam (vertexTimeMap hr hδ q) ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (m + 1)) (s : unitInterval) :
    brokenPathDurationHomotopy hr m (s, ⟨_, hA⟩) =
      (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam (durationTimeMap hr hδ q s) := by
  set Λ := (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam (vertexTimeMap hr hδ q)
  have hc := closedSample_reparam_vertexTimeMap hr hδ q
  have hcs : ∀ i : Fin (m + 1), Λ.closedSample (m + 1) i.castSucc = q.val i :=
    fun i ↦ (hc _).trans (extend_vertexTime_castSucc hr hδ q i)
  have hcs' : ∀ i : Fin (m + 1), Λ.closedSample (m + 1) i.succ = q.val (i + 1) :=
    fun i ↦ (hc _).trans (extend_vertexTime_succ hr hδ q i)
  have hdur : ∀ i, unitInterval.toNNReal (unitInterval.symm s) * (Λ.length / (m + 1)) +
      unitInterval.toNNReal s *
        nndist (Λ.closedSample (m + 1) i.castSucc) (Λ.closedSample (m + 1) i.succ) =
      durationTime hr hδ q s i := fun i ↦ by
    rw [hcs, hcs', MooreFreeLoopSpace.length_reparam, durationTime]
  have hF : ∀ i : Fin (m + 1),
      geodesicInterpolation hr
        ((cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend (vertexTime q i.castSucc),
          (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend (vertexTime q i.succ)) =
        (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend.comp
          (Path.segment (vertexTime q i.castSucc) (vertexTime q i.succ) : C(unitInterval, ℝ)) :=
    fun i ↦ by
      have h₀ : (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) i 0) =
          vertexTime q i.castSucc := vertexTimeMap_arcPoint_zero hr hδ q i.castSucc
      have h₁ : (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) i 1) =
          vertexTime q i.succ := by
        rw [vertexTimeMap_arcPoint, vertexTime_succ, Set.Icc.coe_one, one_mul]
      have h := geodesicInterpolation_extend_vertexTimeMap hr hδ q i.isLt 1
      rwa [h₀, h₁] at h
  ext1
  rw [toMoorePath_brokenPathDurationHomotopy hr m s ⟨Λ, hA⟩ fun i ↦
      ⟨MooreFreeLoopSpace.closedSample_mem_of_mem_arcsWithin hA i, fun h0 ↦ by
        rw [hcs, hcs']
        exact nndist_eq_zero.1
          (nndist_eq_zero_of_durationTime_eq_zero hr hδ q ((hdur i).symm.trans h0))⟩,
    MooreFreeLoopSpace.toMoorePath_reparam, coe_durationTimeMap]
  have e := MoorePath.ofUnitPath_toUnitPath_rescale_length
    ((durationPath hr hδ q s).map (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend)
  rw [MoorePath.toUnitPath_map, MoorePath.length_map, length_durationPath] at e
  rw [e]
  rw [durationPath, map_brokenMoorePath _ (isPathInterpolation_geodesicInterpolation hr) _ _ _ _ _
    (fun i ↦ ⟨by
      rw [Set.mem_ofPred_eq, extend_vertexTime_castSucc hr hδ q, extend_vertexTime_succ hr hδ q]
      exact dist_val_add_one_lt hδ q i, fun h0 ↦ by
      rw [extend_vertexTime_castSucc hr hδ q, extend_vertexTime_succ hr hδ q]
      exact nndist_eq_zero.1 (nndist_eq_zero_of_durationTime_eq_zero hr hδ q h0)⟩) hF]
  exact brokenMoorePath_congr _ _ _ (funext hc) (funext hdur)

/-! #### The slide as a segment of time maps -/

/-- The segment of time maps from the vertex time map to `s ↦ L s`. Reparametrizing the closed
broken geodesic through `q` along it samples the times of the slide of the vertices. -/
private def slideTimeMapPath :
    Path (vertexTimeMap hr hδ q)
      (MooreFreeLoopSpace.mulTimeMap (cyclicDistanceCutBrokenGeodesic hr hδ q).length) where
  toFun u := ⟨(1 - (u : ℝ)) • (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) +
      (u : ℝ) • (MooreFreeLoopSpace.mulTimeMap _ : C(unitInterval, ℝ)),
    MooreFreeLoopSpace.convex_timeMaps _ (vertexTimeMap hr hδ q).property
      (MooreFreeLoopSpace.mulTimeMap _).property (sub_nonneg.2 u.property.2) u.property.1
      (sub_add_cancel 1 _)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

private theorem coe_slideTimeMapPath_apply (u : unitInterval) :
    (slideTimeMapPath hr hδ q u : C(unitInterval, ℝ)) =
      (1 - (u : ℝ)) • (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) +
        (u : ℝ) • (MooreFreeLoopSpace.mulTimeMap (cyclicDistanceCutBrokenGeodesic hr hδ q).length :
          C(unitInterval, ℝ)) :=
  (rfl)

/-- At the `j`-th vertex time of the subdivision, the slide time map is at the `j`-th time of the
slide. -/
private theorem slideTimeMapPath_apply_arcPoint_zero (u : unitInterval) (j : Fin (m + 1)) :
    (slideTimeMapPath hr hδ q u : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) j 0) =
      ((slideTimes hr hδ (k := 0) u q j : ℝ≥0) : ℝ) := by
  have h₀ : (vertexTimeMap hr hδ q : C(unitInterval, ℝ)) (unitInterval.arcPoint (m + 1) j 0) =
      vertexTime q j.castSucc := vertexTimeMap_arcPoint_zero hr hδ q j.castSucc
  have hj : (⟨j - 0, by omega⟩ : Fin (m + 1)) = j := Fin.ext (Nat.sub_zero _)
  rw [coe_slideTimeMapPath_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.smul_apply, h₀, MooreFreeLoopSpace.coe_mulTimeMap_apply, slideTimes_def, hj,
    unitInterval.coe_arcPoint j.isLt]
  simp only [vertexTime, smul_eq_mul, NNReal.coe_add, NNReal.coe_mul, unitInterval.coe_toNNReal,
    unitInterval.coe_symm_eq, NNReal.coe_div, NNReal.coe_natCast, add_zero]
  push_cast
  ring

/-- The sampled vertices of the reparametrizations along the slide time map are the vertices of
the slide. -/
private theorem sample_reparam_slideTimeMapPath (u : unitInterval) (j : Fin (m + 1)) :
    ((cyclicDistanceCutBrokenGeodesic hr hδ q).reparam
        (slideTimeMapPath hr hδ q u)).toMoorePath.sample (m + 1) j =
      (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath
        (slideTimes hr hδ (k := 0) u q j) := by
  rw [MoorePath.sample_eq_toUnitPath_arcPoint, MooreFreeLoopSpace.toUnitPath_reparam,
    ContinuousMap.comp_apply, slideTimeMapPath_apply_arcPoint_zero, MoorePath.extend_coe]

/-- The closed broken geodesic through `q` is `1`-Lipschitz, also read on `ℝ`. -/
private theorem lipschitzWith_extend_cyclicDistanceCutBrokenGeodesic :
    LipschitzWith 1 (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend := by
  have h := (lipschitzWith_brokenGeodesicLoop hr m q.val (dist_val_sub_one_lt hδ q)).comp
    Real.lipschitzWith_toNNReal
  rw [one_mul, ← cyclicDistanceCutBrokenGeodesic_apply hr hδ q] at h
  have he : ⇑(cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.extend =
      (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath ∘ Real.toNNReal :=
    funext fun t ↦ MoorePath.extend_apply _ t
  rw [he]
  exact h

/-- The reparametrizations along the slide time map have short arcs, provided that the loop is
shorter than `(m + 1) r`. -/
private theorem reparam_slideTimeMapPath_mem_arcsWithin
    (hL : ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) < (m + 1) * r)
    (u : unitInterval) :
    (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam (slideTimeMapPath hr hδ q u) ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (m + 1) := by
  rw [MooreFreeLoopSpace.mem_arcsWithin, MooreFreeLoopSpace.toUnitPath_reparam]
  intro i hi a
  rw [Set.mem_ofPred_eq, ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  refine ((lipschitzWith_extend_cyclicDistanceCutBrokenGeodesic hr hδ q).dist_le_mul _ _).trans_lt
    ?_
  set i' : Fin (m + 1) := ⟨i, hi⟩
  set d : ℝ := (nndist (q.val i') (q.val (i' + 1)) : ℝ)
  set L : ℝ := ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ)
  have hd : d < r := dist_val_add_one_lt hδ q i'
  have hℓ : L / (m + 1) < r := (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hval : ∀ b : unitInterval, (slideTimeMapPath hr hδ q u : C(unitInterval, ℝ))
      (unitInterval.arcPoint (m + 1) i b) =
      (1 - u) * (vertexTime q i'.castSucc + b * d) + u * (L * ((i + b) / (m + 1))) := fun b ↦ by
    rw [coe_slideTimeMapPath_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.smul_apply, vertexTimeMap_arcPoint hr hδ q i' b,
      MooreFreeLoopSpace.coe_mulTimeMap_apply, unitInterval.coe_arcPoint hi, smul_eq_mul,
      smul_eq_mul]
    -- `push_cast` reads the edge `d` as a distance; unfold the abbreviations `d` and `L`.
    push_cast
    simp only [d, L, coe_nndist]
  rw [hval, hval, NNReal.coe_one, one_mul, Real.dist_eq]
  have hu₀ := u.property.1
  have hu₁ := u.property.2
  have ha₀ := a.property.1
  have ha₁ := a.property.2
  have hd₀ : 0 ≤ d := NNReal.coe_nonneg _
  have hL₀ : 0 ≤ L / (m + 1) := by positivity
  have key : (1 - u) * (vertexTime q i'.castSucc + (0 : unitInterval) * d) +
        u * (L * ((i + ((0 : unitInterval) : ℝ)) / (m + 1))) -
      ((1 - u) * (vertexTime q i'.castSucc + a * d) + u * (L * ((i + a) / (m + 1)))) =
      -(a * ((1 - u) * d + u * (L / (m + 1)))) := by
    simp only [Set.Icc.coe_zero, zero_mul, add_zero]
    field_simp
    ring
  have hX₀ : 0 ≤ (1 - u) * d + u * (L / (m + 1)) :=
    add_nonneg (mul_nonneg (sub_nonneg.2 hu₁) hd₀) (mul_nonneg hu₀ hL₀)
  -- The step `(1 - u) d + u L / (m + 1)` is a convex combination of two numbers less than `r`.
  have hX : (1 - u) * d + u * (L / (m + 1)) < r := by
    rcases eq_or_lt_of_le hu₀ with h0 | h0
    · rw [← h0]
      simpa using hd
    · nlinarith [mul_lt_mul_of_pos_left hℓ h0, mul_le_mul_of_nonneg_left hd.le (sub_nonneg.2 hu₁)]
  rw [key, abs_neg, abs_of_nonneg (mul_nonneg ha₀ hX₀)]
  exact (mul_le_of_le_one_left hX₀ ha₁).trans_lt hX

/-! #### The square of the straightening homotopy along the slide -/

/-- Closed broken geodesics through equal tuples are equal. -/
private theorem brokenGeodesicLoop_eq_of_eq {n : ℕ} {x y : Fin (n + 1) → M}
    (hx : ∀ i, dist (x i) (x (i - 1)) < r) (hy : ∀ i, dist (y i) (y (i - 1)) < r) (h : x = y) :
    brokenGeodesicLoop hr n x hx = brokenGeodesicLoop hr n y hy := by
  subst h
  rfl

/-- The reparametrization of `γ` by the vertex time map has short arcs. -/
private theorem reparam_vertexTimeMap_mem_arcsWithin
    (hL : ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) < (m + 1) * r) :
    (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam (vertexTimeMap hr hδ q) ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (m + 1) :=
  (slideTimeMapPath hr hδ q).source ▸ reparam_slideTimeMapPath_mem_arcsWithin hr hδ q hL 0

/-- The loops reparametrized along the slide time map, as a path of loops with short arcs from the
reparametrization by the vertex time map to `γ`. -/
private def slideLoopPath
    (hL : ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) < (m + 1) * r)
    (hγ : cyclicDistanceCutBrokenGeodesic hr hδ q ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (m + 1)) :
    Path (⟨_, reparam_vertexTimeMap_mem_arcsWithin hr hδ q hL⟩ :
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (m + 1)) ⟨_, hγ⟩ where
  toFun u := ⟨_, reparam_slideTimeMapPath_mem_arcsWithin hr hδ q hL u⟩
  continuous_toFun := ((map_continuous _).comp (slideTimeMapPath hr hδ q).continuous).subtype_mk _
  source' := Subtype.ext (congrArg (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam
    (slideTimeMapPath hr hδ q).source)
  target' := Subtype.ext ((congrArg (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam
    (slideTimeMapPath hr hδ q).target).trans (MooreFreeLoopSpace.reparam_mulTimeMap _))

/-- The broken geodesic through the samples of the reparametrization of `γ` by the vertex time map
is `γ`. -/
private theorem sampleBrokenGeodesicLoop_reparam_vertexTimeMap
    (hL : ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) < (m + 1) * r) :
    sampleBrokenGeodesicLoop hr m ⟨_, reparam_vertexTimeMap_mem_arcsWithin hr hδ q hL⟩ =
      cyclicDistanceCutBrokenGeodesic hr hδ q := by
  refine (sampleBrokenGeodesicLoop_apply hr m _
    (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin
      (reparam_vertexTimeMap_mem_arcsWithin hr hδ q hL))).trans ?_
  conv_rhs => rw [cyclicDistanceCutBrokenGeodesic_apply]
  refine brokenGeodesicLoop_eq_of_eq hr _ _ (funext fun j ↦ ?_)
  have h := sample_reparam_slideTimeMapPath hr hδ q 0 j
  rw [(slideTimeMapPath hr hδ q).source, slideTimes_zero] at h
  rw [h]
  have hj : (⟨j - 0, by omega⟩ : Fin (m + 1)) = j := Fin.ext (Nat.sub_zero _)
  rw [hj, cyclicDistanceCutBrokenGeodesic_apply, brokenGeodesicLoop_apply_partialSum]

/-- Straightening the arcs of the reparametrization of `γ` by the vertex time map runs along the
reparametrizations of `γ` by the straightened vertex time maps, and then by the time maps of the
changing durations. -/
private theorem evalAt_sampleBrokenGeodesicLoopHomotopy_reparam_vertexTimeMap
    (hL : ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) < (m + 1) * r) :
    (sampleBrokenGeodesicLoopHomotopy hr m).evalAt
        ⟨_, reparam_vertexTimeMap_mem_arcsWithin hr hδ q hL⟩ =
      ((((straightenTimeMapPath hr hδ q).trans (durationTimeMapPath hr hδ q)).map
        (cyclicDistanceCutBrokenGeodesic hr hδ q).reparam.continuous).cast rfl
        ((sampleBrokenGeodesicLoop_reparam_vertexTimeMap hr hδ q hL).trans
          (MooreFreeLoopSpace.reparam_mulTimeMap _).symm)) := by
  set hA := reparam_vertexTimeMap_mem_arcsWithin hr hδ q hL
  refine Path.ext (funext fun t ↦ ?_)
  refine ((ContinuousMap.Homotopy.evalAt_apply _ _ t).trans ?_).trans
    (congrFun ((Path.cast_coe _ _ _).trans (Path.map_coe _ _)) t).symm
  rw [Function.comp_apply, sampleBrokenGeodesicLoopHomotopy_eq_trans,
    ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · rw [MooreFreeLoopSpace.arcStraightening_apply, arcStraighteningMap_reparam_vertexTimeMap,
      straightenTimeMapPath_apply]
  · rw [brokenPathDurationHomotopy_reparam_vertexTimeMap, durationTimeMapPath_apply]

/-- **The square of the straightening homotopy along the slide.** The path of loops of the
straightening homotopy at `γ` is homotopic to the path of broken geodesics through the samples of
the reparametrizations of `γ` along the slide time map. -/
private theorem homotopic_evalAt_sampleBrokenGeodesicLoopHomotopy_map_slideLoopPath
    (hL : ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) < (m + 1) * r)
    (hγ : cyclicDistanceCutBrokenGeodesic hr hδ q ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (m + 1)) :
    ((sampleBrokenGeodesicLoopHomotopy hr m).evalAt ⟨_, hγ⟩).Homotopic
      (((slideLoopPath hr hδ q hL hγ).map (map_continuous (sampleBrokenGeodesicLoop hr m))).cast
        (sampleBrokenGeodesicLoop_reparam_vertexTimeMap hr hδ q hL).symm rfl) := by
  -- At the start of the slide, the side of the square is homotopic to the path of reparametrized
  -- loops itself, since both run along reparametrizations of `γ`.
  have hside : ((sampleBrokenGeodesicLoopHomotopy hr m).evalAt
      ⟨_, reparam_vertexTimeMap_mem_arcsWithin hr hδ q hL⟩).Homotopic
      (((slideLoopPath hr hδ q hL hγ).map continuous_subtypeVal).cast rfl
        (sampleBrokenGeodesicLoop_reparam_vertexTimeMap hr hδ q hL)) := by
    rw [evalAt_sampleBrokenGeodesicLoopHomotopy_reparam_vertexTimeMap hr hδ q hL]
    exact Path.Homotopic.pathCast (MooreFreeLoopSpace.homotopic_map_reparam _
      ((straightenTimeMapPath hr hδ q).trans (durationTimeMapPath hr hδ q))
      (slideTimeMapPath hr hδ q)) rfl _
  -- Cancelling the path of reparametrized loops in the square.
  exact Path.Homotopic.trans_left_cancel
    (e := (slideLoopPath hr hδ q hL hγ).map continuous_subtypeVal)
    ((Path.Homotopic.map_trans_evalAt (sampleBrokenGeodesicLoopHomotopy hr m) _).trans
      (Path.Homotopic.hcomp hside (Path.Homotopic.refl _)))

/-- The cut-offs of a slide bound the length of the loop below `(m + 1) r`. -/
private theorem length_lt_of_sum_le {δ' : Fin (m + 0 + 1) → ℝ} (hδ' : ∀ j, δ' j < r)
    (hm : ∀ j, ∑ i, δ i ≤ ((m + 0 + 1 : ℕ) : ℝ) * δ' j) :
    ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) < (m + 1) * r :=
  calc ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ)
      ≤ ((m + 0 + 1 : ℕ) : ℝ) * δ' 0 :=
        (length_cyclicDistanceCutBrokenGeodesic_le hr hδ q).trans (hm 0)
    _ < ((m + 0 + 1 : ℕ) : ℝ) * r :=
        mul_lt_mul_of_pos_left (hδ' 0) (by exact_mod_cast Nat.succ_pos _)
    _ = (m + 1) * r := by push_cast; ring

/-- **Sliding the vertices and straightening the arcs agree up to homotopy.** Let `q` lie in a
distance cut of stage `m` and let `γ` be the closed broken geodesic through it, with arcs short
enough to be straightened. Sliding the vertices `q` along `γ` to its equally spaced samples, and
taking the closed broken geodesics through the slid vertices, is a path of loops from `γ` to the
closed broken geodesic through the samples of `γ`. It is homotopic, with fixed end points, to the
path of loops along which the arcs of `γ` are straightened between its samples and then run at
unit speed. This is the coherence of the two homotopies of the compact-family approximation of the
free loop space by broken geodesics. -/
theorem homotopic_map_evalAt_cyclicDistanceCutSampleBrokenGeodesicHomotopy
    {δ' : Fin (m + 0 + 1) → ℝ} (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (m + 0 + 1), δ ⟨j - 0, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((m + 0 + 1 : ℕ) : ℝ) * δ' j)
    (hγ : cyclicDistanceCutBrokenGeodesic hr hδ q ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (m + 1)) :
    (((cyclicDistanceCutSampleBrokenGeodesicHomotopy hr (k := 0) hδ hδδ' hm).evalAt q).map
        (cyclicDistanceCutBrokenGeodesic hr hδ').continuous).Homotopic
      (((sampleBrokenGeodesicLoopHomotopy hr m).evalAt ⟨_, hγ⟩).cast
        (cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirstIterate hr (k := 0) hδ hδ' hδδ'
          q)
        (by
          rw [cyclicDistanceCutBrokenGeodesic_apply, sampleBrokenGeodesicLoop_apply hr m _
            (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin hγ)]
          congr 1
          exact coe_cyclicDistanceCutSampleBrokenGeodesic_apply hr hδ _ hm q)) := by
  have hL := length_lt_of_sum_le hr hδ q hδ' hm
  -- The slide, read through the broken geodesics, is the path of broken geodesics through the
  -- samples of the reparametrized loops along the slide time map.
  refine Path.Homotopic.of_coe_eq
    (p' := ((slideLoopPath hr hδ q hL hγ).map (map_continuous (sampleBrokenGeodesicLoop hr m))).cast
      (sampleBrokenGeodesicLoop_reparam_vertexTimeMap hr hδ q hL).symm rfl)
    (q' := (sampleBrokenGeodesicLoopHomotopy hr m).evalAt ⟨_, hγ⟩) (funext fun u ↦ ?_)
    (Path.cast_coe _ _ _)
    (homotopic_evalAt_sampleBrokenGeodesicLoopHomotopy_map_slideLoopPath hr hδ q hL hγ).symm
  rw [Path.map_coe, Function.comp_apply, ContinuousMap.Homotopy.evalAt_apply, Path.cast_coe,
    Path.map_coe, Function.comp_apply, cyclicDistanceCutBrokenGeodesic_apply,
    sampleBrokenGeodesicLoop_apply hr m _
    (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin
      (reparam_slideTimeMapPath_mem_arcsWithin hr hδ q hL u))]
  refine brokenGeodesicLoop_eq_of_eq hr _ _ (funext fun j ↦ ?_)
  rw [coe_cyclicDistanceCutSampleBrokenGeodesicHomotopy_apply]
  exact (sample_reparam_slideTimeMapPath hr hδ q u j).symm

end TimeMap

/-! ### The colimit with local coefficients -/

section Colimit

variable {δ : (n : ℕ) → Fin (n + 1) → ℝ}

/-- The sum of the cut-offs of the tuples of stage `j` with their first vertex repeated `k` more
times is at most `(j + k + 1) δ_{j + k}`, for growing cut-offs and `0 < k`. -/
private theorem sum_repeatCutoff_le (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {j k : ℕ} (hk : 0 < k)
    (i : Fin (j + k + 0 + 1)) :
    ∑ l : Fin (j + k + 1), δ j ⟨l - k, by omega⟩ ≤ ((j + k + 0 + 1 : ℕ) : ℝ) * δ (j + k) i :=
  calc ∑ l : Fin (j + k + 1), δ j ⟨l - k, by omega⟩ ≤ ∑ _l : Fin (j + k + 1), δ (j + k) i :=
        Finset.sum_le_sum fun _ _ ↦ cutoff_le_of_forall_le_succ_of_lt hδ (by omega) _ _
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

include hr in
/-- **The two homotopies of the approximation by broken geodesics are coherent.** For a compact
family `K` of tuples of the distance cut `𝓛ʲM` and a compact family `K'` of free loops containing
their broken geodesics, at a late enough stage `𝓛ᵐM`: the samples `e` of the loops of `K'`, the
homotopy `G` straightening the loops of `K'` into the broken geodesics through their samples, and
the homotopy `H` sliding the vertices of the repeated tuples of `K` to the samples of their broken
geodesics agree over the free loop space, as the local-coefficient form of the compact
approximation asks. -/
private theorem cyclicDistanceCutCocone_coherent (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (j : ℕ)
    (K : Set ((cyclicDistanceCutFunctor M hpos.le hδ).obj j))
    (K' : Set (cyclicDistanceCutCocone hr hlt hpos.le hδ).pt) (hK' : IsCompact K')
    (hKK' : Set.MapsTo ((cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app j) K K') :
    ∃ (i : ℕ) (f : j ⟶ i) (e : C(K', (cyclicDistanceCutFunctor M hpos.le hδ).obj i))
      (G : (((cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app i).hom.comp e).Homotopy
        (ContinuousMap.subtypeVal K'))
      (H : (e.comp ⟨hKK'.restrict,
        ((cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app j).hom.continuous.restrict
          hKK'⟩).Homotopy
          (((cyclicDistanceCutFunctor M hpos.le hδ).map f).hom.comp (ContinuousMap.subtypeVal K))),
      ∀ x : K, ((H.evalAt x).map
        ((cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app i).hom.continuous).Homotopic
          ((G.evalAt ⟨(cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app j x, hKK' x.property⟩).cast
            rfl (ConcreteCategory.congr_hom ((cyclicDistanceCutCocone hr hlt hpos.le hδ).w f)
              x.val)) := by
  have hr0 : 0 < r := hpos.trans (hlt 0 0)
  -- At a late enough stage `m`, the loops of `K'` have short arcs and are sampled into `𝓛ᵐM`.
  obtain ⟨N, hN⟩ :=
    MooreFreeLoopSpace.exists_subset_arcsWithin_mapsTo_sample_cyclicDistanceCut hK' hr0 hpos
  obtain ⟨hKA, hmaps⟩ := hN (j + (N + 1)) (by omega)
  have hmaps' := hmaps (δ (j + (N + 1)))
    fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ (by omega) 0 i
  let ι : C(K', MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (j + (N + 1) + 1)) :=
    ⟨fun γ ↦ ⟨γ.val, hKA γ.property⟩, continuous_subtypeVal.subtype_mk _⟩
  let e : C(K', cyclicDistanceCut (X := M) (δ (j + (N + 1)))) :=
    ⟨fun γ ↦ ⟨_, hmaps' γ.property⟩,
      ((MooreFreeLoopSpace.continuous_sample _).comp continuous_subtypeVal).subtype_mk _⟩
  -- The tuples of `K` with their first vertex repeated lie in a distance cut of stage `m`, whose
  -- broken geodesics are short enough to slide their vertices into `𝓛ᵐM`.
  let δ'' : Fin (j + (N + 1) + 1) → ℝ := fun i ↦ δ j ⟨i - (N + 1), by omega⟩
  have hδ'' : ∀ i, δ'' i < r := fun i ↦ hlt j _
  have hδ''δ : ∀ i : Fin (j + (N + 1) + 0 + 1), δ'' ⟨i - 0, by omega⟩ ≤ δ (j + (N + 1)) i :=
    fun i ↦ cutoff_le_of_forall_le_succ_of_lt hδ (by omega) _ _
  have hm : ∀ i, ∑ l, δ'' l ≤ ((j + (N + 1) + 0 + 1 : ℕ) : ℝ) * δ (j + (N + 1)) i :=
    sum_repeatCutoff_le hδ N.succ_pos
  let ρ : C(K, cyclicDistanceCut (X := M) δ'') :=
    (cyclicDistanceCutRepeatFirstIterate (N + 1) (δ' := δ'') fun _ ↦ le_rfl).comp
      (ContinuousMap.subtypeVal K)
  have hgeo : ∀ x : K, cyclicDistanceCutBrokenGeodesic hr hδ'' (ρ x) =
      (cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app j x :=
    fun x ↦ cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirstIterate hr (hlt j) hδ''
      (fun _ ↦ le_rfl) x.val
  refine ⟨j + (N + 1), homOfLE (Nat.le_add_right j (N + 1)), e,
    ((sampleBrokenGeodesicLoopHomotopy hr (j + (N + 1))).compContinuousMap ι).symm.cast
      (ContinuousMap.ext fun γ ↦ ?_) (ContinuousMap.ext fun γ ↦ rfl),
    ((cyclicDistanceCutSampleBrokenGeodesicHomotopy hr (k := 0) hδ'' hδ''δ hm).compContinuousMap
      ρ).symm.cast (ContinuousMap.ext fun x ↦ ?_) (ContinuousMap.ext fun x ↦ ?_), fun x ↦ ?_⟩
  · -- The broken geodesic through the samples of a loop is `geoᵐ` of its samples.
    rw [ContinuousMap.comp_apply, sampleBrokenGeodesicLoop_apply _ _ _
      (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin (ι γ).property)]
    exact (cyclicDistanceCutBrokenGeodesic_apply hr (hlt _) (e γ)).symm
  · -- Sampling the broken geodesic of a repeated tuple is sampling the broken geodesic of the
    -- tuple.
    refine Subtype.ext ?_
    rw [ContinuousMap.comp_apply, coe_cyclicDistanceCutSampleBrokenGeodesic_apply, hgeo]
    -- The local map `e` samples a loop by its definition.
    exact congrArg (fun γ : MooreFreeLoopSpace M ↦ γ.toMoorePath.sample _)
      (MapsTo.val_restrict_apply hKK' x).symm
  · -- Repeating the first vertex `N + 1` times and then `0` times is the map of the sequence.
    refine Subtype.ext
      ((coe_cyclicDistanceCutRepeatFirstIterate_zero_apply (fun i ↦ hδ''δ i) (ρ x)).trans ?_)
    rw [cyclicDistanceCutFunctor_map_homOfLE M hpos.le hδ j (N + 1)
      (cutoff_sub_le_of_forall_le_succ hδ j (N + 1)), ContinuousMap.comp_apply,
      ContinuousMap.subtypeVal_apply]
    funext i
    rw [ContinuousMap.comp_apply, ContinuousMap.subtypeVal_apply,
      coe_cyclicDistanceCutRepeatFirstIterate_apply, coe_cyclicDistanceCutRepeatFirstIterate_apply]
  · -- The coherence is that of the slide and the straightening at the stage `m`.
    have hγ : cyclicDistanceCutBrokenGeodesic hr hδ'' (ρ x) ∈
        MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (j + (N + 1) + 1) :=
      hgeo x ▸ hKA (hKK' x.property)
    refine Path.Homotopic.of_coe_eq
      (p' := (((cyclicDistanceCutSampleBrokenGeodesicHomotopy hr (k := 0) hδ'' hδ''δ hm).evalAt
        (ρ x)).map (cyclicDistanceCutBrokenGeodesic hr (hlt _)).continuous).symm) ?_ ?_
      (homotopic_map_evalAt_cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ'' (ρ x)
        (hlt _) hδ''δ hm hγ).symm₂
    · exact ContinuousMap.Homotopy.coe_map_evalAt_cast_symm_compContinuousMap _ _ _ _ _ _ _
        (DFunLike.congr_fun (cyclicDistanceCutCocone_ι_app_hom hr hlt hpos.le hδ _))
    · -- The loop `geoʲ x` with its short arcs is the broken geodesic of the repeated tuple.
      exact ContinuousMap.Homotopy.coe_cast_evalAt_cast_symm_compContinuousMap _ _ _ _
        (Subtype.ext (hgeo x).symm) _ _ _ _

/-- **The homology of the free loop space with local coefficients is the colimit of the homology
of the distance cuts.** For cut-offs `δ n i < r` which grow from each stage to the next,
`δ n i ≤ δ (n + 1) j`, and with `δ 0 0` positive, and for a local system `L` on the free loop
space, the broken-geodesic maps `geoⁿ : 𝓛ⁿM → 𝓛M` induce an isomorphism
`colimₙ Hₖ(𝓛ⁿM; (geoⁿ)^* L) ≅ Hₖ(𝓛M; L)`. -/
def isColimitWhiskerOverTwistedHomologyCyclicDistanceCutCocone {R : Type*} [Ring R]
    (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j)
    (L : LocalCoefficientSystem.{_, u, max u w} R (cyclicDistanceCutCocone hr hlt hpos.le hδ).pt)
    (k : ℕ) :
    IsColimit ((LocalCoefficientSystem.overTwistedHomologyCocone L k).whisker
      ((cyclicDistanceCutFunctor M hpos.le hδ).toOver _
        (cyclicDistanceCutCocone hr hlt hpos.le hδ).ι.app
        (cyclicDistanceCutCocone hr hlt hpos.le hδ).w)) :=
  LocalCoefficientSystem.isColimitWhiskerOverTwistedHomologyCoconeOfCompactApprox _ L
    (fun _ hK ↦ exists_cyclicDistanceCutCocone_ι_app_comp_homotopic hr hpos hlt hδ hK)
    (fun j K K' _ hK' hKK' ↦
      let ⟨i, f, e, G, H, h⟩ := cyclicDistanceCutCocone_coherent hr hpos hlt hδ j K K' hK' hKK'
      ⟨i, f, e, G, H, fun x ↦ congrArg L.map (Path.Homotopic.Quotient.eq.2 (h x))⟩) k

end Colimit

end TauCeti.Manifold
