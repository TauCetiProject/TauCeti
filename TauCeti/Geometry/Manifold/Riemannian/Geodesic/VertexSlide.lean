/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Broken
public import TauCeti.Topology.PathSpace.Moore.Lipschitz
public import TauCeti.Topology.PathSpace.Moore.Sampling
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Sliding the sampled vertices along a broken geodesic

Abouzaid's finite-dimensional approximation of the free loop space of a Riemannian manifold `M`
uses the distance cuts `𝓛ⁿM = {q ∈ Mⁿ⁺¹ | d(qᵢ, qᵢ₋₁) ≤ δᵢ}`, the maps `geoⁿ : 𝓛ⁿM → 𝓛M` to the
closed broken geodesics through their vertices
(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`), the embeddings `ιⁿ : 𝓛ⁿM → 𝓛ⁿ⁺¹M`
repeating the first vertex (`TauCeti.cyclicDistanceCutRepeatFirst`), and the sampling maps
`evₘ₊₁ : 𝓛M → Mᵐ⁺¹` at `m + 1` equally spaced times (`TauCeti.MoorePath.sample`). This file
proves that sampling a broken geodesic finely enough gives back its vertices up to homotopy: for
`m = n + k`, the composite `evₘ₊₁ ∘ geoⁿ` lands in a distance cut `𝓛ᵐM` and is homotopic inside it
to the iterate `ιᵐ⁻¹ ∘ ⋯ ∘ ιⁿ` repeating the first vertex `k` more times
(`TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesicHomotopy`). This is the step of the proof
that the colimit of the approximations is weakly equivalent to the free loop space which shows
injectivity on homotopy groups: a sphere in `𝓛ⁿM` whose broken geodesics bound in `𝓛M` already
bounds in some `𝓛ᵐM`.

The homotopy slides the sampled vertices along the broken geodesic. The closed broken geodesic
through `q` is `1`-Lipschitz in its time (`TauCeti.Manifold.lipschitzWith_brokenGeodesicLoop`),
and it passes through the vertex `qᵢ` at the time `d(q₀, q₁) + ⋯ + d(qᵢ₋₁, qᵢ)`
(`TauCeti.Manifold.brokenGeodesicLoop_apply_partialSum`). Evaluated at these vertex times, with the
first one repeated, it gives the iterate of `ι`; evaluated at the equally spaced times it gives the
samples. Along the linear interpolation between the two families of times, the consecutive times
stay ordered and their gaps stay below the cut-offs: the gaps between vertex times are the edges
of `q`, and the gaps between equally spaced times are the length divided by `m + 1`
(`TauCeti.MooreFreeLoopSpace.combo_mem_cyclicDistanceCutTimes`). Since the broken geodesic is
`1`-Lipschitz, the interpolated samples lie in the distance cut all along.

## Main definitions

* `TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesic`: the composite `evₘ₊₁ ∘ geoⁿ` of
  distance cuts.
* `TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesicHomotopy`: the homotopy from the iterate
  of `ι` to `evₘ₊₁ ∘ geoⁿ`.

## Main results

* `TauCeti.Manifold.lipschitzWith_geodesicSegment`, `TauCeti.Manifold.lipschitzWith_brokenGeodesic`,
  `TauCeti.Manifold.lipschitzWith_brokenGeodesicLoop`: broken geodesics are `1`-Lipschitz.
* `TauCeti.Manifold.brokenGeodesic_apply_partialSum`,
  `TauCeti.Manifold.brokenGeodesicLoop_apply_partialSum`: the vertex times.
* `TauCeti.Manifold.homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`:
  `ιᵐ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₘ₊₁ ∘ geoⁿ` as maps `𝓛ⁿM → 𝓛ᵐM`.

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

/-! ### Broken geodesics are `1`-Lipschitz -/

section Lipschitz

include hr

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

/-- A closed broken geodesic is `1`-Lipschitz in its time. -/
theorem lipschitzWith_brokenGeodesicLoop (n : ℕ) (q : Fin (n + 1) → M)
    (h : ∀ i, dist (q i) (q (i - 1)) < r) :
    LipschitzWith 1 (brokenGeodesicLoop hr n q h).toMoorePath := by
  rw [toMoorePath_brokenGeodesicLoop hr n q h (forall_dist_snoc_lt h)]
  exact lipschitzWith_brokenGeodesic hr _ _ _

end Lipschitz

/-! ### The vertex times -/

section Vertex

/-- The distances between consecutive vertices of `q 0, …, q (n + 1)`, after the first one, are
those of `q 1, …, q (n + 1)`. -/
private theorem tail_nndist_castSucc_succ {n : ℕ} (q : Fin (n + 2) → M) :
    Fin.tail (fun k : Fin (n + 1) ↦ nndist (q k.castSucc) (q k.succ)) =
      fun k : Fin n ↦ nndist (Fin.tail q k.castSucc) (Fin.tail q k.succ) := by
  funext k
  simp only [Fin.tail, Fin.succ_castSucc]

/-- The edges of `q 0, …, q n, q 0` are the cyclic edges of `q`. -/
private theorem nndist_snoc_castSucc_succ {n : ℕ} (q : Fin (n + 1) → M) :
    (fun k : Fin (n + 1) ↦ nndist ((Fin.snoc q (q 0) : Fin (n + 2) → M) k.castSucc)
      ((Fin.snoc q (q 0) : Fin (n + 2) → M) k.succ)) = fun k ↦ nndist (q k) (q (k + 1)) :=
  funext fun k ↦ by rw [Fin.snoc_castSucc, Fin.snoc_self_zero_succ]

include hr

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
  induction n with
  | zero => simp
  | succ n ih =>
    rw [brokenGeodesic_succ hr n q h (forall_dist_tail_lt h), MoorePath.length_trans,
      ih (Fin.tail q) (forall_dist_tail_lt h),
      length_geodesicSegment, ← Fin.succ_last, Fin.partialSum_succ', tail_nndist_castSucc_succ]

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

end Vertex

/-! ### Sliding the samples inside a distance cut -/

section Cut

include hr

/-- The length of the closed broken geodesic through a tuple of a distance cut is at most the sum of
the cut-offs. -/
theorem length_cyclicDistanceCutBrokenGeodesic_le {n : ℕ} {δ : Fin (n + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (q : cyclicDistanceCut (X := M) δ) :
    ((cyclicDistanceCutBrokenGeodesic hr hδ q).length : ℝ) ≤ ∑ i, δ i := by
  rw [cyclicDistanceCutBrokenGeodesic_apply, length_brokenGeodesicLoop, NNReal.coe_sum]
  exact Finset.sum_le_sum fun i _ ↦ by
    rw [coe_nndist]
    exact mem_cyclicDistanceCut.1 q.2 i

/-- The `m + 1` equally spaced samples of the closed broken geodesic through a tuple of the distance
cut with cut-offs `δ` lie in the distance cut with cut-offs `δ'` when `∑ i, δ i ≤ (m + 1) * δ' j`
for every `j`: the broken geodesic is `1`-Lipschitz and its length is at most `∑ i, δ i`. -/
theorem sample_cyclicDistanceCutBrokenGeodesic_mem_cyclicDistanceCut {n : ℕ}
    {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r) {m : ℕ} {δ' : Fin (m + 1) → ℝ}
    (hm : ∀ j, ∑ i, δ i ≤ ((m + 1 : ℕ) : ℝ) * δ' j) (q : cyclicDistanceCut (X := M) δ) :
    (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.sample (m + 1) ∈
      cyclicDistanceCut δ' := by
  have hL := length_cyclicDistanceCutBrokenGeodesic_le hr hδ q
  rw [funext (MoorePath.sample_apply _ (m + 1)), MooreFreeLoopSpace.length_toMoorePath]
  rw [cyclicDistanceCutBrokenGeodesic_apply] at hL ⊢
  exact MooreFreeLoopSpace.apply_mem_cyclicDistanceCut (lipschitzWith_brokenGeodesicLoop hr _ _ _)
    (mul_div_mem_cyclicDistanceCutTimes fun j ↦ hL.trans (hm j))

/-- **Sampling broken geodesics, `evₘ₊₁ ∘ geoⁿ : 𝓛ⁿM → 𝓛ᵐM`.** For cut-offs `δ i < r`, the `m + 1`
equally spaced samples (`TauCeti.MoorePath.sample`) of the closed broken geodesic through each tuple
of the distance cut with cut-offs `δ`, as a continuous map to the distance cut with cut-offs `δ'`,
when `∑ i, δ i ≤ (m + 1) * δ' j` for every `j`. -/
def cyclicDistanceCutSampleBrokenGeodesic {n : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (m : ℕ) {δ' : Fin (m + 1) → ℝ} (hm : ∀ j, ∑ i, δ i ≤ ((m + 1 : ℕ) : ℝ) * δ' j) :
    C(cyclicDistanceCut (X := M) δ, cyclicDistanceCut (X := M) δ') where
  toFun q := ⟨(cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.sample (m + 1),
    sample_cyclicDistanceCutBrokenGeodesic_mem_cyclicDistanceCut hr hδ hm q⟩
  continuous_toFun := ((MoorePath.continuous_sample _).comp
    (MooreFreeLoopSpace.continuous_toMoorePath.comp (map_continuous _))).subtype_mk _

@[simp]
theorem coe_cyclicDistanceCutSampleBrokenGeodesic_apply {n : ℕ} {δ : Fin (n + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (m : ℕ) {δ' : Fin (m + 1) → ℝ}
    (hm : ∀ j, ∑ i, δ i ≤ ((m + 1 : ℕ) : ℝ) * δ' j) (q : cyclicDistanceCut (X := M) δ) :
    (cyclicDistanceCutSampleBrokenGeodesic hr hδ m hm q : Fin (m + 1) → M) =
      (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath.sample (m + 1) :=
  (rfl)

/-- The samples of the broken geodesic through `q` at the interpolated times
`(1 - s) aⱼ + s bⱼ` of the slide lie in the distance cut. -/
private theorem slide_mem_cyclicDistanceCut {n k : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδδ' : ∀ i j, δ i ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) (s : unitInterval)
    (q : cyclicDistanceCut (X := M) δ) :
    (fun j : Fin (n + k + 1) ↦ (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath
      (unitInterval.toNNReal (unitInterval.symm s) *
          Fin.partialSum (fun i ↦ nndist (q.1 i) (q.1 (i + 1))) (Fin.castSucc ⟨j - k, by omega⟩) +
        unitInterval.toNNReal s * ((cyclicDistanceCutBrokenGeodesic hr hδ q).length *
          ((j : ℕ) / (n + k + 1 : ℕ) : ℝ≥0)))) ∈ cyclicDistanceCut δ' := by
  have hL := length_cyclicDistanceCutBrokenGeodesic_le hr hδ q
  rw [cyclicDistanceCutBrokenGeodesic_apply] at hL ⊢
  refine MooreFreeLoopSpace.apply_mem_cyclicDistanceCut
    (lipschitzWith_brokenGeodesicLoop hr _ _ _) (combo_mem_cyclicDistanceCutTimes ?_ ?_ s)
  · rw [length_brokenGeodesicLoop_eq_partialSum]
    exact partialSum_mem_cyclicDistanceCutTimes hδδ' q.2
  · exact mul_div_mem_cyclicDistanceCutTimes fun j ↦ hL.trans (hm j)

/-- **Sliding the sampled vertices along the broken geodesics.** For cut-offs `δ i < r` with every
`δ i` at most every `δ' j` and `∑ i, δ i ≤ (n + k + 1) * δ' j`, the homotopy of maps from the
distance cut with cut-offs `δ` to the one with cut-offs `δ'` from the iterate
`ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ` repeating the first vertex `k` more times
(`TauCeti.cyclicDistanceCutRepeatFirstIterate`) to the samples `evₙ₊ₖ₊₁ ∘ geoⁿ` of the broken
geodesics (`TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesic`). At time `s` it evaluates the
broken geodesic through `q` at the times `(1 - s) aⱼ + s bⱼ`, where `aⱼ` is the time at which it
passes through the `j`-th vertex of `(q₀, …, q₀, q₁, …, qₙ)` and `bⱼ = L j / (n + k + 1)` for its
length `L`. -/
def cyclicDistanceCutSampleBrokenGeodesicHomotopy {n k : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r) (hδδ' : ∀ i j, δ i ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    (cyclicDistanceCutRepeatFirstIterate (X := M) k hδδ').Homotopy
      (cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm) where
  toFun x := ⟨fun j ↦ (cyclicDistanceCutBrokenGeodesic hr hδ x.2).toMoorePath
      (unitInterval.toNNReal (unitInterval.symm x.1) *
          Fin.partialSum (fun i ↦ nndist (x.2.1 i) (x.2.1 (i + 1)))
            (Fin.castSucc ⟨j - k, by omega⟩) +
        unitInterval.toNNReal x.1 * ((cyclicDistanceCutBrokenGeodesic hr hδ x.2).length *
          ((j : ℕ) / (n + k + 1 : ℕ) : ℝ≥0))),
    slide_mem_cyclicDistanceCut hr hδ hδδ' hm x.1 x.2⟩
  continuous_toFun := by
    -- The vertex times are partial sums of continuous functions of the tuple.
    have hpartial : ∀ i : Fin (n + 2), Continuous fun q : cyclicDistanceCut (X := M) δ ↦
        Fin.partialSum (fun l ↦ nndist (q.1 l) (q.1 (l + 1))) i := fun i ↦ by
      induction i using Fin.induction with
      | zero => simp only [Fin.partialSum_zero]; exact continuous_const
      | succ i ih =>
        simp only [Fin.partialSum_succ]
        exact ih.add (((continuous_apply _).comp continuous_subtype_val).nndist
          ((continuous_apply _).comp continuous_subtype_val))
    have hgeo : Continuous fun x : unitInterval × cyclicDistanceCut (X := M) δ ↦
        cyclicDistanceCutBrokenGeodesic hr hδ x.2 :=
      (map_continuous (cyclicDistanceCutBrokenGeodesic hr hδ)).comp continuous_snd
    refine Continuous.subtype_mk (continuous_pi fun j ↦
      (MooreFreeLoopSpace.continuous_toMoorePath.comp hgeo).moorePath_eval ?_) _
    refine ((unitInterval.toNNReal_continuous.comp (unitInterval.continuous_symm.comp
      continuous_fst)).mul ((hpartial _).comp continuous_snd)).add
      ((unitInterval.toNNReal_continuous.comp continuous_fst).mul ?_)
    exact (MooreFreeLoopSpace.continuous_length.comp hgeo).mul continuous_const
  map_zero_left q := by
    ext j
    simp only [unitInterval.symm_zero, unitInterval.toNNReal_one, unitInterval.toNNReal_zero,
      one_mul, zero_mul, add_zero, cyclicDistanceCutBrokenGeodesic_apply,
      brokenGeodesicLoop_apply_partialSum, coe_cyclicDistanceCutRepeatFirstIterate_apply]
  map_one_left q := by
    ext j
    simp only [unitInterval.symm_one, unitInterval.toNNReal_one, unitInterval.toNNReal_zero,
      one_mul, zero_mul, zero_add, coe_cyclicDistanceCutSampleBrokenGeodesic_apply,
      MoorePath.sample_apply, MooreFreeLoopSpace.length_toMoorePath]

/-- **`ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₙ₊ₖ₊₁ ∘ geoⁿ`.** For cut-offs `δ i < r` with every `δ i` at most every
`δ' j` and `∑ i, δ i ≤ (n + k + 1) * δ' j`, repeating the first vertex `k` more times and sampling
the broken geodesics at `n + k + 1` equally spaced times are homotopic maps from the distance cut
with cut-offs `δ` to the one with cut-offs `δ'`. -/
theorem homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic {n k : ℕ}
    {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (hδδ' : ∀ i j, δ i ≤ δ' j) (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    (cyclicDistanceCutRepeatFirstIterate (X := M) k hδδ').Homotopic
      (cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm) :=
  ⟨cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm⟩

end Cut

end TauCeti.Manifold
