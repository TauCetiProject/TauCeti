/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Broken
public import TauCeti.Topology.PathSpace.Moore.Sampling
import TauCeti.Topology.Algebra.Monoid

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
(`TauCeti.combo_mem_cyclicDistanceCutTimes`). Since the broken geodesic is
`1`-Lipschitz, the interpolated samples lie in the distance cut all along.

## Main definitions

* `TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesic`: the composite `evₘ₊₁ ∘ geoⁿ` of
  distance cuts.
* `TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesicHomotopy`: the homotopy from the iterate
  of `ι` to `evₘ₊₁ ∘ geoⁿ`.

## Main results

* `TauCeti.Manifold.sample_cyclicDistanceCutBrokenGeodesic_mem_cyclicDistanceCut`: the equally
  spaced samples of a broken geodesic through a tuple of a distance cut lie in a distance cut.
* `TauCeti.Manifold.coe_cyclicDistanceCutSampleBrokenGeodesicHomotopy_apply_zero`: the slide keeps
  the first vertex.
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

/-! ### Sliding the samples inside a distance cut -/

section Cut

include hr

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

/-- The first sample of the broken geodesic through `q` is its base point, the first vertex `q₀`. -/
theorem coe_cyclicDistanceCutSampleBrokenGeodesic_apply_zero {n : ℕ} {δ : Fin (n + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (m : ℕ) {δ' : Fin (m + 1) → ℝ}
    (hm : ∀ j, ∑ i, δ i ≤ ((m + 1 : ℕ) : ℝ) * δ' j) (q : cyclicDistanceCut (X := M) δ) :
    (cyclicDistanceCutSampleBrokenGeodesic hr hδ m hm q : Fin (m + 1) → M) 0 = q.val 0 := by
  simp

/-- The times of the slide at `s`: the convex combination `(1 - s) aⱼ + s bⱼ` of the time `aⱼ` at
which the closed broken geodesic through `q` passes through the `j`-th vertex of
`(q₀, …, q₀, q₁, …, qₙ)` and the equally spaced time `bⱼ = L j / (n + k + 1)` for its length `L`. -/
private def slideTimes {n k : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r) (s : unitInterval)
    (q : cyclicDistanceCut (X := M) δ) (j : Fin (n + k + 1)) : ℝ≥0 :=
  unitInterval.toNNReal (unitInterval.symm s) *
      Fin.partialSum (fun i ↦ nndist (q.val i) (q.val (i + 1))) (Fin.castSucc ⟨j - k, by omega⟩) +
    unitInterval.toNNReal s * ((cyclicDistanceCutBrokenGeodesic hr hδ q).length *
      ((j : ℕ) / (n + k + 1 : ℕ) : ℝ≥0))

/-- At the start of the slide, the times are the vertex times. -/
@[simp]
private theorem slideTimes_zero {n k : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (q : cyclicDistanceCut (X := M) δ) (j : Fin (n + k + 1)) :
    slideTimes hr hδ 0 q j =
      Fin.partialSum (fun i ↦ nndist (q.val i) (q.val (i + 1)))
        (Fin.castSucc ⟨j - k, by omega⟩) := by
  simp [slideTimes]

/-- At the end of the slide, the times are the equally spaced times. -/
@[simp]
private theorem slideTimes_one {n k : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (q : cyclicDistanceCut (X := M) δ) (j : Fin (n + k + 1)) :
    slideTimes hr hδ 1 q j =
      (cyclicDistanceCutBrokenGeodesic hr hδ q).length * ((j : ℕ) / (n + k + 1 : ℕ) : ℝ≥0) := by
  simp [slideTimes]

/-- The times of the slide depend continuously on the slide time and on the tuple. -/
private theorem continuous_slideTimes {n k : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (j : Fin (n + k + 1)) :
    Continuous fun x : unitInterval × cyclicDistanceCut (X := M) δ ↦
      slideTimes hr hδ x.1 x.2 j := by
  -- The vertex times are partial sums of continuous functions of the tuple.
  have hpartial : Continuous fun q : cyclicDistanceCut (X := M) δ ↦
      Fin.partialSum (fun l ↦ nndist (q.val l) (q.val (l + 1))) (Fin.castSucc ⟨j - k, by omega⟩) :=
    Continuous.finPartialSum (fun _ ↦ ((continuous_apply _).comp continuous_subtypeVal).nndist
      ((continuous_apply _).comp continuous_subtypeVal)) _
  refine ((unitInterval.toNNReal_continuous.comp (unitInterval.continuous_symm.comp
    continuous_fst)).mul (hpartial.comp continuous_snd)).add
    ((unitInterval.toNNReal_continuous.comp continuous_fst).mul ?_)
  exact (MooreFreeLoopSpace.continuous_length.comp
    ((map_continuous (cyclicDistanceCutBrokenGeodesic hr hδ)).comp continuous_snd)).mul
    continuous_const

/-- The samples of the broken geodesic through `q` at the times of the slide lie in the distance
cut. -/
private theorem slide_mem_cyclicDistanceCut {n k : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) (s : unitInterval)
    (q : cyclicDistanceCut (X := M) δ) :
    (fun j ↦ (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath (slideTimes hr hδ s q j)) ∈
      cyclicDistanceCut δ' := by
  have hL := length_cyclicDistanceCutBrokenGeodesic_le hr hδ q
  have hvertex : (fun j : Fin (n + k + 1) ↦
      Fin.partialSum (fun i ↦ nndist (q.val i) (q.val (i + 1)))
        (Fin.castSucc ⟨j - k, by omega⟩)) ∈
        cyclicDistanceCutTimes (cyclicDistanceCutBrokenGeodesic hr hδ q).length δ' := by
    rw [cyclicDistanceCutBrokenGeodesic_apply, length_brokenGeodesicLoop_eq_partialSum]
    exact partialSum_mem_cyclicDistanceCutTimes hδδ' q.property
  have hLip : LipschitzWith 1 (cyclicDistanceCutBrokenGeodesic hr hδ q).toMoorePath := by
    rw [cyclicDistanceCutBrokenGeodesic_apply]
    exact lipschitzWith_brokenGeodesicLoop hr _ _ _
  exact MooreFreeLoopSpace.apply_mem_cyclicDistanceCut hLip (combo_mem_cyclicDistanceCutTimes
    hvertex (mul_div_mem_cyclicDistanceCutTimes fun j ↦ hL.trans (hm j)) s)

/-- **Sliding the sampled vertices along the broken geodesics.** For cut-offs `δ i < r` with
`δ (j - k) ≤ δ' j` and `∑ i, δ i ≤ (n + k + 1) * δ' j` for every `j`, the homotopy of maps from the
distance cut with cut-offs `δ` to the one with cut-offs `δ'` from the iterate
`ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ` repeating the first vertex `k` more times
(`TauCeti.cyclicDistanceCutRepeatFirstIterate`) to the samples `evₙ₊ₖ₊₁ ∘ geoⁿ` of the broken
geodesics (`TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesic`). At time `s` it evaluates the
broken geodesic through `q` at the times `(1 - s) aⱼ + s bⱼ`, where `aⱼ` is the time at which it
passes through the `j`-th vertex of `(q₀, …, q₀, q₁, …, qₙ)` and `bⱼ = L j / (n + k + 1)` for its
length `L`. -/
def cyclicDistanceCutSampleBrokenGeodesicHomotopy {n k : ℕ} {δ : Fin (n + 1) → ℝ}
    {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    (cyclicDistanceCutRepeatFirstIterate (X := M) k hδδ').Homotopy
      (cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm) where
  toFun x := ⟨fun j ↦ (cyclicDistanceCutBrokenGeodesic hr hδ x.2).toMoorePath
      (slideTimes hr hδ x.1 x.2 j), slide_mem_cyclicDistanceCut hr hδ hδδ' hm x.1 x.2⟩
  continuous_toFun := Continuous.subtype_mk (continuous_pi fun j ↦
    (MooreFreeLoopSpace.continuous_toMoorePath.comp
      ((map_continuous (cyclicDistanceCutBrokenGeodesic hr hδ)).comp continuous_snd)).moorePath_eval
      (continuous_slideTimes hr hδ j)) _
  map_zero_left q := by
    ext j
    simp only [slideTimes_zero, cyclicDistanceCutBrokenGeodesic_apply,
      brokenGeodesicLoop_apply_partialSum, coe_cyclicDistanceCutRepeatFirstIterate_apply]
  map_one_left q := by
    ext j
    simp only [slideTimes_one, coe_cyclicDistanceCutSampleBrokenGeodesic_apply,
      MoorePath.sample_apply, MooreFreeLoopSpace.length_toMoorePath]

/-- At `p = (s, q)`, the `j`-th vertex of the slide is the broken geodesic through `q` evaluated at
the `j`-th time of the slide at `s`. It is private since the times of the slide are. -/
private theorem coe_cyclicDistanceCutSampleBrokenGeodesicHomotopy_apply {n k : ℕ}
    {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j)
    (p : unitInterval × cyclicDistanceCut (X := M) δ) (j : Fin (n + k + 1)) :
    (cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm p : Fin (n + k + 1) → M) j =
      (cyclicDistanceCutBrokenGeodesic hr hδ p.2).toMoorePath (slideTimes hr hδ p.1 p.2 j) :=
  (rfl)

/-- **The slide keeps the first vertex.** For the vertex `0` both families of times are `0`, so at
every time of the slide the first vertex is the base point `q₀` of the broken geodesic through `q`.
So the slide restricts to the tuples with a prescribed first vertex. -/
@[simp]
theorem coe_cyclicDistanceCutSampleBrokenGeodesicHomotopy_apply_zero {n k : ℕ}
    {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j)
    (p : unitInterval × cyclicDistanceCut (X := M) δ) :
    (cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm p : Fin (n + k + 1) → M) 0 =
      p.2.val 0 := by
  have h0 : slideTimes hr hδ p.1 p.2 (0 : Fin (n + k + 1)) = 0 := by
    simp [slideTimes]
  rw [coe_cyclicDistanceCutSampleBrokenGeodesicHomotopy_apply, h0]
  simp [← MoorePath.source_def]

/-- **`ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₙ₊ₖ₊₁ ∘ geoⁿ`.** For cut-offs `δ i < r` with `δ (j - k) ≤ δ' j` and
`∑ i, δ i ≤ (n + k + 1) * δ' j` for every `j`, repeating the first vertex `k` more times and
sampling the broken geodesics at `n + k + 1` equally spaced times are homotopic maps from the
distance cut with cut-offs `δ` to the one with cut-offs `δ'`. -/
theorem homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic {n k : ℕ}
    {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    (cyclicDistanceCutRepeatFirstIterate (X := M) k hδδ').Homotopic
      (cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm) :=
  ⟨cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm⟩

end Cut

end TauCeti.Manifold
