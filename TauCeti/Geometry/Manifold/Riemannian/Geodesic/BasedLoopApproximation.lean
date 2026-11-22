/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.Approximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.VertexSlide

/-!
# Approximating compact families of based loops by broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r > 0` be a
radius such that the tangent ball of radius `r` at every point is a normal domain. The free loop
space `𝓛M` is approximated by the distance cuts `𝓛ⁿM = {q | d(qᵢ, qᵢ₋₁) ≤ δᵢ}` through the closed
broken geodesics `geoⁿ : 𝓛ⁿM → 𝓛M` and the samplings `evₙ : 𝓛M → Mⁿ⁺¹`: on a compact family of
free loops, every sufficiently fine `geoⁿ ∘ evₙ` is homotopic to the inclusion
(`TauCeti.Manifold.exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic`), and repeating the
first vertex `k` more times, `ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ`, is homotopic to `evₙ₊ₖ₊₁ ∘ geoⁿ`
(`TauCeti.Manifold.homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`). These
are the two hypotheses under which the distance cuts compute the homology of the free loop space
as a colimit.

This file proves the same two statements for the Moore loops `Ω_x M` based at a point `x`, with
the **based distance cuts** `𝓛ⁿ_x M = {q ∈ 𝓛ⁿM | q₀ = x}` (`TauCeti.basedCyclicDistanceCut`) in
place of the distance cuts. The closed broken geodesic through a tuple with first vertex `x` is a
loop based at `x` (`TauCeti.Manifold.basedCyclicDistanceCutBrokenGeodesic`), and the sampling of a
loop based at `x` has first vertex `x`. Both homotopies of the free statements keep the base
point: the homotopy from a free loop to the broken geodesic through its sampled vertices fixes the
first sampled vertex (`TauCeti.Manifold.basepoint_sampleBrokenGeodesicLoopHomotopy`), and so does
the slide of the vertices along a broken geodesic
(`TauCeti.Manifold.coe_cyclicDistanceCutSampleBrokenGeodesicHomotopy_apply_zero`). So they
restrict to the based loops (`TauCeti.MooreLoopSpace.homotopic_codRestrictFreeLoop`) and to the
based distance cuts.

* **Compact-family approximation.** For a compact family `K` of Moore loops based at `x` and
  cut-offs bounded below by `ε > 0` and less than `r`, every sufficiently fine sampling maps `K`
  into the based distance cut, and `geoⁿ ∘ evₙ : K → Ω_x M` is homotopic to the inclusion of `K`
  (`TauCeti.Manifold.exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic`).
* **Sliding the vertices.** Repeating the first vertex `k` more times and sampling the broken
  geodesics at `n + k + 1` equally spaced times are homotopic maps `𝓛ⁿ_x M → 𝓛ⁿ⁺ᵏ_x M`
  (`TauCeti.Manifold.homotopic_basedCyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`).

## Main definitions

* `TauCeti.Manifold.basedCyclicDistanceCutBrokenGeodesic`: the map `geoⁿ : 𝓛ⁿ_x M → Ω_x M` to the
  closed broken geodesics, as Moore loops based at `x`.
* `TauCeti.Manifold.basedCyclicDistanceCutSampleBrokenGeodesic`: the composite
  `evₘ₊₁ ∘ geoⁿ : 𝓛ⁿ_x M → 𝓛ᵐ_x M` of based distance cuts.

## Main results

* `TauCeti.Manifold.homotopic_codRestrictFreeLoop_sampleBrokenGeodesicLoop`: a family of loops
  based at `x` is homotopic, through loops based at `x`, to the broken geodesics through its
  sampled vertices.
* `TauCeti.Manifold.exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic`: on a compact
  family of based loops, every sufficiently fine `geoⁿ ∘ evₙ` is homotopic to the inclusion.
* `TauCeti.Manifold.homotopic_basedCyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`:
  `ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₙ₊ₖ₊₁ ∘ geoⁿ` as maps `𝓛ⁿ_x M → 𝓛ⁿ⁺ᵏ_x M`.

## References

* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16 (the approximation of the based path space by broken geodesics).
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
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

include hr

/-! ### Broken geodesics on a based distance cut -/

/-- **The broken geodesics through the tuples of a based distance cut**, `geoⁿ : 𝓛ⁿ_x M → Ω_x M`:
for cut-offs `δ i < r`, the closed broken geodesic through each tuple of the distance cut with
first vertex `x`, as a continuous map to the Moore loops based at `x`. It is the restriction of
`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`. -/
def basedCyclicDistanceCutBrokenGeodesic {n : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (x : M) : C(basedCyclicDistanceCut (X := M) δ x, MooreLoopSpace M x) :=
  MooreLoopSpace.codRestrictFreeLoop ((cyclicDistanceCutBrokenGeodesic hr hδ).comp
    (ContinuousMap.inclusion (basedCyclicDistanceCut_subset δ x))) fun q ↦ by
      rw [ContinuousMap.comp_apply, cyclicDistanceCutBrokenGeodesic_apply,
        basepoint_brokenGeodesicLoop]
      exact (mem_basedCyclicDistanceCut.1 q.property).2

/-- The broken geodesic through a tuple of the based distance cut, read as a free loop, is the
broken geodesic through the same tuple of the distance cut. -/
@[simp]
theorem toFreeLoop_basedCyclicDistanceCutBrokenGeodesic_apply {n : ℕ} {δ : Fin (n + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (x : M) (q : basedCyclicDistanceCut (X := M) δ x) :
    (basedCyclicDistanceCutBrokenGeodesic hr hδ x q).toFreeLoop =
      cyclicDistanceCutBrokenGeodesic hr hδ ⟨q.val, (mem_basedCyclicDistanceCut.1 q.property).1⟩ :=
  MooreLoopSpace.toFreeLoop_codRestrictFreeLoop_apply _ _ q

/-! ### Compact families of based loops -/

/-- **Based loops are homotopic, through based loops, to the broken geodesics through their sampled
vertices.** For a continuous family `ι` of free loops based at `x` whose `n + 1` arcs lie within
distance `r` of their initial vertices, the family and the closed broken geodesics through its
sampled vertices are homotopic as families of Moore loops based at `x`: the homotopy
`TauCeti.Manifold.sampleBrokenGeodesicLoopHomotopy` keeps the base point. -/
theorem homotopic_codRestrictFreeLoop_sampleBrokenGeodesicLoop {Y : Type*} [TopologicalSpace Y]
    {n : ℕ} {x : M}
    (ι : C(Y, MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)))
    {hf : ∀ y, ((ContinuousMap.subtypeVal _).comp ι y).basepoint = x}
    {hg : ∀ y, ((sampleBrokenGeodesicLoop hr n).comp ι y).basepoint = x} :
    (MooreLoopSpace.codRestrictFreeLoop _ hf).Homotopic (MooreLoopSpace.codRestrictFreeLoop _ hg) :=
  MooreLoopSpace.homotopic_codRestrictFreeLoop
    ((sampleBrokenGeodesicLoopHomotopy hr n).compContinuousMap ι) fun p ↦ by simpa using hf p.2

/-- **The compact-family approximation of the based loop space by broken geodesics.** For a
compact family `K` of Moore loops based at `x` and `ε > 0` there is `N` such that for every `n ≥ N`
and all cut-offs `ε ≤ δ i < r`, the sampling `evₙ` at `n + 1` times maps `K` into the based distance
cut `𝓛ⁿ_x M = {q | q 0 = x, dist (q i) (q (i - 1)) ≤ δ i}`, and `geoⁿ ∘ evₙ : K → Ω_x M`, with
`geoⁿ` the closed broken geodesic map, is homotopic to the inclusion of `K`. -/
theorem exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic {x : M}
    {K : Set (MooreLoopSpace M x)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ δ : Fin (n + 1) → ℝ, (∀ i, ε ≤ δ i) → ∀ hδ : ∀ i, δ i < r,
      ∃ e : C(K, basedCyclicDistanceCut (X := M) δ x),
        (∀ γ, (e γ : Fin (n + 1) → M) = (γ : MooreLoopSpace M x).toMoorePath.sample (n + 1)) ∧
        ((basedCyclicDistanceCutBrokenGeodesic hr hδ x).comp e).Homotopic
          (ContinuousMap.subtypeVal K) := by
  by_cases hr0 : 0 < r
  swap
  · exact ⟨0, fun n _ δ hεδ hδ ↦ absurd ((hε.trans_le (hεδ 0)).trans (hδ 0)) hr0⟩
  -- The loops of `K`, read as free loops, form a compact family.
  have hK' : IsCompact (MooreLoopSpace.toFreeLoop '' K) :=
    hK.image MooreLoopSpace.continuous_toFreeLoop
  obtain ⟨N₁, -, hN₁⟩ := MoorePath.exists_subset_arcsWithin
    (hK'.image MooreFreeLoopSpace.continuous_toMoorePath) (Metric.dist_mem_uniformity hr0)
  obtain ⟨N₂, hN₂⟩ := MooreFreeLoopSpace.exists_mapsTo_sample_cyclicDistanceCut hK' hε
  refine ⟨max N₁ N₂, fun n hn δ hεδ hδ ↦ ?_⟩
  have hKA (γ : K) : (γ : MooreLoopSpace M x).toFreeLoop ∈
      MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1) :=
    MooreFreeLoopSpace.mem_arcsWithin.2 (MoorePath.mem_arcsWithin.1
      (hN₁ (n + 1) (by omega) ⟨_, ⟨γ, γ.property, rfl⟩, rfl⟩))
  have hmaps := hN₂ n (le_of_max_le_right hn) δ hεδ
  let ι : C(K, MooreFreeLoopSpace.arcsWithin {p : M × M | dist p.1 p.2 < r} (n + 1)) :=
    ⟨fun γ ↦ ⟨(γ : MooreLoopSpace M x).toFreeLoop, hKA γ⟩,
      (MooreLoopSpace.continuous_toFreeLoop.comp continuous_subtypeVal).subtype_mk _⟩
  let e : C(K, basedCyclicDistanceCut (X := M) δ x) :=
    ⟨fun γ ↦ ⟨(γ : MooreLoopSpace M x).toMoorePath.sample (n + 1),
        mem_basedCyclicDistanceCut.2
          ⟨by simpa only [MooreLoopSpace.toMoorePath_toFreeLoop] using hmaps ⟨γ, γ.property, rfl⟩,
            by rw [MoorePath.sample_zero, MooreLoopSpace.source_eq]⟩⟩,
      ((MoorePath.continuous_sample _).comp
        (MooreLoopSpace.continuous_toMoorePath.comp continuous_subtypeVal)).subtype_mk _⟩
  refine ⟨e, fun γ ↦ rfl, ?_⟩
  -- On `K`, the inclusion is the family `ι` of free loops and `geoⁿ ∘ evₙ` is the family of broken
  -- geodesics through their sampled vertices, both read as based loops.
  have h₀ : MooreLoopSpace.codRestrictFreeLoop ((ContinuousMap.subtypeVal _).comp ι)
      (fun γ ↦ by simp [ι]) = ContinuousMap.subtypeVal K :=
    ContinuousMap.ext fun γ ↦ MooreLoopSpace.toFreeLoop_injective <| by
      rw [MooreLoopSpace.toFreeLoop_codRestrictFreeLoop_apply]
      -- `ι γ` is `γ` read as a free loop, by its definition above
      rfl
  have h₁ : MooreLoopSpace.codRestrictFreeLoop ((sampleBrokenGeodesicLoop hr n).comp ι)
      (fun γ ↦ by simp [ι]) = (basedCyclicDistanceCutBrokenGeodesic hr hδ x).comp e :=
    ContinuousMap.ext fun γ ↦ MooreLoopSpace.toFreeLoop_injective <| by
      rw [MooreLoopSpace.toFreeLoop_codRestrictFreeLoop_apply, ContinuousMap.comp_apply,
        sampleBrokenGeodesicLoop_apply hr n (ι γ)
          (MooreFreeLoopSpace.dist_sample_sub_one_lt_of_mem_arcsWithin (hKA γ))]
      simp [ι, e]
  rw [← h₀, ← h₁]
  exact (homotopic_codRestrictFreeLoop_sampleBrokenGeodesicLoop hr ι).symm

/-! ### Sliding the samples inside a based distance cut -/

/-- **Sampling based broken geodesics, `evₘ₊₁ ∘ geoⁿ : 𝓛ⁿ_x M → 𝓛ᵐ_x M`.** For cut-offs `δ i < r`,
the `m + 1` equally spaced samples of the closed broken geodesic through each tuple of the based
distance cut at `x` with cut-offs `δ`, as a continuous map to the based distance cut at `x` with
cut-offs `δ'`, when `∑ i, δ i ≤ (m + 1) * δ' j` for every `j`. It is the restriction of
`TauCeti.Manifold.cyclicDistanceCutSampleBrokenGeodesic`. -/
def basedCyclicDistanceCutSampleBrokenGeodesic {n : ℕ} {δ : Fin (n + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (m : ℕ) {δ' : Fin (m + 1) → ℝ} (hm : ∀ j, ∑ i, δ i ≤ ((m + 1 : ℕ) : ℝ) * δ' j) (x : M) :
    C(basedCyclicDistanceCut (X := M) δ x, basedCyclicDistanceCut (X := M) δ' x) where
  toFun q := ⟨cyclicDistanceCutSampleBrokenGeodesic hr hδ m hm
    ⟨q.val, (mem_basedCyclicDistanceCut.1 q.property).1⟩, mem_basedCyclicDistanceCut.2
    ⟨(cyclicDistanceCutSampleBrokenGeodesic hr hδ m hm
      ⟨q.val, (mem_basedCyclicDistanceCut.1 q.property).1⟩).property, by
      rw [coe_cyclicDistanceCutSampleBrokenGeodesic_apply_zero]
      exact (mem_basedCyclicDistanceCut.1 q.property).2⟩⟩
  continuous_toFun := (continuous_subtypeVal.comp ((map_continuous _).comp
    ((continuous_subtypeVal).subtype_mk _))).subtype_mk _

@[simp]
theorem coe_basedCyclicDistanceCutSampleBrokenGeodesic_apply {n : ℕ} {δ : Fin (n + 1) → ℝ}
    (hδ : ∀ i, δ i < r) (m : ℕ) {δ' : Fin (m + 1) → ℝ}
    (hm : ∀ j, ∑ i, δ i ≤ ((m + 1 : ℕ) : ℝ) * δ' j) (x : M)
    (q : basedCyclicDistanceCut (X := M) δ x) :
    (basedCyclicDistanceCutSampleBrokenGeodesic hr hδ m hm x q : Fin (m + 1) → M) =
      (cyclicDistanceCutBrokenGeodesic hr hδ
        ⟨q.val, (mem_basedCyclicDistanceCut.1 q.property).1⟩).toMoorePath.sample (m + 1) :=
  coe_cyclicDistanceCutSampleBrokenGeodesic_apply hr hδ m hm _

/-- **`ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₙ₊ₖ₊₁ ∘ geoⁿ` on based distance cuts.** For cut-offs `δ i < r` with
`δ (j - k) ≤ δ' j` and `∑ i, δ i ≤ (n + k + 1) * δ' j` for every `j`, repeating the first vertex `k`
more times and sampling the broken geodesics at `n + k + 1` equally spaced times are homotopic
maps from the based distance cut at `x` with cut-offs `δ` to the one with cut-offs `δ'`. -/
theorem homotopic_basedCyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic {n k : ℕ}
    {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ} (hδ : ∀ i, δ i < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) (x : M) :
    (basedCyclicDistanceCutRepeatFirstIterate (X := M) k hδδ' x).Homotopic
      (basedCyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm x) := by
  -- The slide of the vertices along the broken geodesics keeps the first vertex, so it restricts
  -- to the based distance cuts.
  let F := cyclicDistanceCutSampleBrokenGeodesicHomotopy hr hδ hδδ' hm
  let j : C(basedCyclicDistanceCut (X := M) δ x, cyclicDistanceCut (X := M) δ) :=
    ContinuousMap.inclusion (basedCyclicDistanceCut_subset δ x)
  exact ⟨{ toFun := fun p ↦ ⟨F (p.1, j p.2), mem_basedCyclicDistanceCut.2
              ⟨(F (p.1, j p.2)).property, by
                rw [coe_cyclicDistanceCutSampleBrokenGeodesicHomotopy_apply_zero]
                exact (mem_basedCyclicDistanceCut.1 p.2.property).2⟩⟩
           continuous_toFun := (continuous_subtypeVal.comp ((map_continuous F).comp
              (continuous_fst.prodMk ((map_continuous j).comp continuous_snd)))).subtype_mk _
           map_zero_left := fun q ↦ Subtype.ext <| funext fun i ↦ by simp [j]
           map_one_left := fun q ↦ Subtype.ext <| funext fun i ↦ by simp [j] }⟩

end TauCeti.Manifold
