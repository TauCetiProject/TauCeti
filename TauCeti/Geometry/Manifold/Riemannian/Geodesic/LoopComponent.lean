/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoopApproximation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.VertexSlide
public import TauCeti.Topology.Homotopy.Homotopic.PathComponent
public import TauCeti.Topology.PathComponent

/-!
# Approximating the components of the free loop space by broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, `r > 0` a radius such
that the tangent ball of radius `r` at every point is a normal domain, and `S` a union of path
components of the free Moore loop space `𝓛M`: for instance the component `𝓛₀M` of the
contractible loops, or the free loops in a given free homotopy class. The free loop space is
approximated by the distance cuts `𝓛ⁿM = {q ∈ Mⁿ⁺¹ | d(qᵢ, qᵢ₋₁) ≤ δᵢ}` through the closed broken
geodesic maps `geoⁿ : 𝓛ⁿM → 𝓛M` (`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic`). The part of
`𝓛ⁿM` approximating `S` is the preimage `(geoⁿ)⁻¹(S)`, mapped to `S` by the restriction of `geoⁿ`
(`ContinuousMap.restrictPreimage`).

The two properties of the approximation of `𝓛M` hold for these restrictions, so that they
approximate `S` in the same way.

* **Compact families.** For a compact family `K ⊆ S`, every sufficiently fine sampling `evₙ` maps
  `K` into `(geoⁿ)⁻¹(S)`, and `geoⁿ ∘ evₙ` is homotopic to the inclusion of `K` as maps `K → S`
  (`TauCeti.Manifold.exists_restrictPreimage_cyclicDistanceCutBrokenGeodesic_comp_homotopic`).
* **The vertex slide.** Repeating the first vertex `k` more times, `ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ`, and the
  composite `evₙ₊ₖ₊₁ ∘ geoⁿ` both map `(geoⁿ)⁻¹(S)` into `(geoⁿ⁺ᵏ)⁻¹(S)`
  (`TauCeti.Manifold.mapsTo_cyclicDistanceCutRepeatFirstIterate_preimage`,
  `TauCeti.Manifold.mapsTo_cyclicDistanceCutSampleBrokenGeodesic_preimage`), and they are homotopic
  as such maps
  (`homotopic_mapsToRestrict_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`).

Both follow from the statements for all free loops
(`TauCeti.Manifold.exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic`,
`TauCeti.Manifold.homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`), because a
homotopy moves each point inside its path component (`ContinuousMap.Homotopic.codRestrict`). For
the vertex slide the relevant union of path components is `(geoⁿ⁺ᵏ)⁻¹(S)`, which is one since
`geoⁿ⁺ᵏ` is continuous, and `geoⁿ⁺ᵏ ∘ (ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ) = geoⁿ`
(`TauCeti.Manifold.cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirstIterate`).

## Main results

* `TauCeti.Manifold.exists_restrictPreimage_cyclicDistanceCutBrokenGeodesic_comp_homotopic`: on a
  compact family of free loops in `S`, every sufficiently fine `geoⁿ ∘ evₙ` is homotopic to the
  inclusion through loops in `S`.
* `homotopic_mapsToRestrict_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`:
  `ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₙ₊ₖ₊₁ ∘ geoⁿ` as maps `(geoⁿ)⁻¹(S) → (geoⁿ⁺ᵏ)⁻¹(S)`.

## References

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
  {S : Set (MooreFreeLoopSpace M)}

include hr

/-! ### Compact families -/

/-- **The compact-family approximation of a union of components of the free loop space.** Let `S`
be a union of path components of the free loop space, `K ⊆ S` a compact family and `ε > 0`. There
is `N` such that for every `n ≥ N` and all cut-offs `ε ≤ δ i < r`, the sampling `evₙ` at `n + 1`
times maps `K` into the part `(geoⁿ)⁻¹(S)` of the distance cut whose broken geodesics lie in `S`,
and `geoⁿ ∘ evₙ` is homotopic to the inclusion of `K` as maps `K → S`. -/
theorem exists_restrictPreimage_cyclicDistanceCutBrokenGeodesic_comp_homotopic
    (hS : ∀ γ ∈ S, pathComponent γ ⊆ S) {K : Set (MooreFreeLoopSpace M)} (hK : IsCompact K)
    (hKS : K ⊆ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ δ : Fin (n + 1) → ℝ, (∀ i, ε ≤ δ i) → ∀ hδ : ∀ i, δ i < r,
      ∃ e : C(K, cyclicDistanceCutBrokenGeodesic hr hδ ⁻¹' S),
        (∀ γ, ((e γ : cyclicDistanceCut (X := M) δ) : Fin (n + 1) → M) =
          (γ : MooreFreeLoopSpace M).toMoorePath.sample (n + 1)) ∧
        (((cyclicDistanceCutBrokenGeodesic hr hδ).restrictPreimage S).comp e).Homotopic
          (ContinuousMap.inclusion hKS) := by
  obtain ⟨N, hN⟩ := exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic hr hK hε
  refine ⟨N, fun n hn δ hεδ hδ ↦ ?_⟩
  obtain ⟨e, he, hhom⟩ := hN n hn δ hεδ hδ
  -- `geoⁿ ∘ evₙ` is homotopic to the inclusion of `K ⊆ S`, so it takes its values in `S`.
  have hmem (γ : K) : cyclicDistanceCutBrokenGeodesic hr hδ (e γ) ∈ S :=
    hhom.symm.apply_mem hS (hKS γ.property)
  refine ⟨⟨fun γ ↦ ⟨e γ, hmem γ⟩, (map_continuous e).subtype_mk _⟩, he, ?_⟩
  -- The free homotopy never leaves `S`. Both sides are the corestrictions to `S` of the maps of
  -- the free homotopy, by definition of `restrictPreimage` and `inclusion`.
  exact hhom.codRestrict hS hmem fun γ ↦ hKS γ.property

/-! ### The vertex slide -/

section Slide

variable {n k : ℕ} {δ : Fin (n + 1) → ℝ} {δ' : Fin (n + k + 1) → ℝ}

/-- Repeating the first vertex `k` more times maps the part of a distance cut whose broken
geodesics lie in a set `S` of free loops into the corresponding part of the larger distance cut,
since it does not change the broken geodesics. -/
theorem mapsTo_cyclicDistanceCutRepeatFirstIterate_preimage (hδ : ∀ i, δ i < r)
    (hδ' : ∀ j, δ' j < r) (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (S : Set (MooreFreeLoopSpace M)) :
    MapsTo (cyclicDistanceCutRepeatFirstIterate (X := M) k hδδ')
      (cyclicDistanceCutBrokenGeodesic hr hδ ⁻¹' S)
      (cyclicDistanceCutBrokenGeodesic hr hδ' ⁻¹' S) := fun _ hq ↦ by
  rwa [mem_preimage, cyclicDistanceCutBrokenGeodesic_cyclicDistanceCutRepeatFirstIterate]

/-- Sampling the broken geodesics at `n + k + 1` equally spaced times maps the part of a distance
cut whose broken geodesics lie in a union `S` of path components of the free loop space into the
corresponding part of the larger distance cut. -/
theorem mapsTo_cyclicDistanceCutSampleBrokenGeodesic_preimage
    (hS : ∀ γ ∈ S, pathComponent γ ⊆ S) (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    MapsTo (cyclicDistanceCutSampleBrokenGeodesic hr hδ (n + k) hm)
      (cyclicDistanceCutBrokenGeodesic hr hδ ⁻¹' S)
      (cyclicDistanceCutBrokenGeodesic hr hδ' ⁻¹' S) := fun _ hq ↦
  -- Composed with `geoⁿ⁺ᵏ`, the vertex slide is a free homotopy starting at `geoⁿ q ∈ S`.
  ((ContinuousMap.Homotopic.refl (cyclicDistanceCutBrokenGeodesic hr hδ')).comp
    (homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic hr hδ hδδ' hm)).apply_mem
      hS (mapsTo_cyclicDistanceCutRepeatFirstIterate_preimage hr hδ hδ' hδδ' S hq)

/-- **`ιⁿ⁺ᵏ⁻¹ ∘ ⋯ ∘ ιⁿ ≃ evₙ₊ₖ₊₁ ∘ geoⁿ` over a union of components of the free loop space.** For
a union `S` of path components of the free loop space and cut-offs as in
`TauCeti.Manifold.homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic`, below `r`,
repeating the first vertex `k` more times and sampling the broken geodesics at `n + k + 1` equally
spaced times are homotopic maps from the part `(geoⁿ)⁻¹(S)` of the distance cut with cut-offs `δ`
to the part `(geoⁿ⁺ᵏ)⁻¹(S)` of the one with cut-offs `δ'`. -/
theorem homotopic_mapsToRestrict_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic
    (hS : ∀ γ ∈ S, pathComponent γ ⊆ S) (hδ : ∀ i, δ i < r) (hδ' : ∀ j, δ' j < r)
    (hδδ' : ∀ j : Fin (n + k + 1), δ ⟨j - k, by omega⟩ ≤ δ' j)
    (hm : ∀ j, ∑ i, δ i ≤ ((n + k + 1 : ℕ) : ℝ) * δ' j) :
    (⟨(mapsTo_cyclicDistanceCutRepeatFirstIterate_preimage hr hδ hδ' hδδ' S).restrict,
        (map_continuous _).restrict _⟩ :
        C(cyclicDistanceCutBrokenGeodesic hr hδ ⁻¹' S,
          cyclicDistanceCutBrokenGeodesic hr hδ' ⁻¹' S)).Homotopic
      ⟨(mapsTo_cyclicDistanceCutSampleBrokenGeodesic_preimage hr hS hδ hδ' hδδ' hm).restrict,
        (map_continuous _).restrict _⟩ :=
  -- The vertex slide on `(geoⁿ)⁻¹(S)` never leaves `(geoⁿ⁺ᵏ)⁻¹(S)`, a union of path components of
  -- the larger cut since `geoⁿ⁺ᵏ` is continuous. Both sides are the corestrictions of the
  -- restrictions to `(geoⁿ)⁻¹(S)` of the two maps, by definition of `MapsTo.restrict`.
  ((homotopic_cyclicDistanceCutRepeatFirstIterate_sampleBrokenGeodesic hr hδ hδδ' hm).comp
    (ContinuousMap.Homotopic.refl (ContinuousMap.subtypeVal _))).codRestrict
      (fun _ hq ↦ (map_continuous _).pathComponent_subset_preimage hS hq)
      (fun q ↦ mapsTo_cyclicDistanceCutRepeatFirstIterate_preimage hr hδ hδ' hδδ' S q.property)
      (fun q ↦
        mapsTo_cyclicDistanceCutSampleBrokenGeodesic_preimage hr hS hδ hδ' hδδ' hm q.property)

end Slide

end TauCeti.Manifold
