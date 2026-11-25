/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.Homology
public import TauCeti.Topology.Homotopy.CompactApproximation

/-!
# Homotopy classes of maps into the free loop space from broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r` be a
radius such that the tangent ball of radius `r` at every point is a normal domain. For cut-offs
`δ n i < r` which grow from each stage to the next and start positive, the distance cuts

`𝓛ⁿM = {q ∈ Mⁿ⁺¹ | d(qᵢ, qᵢ₋₁) ≤ δ n i}`

form a sequence `𝓛⁰M → 𝓛¹M → ⋯` whose maps repeat the first vertex
(`TauCeti.cyclicDistanceCutFunctor`), and the closed broken geodesics through the tuples,
`geoⁿ : 𝓛ⁿM → 𝓛M`, form a cocone over it (`TauCeti.Manifold.cyclicDistanceCutCocone`). This
cocone approximates the free loop space on compact sets up to homotopy, which gives the singular
homology of `𝓛M` as the colimit of that of the `𝓛ⁿM`
(`TauCeti.Manifold.isColimitMapCoconeSingularHomologyCyclicDistanceCutCocone`). This file gives
the corresponding statement for homotopy classes of maps out of a compact space `T`, such as a
sphere or a disc: the free homotopy classes `[T, 𝓛M]` are the colimit of the classes `[T, 𝓛ⁿM]`.

* Every map `T → 𝓛M` is homotopic to `geoⁿ ∘ ψ` for some `n` and some `ψ : T → 𝓛ⁿM`
  (`TauCeti.Manifold.exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace`).
* If `geoⁿ ∘ ψ₀` and `geoⁿ ∘ ψ₁` are homotopic, then `ψ₀` and `ψ₁` become homotopic in some later
  distance cut `𝓛ᵏM`, after repeating their first vertices
  (`TauCeti.Manifold.exists_cyclicDistanceCutFunctor_map_comp_homotopic`).

So the spheres of `𝓛M`, and the homotopies between them, are all seen up to free homotopy by the
finite-dimensional approximations. This is the homotopical half of Abouzaid's comparison of the
broken-geodesic approximation with the free loop space. The homotopies are free, so the
statements concern free homotopy classes rather than homotopy groups at a chosen basepoint, and
no topology is put on a colimit of the spaces `𝓛ⁿM`.

The same holds for a union `S` of path components of the free loop space, such as the contractible
loops `𝓛₀M` or the loops in one free homotopy class, with the parts `(geoⁿ)⁻¹(S)` of the distance
cuts in place of the `𝓛ⁿM`, and homotopies within `S` (in the namespace `TauCeti.Manifold`,
`exists_restrictPreimage_cyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace` and
`exists_preimageFunctor_map_comp_homotopic`).

## Main results

* `TauCeti.Manifold.exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace`: maps
  of a compact space into the free loop space are broken geodesics up to homotopy.
* `TauCeti.Manifold.exists_cyclicDistanceCutFunctor_map_comp_homotopic`: maps into a distance cut
  whose broken geodesics are homotopic are homotopic in a later distance cut.
* `exists_restrictPreimage_cyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace`,
  `TauCeti.Manifold.exists_preimageFunctor_map_comp_homotopic`: the same within a union of path
  components of the free loop space, the first also in the namespace `TauCeti.Manifold`.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public section

open Bundle CategoryTheory Limits Manifold Metric Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {r : ℝ} (hr : ∀ q : M, IsNormalDomain I M q (ball 0 r))
  {δ : (n : ℕ) → Fin (n + 1) → ℝ} {T : Type*} [TopologicalSpace T] [CompactSpace T]

/-- **Maps of a compact space into the free loop space are broken geodesics up to homotopy.**
Let the cut-offs `δ n i < r` grow from each stage to the next and start positive. Every map `φ` of
a compact space into the free loop space is homotopic to `geoⁿ ∘ ψ` for some `n` and some map `ψ`
into the distance cut `𝓛ⁿM`. -/
theorem exists_cyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j)
    (φ : C(T, MooreFreeLoopSpace M)) :
    ∃ (n : ℕ) (ψ : C(T, cyclicDistanceCut (X := M) (δ n))),
      ((cyclicDistanceCutBrokenGeodesic hr (hlt n)).comp ψ).Homotopic φ := by
  obtain ⟨n, ψ, h⟩ := exists_ι_app_comp_homotopic (c := cyclicDistanceCutCocone hr hlt hpos.le hδ)
    (fun _ hK ↦ exists_cyclicDistanceCutCocone_ι_app_comp_homotopic hr hpos hlt hδ hK) φ
  rw [cyclicDistanceCutCocone_ι_app_hom] at h
  exact ⟨n, ψ, h⟩

/-- **Maps into a distance cut whose broken geodesics are homotopic are homotopic in a later
distance cut.** Let the cut-offs `δ n i < r` grow from each stage to the next and start positive.
If two maps `ψ₀` and `ψ₁` of a compact space into the distance cut `𝓛ⁿM` have homotopic broken
geodesics `geoⁿ ∘ ψ₀` and `geoⁿ ∘ ψ₁`, then for some `k ≥ n` their composites with the map
`𝓛ⁿM → 𝓛ᵏM` of the sequence of distance cuts, which repeats the first vertex, are homotopic. -/
theorem exists_cyclicDistanceCutFunctor_map_comp_homotopic (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n : ℕ}
    {ψ₀ ψ₁ : C(T, cyclicDistanceCut (X := M) (δ n))}
    (h : ((cyclicDistanceCutBrokenGeodesic hr (hlt n)).comp ψ₀).Homotopic
      ((cyclicDistanceCutBrokenGeodesic hr (hlt n)).comp ψ₁)) :
    ∃ (k : ℕ) (hnk : n ≤ k),
      (((cyclicDistanceCutFunctor M hpos.le hδ).map (homOfLE hnk)).hom.comp ψ₀).Homotopic
        (((cyclicDistanceCutFunctor M hpos.le hδ).map (homOfLE hnk)).hom.comp ψ₁) := by
  rw [← cyclicDistanceCutCocone_ι_app_hom hr hlt hpos.le hδ n] at h
  exact exists_map_homOfLE_comp_homotopic_map_homOfLE_comp (fun _ _ _ _ hL hKL ↦
    exists_comp_cyclicDistanceCutCocone_ι_app_homotopic_map hr hpos hlt hδ hL hKL) h

section Component

variable {S : Set (MooreFreeLoopSpace M)}

/-- **Maps of a compact space into a union of components of the free loop space are broken
geodesics up to homotopy within it.** Let `S` be a union of path components of the free loop space
and let the cut-offs `δ n i < r` grow from each stage to the next and start positive. Every map `φ`
of a compact space into `S` is homotopic within `S` to `geoⁿ ∘ ψ` for some `n` and some map `ψ`
into the part `(geoⁿ)⁻¹(S)` of the distance cut `𝓛ⁿM`. -/
theorem exists_restrictPreimage_cyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace
    (hS : ∀ γ ∈ S, pathComponent γ ⊆ S) (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r)
    (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) (φ : C(T, S)) :
    ∃ (n : ℕ) (ψ : C(T, cyclicDistanceCutBrokenGeodesic hr (hlt n) ⁻¹' S)),
      (((cyclicDistanceCutBrokenGeodesic hr (hlt n)).restrictPreimage S).comp ψ).Homotopic φ := by
  obtain ⟨n, ψ, h⟩ := exists_ι_app_comp_homotopic
    (c := (cyclicDistanceCutCocone hr hlt hpos.le hδ).restrictPreimage S)
    (fun _ hK ↦
      exists_restrictPreimage_cyclicDistanceCutCocone_ι_app_comp_homotopic hr hS hpos hlt hδ hK) φ
  -- The leg of the cocone at `n` is the restriction of `geoⁿ` to `(geoⁿ)⁻¹(S)`, by definition
  -- (`CategoryTheory.Limits.Cocone.restrictPreimage_ι_app_hom` and
  -- `cyclicDistanceCutCocone_ι_app_hom`).
  exact ⟨n, ψ, h⟩

/-- **Maps into the parts of the distance cuts over a union of components whose broken geodesics
are homotopic within it are homotopic in a later part.** Let `S` be a union of path components of
the free loop space and let the cut-offs `δ n i < r` grow from each stage to the next and start
positive. If two maps `ψ₀` and `ψ₁` of a compact space into the part `(geoⁿ)⁻¹(S)` of the distance
cut `𝓛ⁿM` have broken geodesics homotopic within `S`, then for some `k ≥ n` their composites with
the map `(geoⁿ)⁻¹(S) → (geoᵏ)⁻¹(S)` of the parts over `S` of the sequence of distance cuts are
homotopic. -/
theorem exists_preimageFunctor_map_comp_homotopic (hS : ∀ γ ∈ S, pathComponent γ ⊆ S)
    (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {n : ℕ}
    {ψ₀ ψ₁ : C(T, cyclicDistanceCutBrokenGeodesic hr (hlt n) ⁻¹' S)}
    (h : (((cyclicDistanceCutBrokenGeodesic hr (hlt n)).restrictPreimage S).comp ψ₀).Homotopic
      (((cyclicDistanceCutBrokenGeodesic hr (hlt n)).restrictPreimage S).comp ψ₁)) :
    ∃ (k : ℕ) (hnk : n ≤ k),
      ((((cyclicDistanceCutCocone hr hlt hpos.le hδ).preimageFunctor S).map
          (homOfLE hnk)).hom.comp ψ₀).Homotopic
        ((((cyclicDistanceCutCocone hr hlt hpos.le hδ).preimageFunctor S).map
          (homOfLE hnk)).hom.comp ψ₁) := by
  -- The leg of the cocone at `n` is the restriction of `geoⁿ` to `(geoⁿ)⁻¹(S)`, by definition
  -- (`CategoryTheory.Limits.Cocone.restrictPreimage_ι_app_hom` and
  -- `cyclicDistanceCutCocone_ι_app_hom`).
  exact exists_map_homOfLE_comp_homotopic_map_homOfLE_comp (fun _ _ _ _ hL hKL ↦
    exists_comp_restrictPreimage_cyclicDistanceCutCocone_ι_app_homotopic_map hr hS hpos hlt hδ hL
      hKL) h

end Component

end TauCeti.Manifold
