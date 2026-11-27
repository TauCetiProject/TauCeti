/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.BasedLoop.Homology
public import TauCeti.Topology.Homotopy.CompactApproximation

/-!
# Homotopy classes of maps into the based loop space from broken geodesics

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `r` be a
radius such that the tangent ball of radius `r` at every point is a normal domain. For cut-offs
`δ n i < r` which grow from each stage to the next and start positive, the based distance cuts
`𝓛ⁿ_x M = {q ∈ Mⁿ⁺¹ | q₀ = x, d(qᵢ, qᵢ₋₁) ≤ δ n i}` at a point `x` form a sequence
`𝓛⁰_x M → 𝓛¹_x M → ⋯` (`TauCeti.basedCyclicDistanceCutFunctor`), and the closed broken geodesics
through the tuples, `geoⁿ : 𝓛ⁿ_x M → Ω_x M`, form a cocone over it with apex the Moore loops based
at `x` (`TauCeti.Manifold.basedCyclicDistanceCutCocone`). This file is the based form of
`TauCeti.Geometry.Manifold.Riemannian.Geodesic.FreeLoop.HomotopyClass`: for every compact space
`T`, the free homotopy classes `[T, Ω_x M]` are the colimit of the classes `[T, 𝓛ⁿ_x M]`.

* Every map `T → Ω_x M` is homotopic to `geoⁿ ∘ ψ` for some `n` and some `ψ : T → 𝓛ⁿ_x M`
  (`TauCeti.Manifold.exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace`).
* If `geoⁿ ∘ ψ₀` and `geoⁿ ∘ ψ₁` are homotopic, then `ψ₀` and `ψ₁` become homotopic in some later
  based distance cut `𝓛ᵏ_x M`, after repeating their first vertices
  (`TauCeti.Manifold.exists_basedCyclicDistanceCutFunctor_map_comp_homotopic`).

The homotopies are free homotopies of maps into `Ω_x M`, in which every loop is based at `x`; the
loop space itself carries no chosen loop as basepoint, and no topology is put on a colimit of the
spaces `𝓛ⁿ_x M`.

## Main results

* `TauCeti.Manifold.exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace`:
  maps of a compact space into the based loop space are broken geodesics up to homotopy.
* `TauCeti.Manifold.exists_basedCyclicDistanceCutFunctor_map_comp_homotopic`: maps into a based
  distance cut whose broken geodesics are homotopic are homotopic in a later based distance cut.

## References

* J. Milnor, *Morse theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §16 (the approximation of the based path space by broken geodesics).
* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry and
  topology*, IRMA Lect. Math. Theor. Phys. 24, Eur. Math. Soc., 2015, §11.2, Proposition 11.2.4.
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

/-- **Maps of a compact space into the based loop space are broken geodesics up to homotopy.**
Let the cut-offs `δ n i < r` grow from each stage to the next and start positive. Every map `φ` of
a compact space into the Moore loops based at `x` is homotopic to `geoⁿ ∘ ψ` for some `n` and some
map `ψ` into the based distance cut `𝓛ⁿ_x M`. -/
theorem exists_basedCyclicDistanceCutBrokenGeodesic_comp_homotopic_of_compactSpace
    (hpos : 0 < δ 0 0) (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {x : M}
    (φ : C(T, MooreLoopSpace M x)) :
    ∃ (n : ℕ) (ψ : C(T, basedCyclicDistanceCut (X := M) (δ n) x)),
      ((basedCyclicDistanceCutBrokenGeodesic hr (hlt n) x).comp ψ).Homotopic φ := by
  obtain ⟨n, ψ, h⟩ :=
    exists_ι_app_comp_homotopic (c := basedCyclicDistanceCutCocone hr hlt hpos.le hδ x)
      (fun _ hK ↦ exists_basedCyclicDistanceCutCocone_ι_app_comp_homotopic hr hpos hlt hδ hK) φ
  rw [basedCyclicDistanceCutCocone_ι_app_hom] at h
  exact ⟨n, ψ, h⟩

/-- **Maps into a based distance cut whose broken geodesics are homotopic are homotopic in a later
based distance cut.** Let the cut-offs `δ n i < r` grow from each stage to the next and start
positive. If two maps `ψ₀` and `ψ₁` of a compact space into the based distance cut `𝓛ⁿ_x M` have
homotopic broken geodesics `geoⁿ ∘ ψ₀` and `geoⁿ ∘ ψ₁`, then for some `k ≥ n` their composites with
the map `𝓛ⁿ_x M → 𝓛ᵏ_x M` of the sequence of based distance cuts are homotopic. -/
theorem exists_basedCyclicDistanceCutFunctor_map_comp_homotopic (hpos : 0 < δ 0 0)
    (hlt : ∀ n i, δ n i < r) (hδ : ∀ n i j, δ n i ≤ δ (n + 1) j) {x : M} {n : ℕ}
    {ψ₀ ψ₁ : C(T, basedCyclicDistanceCut (X := M) (δ n) x)}
    (h : ((basedCyclicDistanceCutBrokenGeodesic hr (hlt n) x).comp ψ₀).Homotopic
      ((basedCyclicDistanceCutBrokenGeodesic hr (hlt n) x).comp ψ₁)) :
    ∃ (k : ℕ) (hnk : n ≤ k),
      (((basedCyclicDistanceCutFunctor M hpos.le hδ x).map (homOfLE hnk)).hom.comp ψ₀).Homotopic
        (((basedCyclicDistanceCutFunctor M hpos.le hδ x).map (homOfLE hnk)).hom.comp ψ₁) := by
  rw [← basedCyclicDistanceCutCocone_ι_app_hom hr hlt hpos.le hδ x n] at h
  exact exists_map_homOfLE_comp_homotopic_map_homOfLE_comp (fun _ _ _ _ hL hKL ↦
    exists_comp_basedCyclicDistanceCutCocone_ι_app_homotopic_map hr hpos hlt hδ hL hKL) h

end TauCeti.Manifold
