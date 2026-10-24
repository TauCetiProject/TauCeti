/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.NormalizedChart

/-!
# Disjoint Morse charts at a critical level

Passing a critical value `c` of a Morse function `f` attaches one handle at each critical point
on the level `f⁻¹(c)`. Milnor's construction (*Morse Theory*, Theorem 3.2) works in normalized
Morse charts around these points, in which

`f = c - Σ_{i < λ} yᵢ² + Σ_{i ≥ λ} yᵢ²`,

modifies `f` inside the ellipsoid `‖u‖² + 2‖v‖² ≤ 2ε` of each chart, and attaches the cell
`{‖u‖² ≤ ε, v = 0}`; here `u` collects the `λ` negative coordinates and `v` the others. Before any
of this can be done, the charts and the width `ε` have to be chosen compatibly:

* the band `f⁻¹[c - ε, c + ε]` contains no critical points except those on the level `f⁻¹(c)`;
* the charts at the distinct critical points on that level have pairwise disjoint sources;
* the image of every chart contains the closed ball of radius `√(2ε)` about its centre, and hence
  both the ellipsoid and the closed negative-coordinate disc of radius `√ε`.

This file proves that such choices exist when the band `f⁻¹[c - δ, c + δ]` is compact, for every
`0 < δ`. Each condition persists when `ε` decreases. The charts can moreover be placed inside
prescribed neighbourhoods of their centres.

## Main results

* `TauCeti.IsManifoldNondegenerateCriticalPoint.exists_normalized_morseChart_subset`: a
  normalized Morse chart with source inside a prescribed neighbourhood of the critical point.
* `TauCeti.exists_pairwise_disjoint_normalized_morseCharts`: normalized Morse charts with pairwise
  disjoint sources at finitely many nondegenerate critical points of a Hausdorff manifold.
* `TauCeti.IsMorse.exists_admissible_morseCharts`: the compatible choice of the width `ε` and of
  disjoint normalized Morse charts at all critical points on the level `f⁻¹(c)`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, proof of Theorem 3.2 and Remark 3.3.
-/

public section

open Function Set Filter Topology Metric
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {f : M → ℝ} {x : M}

/-- **The normalized Morse lemma in a prescribed neighbourhood.** At a nondegenerate critical
point `x` of a function `f` which is smooth near `x`, every neighbourhood `U` of `x` contains the
source of a normalized Morse chart: a partial diffeomorphism `ψ` onto an open subset of
`EuclideanSpace ℝ (Fin m)`, `m = dim M`, with `ψ x = 0` and

`f y = f x - Σ_{i < λ} (ψ y)ᵢ² + Σ_{i ≥ λ} (ψ y)ᵢ²`

on its whole source, where `λ` is the manifold Morse index of `f` at `x`. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_normalized_morseChart_subset
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : IsManifoldNondegenerateCriticalPoint I f x) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
      x ∈ ψ.source ∧ ψ.source ⊆ U ∧ ψ x = 0 ∧ ∀ y ∈ ψ.source,
        f y = f x + ∑ i, (if i.val < manifoldMorseIndex I f x then -1 else 1) * ψ y i ^ 2 := by
  obtain ⟨ψ, hxψ, hψx, hψ⟩ := h.exists_normalized_morseChart hf
  refine ⟨ψ.restrOpen (interior U) isOpen_interior, ?_, ?_, ?_, fun y hy ↦ ?_⟩
  · simpa using ⟨hxψ, mem_interior_iff_mem_nhds.2 hU⟩
  · simpa using inter_subset_right.trans interior_subset
  · simpa using hψx
  · simp only [PartialDiffeomorph.restrOpen_source] at hy
    simpa using hψ y hy.1

/-- **Disjoint normalized Morse charts.** At finitely many nondegenerate critical points of a
function on a Hausdorff manifold, smooth near each of them, there are normalized Morse charts with
pairwise disjoint sources, each inside a prescribed neighbourhood of its centre. The charts are
indexed by the points of the finite set `S`. -/
theorem exists_pairwise_disjoint_normalized_morseCharts [T2Space M] {S : Set M} (hS : S.Finite)
    (hf : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℝ) ∞ f y)
    (h : ∀ x ∈ S, IsManifoldNondegenerateCriticalPoint I f x) {U : M → Set M}
    (hU : ∀ x ∈ S, U x ∈ 𝓝 x) :
    ∃ ψ : S → PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
      Pairwise (Disjoint on fun p ↦ (ψ p).source) ∧ ∀ p : S,
        ↑p ∈ (ψ p).source ∧ (ψ p).source ⊆ U p ∧ ψ p p = 0 ∧ ∀ y ∈ (ψ p).source,
          f y = f p + ∑ i, (if i.val < manifoldMorseIndex I f p then -1 else 1) * ψ p y i ^ 2 := by
  -- Separate the points of `S` by open sets and choose each chart inside its separating set.
  obtain ⟨V, hV, hdisj⟩ := hS.t2_separation
  choose ψ hψ using fun p : S ↦ (h p p.2).exists_normalized_morseChart_subset (hf p p.2)
    (inter_mem (hU p p.2) ((hV p).2.mem_nhds (hV p).1))
  refine ⟨ψ, fun p q hpq ↦ ?_, fun p ↦ ⟨(hψ p).1, (hψ p).2.1.trans inter_subset_left,
    (hψ p).2.2⟩⟩
  exact (hdisj p.2 q.2 (Subtype.coe_injective.ne hpq)).mono
    ((hψ p).2.1.trans inter_subset_right) ((hψ q).2.1.trans inter_subset_right)

/-- **Admissible Morse charts at a critical level.** Let `f` be a Morse function on a Hausdorff
manifold whose band `f⁻¹[c - δ, c + δ]` is compact, for some `0 < δ`. Then there are a width
`0 < ε ≤ δ` and normalized Morse charts `ψ p`, indexed by the critical points `p` on the level
`f⁻¹(c)`, such that

* the only critical points in the band `f⁻¹[c - ε, c + ε]` are those on the level `f⁻¹(c)`;
* the chart sources are pairwise disjoint, and each lies in a prescribed neighbourhood `U p`;
* `ψ p p = 0`, and `f = c - Σ_{i < λ} (ψ p)ᵢ² + Σ_{i ≥ λ} (ψ p)ᵢ²` on the source of `ψ p`, where
  `λ` is the Morse index of `f` at `p`;
* the target of each chart contains the closed ball of radius `√(2ε)` about `0`.

The last condition places Milnor's ellipsoid `‖u‖² + 2‖v‖² ≤ 2ε` inside every chart. All of these
conditions persist when `ε` is decreased. -/
theorem IsMorse.exists_admissible_morseCharts [T2Space M] (hf : IsMorse I f) {c δ : ℝ}
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) {U : M → Set M}
    (hU : ∀ x ∈ criticalPoints I f ∩ f ⁻¹' {c}, U x ∈ 𝓝 x) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' {c} ∧
      ∃ ψ : ↥(criticalPoints I f ∩ f ⁻¹' {c}) →
          PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞,
        Pairwise (Disjoint on fun p ↦ (ψ p).source) ∧ ∀ p,
          ↑p ∈ (ψ p).source ∧ (ψ p).source ⊆ U p ∧ ψ p p = 0 ∧
          closedBall 0 √(2 * ε) ⊆ (ψ p).target ∧ ∀ y ∈ (ψ p).source,
            f y = c + ∑ i, (if i.val < manifoldMorseIndex I f p then -1 else 1) * ψ p y i ^ 2 := by
  set S := criticalPoints I f ∩ f ⁻¹' {c}
  have hS : S.Finite := (hf.finite_criticalPoints_inter hcompact).subset
    (inter_subset_inter_right _ (preimage_mono (by simp [hδ.le])))
  have : Finite S := hS.to_subtype
  obtain ⟨ε₁, hε₁, hε₁δ, hband⟩ := hf.exists_criticalPoints_inter_preimage_Icc_subset hδ hcompact
  obtain ⟨ψ, hdisj, hψ⟩ := exists_pairwise_disjoint_normalized_morseCharts hS
    (fun _ _ ↦ Eventually.of_forall fun _ ↦ hf.contMDiff.contMDiffAt)
    (fun x hx ↦ hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx.1) hU
  -- The finitely many chart targets are neighbourhoods of `0`, so they share a closed ball.
  have htarget : ∀ᶠ v in 𝓝 0, ∀ p, v ∈ (ψ p).target := eventually_all.2 fun p ↦
    (ψ p).open_target.mem_nhds ((hψ p).2.2.1 ▸ (ψ p).map_source (hψ p).1)
  obtain ⟨r, hr, hrball⟩ := nhds_basis_closedBall.eventually_iff.1 htarget
  refine ⟨min ε₁ (r ^ 2 / 2), lt_min hε₁ (by positivity), (min_le_left _ _).trans hε₁δ,
    fun y ⟨hy, hyε⟩ ↦ hband ⟨hy, Icc_subset_Icc ?_ ?_ hyε⟩, ψ, hdisj, fun p ↦
      ⟨(hψ p).1, (hψ p).2.1, (hψ p).2.2.1, fun v hv ↦ hrball (closedBall_subset_closedBall ?_ hv) p,
        fun y hy ↦ p.2.2 ▸ (hψ p).2.2.2 y hy⟩⟩
  · linarith [min_le_left ε₁ (r ^ 2 / 2)]
  · linarith [min_le_left ε₁ (r ^ 2 / 2)]
  · rw [Real.sqrt_le_left hr.le]
    linarith [min_le_right ε₁ (r ^ 2 / 2)]

end TauCeti
