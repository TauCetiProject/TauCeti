/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import TauCeti.Topology.VectorBundle.Bilinear

/-!
# Openness of the metric cone on a compact base

The positive-definite smooth sections of the symmetric bilinear bundle form an open cone in
the compact derivative topology whenever the base is compact and the bundle has finite rank.
The topology is the existing `ContMDiffSection.frameTopology`, for any supplied covering system
of smooth frames of the symmetric bundle. No background metric is chosen.

More locally, positivity on any compact subset of the base is an open condition on sections.
This follows from the openness of positive definiteness in the total space and joint continuity
of section evaluation. Compactness is essential for the global statement: on a noncompact base,
compact derivative neighborhoods do not control a section outside a compact set.

All available derivatives are included in the frame topology. The results allow any regularity,
including smooth sections, and allow models with corners. They do not assert a comparison with
finite-atlas C² topologies on metrics.

## References

* R. Hamilton, *The inverse function theorem of Nash and Moser*, Part I, Example 1.1.5,
  for the smooth section space containing the metric cone.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace TauCeti
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [LocallyCompactSpace EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V IB]
  {ι : Type*}
  (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
    (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)

/-- Positive definiteness on a compact subset of the base is an open condition on symmetric
sections in the compact derivative topology of any covering frame system. -/
theorem isOpen_setOf_forall_pos_symmetricSection_frameTopology
    (hcover : ∀ x, ∃ i, x ∈ U i) {K : Set B} (hK : IsCompact K) :
    let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
    IsOpen {σ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ,
        fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯ |
      ∀ x ∈ K, ∀ v : V x, v ≠ 0 → 0 < (σ x : V x →L[ℝ] V x →L[ℝ] ℝ) v v} := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  exact hK.isOpen_setOf_forall_mem_forall_bilinear_apply_self_pos
    (fun (σ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ,
        fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯) x ↦
      (σ x : V x →L[ℝ] V x →L[ℝ] ℝ))
    (TauCeti.continuous_totalSpace_coe_symmetricBilinearMaps.comp
      (ContMDiffSection.continuous_totalSpace_eval e U hU hcover))

/-- On a compact base, the metric cone of positive-definite symmetric sections is open in the
compact derivative topology. In particular this applies to smooth metrics on the tangent bundle. -/
theorem isOpen_positiveDefiniteSymmetricSections_frameTopology [CompactSpace B]
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
    IsOpen (positiveDefiniteSymmetricSections IB n F V) := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := n) e U hU
  have h := isOpen_setOf_forall_pos_symmetricSection_frameTopology (IB := IB) (n := n)
    e U hU hcover
    isCompact_univ
  dsimp only at h ⊢
  convert h using 1
  ext σ
  simp

end TauCeti.Manifold
