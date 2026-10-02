/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ZeroChart
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Smooth atlases on regular zero sets of bundle sections

For a section along a map from a Banach space, continuous at its zeros, regular Fredholm zeros
of constant index `n` form a manifold modelled on `Fin n → 𝕜`. The atlas is on the actual zero
set, not on an extended fiber-coordinate equation, which can have spurious zeros outside a
trivialization.

We choose a bundle trivialization at each zero, use `sectionZeroChart`, and restrict its source
to the neighbourhood where the implicit-function coordinate map has invertible derivative.
The inverse charts are then smooth throughout their targets. Chart transitions are inverse
charts followed by continuous linear projections of ambient displacement, so no global
trivialization is needed. Atlas assembly follows `levelSetChartedSpace` and
`isManifold_levelSet` for ordinary maps.

Smoothness is stated in fiber coordinates at zeros in the chosen trivializations and regular
implicit-coordinate neighbourhoods, and is required only for nonzero differentiability order.
At order zero, chart continuity suffices. Only the base map needs to be continuous at the zeros;
no differentiability of that map or smooth bundle structure is needed once these coordinate
hypotheses are supplied. The parameter space is a Banach space, not an arbitrary manifold. No
second-countability hypothesis is imposed: `IsManifold`
asserts smooth compatibility of the atlas, not second countability.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.3, for the regular-zero theorem for Fredholm sections.
-/

public section

open Bundle Set
open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 X B F : Type*} {E : B → Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace B] [∀ a, TopologicalSpace (E a)]
  [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {b : X → B} {s : ∀ y, E (b y)}
  {e : ↥{y | s y = 0} → Trivialization F (π F E)}
  [∀ z, MemTrivializationAtlas (e z)]
  {D : ↥{y | s y = 0} → X →L[𝕜] F} {n : ℕ}

variable
  (hf : ∀ z, HasStrictFDerivAt (fun y ↦ (e z ⟨b y, s y⟩).2) (D z) z.1)
  (hFred : ∀ z, ContinuousLinearMap.IsFredholm (D z))
  (hsurj : ∀ z, Function.Surjective (D z))
  (hindex : ∀ z, ContinuousLinearMap.index (D z) = n)

variable (hb : ∀ z : ↥{y | s y = 0}, ContinuousAt b z.1)
  (he : ∀ z, b z.1 ∈ (e z).baseSet)

variable {m : ℕ∞ω}
  (hs : m ≠ 0 → ∀ z w : ↥{y | s y = 0}, b w.1 ∈ (e z).baseSet →
    w.1 ∈ (hf z).implicitCoordSource (LinearMap.range_eq_top.2 (hsurj z))
      (hFred z).closedComplemented_ker →
    ContDiffAt 𝕜 m (fun y ↦ (e z ⟨b y, s y⟩).2) w.1)

include hs in
/-- The inverse preferred chart, included into the ambient parameter space, is smooth on its
whole target, not merely at the origin. -/
theorem contDiffOn_coe_sectionZeroChartAt_symm (z : ↥{y | s y = 0}) :
    ContDiffOn 𝕜 m (fun k ↦ ((sectionZeroChartAt hf hFred hsurj hindex z).symm k : X))
      (sectionZeroChartAt hf hFred hsurj hindex z).target := by
  by_cases hm : m = 0
  · subst m
    exact contDiffOn_zero.2 (continuous_subtype_val.comp_continuousOn
      (sectionZeroChartAt hf hFred hsurj hindex z).continuousOn_symm)
  let K := (D z).kerModelEquiv (hFred z).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hsurj z)).2 (hindex z))
  let ψ := sectionZeroChart (hf z) (LinearMap.range_eq_top.2 (hsurj z))
    (hFred z).closedComplemented_ker z.2
  intro k hk
  have hk' := hk
  rw [sectionZeroChartAt_target] at hk'
  let w := ψ.symm (K.symm k)
  have hw : w ∈ ψ.source := ψ.map_target hk'.1
  have hbase : b w.1 ∈ (e z).baseSet := by
    rw [sectionZeroChart_source] at hw
    exact interior_subset (s := b ⁻¹' (e z).baseSet) hw.2
  have hval : ∀ j, ((sectionZeroChartAt hf hFred hsurj hindex z).symm j : X) =
      (ψ.symm (K.symm j) : X) := fun j ↦ congrArg Subtype.val
        (sectionZeroChartAt_symm_apply hf hFred hsurj hindex z j)
  have hmem : w.1 ∈ (hf z).implicitCoordSource (LinearMap.range_eq_top.2 (hsurj z))
      (hFred z).closedComplemented_ker := by
    simpa only [Set.mem_preimage, hval] using hk'.2
  have hcoord : ContDiffAt 𝕜 m (fun y ↦ (e z ⟨b y, s y⟩).2) w.1 := hs hm z w hbase hmem
  have hinner : ContDiffAt 𝕜 m (fun j ↦ (ψ.symm j : X)) (K.symm k) :=
    contDiffAt_coe_sectionZeroChart_symm_of_mem (hf z) _ _ z.2 hk'.1 hmem
      (hcoord.differentiableAt hm).hasFDerivAt hcoord
  have hcomp := hinner.comp k K.symm.contDiff.contDiffAt
  exact hcomp.contDiffWithinAt.congr (fun j _ ↦ hval j) (hval k)

include hs in
/-- Transitions between the preferred charts of the zero set are smooth. -/
theorem contDiffOn_sectionZeroChartAt_trans (z w : ↥{y | s y = 0}) :
    ContDiffOn 𝕜 m
      ((sectionZeroChartAt hf hFred hsurj hindex z).symm.trans
        (sectionZeroChartAt hf hFred hsurj hindex w))
      ((sectionZeroChartAt hf hFred hsurj hindex z).symm.trans
        (sectionZeroChartAt hf hFred hsurj hindex w)).source := by
  let χ := sectionZeroChartAt hf hFred hsurj hindex z
  let χ' := sectionZeroChartAt hf hFred hsurj hindex w
  let Ψ : X →L[𝕜] (Fin n → 𝕜) :=
    ((D w).kerModelEquiv (hFred w).finite_ker
      ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D w) (hsurj w)).2 (hindex w)) :
        (D w).ker →L[𝕜] (Fin n → 𝕜)).comp (Classical.choose (hFred w).closedComplemented_ker)
  have hbase := (contDiffOn_coe_sectionZeroChartAt_symm hf hFred hsurj hindex hs z).mono
    (t := (χ.symm.trans χ').source) (fun _ hk ↦ hk.1)
  have hcomp := Ψ.contDiff.comp_contDiffOn (hbase.sub (contDiffOn_const (c := w.1)))
  refine hcomp.congr fun k _ ↦ ?_
  simp only [Function.comp_def, OpenPartialHomeomorph.coe_trans,
    sectionZeroChartAt_apply, Ψ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

include hs in
/-- The actual zero set of a regular Fredholm section of constant index is a smooth manifold
of dimension that index, with the preferred section-zero atlas. -/
theorem isManifold_sectionZero :
    letI := sectionZeroChartedSpace hf hFred hsurj hindex hb he
    IsManifold (modelWithCornersSelf 𝕜 (Fin n → 𝕜)) m ↥{y | s y = 0} := by
  let _i := sectionZeroChartedSpace hf hFred hsurj hindex hb he
  refine isManifold_of_contDiffOn _ _ _ fun χ χ' hχ hχ' ↦ ?_
  rw [sectionZeroChartedSpace_atlas] at hχ hχ'
  obtain ⟨z, rfl⟩ := hχ
  obtain ⟨w, rfl⟩ := hχ'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id, Function.comp_id, Function.id_comp] using
    contDiffOn_sectionZeroChartAt_trans hf hFred hsurj hindex hs z w

end TauCeti
