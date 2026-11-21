/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ZeroChart

/-!
# Charts on regular zero sets of sections over Banach manifolds

A source chart and the complemented-kernel implicit function theorem give coordinates on
regular zeros of a bundle section. The charts are on the actual zero set. Their sources are
restricted to the bundle trivialization's base set and the neighbourhood where the implicit
coordinate map has invertible derivative. The derivatives at the zeros are surjective with
complemented kernels, and the charts read each kernel through a chosen identification with a
common model space `Y`. The kernels may be infinite-dimensional, as for the universal sections of
parametric transversality. For a surjective Fredholm derivative of constant index `n`, the model
is `Fin n → 𝕜`, through `ContinuousLinearMap.kerModelEquiv`.

`sectionZeroChartedSpace` assembles this atlas. Smoothness of transitions and the inclusion are
proved in `Section.Manifold`. The source is modelled on a Banach space without boundary.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.3.

The construction uses Mathlib's complemented-kernel implicit function theorem and
`OpenPartialHomeomorph.subtypeCoord`.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {𝕜 X M B F Y : Type*} {E : B → Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [TopologicalSpace M] [ChartedSpace X M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [TopologicalSpace B] [∀ a, TopologicalSpace (E a)]
  [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {b : M → B} {s : ∀ y, E (b y)}
  {e : ↥{y | s y = 0} → Trivialization F (π F E)}
  [∀ z, MemTrivializationAtlas (e z)]
  {D : ↥{y | s y = 0} → X →L[𝕜] F}

variable
  (hf : ∀ z, HasStrictFDerivAt
    (fun y ↦ (e z ⟨b ((chartAt X z.val).symm y), s ((chartAt X z.val).symm y)⟩).2)
    (D z) (chartAt X z.val z.val))
  (hsurj : ∀ z, Function.Surjective (D z))
  (hker : ∀ z, (D z).ker.ClosedComplemented)
  (K : ∀ z, (D z).ker ≃L[𝕜] Y)

private noncomputable def sectionZeroAmbientChart (z : ↥{y | s y = 0}) :
    OpenPartialHomeomorph M (F × (D z).ker) :=
  ((chartAt X z.val).restrOpen (interior (b ⁻¹' (e z).baseSet)) isOpen_interior).trans
    (((hf z).implicitToOpenPartialHomeomorphOfComplemented _ _
      (LinearMap.range_eq_top.2 (hsurj z)) (hker z)).restrOpen
      ((hf z).implicitCoordSource (LinearMap.range_eq_top.2 (hsurj z)) (hker z))
      ((hf z).isOpen_implicitCoordSource _ _))

omit [∀ a, Module 𝕜 (E a)] [VectorBundle 𝕜 F E]
  [∀ z, MemTrivializationAtlas (e z)] [∀ a, TopologicalSpace (E a)] [FiberBundle F E] in
private theorem sectionZeroAmbientChart_fst (z : ↥{y | s y = 0}) {y : M}
    (hy : y ∈ (sectionZeroAmbientChart hf hsurj hker z).source) :
    (sectionZeroAmbientChart hf hsurj hker z y).1 = (e z ⟨b y, s y⟩).2 := by
  rw [sectionZeroAmbientChart, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.coe_restrOpen,
    (hf z).implicitToOpenPartialHomeomorphOfComplemented_fst]
  rw [OpenPartialHomeomorph.coe_restrOpen, (chartAt X z.val).left_inv hy.1.1]

private theorem sectionZeroAmbientChart_slice_mem (z : ↥{y | s y = 0})
    {k : (D z).ker} (hk : (0, k) ∈ (sectionZeroAmbientChart hf hsurj hker z).target) :
    (sectionZeroAmbientChart hf hsurj hker z).symm (0, k) ∈ {y | s y = 0} := by
  let Ψ := sectionZeroAmbientChart hf hsurj hker z
  have hy := Ψ.map_target hk
  have hbase : b (Ψ.symm (0, k)) ∈ (e z).baseSet :=
    interior_subset (s := b ⁻¹' (e z).baseSet) hy.1.2
  have hzero : (e z ⟨b (Ψ.symm (0, k)), s (Ψ.symm (0, k))⟩).2 = 0 := by
    rw [← sectionZeroAmbientChart_fst hf hsurj hker z hy]
    exact congrArg Prod.fst (Ψ.right_inv hk)
  exact ((e z).continuousLinearEquivAt 𝕜 _ hbase).map_eq_zero_iff.1 hzero

private theorem sectionZeroAmbientChart_mk_snd (z : ↥{y | s y = 0}) {y : M}
    (hy : y ∈ (sectionZeroAmbientChart hf hsurj hker z).source) (hz : s y = 0) :
    (0, (sectionZeroAmbientChart hf hsurj hker z y).2) =
      sectionZeroAmbientChart hf hsurj hker z y := by
  apply Prod.ext
  · rw [sectionZeroAmbientChart_fst hf hsurj hker z hy, hz]
    exact (congrArg Prod.snd ((e z).zeroSection 𝕜
      (interior_subset (s := b ⁻¹' (e z).baseSet) hy.1.2))).symm
  · rfl

/-- The preferred chart at a regular zero, in source-manifold coordinates. Its source is
restricted to the bundle trivialization and the regular implicit-coordinate neighbourhood, and
its kernel coordinates are read in the model `Y` through `K z`. -/
noncomputable def sectionZeroChartAt (z : ↥{y | s y = 0}) :
    OpenPartialHomeomorph ↥{y | s y = 0} Y :=
  let Ψ := sectionZeroAmbientChart hf hsurj hker z
  (Ψ.subtypeCoord {y | s y = 0} ⟨z⟩ (fun k ↦ (0, k)) Prod.snd
    (sectionZeroAmbientChart_slice_mem hf hsurj hker z)
    (fun hy hz ↦ sectionZeroAmbientChart_mk_snd hf hsurj hker z hy hz)
    -- Preserve the retraction type when elaborating the subtype-coordinate construction.
    (show Set.LeftInvOn Prod.snd (fun k : (D z).ker ↦ ((0 : F), k))
      ((fun k ↦ (0, k)) ⁻¹' Ψ.target) from fun _ _ ↦ rfl)
    (continuous_const.prodMk continuous_id) continuous_snd.continuousOn).transHomeomorph
      (K z).toHomeomorph

/-- A preferred chart's source consists of zeros in the source-chart and bundle
trivialization domains, whose coordinates belong to the regular implicit-function source. -/
@[simp]
theorem sectionZeroChartAt_source (z : ↥{y | s y = 0}) :
    (sectionZeroChartAt hf hsurj hker K z).source =
      Subtype.val ⁻¹' (((chartAt X z.val).source ∩ interior (b ⁻¹' (e z).baseSet)) ∩
        (chartAt X z.val) ⁻¹'
          (((hf z).implicitToOpenPartialHomeomorphOfComplemented _ _
            (LinearMap.range_eq_top.2 (hsurj z)) (hker z)).source ∩
            (hf z).implicitCoordSource (LinearMap.range_eq_top.2 (hsurj z)) (hker z))) := by
  rw [sectionZeroChartAt, OpenPartialHomeomorph.transHomeomorph_source,
    OpenPartialHomeomorph.subtypeCoord_source]
  rfl

/-- The preferred chart reads source-chart displacement through the kernel projection. -/
theorem sectionZeroChartAt_apply (z w : ↥{y | s y = 0}) :
    sectionZeroChartAt hf hsurj hker K z w =
      K z (Classical.choose (hker z) (chartAt X z.val w.val - chartAt X z.val z.val)) := by
  rw [sectionZeroChartAt, OpenPartialHomeomorph.transHomeomorph_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_toHomeomorph,
    OpenPartialHomeomorph.subtypeCoord_apply, sectionZeroAmbientChart,
    OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.coe_restrOpen,
    (hf z).implicitToOpenPartialHomeomorphOfComplemented_apply]
  rw [OpenPartialHomeomorph.coe_restrOpen]

/-- The target is the implicit zero slice whose inverse stays in the regular neighbourhood,
the source-chart target, and the bundle-trivialization domain. -/
@[simp]
theorem mem_sectionZeroChartAt_target_iff (z : ↥{y | s y = 0}) (k : Y) :
    k ∈ (sectionZeroChartAt hf hsurj hker K z).target ↔
      let Φ := (hf z).implicitToOpenPartialHomeomorphOfComplemented _ _
        (LinearMap.range_eq_top.2 (hsurj z)) (hker z)
      (0, (K z).symm k) ∈ Φ.target ∧
        Φ.symm (0, (K z).symm k) ∈ (hf z).implicitCoordSource
          (LinearMap.range_eq_top.2 (hsurj z)) (hker z) ∧
        Φ.symm (0, (K z).symm k) ∈ (chartAt X z.val).target ∧
        (chartAt X z.val).symm (Φ.symm (0, (K z).symm k)) ∈ interior (b ⁻¹' (e z).baseSet) := by
  rw [sectionZeroChartAt, OpenPartialHomeomorph.transHomeomorph_target,
    OpenPartialHomeomorph.subtypeCoord_target]
  simp only [sectionZeroAmbientChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target,
    OpenPartialHomeomorph.coe_restrOpen_symm,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, Set.mem_preimage,
    Set.mem_inter_iff, and_assoc]
  rfl

/-- On the target, the inverse preferred chart is the inverse ambient source chart applied
to the inverse implicit coordinates on the zero slice. -/
theorem coe_sectionZeroChartAt_symm_apply (z : ↥{y | s y = 0}) {k : Y}
    (hk : k ∈ (sectionZeroChartAt hf hsurj hker K z).target) :
    ((sectionZeroChartAt hf hsurj hker K z).symm k : M) =
      (chartAt X z.val).symm
        (((hf z).implicitToOpenPartialHomeomorphOfComplemented _ _
          (LinearMap.range_eq_top.2 (hsurj z)) (hker z)).symm
        (0, (K z).symm k)) := by
  rw [sectionZeroChartAt, OpenPartialHomeomorph.transHomeomorph_target,
    Set.mem_preimage, ContinuousLinearEquiv.coe_symm_toHomeomorph,
    OpenPartialHomeomorph.subtypeCoord_target, Set.mem_preimage] at hk
  rw [sectionZeroChartAt, OpenPartialHomeomorph.transHomeomorph_symm_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_symm_toHomeomorph,
    OpenPartialHomeomorph.coe_subtypeCoord_symm_apply _ _ _ _ _ _ _ _ _ _ hk,
    sectionZeroAmbientChart, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
    OpenPartialHomeomorph.coe_restrOpen_symm]
  rw [OpenPartialHomeomorph.coe_restrOpen_symm]

/-- The inverse chart remains in the ambient source-chart source, the bundle-trivialization
base set, and the regular implicit-function neighbourhood. -/
theorem sectionZeroChartAt_symm_mem_source_and_baseSet_and_implicitCoordSource
    (z : ↥{y | s y = 0}) {k : Y}
    (hk : k ∈ (sectionZeroChartAt hf hsurj hker K z).target) :
    let y := ((sectionZeroChartAt hf hsurj hker K z).symm k : M)
    y ∈ (chartAt X z.val).source ∧ b y ∈ (e z).baseSet ∧
      chartAt X z.val y ∈ (hf z).implicitCoordSource
        (LinearMap.range_eq_top.2 (hsurj z)) (hker z) := by
  have h := (sectionZeroChartAt hf hsurj hker K z).map_target hk
  rw [sectionZeroChartAt_source] at h
  exact ⟨h.1.1, interior_subset (s := b ⁻¹' (e z).baseSet) h.1.2, h.2.2⟩

/-- A preferred chart is centred at its zero. -/
@[simp]
theorem sectionZeroChartAt_apply_self (z : ↥{y | s y = 0}) :
    sectionZeroChartAt hf hsurj hker K z z = 0 := by
  rw [sectionZeroChartAt_apply]
  simp

variable (hb : ∀ z : ↥{y | s y = 0}, ContinuousAt b z.val)
  (he : ∀ z, b z.val ∈ (e z).baseSet)

include hb he in
/-- Every zero lies in the source of its preferred chart. -/
theorem mem_sectionZeroChartAt_source (z : ↥{y | s y = 0}) :
    z ∈ (sectionZeroChartAt hf hsurj hker K z).source := by
  rw [sectionZeroChartAt_source]
  exact ⟨⟨mem_chart_source X z.val,
    mem_interior_iff_mem_nhds.2 ((hb z).preimage_mem_nhds
      ((e z).open_baseSet.mem_nhds (he z)))⟩,
    (hf z).mem_implicitToOpenPartialHomeomorphOfComplemented_source _ _,
    (hf z).mem_implicitCoordSource _ _⟩

include hb he in
/-- The origin belongs to the preferred chart target. -/
theorem mem_sectionZeroChartAt_target (z : ↥{y | s y = 0}) :
    (0 : Y) ∈ (sectionZeroChartAt hf hsurj hker K z).target :=
  sectionZeroChartAt_apply_self hf hsurj hker K z ▸
    (sectionZeroChartAt hf hsurj hker K z).map_source
      (mem_sectionZeroChartAt_source hf hsurj hker K hb he z)

include hb he in
/-- The inverse chart sends the origin to its zero. -/
@[simp]
theorem sectionZeroChartAt_symm_zero (z : ↥{y | s y = 0}) :
    (sectionZeroChartAt hf hsurj hker K z).symm 0 = z := by
  rw [← sectionZeroChartAt_apply_self hf hsurj hker K z]
  exact (sectionZeroChartAt hf hsurj hker K z).left_inv
    (mem_sectionZeroChartAt_source hf hsurj hker K hb he z)

/-- The atlas of preferred implicit-function charts on the actual section zero set. -/
@[irreducible]
noncomputable def sectionZeroChartedSpace : ChartedSpace Y ↥{y | s y = 0} where
  atlas := Set.range (sectionZeroChartAt hf hsurj hker K)
  chartAt := sectionZeroChartAt hf hsurj hker K
  mem_chart_source z := mem_sectionZeroChartAt_source hf hsurj hker K hb he z
  chart_mem_atlas z := Set.mem_range_self z

/-- The installed preferred charts are `sectionZeroChartAt`. -/
@[simp]
theorem sectionZeroChartedSpace_chartAt (z : ↥{y | s y = 0}) :
    @chartAt Y _ ↥{y | s y = 0} _
      (sectionZeroChartedSpace hf hsurj hker K hb he) z =
      sectionZeroChartAt hf hsurj hker K z := by
  unfold sectionZeroChartedSpace
  rfl

/-- The installed atlas consists exactly of the preferred charts. -/
@[simp]
theorem sectionZeroChartedSpace_atlas :
    @atlas Y _ ↥{y | s y = 0} _
      (sectionZeroChartedSpace hf hsurj hker K hb he) =
      Set.range (sectionZeroChartAt hf hsurj hker K) := by
  unfold atlas sectionZeroChartedSpace
  rfl

end TauCeti
