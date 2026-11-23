/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Chart
public import Mathlib.Geometry.Manifold.Immersion
import TauCeti.Analysis.Calculus.ContDiff.Shear
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Smooth atlases on regular zero sets of bundle sections

For a section along a map from a Banach manifold, continuous at its zeros, the zeros at which the
coordinate derivative is surjective with complemented kernel form a manifold modelled on any
Banach space `Y` with chosen identifications of all these kernels. The kernels may be
infinite-dimensional. For a surjective Fredholm derivative of constant index `n`, the model is
`Fin n → 𝕜` through `ContinuousLinearMap.kerModelEquiv`, so regular zeros of a Fredholm section
form a manifold of dimension the index. The atlas is on the actual zero set, not on an extended
fiber-coordinate equation, which can have spurious zeros outside a trivialization.

We choose a bundle trivialization at each zero, compose a source chart with implicit coordinates,
and restrict the source to the neighbourhood where the implicit-function coordinate map has
invertible derivative.
The inverse charts are then smooth throughout their targets. Chart transitions are inverse
charts followed by ambient source charts and linear projections of coordinate displacement,
so no global trivialization is needed. Atlas assembly follows `levelSetChartedSpace` and
`isManifold_levelSet` for ordinary maps. The inclusion into the parameter space is smooth
for this atlas and is an immersion with complement the fiber model.

Smoothness is stated in fiber coordinates and preferred source charts at zeros in the chosen
trivializations and regular implicit-coordinate neighbourhoods. It is required only for nonzero
differentiability order.
At order zero, chart continuity suffices. Only the base map needs to be continuous at the zeros;
no differentiability of that map or smooth bundle structure is needed once these coordinate
hypotheses are supplied. The source is a manifold modelled on a Banach space without boundary. No
second-countability hypothesis is imposed: `IsManifold`
asserts smooth compatibility of the atlas, not second countability.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.3, for the regular-zero theorem for Fredholm sections.
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191, 1999, Chapter II, §2, for
  submanifolds cut out by maps whose derivatives are surjective with complemented kernels.
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

variable (hb : ∀ z : ↥{y | s y = 0}, ContinuousAt b z.val)
  (he : ∀ z, b z.val ∈ (e z).baseSet)

variable {m : ℕ∞ω} [IsManifold 𝓘(𝕜, X) m M]
  (hs : m ≠ 0 → ∀ z w : ↥{y | s y = 0}, w.val ∈ (chartAt X z.val).source →
    b w.val ∈ (e z).baseSet →
    chartAt X z.val w.val ∈ (hf z).implicitCoordSource
      (LinearMap.range_eq_top.2 (hsurj z)) (hker z) →
    ContDiffAt 𝕜 m
      (fun y ↦ (e z ⟨b ((chartAt X z.val).symm y), s ((chartAt X z.val).symm y)⟩).2)
      (chartAt X z.val w.val))

include hs in
/-- The inverse preferred chart, included into the source manifold, is smooth throughout
its target. -/
theorem contMDiffOn_coe_sectionZeroChartAt_symm (z : ↥{y | s y = 0}) :
    ContMDiffOn 𝓘(𝕜, Y) 𝓘(𝕜, X) m
      (fun k ↦ ((sectionZeroChartAt hf hsurj hker K z).symm k : M))
      (sectionZeroChartAt hf hsurj hker K z).target := by
  by_cases hm : m = 0
  · subst m
    exact contMDiffOn_zero_iff.2 (continuous_subtypeVal.comp_continuousOn
      (sectionZeroChartAt hf hsurj hker K z).continuousOn_symm)
  let Φ := (hf z).implicitToOpenPartialHomeomorphOfComplemented _ _
    (LinearMap.range_eq_top.2 (hsurj z)) (hker z)
  intro k hk
  let w := (sectionZeroChartAt hf hsurj hker K z).symm k
  have ht := (mem_sectionZeroChartAt_target_iff hf hsurj hker K z k).1 hk
  have hw := sectionZeroChartAt_symm_mem_source_and_baseSet_and_implicitCoordSource
    hf hsurj hker K z hk
  have hval : (w : M) = (chartAt X z.val).symm (Φ.symm (0, (K z).symm k)) :=
    coe_sectionZeroChartAt_symm_apply hf hsurj hker K z hk
  have hround : chartAt X z.val w.val = Φ.symm (0, (K z).symm k) := by
    rw [hval, (chartAt X z.val).right_inv ht.2.2.1]
  have hcoord := hs hm z w hw.1 hw.2.1 hw.2.2
  rw [hround] at hcoord
  have hinner : ContDiffAt 𝕜 m Φ.symm (0, (K z).symm k) :=
    (hf z).contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem _ _
      ht.1 ht.2.1 hcoord
  have hslice : ContDiffAt 𝕜 m (fun j ↦ Φ.symm (0, (K z).symm j)) k :=
    hinner.comp k (contDiffAt_const.prodMk (K z).symm.contDiff.contDiffAt)
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, X)) z.val) ht.2.2.1).comp k
      hslice.contMDiffAt
  apply (hc.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(sectionZeroChartAt hf hsurj hker K z).open_target.mem_nhds hk]
    with j hj
  exact coe_sectionZeroChartAt_symm_apply hf hsurj hker K z hj

include hs in
/-- Transitions between the preferred charts of the zero set are smooth. -/
theorem contDiffOn_sectionZeroChartAt_trans (z w : ↥{y | s y = 0}) :
    ContDiffOn 𝕜 m
      ((sectionZeroChartAt hf hsurj hker K z).symm.trans
        (sectionZeroChartAt hf hsurj hker K w))
      ((sectionZeroChartAt hf hsurj hker K z).symm.trans
        (sectionZeroChartAt hf hsurj hker K w)).source := by
  let χ := sectionZeroChartAt hf hsurj hker K z
  let χ' := sectionZeroChartAt hf hsurj hker K w
  let Ψ : X →L[𝕜] Y :=
    (K w : (D w).ker →L[𝕜] Y).comp (Classical.choose (hker w))
  have hbase := (contMDiffOn_coe_sectionZeroChartAt_symm hf hsurj hker K hs z).mono
    (t := (χ.symm.trans χ').source) (fun _ hk ↦ hk.1)
  have hc : ContMDiffOn 𝓘(𝕜, Y) 𝓘(𝕜, X) m
      (fun k ↦ chartAt X w.val ((χ.symm k : M))) (χ.symm.trans χ').source :=
    contMDiffOn_chart.comp hbase fun k hk ↦
      ((sectionZeroChartAt_source hf hsurj hker K w) ▸ hk.2).1.1
  have hcomp := Ψ.contDiff.comp_contDiffOn
    ((contMDiffOn_iff_contDiffOn.1 hc).sub
      (contDiffOn_const (c := chartAt X w.val w.val)))
  refine hcomp.congr fun k _ ↦ ?_
  simp only [Function.comp_def, OpenPartialHomeomorph.coe_trans,
    sectionZeroChartAt_apply, Ψ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rfl

include hs in
/-- The actual zero set of a section whose coordinate derivatives at the zeros are surjective
with complemented kernels is a smooth manifold modelled on `Y`, with the preferred section-zero
atlas. For a Fredholm section of constant index `n`, with `Y = Fin n → 𝕜`, it is a manifold of
dimension the index. -/
theorem isManifold_sectionZero :
    letI := sectionZeroChartedSpace hf hsurj hker K hb he
    IsManifold (modelWithCornersSelf 𝕜 Y) m ↥{y | s y = 0} := by
  let _i := sectionZeroChartedSpace hf hsurj hker K hb he
  refine isManifold_of_contDiffOn _ _ _ fun χ χ' hχ hχ' ↦ ?_
  rw [sectionZeroChartedSpace_atlas] at hχ hχ'
  obtain ⟨z, rfl⟩ := hχ
  obtain ⟨w, rfl⟩ := hχ'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id, Function.comp_id, Function.id_comp] using
    contDiffOn_sectionZeroChartAt_trans hf hsurj hker K hs z w

/-- The differential of the zero-set inclusion at a zero is the inclusion of the kernel
of its coordinate derivative, read through the identification `K z` of that kernel with `Y`.
Both tangent spaces use the preferred charts, so the ambient source-chart differential at its
centre is the identity. -/
theorem hasMFDerivAt_coe_sectionZero (z : ↥{y | s y = 0}) :
    letI := sectionZeroChartedSpace hf hsurj hker K hb he
    HasMFDerivAt 𝓘(𝕜, Y) 𝓘(𝕜, X)
      (Subtype.val : ↥{y | s y = 0} → M) z
      ((D z).ker.subtypeL.comp ((K z).symm : Y →L[𝕜] (D z).ker)) := by
  let _ := sectionZeroChartedSpace hf hsurj hker K hb he
  have hzero : (e z ⟨b ((chartAt X z.val).symm (chartAt X z.val z.val)),
      s ((chartAt X z.val).symm (chartAt X z.val z.val))⟩).2 = 0 := by
    rw [(chartAt X z.val).left_inv (mem_chart_source X z.val), z.property]
    exact congrArg Prod.snd ((e z).zeroSection 𝕜 (he z))
  let ψ := levelSetChart (hf z) (LinearMap.range_eq_top.2 (hsurj z)) (hker z) hzero
  have hderiv : HasFDerivAt (fun k ↦ (ψ.symm k : X)) (D z).ker.subtypeL ((K z).symm 0) := by
    simpa only [map_zero] using (hasStrictFDerivAt_coe_levelSetChart_symm
      (hf z) _ _ hzero).hasFDerivAt
  have hcomp := hderiv.comp 0 (K z).symm.hasFDerivAt
  have hcoord : HasFDerivAt
      (fun k ↦ chartAt X z.val ((sectionZeroChartAt hf hsurj hker K z).symm k : M))
      ((D z).ker.subtypeL.comp ((K z).symm : Y →L[𝕜] (D z).ker)) 0 := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [(sectionZeroChartAt hf hsurj hker K z).open_target.mem_nhds
      (mem_sectionZeroChartAt_target hf hsurj hker K hb he z)] with k hk
    have ht := (mem_sectionZeroChartAt_target_iff hf hsurj hker K z k).1 hk
    rw [coe_sectionZeroChartAt_symm_apply hf hsurj hker K z hk,
      (chartAt X z.val).right_inv ht.2.2.1]
    symm
    apply levelSetChart_symm_apply (hf z) _ _ hzero
    rw [levelSetChart_target]
    exact ht.1
  refine ⟨continuous_subtypeVal.continuousAt, ?_⟩
  -- The preferred source and target charts are exactly the coordinate map in `hcoord`;
  -- the tangent-space casts for these boundaryless models are identity maps.
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, sectionZeroChartedSpace_chartAt,
    sectionZeroChartAt_apply_self, Function.comp_def, Set.range_id, id_eq]
  convert hcoord.hasFDerivWithinAt using 1
  ext v
  rfl

include hs in
/-- For the preferred section-zero atlas, the inclusion into the Banach source manifold is
an immersion with complement the fiber model `F`. Only the atlas's coordinate smoothness
hypotheses are needed; no smooth bundle structure or differentiability of the base map is
required. -/
theorem isImmersionOfComplement_coe_sectionZero :
    letI := sectionZeroChartedSpace hf hsurj hker K hb he
    Manifold.IsImmersionOfComplement F 𝓘(𝕜, Y) 𝓘(𝕜, X) m
      (Subtype.val : ↥{y | s y = 0} → M) := by
  let _ := sectionZeroChartedSpace hf hsurj hker K hb he
  let := isManifold_sectionZero hf hsurj hker K hb he hs
  intro z
  let χ := sectionZeroChartAt hf hsurj hker K z
  obtain ⟨A, hA₁, hA₂⟩ :=
    ContinuousLinearMap.exists_continuousLinearEquiv_symm_eq (D z) (hsurj z) (hker z) (K z)
  let g (u : Y) := D z (chartAt X z.val (χ.symm u : M) - chartAt X z.val z.val)
  have hg : ContDiffOn 𝕜 m g χ.target :=
    (D z).contDiff.comp_contDiffOn ((contMDiffOn_iff_contDiffOn.1
      (contMDiffOn_chart.comp
        (contMDiffOn_coe_sectionZeroChartAt_symm hf hsurj hker K hs z)
        (fun k hk ↦ (sectionZeroChartAt_symm_mem_source_and_baseSet_and_implicitCoordSource
          hf hsurj hker K z hk).1))).sub
          contDiffOn_const)
  -- Subtract the smooth graph in the transverse coordinate. This uses smoothness only
  -- along the zero manifold, rather than requiring smoothness off the zero set.
  obtain ⟨Ψ, hΨ, hΨ', hΨsrc, hΨ_apply⟩ :=
    A.exists_contDiffOn_shear (chartAt X z.val z.val) χ.open_target hg
  have hcoord (w : ↥{y | s y = 0}) : (A.symm (chartAt X z.val w.val - chartAt X z.val z.val)).1 = χ
      w := by
    rw [hA₁]
    exact (sectionZeroChartAt_apply hf hsurj hker K z w).symm
  have hc := trans_mem_maximalAtlas_of_contDiffAt
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, X)) (n := m) z.val)
    (fun _ hz ↦ hΨ.contDiffAt (Ψ.open_source.mem_nhds hz))
    (fun _ hz ↦ hΨ'.contDiffAt (Ψ.open_target.mem_nhds hz))
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtypeVal.continuousAt A χ ((chartAt X z.val).trans Ψ)
    (mem_sectionZeroChartAt_source hf hsurj hker K hb he z)
  · have h₀ : (A.symm (chartAt X z.val z.val - chartAt X z.val z.val)).1 ∈ χ.target := by
      rw [sub_self, map_zero]
      exact mem_sectionZeroChartAt_target hf hsurj hker K hb he z
    exact ⟨mem_chart_source X z.val, (hΨsrc _).2 h₀⟩
  · simpa only [sectionZeroChartedSpace_chartAt] using
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, Y)) (n := m) z)
  · exact hc
  · intro u hu
    have hu' : u ∈ χ.target := by simpa using hu
    have hp : (A.symm (chartAt X z.val (χ.symm u : M) - chartAt X z.val z.val)).1 = u :=
      (hcoord (χ.symm u)).trans (χ.right_inv hu')
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [OpenPartialHomeomorph.trans_apply, hΨ_apply, hp]
    congr 1
    apply Prod.ext
    · rfl
    rw [hA₂]
    exact sub_self _

end TauCeti
