/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Chart
public import Mathlib.Geometry.Manifold.Immersion
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Smooth atlases on regular zero sets of bundle sections

For a section along a map from a Banach manifold, continuous at its zeros, regular Fredholm zeros
of constant index `n` form a manifold modelled on `Fin n → 𝕜`. The atlas is on the actual zero
set, not on an extended fiber-coordinate equation, which can have spurious zeros outside a
trivialization.

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
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti

section General

variable {𝕜 V W Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {m : ℕ∞ω}

/-- **A shear chart of a normed space**: given a linear homeomorphism `A : V × W ≃ Y`, a basepoint
`c₀` and a map `g : V → W` which is `C^m` on an open set `U`, there is a partial homeomorphism of
`Y`, `C^m` with `C^m` inverse, which sends `x` to `A (u, w - g u)`, where `(u, w) = A⁻¹ (x - c₀)`,
and whose source is the set of points with `u ∈ U`. -/
theorem exists_contDiffOn_shear (A : (V × W) ≃L[𝕜] Y) (c₀ : Y) {U : Set V}
    (hU : IsOpen U) {g : V → W} (hg : ContDiffOn 𝕜 m g U) :
    ∃ Ψ : OpenPartialHomeomorph Y Y, ContDiffOn 𝕜 m Ψ Ψ.source ∧ ContDiffOn 𝕜 m Ψ.symm Ψ.target ∧
      (∀ x, x ∈ Ψ.source ↔ (A.symm (x - c₀)).1 ∈ U) ∧
      ∀ x, Ψ x = A ((A.symm (x - c₀)).1, (A.symm (x - c₀)).2 - g (A.symm (x - c₀)).1) := by
  have hminus : ContDiffOn 𝕜 m (fun p : V × W ↦ (p.1, p.2 - g p.1)) (Prod.fst ⁻¹' U) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.sub
      (hg.comp contDiffOn_fst (fun _ hp ↦ hp)))
  have hplus : ContDiffOn 𝕜 m (fun p : V × W ↦ (p.1, p.2 + g p.1)) (Prod.fst ⁻¹' U) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add
      (hg.comp contDiffOn_fst (fun _ hp ↦ hp)))
  -- Subtract the smooth graph in the transverse coordinate.
  let shear : OpenPartialHomeomorph (V × W) (V × W) :=
    { toFun := fun p ↦ (p.1, p.2 - g p.1)
      invFun := fun p ↦ (p.1, p.2 + g p.1)
      source := Prod.fst ⁻¹' U
      target := Prod.fst ⁻¹' U
      map_source' := fun _ hp ↦ hp
      map_target' := fun _ hp ↦ hp
      left_inv' := fun p _ ↦ by simp
      right_inv' := fun p _ ↦ by simp
      open_source := hU.preimage continuous_fst
      open_target := hU.preimage continuous_fst
      continuousOn_toFun := hminus.continuousOn
      continuousOn_invFun := hplus.continuousOn }
  let affine := (Homeomorph.addRight (-c₀)).trans A.symm.toHomeomorph
  let Ψ := (affine.toOpenPartialHomeomorph.trans shear).transHomeomorph A.toHomeomorph
  have hΨ_apply (x : Y) : Ψ x =
      A ((A.symm (x - c₀)).1, (A.symm (x - c₀)).2 - g (A.symm (x - c₀)).1) := by
    simp only [Ψ, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
      OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      affine, Homeomorph.trans_apply, Homeomorph.coe_addRight,
      ContinuousLinearEquiv.coe_toHomeomorph, ← sub_eq_add_neg]
    rfl
  refine ⟨Ψ, ?_, ?_, fun x ↦ ?_, hΨ_apply⟩
  · exact A.contDiff.comp_contDiffOn
      (hminus.comp (A.symm.contDiff.comp (contDiff_id.add contDiff_const)).contDiffOn
        (fun _ (hp : _ ∈ Ψ.source) ↦ hp.2))
  · exact (A.contDiff.comp_contDiffOn
      (hplus.comp A.symm.contDiff.contDiffOn (fun _ hp ↦ Set.mem_of_mem_inter_left hp))).add
        contDiffOn_const
  · simp [Ψ, affine, shear, ← sub_eq_add_neg]

end General

section Fredholm

variable {𝕜 X F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] {n : ℕ}

/-- A surjective Fredholm map `D : X → F` of index `n` gives a linear homeomorphism
`(Fin n → 𝕜) × F ≃ X` whose inverse has the kernel model coordinate of the chosen kernel
projection as first component and `D` itself as second component. -/
theorem exists_continuousLinearEquiv_symm_eq (D : X →L[𝕜] F) (hFred : D.IsFredholm)
    (hsurj : Function.Surjective D) (hindex : D.index = n) :
    ∃ A : ((Fin n → 𝕜) × F) ≃L[𝕜] X,
      (∀ x, (A.symm x).1 = D.kerModelEquiv hFred.finite_ker
        ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq D hsurj).2 hindex)
        (Classical.choose hFred.closedComplemented_ker x)) ∧
      ∀ x, (A.symm x).2 = D x := by
  let K := D.kerModelEquiv hFred.finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq D hsurj).2 hindex)
  let L := D.implicitCoordEquiv (LinearMap.range_eq_top.2 hsurj)
    hFred.closedComplemented_ker
  have hL (x : X) : L x = (D x, Classical.choose hFred.closedComplemented_ker x) :=
    congrArg (fun T : X →L[𝕜] F × D.ker ↦ T x) (D.coe_implicitCoordEquiv _ _)
  let A : ((Fin n → 𝕜) × F) ≃L[𝕜] X :=
    ((K.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans
      (ContinuousLinearEquiv.prodComm 𝕜 _ _)).trans L.symm
  -- Inverting the product equivalences puts the kernel coordinate first.
  have hA_symm (x : X) : A.symm x = (K (L x).2, (L x).1) := by
    simp only [A, ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodComm_symm,
      ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.prodComm_apply,
      ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
      Prod.fst_swap, Prod.snd_swap]
  exact ⟨A, fun x ↦ by rw [hA_symm, hL], fun x ↦ by rw [hA_symm, hL]⟩

end Fredholm

variable {𝕜 X M B F : Type*} {E : B → Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [TopologicalSpace M] [ChartedSpace X M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace B] [∀ a, TopologicalSpace (E a)]
  [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {b : M → B} {s : ∀ y, E (b y)}
  {e : ↥{y | s y = 0} → Trivialization F (π F E)}
  [∀ z, MemTrivializationAtlas (e z)]
  {D : ↥{y | s y = 0} → X →L[𝕜] F} {n : ℕ}

variable
  (hf : ∀ z, HasStrictFDerivAt
    (fun y ↦ (e z ⟨b ((chartAt X z.1).symm y), s ((chartAt X z.1).symm y)⟩).2)
    (D z) (chartAt X z.1 z.1))
  (hFred : ∀ z, ContinuousLinearMap.IsFredholm (D z))
  (hsurj : ∀ z, Function.Surjective (D z))
  (hindex : ∀ z, ContinuousLinearMap.index (D z) = n)

variable (hb : ∀ z : ↥{y | s y = 0}, ContinuousAt b z.1)
  (he : ∀ z, b z.1 ∈ (e z).baseSet)

variable {m : ℕ∞ω} [IsManifold 𝓘(𝕜, X) m M]
  (hs : m ≠ 0 → ∀ z w : ↥{y | s y = 0}, w.1 ∈ (chartAt X z.1).source →
    b w.1 ∈ (e z).baseSet →
    chartAt X z.1 w.1 ∈ (hf z).implicitCoordSource
      (LinearMap.range_eq_top.2 (hsurj z)) (hFred z).closedComplemented_ker →
    ContDiffAt 𝕜 m
      (fun y ↦ (e z ⟨b ((chartAt X z.1).symm y), s ((chartAt X z.1).symm y)⟩).2)
      (chartAt X z.1 w.1))

include hs in
/-- The inverse preferred chart, included into the source manifold, is smooth throughout
its target. -/
theorem contMDiffOn_coe_sectionZeroChartAt_symm (z : ↥{y | s y = 0}) :
    ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
      (fun k ↦ ((sectionZeroChartAt hf hFred hsurj hindex z).symm k : M))
      (sectionZeroChartAt hf hFred hsurj hindex z).target := by
  by_cases hm : m = 0
  · subst m
    exact contMDiffOn_zero_iff.2 (continuous_subtype_val.comp_continuousOn
      (sectionZeroChartAt hf hFred hsurj hindex z).continuousOn_symm)
  let K := (D z).kerModelEquiv (hFred z).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hsurj z)).2 (hindex z))
  let Φ := (hf z).implicitToOpenPartialHomeomorphOfComplemented _ _
    (LinearMap.range_eq_top.2 (hsurj z)) (hFred z).closedComplemented_ker
  intro k hk
  let w := (sectionZeroChartAt hf hFred hsurj hindex z).symm k
  have ht := (mem_sectionZeroChartAt_target_iff hf hFred hsurj hindex z k).1 hk
  have hw := sectionZeroChartAt_symm_mem_source_and_baseSet_and_implicitCoordSource
    hf hFred hsurj hindex z hk
  have hval : (w : M) = (chartAt X z.1).symm (Φ.symm (0, K.symm k)) :=
    coe_sectionZeroChartAt_symm_apply hf hFred hsurj hindex z hk
  have hround : chartAt X z.1 w.1 = Φ.symm (0, K.symm k) := by
    rw [hval, (chartAt X z.1).right_inv ht.2.2.1]
  have hcoord := hs hm z w hw.1 hw.2.1 hw.2.2
  rw [hround] at hcoord
  have hinner : ContDiffAt 𝕜 m Φ.symm (0, K.symm k) :=
    (hf z).contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem _ _
      ht.1 ht.2.1 (hcoord.differentiableAt hm).hasFDerivAt hcoord
  have hslice : ContDiffAt 𝕜 m (fun j ↦ Φ.symm (0, K.symm j)) k :=
    hinner.comp k (contDiffAt_const.prodMk K.symm.contDiff.contDiffAt)
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, X)) z.1) ht.2.2.1).comp k
      hslice.contMDiffAt
  apply (hc.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(sectionZeroChartAt hf hFred hsurj hindex z).open_target.mem_nhds hk]
    with j hj
  exact coe_sectionZeroChartAt_symm_apply hf hFred hsurj hindex z hj

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
  have hbase := (contMDiffOn_coe_sectionZeroChartAt_symm hf hFred hsurj hindex hs z).mono
    (t := (χ.symm.trans χ').source) (fun _ hk ↦ hk.1)
  have hc : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
      (fun k ↦ chartAt X w.1 ((χ.symm k : M))) (χ.symm.trans χ').source :=
    contMDiffOn_chart.comp hbase fun k hk ↦
      ((sectionZeroChartAt_source hf hFred hsurj hindex w) ▸ hk.2).1.1
  have hcomp := Ψ.contDiff.comp_contDiffOn
    ((contMDiffOn_iff_contDiffOn.1 hc).sub
      (contDiffOn_const (c := chartAt X w.1 w.1)))
  refine hcomp.congr fun k _ ↦ ?_
  simp only [Function.comp_def, OpenPartialHomeomorph.coe_trans,
    sectionZeroChartAt_apply, Ψ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rfl

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

/-- The differential of the zero-set inclusion at a zero is the inclusion of the kernel
of its coordinate derivative, read through the index model. Both tangent spaces use the
preferred charts, so the ambient source-chart differential at its centre is the identity. -/
theorem hasMFDerivAt_coe_sectionZero (z : ↥{y | s y = 0}) :
    letI := sectionZeroChartedSpace hf hFred hsurj hindex hb he
    HasMFDerivAt 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X)
      (Subtype.val : ↥{y | s y = 0} → M) z
      ((D z).ker.subtypeL.comp
        (((D z).kerModelEquiv (hFred z).finite_ker
          ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hsurj z)).2
            (hindex z))).symm : (Fin n → 𝕜) →L[𝕜] (D z).ker)) := by
  let _ := sectionZeroChartedSpace hf hFred hsurj hindex hb he
  let K := (D z).kerModelEquiv (hFred z).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hsurj z)).2 (hindex z))
  have hzero : (e z ⟨b ((chartAt X z.1).symm (chartAt X z.1 z.1)),
      s ((chartAt X z.1).symm (chartAt X z.1 z.1))⟩).2 = 0 := by
    rw [(chartAt X z.1).left_inv (mem_chart_source X z.1), z.2]
    exact congrArg Prod.snd ((e z).zeroSection 𝕜 (he z))
  let ψ := levelSetChart (hf z) (LinearMap.range_eq_top.2 (hsurj z))
    (hFred z).closedComplemented_ker hzero
  have hderiv : HasFDerivAt (fun k ↦ (ψ.symm k : X)) (D z).ker.subtypeL (K.symm 0) := by
    simpa only [map_zero] using (hasStrictFDerivAt_coe_levelSetChart_symm
      (hf z) _ _ hzero).hasFDerivAt
  have hcomp := hderiv.comp 0 K.symm.hasFDerivAt
  have hcoord : HasFDerivAt
      (fun k ↦ chartAt X z.1 ((sectionZeroChartAt hf hFred hsurj hindex z).symm k : M))
      ((D z).ker.subtypeL.comp (K.symm : (Fin n → 𝕜) →L[𝕜] (D z).ker)) 0 := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [(sectionZeroChartAt hf hFred hsurj hindex z).open_target.mem_nhds
      (mem_sectionZeroChartAt_target hf hFred hsurj hindex hb he z)] with k hk
    have ht := (mem_sectionZeroChartAt_target_iff hf hFred hsurj hindex z k).1 hk
    rw [coe_sectionZeroChartAt_symm_apply hf hFred hsurj hindex z hk,
      (chartAt X z.1).right_inv ht.2.2.1]
    symm
    apply levelSetChart_symm_apply (hf z) _ _ hzero
    rw [levelSetChart_target]
    exact ht.1
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
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
    letI := sectionZeroChartedSpace hf hFred hsurj hindex hb he
    Manifold.IsImmersionOfComplement F 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
      (Subtype.val : ↥{y | s y = 0} → M) := by
  let _ := sectionZeroChartedSpace hf hFred hsurj hindex hb he
  let := isManifold_sectionZero hf hFred hsurj hindex hb he hs
  intro z
  let χ := sectionZeroChartAt hf hFred hsurj hindex z
  obtain ⟨A, hA₁, hA₂⟩ := exists_continuousLinearEquiv_symm_eq (D z) (hFred z) (hsurj z) (hindex z)
  let g (u : Fin n → 𝕜) := D z (chartAt X z.1 (χ.symm u : M) - chartAt X z.1 z.1)
  have hg : ContDiffOn 𝕜 m g χ.target :=
    (D z).contDiff.comp_contDiffOn ((contMDiffOn_iff_contDiffOn.1
      (contMDiffOn_chart.comp
        (contMDiffOn_coe_sectionZeroChartAt_symm hf hFred hsurj hindex hs z)
        (fun k hk ↦ (sectionZeroChartAt_symm_mem_source_and_baseSet_and_implicitCoordSource
          hf hFred hsurj hindex z hk).1))).sub
          contDiffOn_const)
  -- Subtract the smooth graph in the transverse coordinate. This uses smoothness only
  -- along the zero manifold, rather than requiring smoothness off the zero set.
  obtain ⟨Ψ, hΨ, hΨ', hΨsrc, hΨ_apply⟩ :=
    exists_contDiffOn_shear A (chartAt X z.1 z.1) χ.open_target hg
  have hcoord (w : ↥{y | s y = 0}) : (A.symm (chartAt X z.1 w.1 - chartAt X z.1 z.1)).1 = χ w := by
    rw [hA₁]
    exact (sectionZeroChartAt_apply hf hFred hsurj hindex z w).symm
  have hc := trans_mem_maximalAtlas_of_contDiffAt
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, X)) (n := m) z.1)
    (fun _ hz ↦ hΨ.contDiffAt (Ψ.open_source.mem_nhds hz))
    (fun _ hz ↦ hΨ'.contDiffAt (Ψ.open_target.mem_nhds hz))
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt A χ ((chartAt X z.1).trans Ψ)
    (mem_sectionZeroChartAt_source hf hFred hsurj hindex hb he z)
  · refine ⟨mem_chart_source X z.1, (hΨsrc _).2 ?_⟩
    change (A.symm (chartAt X z.1 z.1 - chartAt X z.1 z.1)).1 ∈ χ.target
    rw [sub_self, map_zero]
    exact mem_sectionZeroChartAt_target hf hFred hsurj hindex hb he z
  · simpa only [sectionZeroChartedSpace_chartAt] using
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, Fin n → 𝕜)) (n := m) z)
  · exact hc
  · intro u hu
    have hu' : u ∈ χ.target := by simpa using hu
    have hp : (A.symm (chartAt X z.1 (χ.symm u : M) - chartAt X z.1 z.1)).1 = u :=
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
