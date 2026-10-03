/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ZeroChart
public import Mathlib.Geometry.Manifold.Immersion

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
`isManifold_levelSet` for ordinary maps. The inclusion into the parameter space is smooth
for this atlas and is an immersion with complement the fiber model.

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
open scoped ContDiff Manifold Topology

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

/-- The derivative of the zero-manifold inclusion at a zero is the inclusion of the kernel
of the fiber-coordinate derivative `D z`, read through its identification with the index model. -/
theorem hasMFDerivAt_coe_sectionZero (z : ↥{y | s y = 0}) :
    letI := sectionZeroChartedSpace hf hFred hsurj hindex hb he
    HasMFDerivAt (modelWithCornersSelf 𝕜 (Fin n → 𝕜)) (modelWithCornersSelf 𝕜 X)
      (Subtype.val : ↥{y | s y = 0} → X) z
      ((D z).ker.subtypeL.comp
        (((D z).kerModelEquiv (hFred z).finite_ker
          ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hsurj z)).2
            (hindex z))).symm : (Fin n → 𝕜) →L[𝕜] (D z).ker)) := by
  let _ := sectionZeroChartedSpace hf hFred hsurj hindex hb he
  let K := (D z).kerModelEquiv (hFred z).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hsurj z)).2 (hindex z))
  let ψ := sectionZeroChart (hf z) (LinearMap.range_eq_top.2 (hsurj z))
    (hFred z).closedComplemented_ker z.2
  have hderiv : HasFDerivAt (fun k ↦ (ψ.symm k : X)) (D z).ker.subtypeL (K.symm 0) := by
    simpa only [map_zero] using (hasStrictFDerivAt_coe_sectionZeroChart_symm
      (hb z) (he z) (hf z) _ _ z.2).hasFDerivAt
  have hcomp := hderiv.comp 0 K.symm.hasFDerivAt
  have hcoord : HasFDerivAt
      (fun k ↦ ((sectionZeroChartAt hf hFred hsurj hindex z).symm k : X))
      ((D z).ker.subtypeL.comp (K.symm : (Fin n → 𝕜) →L[𝕜] (D z).ker)) 0 := by
    simpa only [Function.comp_def, sectionZeroChartAt_symm_apply] using hcomp
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  -- In the preferred zero chart, the derivative is exactly the derivative of the inverse
  -- parametrization. The model tangent-space casts in `HasMFDerivAt` are identities here.
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    sectionZeroChartedSpace_chartAt, sectionZeroChartAt_apply_self,
    Function.comp_def, Set.range_id, id_eq]
  convert hcoord.hasFDerivWithinAt using 1
  ext v
  rfl

include hs in
/-- For the preferred section-zero atlas, the inclusion into the Banach parameter space is
an immersion with complement the fiber model `F`. Only the atlas's coordinate smoothness
hypotheses are needed; no smooth bundle structure or differentiability of the base map is
required. -/
theorem isImmersionOfComplement_coe_sectionZero :
    letI := sectionZeroChartedSpace hf hFred hsurj hindex hb he
    Manifold.IsImmersionOfComplement F 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
      (Subtype.val : ↥{y | s y = 0} → X) := by
  let _ := sectionZeroChartedSpace hf hFred hsurj hindex hb he
  let := isManifold_sectionZero hf hFred hsurj hindex hb he hs
  intro z
  let χ := sectionZeroChartAt hf hFred hsurj hindex z
  let K := (D z).kerModelEquiv (hFred z).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hsurj z)).2 (hindex z))
  let L := (D z).implicitCoordEquiv (LinearMap.range_eq_top.2 (hsurj z))
    (hFred z).closedComplemented_ker
  have hL (x : X) : L x = (D z x, Classical.choose (hFred z).closedComplemented_ker x) :=
    congrArg (fun T : X →L[𝕜] F × (D z).ker ↦ T x) ((D z).coe_implicitCoordEquiv _ _)
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
  let g (u : Fin n → 𝕜) := D z ((χ.symm u : X) - z.1)
  have hg : ContDiffOn 𝕜 m g χ.target :=
    (D z).contDiff.comp_contDiffOn
      ((contDiffOn_coe_sectionZeroChartAt_symm hf hFred hsurj hindex hs z).sub contDiffOn_const)
  have hminus : ContDiffOn 𝕜 m (fun p : (Fin n → 𝕜) × F ↦ (p.1, p.2 - g p.1))
      (Prod.fst ⁻¹' χ.target) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.sub
      (hg.comp contDiffOn_fst (fun _ hp ↦ hp)))
  have hplus : ContDiffOn 𝕜 m (fun p : (Fin n → 𝕜) × F ↦ (p.1, p.2 + g p.1))
      (Prod.fst ⁻¹' χ.target) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add
      (hg.comp contDiffOn_fst (fun _ hp ↦ hp)))
  -- Subtract the smooth graph in the transverse coordinate. This uses smoothness only
  -- along the zero manifold, rather than requiring smoothness off the zero set.
  let shear : OpenPartialHomeomorph ((Fin n → 𝕜) × F) ((Fin n → 𝕜) × F) :=
    { toFun := fun p ↦ (p.1, p.2 - g p.1)
      invFun := fun p ↦ (p.1, p.2 + g p.1)
      source := Prod.fst ⁻¹' χ.target
      target := Prod.fst ⁻¹' χ.target
      map_source' := fun _ hp ↦ hp
      map_target' := fun _ hp ↦ hp
      left_inv' := fun p _ ↦ by simp
      right_inv' := fun p _ ↦ by simp
      open_source := χ.open_target.preimage continuous_fst
      open_target := χ.open_target.preimage continuous_fst
      continuousOn_toFun := hminus.continuousOn
      continuousOn_invFun := hplus.continuousOn }
  let affine := (Homeomorph.addRight (-z.1)).trans A.symm.toHomeomorph
  let Ψ := (affine.toOpenPartialHomeomorph.trans shear).transHomeomorph A.toHomeomorph
  -- Evaluate the affine translation and the graph shear through their composition API.
  have hΨ_apply (x : X) : Ψ x =
      A ((A.symm (x - z.1)).1, (A.symm (x - z.1)).2 - g (A.symm (x - z.1)).1) := by
    simp only [Ψ, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
      OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      affine, Homeomorph.trans_apply, Homeomorph.coe_addRight,
      ContinuousLinearEquiv.coe_toHomeomorph, ← sub_eq_add_neg]
    rfl
  have hΨ : Ψ ∈ IsManifold.maximalAtlas 𝓘(𝕜, X) m X := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · apply ContDiffOn.contMDiffOn
      exact A.contDiff.comp_contDiffOn
        (hminus.comp (A.symm.contDiff.comp (contDiff_id.add contDiff_const)).contDiffOn
          (fun _ hp ↦ hp.2))
    · apply ContDiffOn.contMDiffOn
      exact ((A.contDiff.comp_contDiffOn
        (hplus.comp A.symm.contDiff.contDiffOn (fun _ hp ↦ hp.1))).add
          contDiffOn_const)
  have hcoord (w : ↥{y | s y = 0}) : (A.symm (w.1 - z.1)).1 = χ w := by
    rw [hA_symm, hL]
    exact (sectionZeroChartAt_apply hf hFred hsurj hindex z w).symm
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt A χ Ψ
    (mem_sectionZeroChartAt_source hf hFred hsurj hindex hb he z)
  · simpa [Ψ, affine, shear, hcoord, χ] using
      mem_sectionZeroChartAt_target hf hFred hsurj hindex hb he z
  · simpa only [sectionZeroChartedSpace_chartAt] using
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, Fin n → 𝕜)) (n := m) z)
  · exact hΨ
  · intro u hu
    have hu' : u ∈ χ.target := by simpa using hu
    have hp : (A.symm ((χ.symm u : X) - z.1)).1 = u :=
      (hcoord (χ.symm u)).trans (χ.right_inv hu')
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [hΨ_apply, hp]
    congr 1
    apply Prod.ext
    · rfl
    rw [hA_symm, hL]
    exact sub_self _

end TauCeti
