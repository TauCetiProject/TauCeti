/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Manifold
public import Mathlib.Geometry.Manifold.Immersion

/-!
# Zero manifolds of smooth Fredholm sections

Over `ℝ` or `ℂ`, a smooth section along a map from a Banach space has a smooth zero manifold
whenever its intrinsic linearization is surjective Fredholm of constant index at its zeros.
This file derives
all the fiber-coordinate hypotheses of the section-zero atlas from smoothness of the map into
the total space. The inclusion of the zero manifold into the parameter space is a smooth
immersion, with tangent image equal to the kernel of the intrinsic linearization.

Smoothness is needed only at zeros, not everywhere. Fredholmness, surjectivity and the index
are stated intrinsically, so callers need not choose a trivialization or supply derivatives of
coordinate expressions. The source is a Banach space; arbitrary manifold sources are not
covered here. As usual, `IsManifold` asserts smooth compatibility of charts, without imposing
second countability.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.3, for regular zeros of Fredholm sections.

The construction consumes `sectionZeroChartedSpace` and `isManifold_sectionZero`.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {𝕜 X B F : Type*} {E : B → Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace B] [∀ a, TopologicalSpace (E a)]
  [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {b : X → B} {s : ∀ y, E (b y)}
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {m : ℕ∞ω} [ContMDiffVectorBundle m F E I]

/-- Regular zeros of a smooth Fredholm section along a map from a Banach space form a smooth
manifold of dimension the intrinsic Fredholm index. Its inclusion into the parameter space is
a smooth immersion with complement `F`, and tangent image the intrinsic linearization's kernel.
Only smoothness at zeros is required, at a nonzero differentiability order.

The charted-space structure is supplied as a witness, so it can be installed locally with
`letI`. No chartwise derivative or smoothness hypotheses need to be supplied by the caller. -/
theorem exists_isManifold_sectionZero_of_contMDiff {n : ℕ} (hm : m ≠ 0)
    : letI := ContMDiffVectorBundle.of_le (F := F) (E := E) (IB := I)
        (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    (∀ x, s x = 0 → ContMDiffAt 𝓘(𝕜, X) (I.prod 𝓘(𝕜, F)) m
      (fun y ↦ (⟨b y, s y⟩ : TotalSpace F E)) x) →
    (∀ x, s x = 0 →
      ContinuousLinearMap.IsFredholm (sectionLinearization (𝕜 := 𝕜) (F := F) b s x)) →
    (∀ x, s x = 0 →
      Function.Surjective (sectionLinearization (𝕜 := 𝕜) (F := F) b s x)) →
    (∀ x, s x = 0 →
      LinearMap.index (sectionLinearization (𝕜 := 𝕜) (F := F) b s x).toLinearMap = n) →
    ∃ cs : ChartedSpace (Fin n → 𝕜) ↥{y | s y = 0},
      letI := cs
      IsManifold 𝓘(𝕜, Fin n → 𝕜) m ↥{y | s y = 0} ∧
        ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
          (Subtype.val : ↥{y | s y = 0} → X) ∧
        Manifold.IsImmersionOfComplement F 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
          (Subtype.val : ↥{y | s y = 0} → X) ∧
        ∀ z : ↥{y | s y = 0},
          Function.Injective (mvfderiv 𝓘(𝕜, Fin n → 𝕜) Subtype.val z) ∧
          (mvfderiv 𝓘(𝕜, Fin n → 𝕜) Subtype.val z).range =
            (sectionLinearization (𝕜 := 𝕜) (F := F) b s z.1).ker := by
  let := ContMDiffVectorBundle.of_le (F := F) (E := E) (IB := I)
    (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  intro hs hFred hsurj hindex
  -- Smoothness into the total space supplies smooth coordinates in every relevant chart.
  let e (z : ↥{y | s y = 0}) := trivializationAt F E (b z.1)
  have he (z : ↥{y | s y = 0}) : b z.1 ∈ (e z).baseSet :=
    mem_baseSet_trivializationAt F E (b z.1)
  have hcoord (z w : ↥{y | s y = 0}) (hw : b w.1 ∈ (e z).baseSet) :
      ContDiffAt 𝕜 m (fun y ↦ (e z ⟨b y, s y⟩).2) w.1 := by
    exact contMDiffAt_iff_contDiffAt.1
      (((e z).contMDiffAt_iff ((e z).mem_source.2 hw)).1 (hs w.1 w.2)).2
  have hb (z : ↥{y | s y = 0}) : MDifferentiableAt 𝓘(𝕜, X) I b z.1 :=
    ((contMDiffAt_totalSpace.1 (hs z.1 z.2)).1).mdifferentiableAt hm
  -- Transport the intrinsic hypotheses to the coordinate derivatives used by the atlas.
  let D (z : ↥{y | s y = 0}) := fderiv 𝕜 (fun y ↦ (e z ⟨b y, s y⟩).2) z.1
  have hf (z : ↥{y | s y = 0}) :
      HasStrictFDerivAt (fun y ↦ (e z ⟨b y, s y⟩).2) (D z) z.1 :=
    (hcoord z z (he z)).hasStrictFDerivAt hm
  have hF (z : ↥{y | s y = 0}) : ContinuousLinearMap.IsFredholm (D z) :=
    (isFredholm_sectionLinearization_iff (hb z) (he z)
      ((hcoord z z (he z)).differentiableAt hm) z.2).1 (hFred z.1 z.2)
  have hS (z : ↥{y | s y = 0}) : Function.Surjective (D z) :=
    (surjective_sectionLinearization_iff (hb z) (he z)
      ((hcoord z z (he z)).differentiableAt hm) z.2).1 (hsurj z.1 z.2)
  have hN (z : ↥{y | s y = 0}) : ContinuousLinearMap.index (D z) = n := by
    rw [← index_sectionLinearization (hb z) (he z)
      ((hcoord z z (he z)).differentiableAt hm) z.2]
    exact hindex z.1 z.2
  have hsmooth : m ≠ 0 → ∀ z w : ↥{y | s y = 0}, b w.1 ∈ (e z).baseSet →
      w.1 ∈ (hf z).implicitCoordSource (LinearMap.range_eq_top.2 (hS z))
        (hF z).closedComplemented_ker →
      ContDiffAt 𝕜 m (fun y ↦ (e z ⟨b y, s y⟩).2) w.1 :=
    fun _ z w hw _ ↦ hcoord z w hw
  let _ := sectionZeroChartedSpace hf hF hS hN (fun z ↦ (hb z).continuousAt) he
  let := isManifold_sectionZero hf hF hS hN (fun z ↦ (hb z).continuousAt) he hsmooth
  have himm : Manifold.IsImmersionOfComplement F 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
      (Subtype.val : ↥{y | s y = 0} → X) := by
    intro z
    let χ := sectionZeroChartAt hf hF hS hN z
    let K := (D z).kerModelEquiv (hF z).finite_ker
      ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hS z)).2 (hN z))
    let L := (D z).implicitCoordEquiv (LinearMap.range_eq_top.2 (hS z))
      (hF z).closedComplemented_ker
    have hL (x : X) : L x = (D z x, Classical.choose (hF z).closedComplemented_ker x) :=
      congrArg (fun T : X →L[𝕜] F × (D z).ker ↦ T x) ((D z).coe_implicitCoordEquiv _ _)
    let A : ((Fin n → 𝕜) × F) ≃L[𝕜] X :=
      ((K.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans
        (ContinuousLinearEquiv.prodComm 𝕜 _ _)).trans L.symm
    let g (u : Fin n → 𝕜) := D z ((χ.symm u : X) - z.1)
    have hg : ContDiffOn 𝕜 m g χ.target :=
      (D z).contDiff.comp_contDiffOn
        ((contDiffOn_coe_sectionZeroChartAt_symm hf hF hS hN hsmooth z).sub contDiffOn_const)
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
      change K (L (w.1 - z.1)).2 = χ w
      rw [hL]
      exact (sectionZeroChartAt_apply hf hF hS hN z w).symm
    apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
      continuous_subtype_val.continuousAt A χ Ψ
      (mem_sectionZeroChartAt_source hf hF hS hN (fun z ↦ (hb z).continuousAt) he z)
    · simpa [Ψ, affine, shear, hcoord, χ] using
        mem_sectionZeroChartAt_target hf hF hS hN (fun z ↦ (hb z).continuousAt) he z
    · simpa only [sectionZeroChartedSpace_chartAt] using
        (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, Fin n → 𝕜)) (n := m) z)
    · exact hΨ
    · intro u hu
      have hu' : u ∈ χ.target := by simpa using hu
      have hp : (A.symm ((χ.symm u : X) - z.1)).1 = u :=
        (hcoord (χ.symm u)).trans (χ.right_inv hu')
      simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
      rw [show Ψ = (affine.toOpenPartialHomeomorph.trans shear).transHomeomorph
        A.toHomeomorph from rfl, OpenPartialHomeomorph.transHomeomorph_apply,
        Function.comp_apply, OpenPartialHomeomorph.trans_apply]
      simp only [Homeomorph.toOpenPartialHomeomorph_apply, affine, Homeomorph.trans_apply,
        Homeomorph.coe_addRight, ContinuousLinearEquiv.coe_toHomeomorph]
      rw [← sub_eq_add_neg]
      change A ((A.symm ((χ.symm u : X) - z.1)).1,
        (A.symm ((χ.symm u : X) - z.1)).2 - g (A.symm ((χ.symm u : X) - z.1)).1) = A (u, 0)
      rw [hp]
      congr 1
      apply Prod.ext
      · rfl
      change (L ((χ.symm u : X) - z.1)).1 - g u = 0
      rw [hL]
      exact sub_self _
  refine ⟨sectionZeroChartedSpace hf hF hS hN (fun z ↦ (hb z).continuousAt) he,
    isManifold_sectionZero hf hF hS hN (fun z ↦ (hb z).continuousAt) he hsmooth,
    contMDiff_coe_sectionZero hf hF hS hN (fun z ↦ (hb z).continuousAt) he hsmooth, himm, ?_⟩
  -- The inclusion derivative is a kernel inclusion composed with an equivalence.
  intro z
  let K := (D z).kerModelEquiv (hF z).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hS z)).2 (hN z))
  let T : (Fin n → 𝕜) →L[𝕜] X :=
    (D z).ker.subtypeL.comp (K.symm : (Fin n → 𝕜) →L[𝕜] (D z).ker)
  have hinj : Function.Injective T := Subtype.val_injective.comp K.symm.injective
  have hrange : T.range = (sectionLinearization (𝕜 := 𝕜) (F := F) b s z.1).ker := by
    rw [sectionLinearization_eq_symmL_comp (hb z) (he z)
      ((hcoord z z (he z)).differentiableAt hm) z.2,
      ← (e z).symm_continuousLinearEquivAt_eq' (he z)]
    simp only [T, ContinuousLinearMap.toLinearMap_comp, Submodule.toLinearMap_subtypeL,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
    rw [LinearMap.range_comp_of_range_eq_top (D z).ker.subtype
      (f := K.symm.toLinearEquiv.toLinearMap) K.symm.toLinearEquiv.range,
      LinearMap.ker_comp_of_ker_eq_bot _
        (LinearMap.ker_eq_bot.2 ((e z).continuousLinearEquivAt 𝕜 (b z.1) (he z)).symm.injective)]
    exact Submodule.range_subtype _
  have hd := (hasMFDerivAt_coe_sectionZero hf hF hS hN
    (fun z ↦ (hb z).continuousAt) he z).mfderiv
  have hv : mvfderiv 𝓘(𝕜, Fin n → 𝕜) (Subtype.val : ↥{y | s y = 0} → X) z = T := by
    -- The target is a normed space, so its canonical tangent identification is the identity.
    change mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) Subtype.val z = T
    exact hd
  exact hv.symm ▸ ⟨hinj, hrange⟩

end TauCeti
