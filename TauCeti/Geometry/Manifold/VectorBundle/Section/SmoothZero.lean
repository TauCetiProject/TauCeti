/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Manifold

import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Zero manifolds of smooth Fredholm sections

Over `ℝ` or `ℂ`, a smooth section along a map from a Banach manifold has a smooth zero manifold
whenever its intrinsic linearization is surjective Fredholm of constant index at its zeros.
This file derives the fiber-coordinate hypotheses of the section-zero atlas from smoothness into
the total space. The inclusion of the zero manifold into the parameter space is a smooth
immersion, with tangent image equal to the kernel of the intrinsic linearization.

Smoothness is needed only at zeros, not everywhere. Fredholmness, surjectivity and the index
are stated intrinsically, so callers need not choose a trivialization or supply derivatives of
coordinate expressions. The source is a boundaryless manifold modelled on a Banach space.
As usual, `IsManifold` asserts smooth compatibility of charts, without imposing
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

variable {𝕜 X M B F : Type*} {E : B → Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [TopologicalSpace M] [ChartedSpace X M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace B] [∀ a, TopologicalSpace (E a)]
  [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {b : M → B} {s : ∀ y, E (b y)}
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {m : ℕ∞ω} [IsManifold 𝓘(𝕜, X) m M] [ContMDiffVectorBundle m F E I]

/-- Regular zeros of a smooth Fredholm section along a map from a Banach manifold form a smooth
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
      ContinuousLinearMap.IsFredholm (sectionLinearization (F := F) 𝓘(𝕜, X) b s x)) →
    (∀ x, s x = 0 →
      Function.Surjective (sectionLinearization (F := F) 𝓘(𝕜, X) b s x)) →
    (∀ x, s x = 0 →
      LinearMap.index (sectionLinearization (F := F) 𝓘(𝕜, X) b s x).toLinearMap = n) →
    ∃ cs : ChartedSpace (Fin n → 𝕜) ↥{y | s y = 0},
      letI := cs
      IsManifold 𝓘(𝕜, Fin n → 𝕜) m ↥{y | s y = 0} ∧
        Manifold.IsImmersionOfComplement F 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
          (Subtype.val : ↥{y | s y = 0} → M) ∧
        ∀ z : ↥{y | s y = 0},
          (mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) Subtype.val z).range =
            (sectionLinearization (F := F) 𝓘(𝕜, X) b s z.1).ker := by
  let := ContMDiffVectorBundle.of_le (F := F) (E := E) (IB := I)
    (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  intro hs hFred hsurj hindex
  -- Smoothness into the total space supplies smooth coordinates in every relevant chart.
  let e (z : ↥{y | s y = 0}) := trivializationAt F E (b z.1)
  have he (z : ↥{y | s y = 0}) : b z.1 ∈ (e z).baseSet :=
    mem_baseSet_trivializationAt F E (b z.1)
  have hcoord (z w : ↥{y | s y = 0}) (hw : b w.1 ∈ (e z).baseSet) :
      ContMDiffAt 𝓘(𝕜, X) 𝓘(𝕜, F) m (fun y ↦ (e z ⟨b y, s y⟩).2) w.1 :=
    (((e z).contMDiffAt_iff ((e z).mem_source.2 hw)).1 (hs w.1 w.2)).2
  have hb (z : ↥{y | s y = 0}) : ContinuousAt b z.1 :=
    (contMDiffAt_totalSpace_iff.1 (hs z.1 z.2)).1.continuousAt
  have hchart (z w : ↥{y | s y = 0}) (hc : w.1 ∈ (chartAt X z.1).source)
      (hw : b w.1 ∈ (e z).baseSet) :
      ContDiffAt 𝕜 m
        (fun y ↦ (e z ⟨b ((chartAt X z.1).symm y), s ((chartAt X z.1).symm y)⟩).2)
        (chartAt X z.1 w.1) := by
    have hi := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, X)) (n := m) z.1)
      ((chartAt X z.1).map_source hc)
    have h := (hcoord z w hw).comp_of_eq hi ((chartAt X z.1).left_inv hc)
    exact contMDiffAt_iff_contDiffAt.1 h
  let D (z : ↥{y | s y = 0}) := fderiv 𝕜
    (fun y ↦ (e z ⟨b ((chartAt X z.1).symm y), s ((chartAt X z.1).symm y)⟩).2)
    (chartAt X z.1 z.1)
  have hf (z : ↥{y | s y = 0}) : HasStrictFDerivAt
      (fun y ↦ (e z ⟨b ((chartAt X z.1).symm y), s ((chartAt X z.1).symm y)⟩).2)
      (D z) (chartAt X z.1 z.1) :=
    (hchart z z (mem_chart_source X z.1) (he z)).hasStrictFDerivAt_fderiv hm
  have hmd (z : ↥{y | s y = 0}) :
      MDifferentiableAt 𝓘(𝕜, X) 𝓘(𝕜, F) (fun y ↦ (e z ⟨b y, s y⟩).2) z.1 :=
    (hcoord z z (he z)).mdifferentiableAt hm
  -- `mvfderiv` is the derivative in the preferred source chart. For a boundaryless
  -- self model its domain is all of the model space, exactly as in `D`.
  have hD (z : ↥{y | s y = 0}) :
      mvfderiv 𝓘(𝕜, X) (fun y ↦ (e z ⟨b y, s y⟩).2) z.1 = D z := by
    rw [(hmd z).mvfderiv_eq_fderiv_comp_extChartAt_symm]
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_def]
    rfl
  have hF (z : ↥{y | s y = 0}) : ContinuousLinearMap.IsFredholm (D z) := by
    have h := (isFredholm_sectionLinearization_iff (hb z) (he z) (hmd z) z.2).1
      (hFred z.1 z.2)
    rwa [hD] at h
  have hS (z : ↥{y | s y = 0}) : Function.Surjective (D z) := by
    have h := (surjective_sectionLinearization_iff (hb z) (he z) (hmd z) z.2).1
      (hsurj z.1 z.2)
    rwa [hD] at h
  have hN (z : ↥{y | s y = 0}) : ContinuousLinearMap.index (D z) = n := by
    have h := (index_sectionLinearization (hb z) (he z) (hmd z) z.2).symm.trans
      (hindex z.1 z.2)
    have hd := congrArg (fun L : TangentSpace 𝓘(𝕜, X) z.1 →L[𝕜] F ↦
      LinearMap.index L.toLinearMap) (hD z).symm
    rw [ContinuousLinearMap.index_def]
    exact hd.trans h
  have hsmooth : m ≠ 0 → ∀ z w : ↥{y | s y = 0}, w.1 ∈ (chartAt X z.1).source →
      b w.1 ∈ (e z).baseSet →
      chartAt X z.1 w.1 ∈ (hf z).implicitCoordSource
        (LinearMap.range_eq_top.2 (hS z)) (hF z).closedComplemented_ker →
      ContDiffAt 𝕜 m
        (fun y ↦ (e z ⟨b ((chartAt X z.1).symm y), s ((chartAt X z.1).symm y)⟩).2)
        (chartAt X z.1 w.1) := fun _ z w hc hw _ ↦ hchart z w hc hw
  let _ := sectionZeroChartedSpace hf hF hS hN hb he
  let := isManifold_sectionZero hf hF hS hN hb he hsmooth
  refine ⟨sectionZeroChartedSpace hf hF hS hN hb he,
    isManifold_sectionZero hf hF hS hN hb he hsmooth,
    isImmersionOfComplement_coe_sectionZero hf hF hS hN hb he hsmooth, ?_⟩
  -- The inclusion derivative is a kernel inclusion composed with an equivalence.
  intro z
  let K := (D z).kerModelEquiv (hF z).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z) (hS z)).2 (hN z))
  let T : (Fin n → 𝕜) →L[𝕜] X :=
    (D z).ker.subtypeL.comp (K.symm : (Fin n → 𝕜) →L[𝕜] (D z).ker)
  have hmf (z : ↥{y | s y = 0}) :
      HasMFDerivAt 𝓘(𝕜, X) 𝓘(𝕜, F) (fun y ↦ (e z ⟨b y, s y⟩).2) z.1 (D z) := by
    -- The normed target's tangent identification acts as the identity on vectors;
    -- evaluate `hD` to preserve the tangent carriers while identifying the derivative.
    have hd : (D z : TangentSpace 𝓘(𝕜, X) z.1 →L[𝕜]
        TangentSpace 𝓘(𝕜, F) ((e z ⟨b z.1, s z.1⟩).2)) =
        mfderiv 𝓘(𝕜, X) 𝓘(𝕜, F) (fun y ↦ (e z ⟨b y, s y⟩).2) z.1 := by
      ext v
      exact congrArg (fun L : TangentSpace 𝓘(𝕜, X) z.1 →L[𝕜] F ↦ L v) (hD z).symm
    exact (hmd z).hasMFDerivAt.congr_mfderiv hd.symm
  have hrange : T.range = (sectionLinearization (F := F) 𝓘(𝕜, X) b s z.1).ker :=
    range_subtypeL_comp_eq_ker_sectionLinearization (hb z) (he z) (hmf z) z.2 K
  exact (hasMFDerivAt_coe_sectionZero hf hF hS hN hb he z).mfderiv.symm ▸ hrange

/-- A globally smooth section with regular Fredholm zeros of index zero has finitely many
zeros on a compact source. Its actual zero manifold is discrete, rather than merely having
an assumed isolated-zero property. -/
theorem finite_sectionZero_of_contMDiff [CompactSpace M]
    (hm : m ≠ 0)
    (hs : ContMDiff 𝓘(𝕜, X) (I.prod 𝓘(𝕜, F)) m
      (fun y ↦ (⟨b y, s y⟩ : TotalSpace F E)))
    (hFred : ∀ x, s x = 0 →
      ContinuousLinearMap.IsFredholm (sectionLinearization (F := F) 𝓘(𝕜, X) b s x))
    (hsurj : ∀ x, s x = 0 →
      Function.Surjective (sectionLinearization (F := F) 𝓘(𝕜, X) b s x))
    (hindex : ∀ x, s x = 0 →
      LinearMap.index (sectionLinearization (F := F) 𝓘(𝕜, X) b s x).toLinearMap = 0) :
    {x | s x = 0}.Finite := by
  have hclosed : IsClosed {x | s x = 0} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    let e := trivializationAt F E (b x)
    have he : b x ∈ e.baseSet := mem_baseSet_trivializationAt F E (b x)
    have hc := contMDiffAt_totalSpace.mp (hs x)
    have hne : (e ⟨b x, s x⟩).2 ≠ 0 := by
      intro hzero
      apply hx
      apply (e.continuousLinearEquivAt 𝕜 (b x) he).injective
      rw [map_zero]
      simpa only [e.apply_eq_prod_continuousLinearEquivAt 𝕜 (b x) he] using hzero
    have hv : ∀ᶠ y in 𝓝 x, (e ⟨b y, s y⟩).2 ≠ 0 :=
      hc.2.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hne)
    have hb : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
      hc.1.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)
    filter_upwards [hv, hb] with y hy hby
    intro hzero
    apply hy
    rw [hzero]
    exact congrArg Prod.snd (e.zeroSection 𝕜 hby)
  obtain ⟨cs, -, -, -⟩ := exists_isManifold_sectionZero_of_contMDiff hm
    (fun x _ ↦ hs x) hFred hsurj hindex
  let := cs
  let : DiscreteTopology ↥{x | s x = 0} := ChartedSpace.discreteTopology (Fin 0 → 𝕜) _
  let : CompactSpace ↥{x | s x = 0} := isCompact_iff_compactSpace.mp hclosed.isCompact
  let : Finite ↥{x | s x = 0} := finite_of_compact_of_discrete
  exact Set.toFinite _

end TauCeti
