/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Manifold

import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Zero manifolds of smooth sections

Over `ℝ` or `ℂ`, a smooth section along a map from a Banach manifold has a smooth zero manifold
whenever its intrinsic linearization is surjective with complemented kernel at its zeros and these
kernels are all isomorphic to a fixed model space. The kernels may be infinite-dimensional, as
for the universal sections of parametric transversality. When the linearization is Fredholm of
constant index `n`, the model is `Fin n → 𝕜`.
This file derives the fiber-coordinate hypotheses of the section-zero atlas from smoothness into
the total space. The inclusion of the zero manifold into the parameter space is a smooth
immersion, with tangent image equal to the kernel of the intrinsic linearization.

Smoothness is needed only at zeros, not everywhere. Surjectivity, complemented kernels,
Fredholmness and the index are stated intrinsically, so callers need not choose a trivialization
or supply derivatives of coordinate expressions. The source is a boundaryless manifold modelled
on a Banach space. As usual, `IsManifold` asserts smooth compatibility of charts, without imposing
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

/-- Regular zeros of a smooth section along a map from a Banach manifold, at which the intrinsic
linearization is surjective with complemented kernel, form a smooth manifold modelled on any space
`Y` isomorphic to all these kernels. The kernels may be infinite-dimensional. The inclusion into
the parameter space is a smooth immersion with complement `F`, and tangent image the intrinsic
linearization's kernel. Only smoothness at zeros is required, at a nonzero differentiability order.

The charted-space structure is supplied as a witness, so it can be installed locally with
`letI`. No chartwise derivative or smoothness hypotheses need to be supplied by the caller. -/
theorem exists_isManifold_sectionZero_of_contMDiff_of_closedComplemented {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (hm : m ≠ 0)
    : letI := ContMDiffVectorBundle.of_le (F := F) (E := E) (IB := I)
        (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    (∀ x, s x = 0 → ContMDiffAt 𝓘(𝕜, X) (I.prod 𝓘(𝕜, F)) m
      (fun y ↦ (⟨b y, s y⟩ : TotalSpace F E)) x) →
    (∀ x, s x = 0 →
      Function.Surjective (sectionLinearization (F := F) 𝓘(𝕜, X) b s x)) →
    (∀ x, s x = 0 →
      (sectionLinearization (F := F) 𝓘(𝕜, X) b s x).ker.ClosedComplemented) →
    (∀ x, s x = 0 →
      Nonempty ((sectionLinearization (F := F) 𝓘(𝕜, X) b s x).ker ≃L[𝕜] Y)) →
    ∃ cs : ChartedSpace Y ↥{y | s y = 0},
      letI := cs
      IsManifold 𝓘(𝕜, Y) m ↥{y | s y = 0} ∧
        Manifold.IsImmersionOfComplement F 𝓘(𝕜, Y) 𝓘(𝕜, X) m
          (Subtype.val : ↥{y | s y = 0} → M) ∧
        ∀ z : ↥{y | s y = 0},
          (mfderiv 𝓘(𝕜, Y) 𝓘(𝕜, X) Subtype.val z).range =
            (sectionLinearization (F := F) 𝓘(𝕜, X) b s z.val).ker := by
  let := ContMDiffVectorBundle.of_le (F := F) (E := E) (IB := I)
    (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  intro hs hsurj hker hY
  -- The proof reads the section in the trivialization at each zero and in the source chart
  -- there, transfers surjectivity, the complemented kernel and its model from the intrinsic
  -- linearization to the derivative `D z` of these coordinates, installs the section-zero
  -- atlas, and identifies the tangent image of the inclusion.
  -- Smoothness into the total space supplies smooth coordinates in every relevant chart.
  let e (z : ↥{y | s y = 0}) := trivializationAt F E (b z.val)
  have he (z : ↥{y | s y = 0}) : b z.val ∈ (e z).baseSet :=
    mem_baseSet_trivializationAt F E (b z.val)
  have hcoord (z w : ↥{y | s y = 0}) (hw : b w.val ∈ (e z).baseSet) :
      ContMDiffAt 𝓘(𝕜, X) 𝓘(𝕜, F) m (fun y ↦ (e z ⟨b y, s y⟩).2) w.val :=
    (((e z).contMDiffAt_iff ((e z).mem_source.2 hw)).1 (hs w.val w.property)).2
  have hb (z : ↥{y | s y = 0}) : ContinuousAt b z.val :=
    (contMDiffAt_totalSpace_iff.1 (hs z.val z.property)).1.continuousAt
  have hchart (z w : ↥{y | s y = 0}) (hc : w.val ∈ (chartAt X z.val).source)
      (hw : b w.val ∈ (e z).baseSet) :
      ContDiffAt 𝕜 m
        (fun y ↦ (e z ⟨b ((chartAt X z.val).symm y), s ((chartAt X z.val).symm y)⟩).2)
        (chartAt X z.val w.val) := by
    have hi := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, X)) (n := m) z.val)
      ((chartAt X z.val).map_source hc)
    have h := (hcoord z w hw).comp_of_eq hi ((chartAt X z.val).left_inv hc)
    exact contMDiffAt_iff_contDiffAt.1 h
  let D (z : ↥{y | s y = 0}) := fderiv 𝕜
    (fun y ↦ (e z ⟨b ((chartAt X z.val).symm y), s ((chartAt X z.val).symm y)⟩).2)
    (chartAt X z.val z.val)
  have hf (z : ↥{y | s y = 0}) : HasStrictFDerivAt
      (fun y ↦ (e z ⟨b ((chartAt X z.val).symm y), s ((chartAt X z.val).symm y)⟩).2)
      (D z) (chartAt X z.val z.val) :=
    (hchart z z (mem_chart_source X z.val) (he z)).hasStrictFDerivAt_fderiv hm
  have hmd (z : ↥{y | s y = 0}) :
      MDifferentiableAt 𝓘(𝕜, X) 𝓘(𝕜, F) (fun y ↦ (e z ⟨b y, s y⟩).2) z.val :=
    (hcoord z z (he z)).mdifferentiableAt hm
  -- `mvfderiv` is the derivative in the preferred source chart. For a boundaryless
  -- self model its domain is all of the model space, exactly as in `D`.
  have hD (z : ↥{y | s y = 0}) :
      mvfderiv 𝓘(𝕜, X) (fun y ↦ (e z ⟨b y, s y⟩).2) z.val = D z := by
    rw [TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm]
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_def]
    rfl
  have hS (z : ↥{y | s y = 0}) : Function.Surjective (D z) := by
    have h := (surjective_sectionLinearization_iff (hb z) (he z) (hmd z) z.property).1
      (hsurj z.val z.property)
    rwa [hD] at h
  -- The coordinate derivative has the same kernel as the intrinsic linearization.
  have hK (z : ↥{y | s y = 0}) : (D z).ker.ClosedComplemented := by
    have h := hker z.val z.property
    rwa [ker_sectionLinearization (hb z) (he z) (hmd z) z.property, hD] at h
  have hKY (z : ↥{y | s y = 0}) : Nonempty ((D z).ker ≃L[𝕜] Y) := by
    have h := hY z.val z.property
    rwa [ker_sectionLinearization (hb z) (he z) (hmd z) z.property, hD] at h
  let K (z : ↥{y | s y = 0}) : (D z).ker ≃L[𝕜] Y := (hKY z).some
  have hsmooth : m ≠ 0 → ∀ z w : ↥{y | s y = 0}, w.val ∈ (chartAt X z.val).source →
      b w.val ∈ (e z).baseSet →
      chartAt X z.val w.val ∈ (hf z).implicitCoordSource
        (LinearMap.range_eq_top.2 (hS z)) (hK z) →
      ContDiffAt 𝕜 m
        (fun y ↦ (e z ⟨b ((chartAt X z.val).symm y), s ((chartAt X z.val).symm y)⟩).2)
        (chartAt X z.val w.val) := fun _ z w hc hw _ ↦ hchart z w hc hw
  let _ := sectionZeroChartedSpace hf hS hK K hb he
  let := isManifold_sectionZero hf hS hK K hb he hsmooth
  refine ⟨sectionZeroChartedSpace hf hS hK K hb he,
    isManifold_sectionZero hf hS hK K hb he hsmooth,
    isImmersionOfComplement_coe_sectionZero hf hS hK K hb he hsmooth, ?_⟩
  -- The inclusion derivative is a kernel inclusion composed with an equivalence.
  intro z
  let T : Y →L[𝕜] X := (D z).ker.subtypeL.comp ((K z).symm : Y →L[𝕜] (D z).ker)
  have hmf (z : ↥{y | s y = 0}) :
      HasMFDerivAt 𝓘(𝕜, X) 𝓘(𝕜, F) (fun y ↦ (e z ⟨b y, s y⟩).2) z.val (D z) := by
    -- The normed target's tangent identification acts as the identity on vectors;
    -- evaluate `hD` to preserve the tangent carriers while identifying the derivative.
    have hd : (D z : TangentSpace 𝓘(𝕜, X) z.val →L[𝕜]
        TangentSpace 𝓘(𝕜, F) ((e z ⟨b z.val, s z.val⟩).2)) =
        mfderiv 𝓘(𝕜, X) 𝓘(𝕜, F) (fun y ↦ (e z ⟨b y, s y⟩).2) z.val := by
      ext v
      exact congrArg (fun L : TangentSpace 𝓘(𝕜, X) z.val →L[𝕜] F ↦ L v) (hD z).symm
    exact (hmd z).hasMFDerivAt.congr_mfderiv hd.symm
  have hrange : T.range = (sectionLinearization (F := F) 𝓘(𝕜, X) b s z.val).ker :=
    range_subtypeL_comp_eq_ker_sectionLinearization (hb z) (he z) (hmf z) z.property (K z)
  exact (hasMFDerivAt_coe_sectionZero hf hS hK K hb he z).mfderiv.symm ▸ hrange

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
            (sectionLinearization (F := F) 𝓘(𝕜, X) b s z.val).ker := by
  intro hs hFred hsurj hindex
  refine exists_isManifold_sectionZero_of_contMDiff_of_closedComplemented hm hs hsurj
    (fun x hx ↦ (hFred x hx).closedComplemented_ker) fun x hx ↦ ?_
  -- A surjective Fredholm map of index `n` has an `n`-dimensional kernel.
  have := (hFred x hx).finite_ker
  have hn : Module.finrank 𝕜 (sectionLinearization (F := F) 𝓘(𝕜, X) b s x).ker = n :=
    (ContinuousLinearMap.finrank_ker_eq_iff_index_eq _ (hsurj x hx)).2
      ((ContinuousLinearMap.index_def _).trans (hindex x hx))
  exact ⟨ContinuousLinearEquiv.ofFinrankEq (by rw [hn, Module.finrank_fin_fun])⟩

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
    have hc := contMDiffAt_totalSpace_iff.mp (hs x)
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
