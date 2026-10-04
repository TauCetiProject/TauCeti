/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Manifold

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
      ContinuousLinearMap.IsFredholm (sectionLinearization (F := F) 𝓘(𝕜, X) b s x)) →
    (∀ x, s x = 0 →
      Function.Surjective (sectionLinearization (F := F) 𝓘(𝕜, X) b s x)) →
    (∀ x, s x = 0 →
      LinearMap.index (sectionLinearization (F := F) 𝓘(𝕜, X) b s x).toLinearMap = n) →
    ∃ cs : ChartedSpace (Fin n → 𝕜) ↥{y | s y = 0},
      letI := cs
      IsManifold 𝓘(𝕜, Fin n → 𝕜) m ↥{y | s y = 0} ∧
        Manifold.IsImmersionOfComplement F 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) m
          (Subtype.val : ↥{y | s y = 0} → X) ∧
        ∀ z : ↥{y | s y = 0},
          (mvfderiv 𝓘(𝕜, Fin n → 𝕜) Subtype.val z).range =
            (sectionLinearization (F := F) 𝓘(𝕜, X) b s z.1).ker := by
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
  have hb (z : ↥{y | s y = 0}) : ContinuousAt b z.1 :=
    (contMDiffAt_totalSpace.1 (hs z.1 z.2)).1.continuousAt
  -- Transport the intrinsic hypotheses to the coordinate derivatives used by the atlas.
  let D (z : ↥{y | s y = 0}) := fderiv 𝕜 (fun y ↦ (e z ⟨b y, s y⟩).2) z.1
  -- The smooth-to-strict-derivative theorem uses the real/complex mean value theorem.
  have hf (z : ↥{y | s y = 0}) :
      HasStrictFDerivAt (fun y ↦ (e z ⟨b y, s y⟩).2) (D z) z.1 :=
    (hcoord z z (he z)).hasStrictFDerivAt hm
  have hmd (z : ↥{y | s y = 0}) :
      MDifferentiableAt 𝓘(𝕜, X) 𝓘(𝕜, F) (fun y ↦ (e z ⟨b y, s y⟩).2) z.1 :=
    ((hcoord z z (he z)).differentiableAt hm).mdifferentiableAt
  -- The coordinate derivative is `D z` read on the tangent space through
  -- `NormedSpace.fromTangentSpace`; Fredholmness, surjectivity, and index transport along it.
  have hD (z : ↥{y | s y = 0}) :
      mvfderiv 𝓘(𝕜, X) (fun y ↦ (e z ⟨b y, s y⟩).2) z.1 =
        (D z).comp (NormedSpace.fromTangentSpace (𝕜 := 𝕜) z.1).toContinuousLinearMap :=
    mvfderiv_eq_fderiv
  have hF (z : ↥{y | s y = 0}) : ContinuousLinearMap.IsFredholm (D z) := by
    have h := (isFredholm_sectionLinearization_iff (hb z) (he z) (hmd z) z.2).1
      (hFred z.1 z.2)
    rwa [hD, ContinuousLinearMap.isFredholm_comp_equiv] at h
  have hS (z : ↥{y | s y = 0}) : Function.Surjective (D z) := by
    have h := (surjective_sectionLinearization_iff (hb z) (he z) (hmd z) z.2).1
      (hsurj z.1 z.2)
    rw [hD, ContinuousLinearMap.coe_comp] at h
    exact h.of_comp
  have hN (z : ↥{y | s y = 0}) : ContinuousLinearMap.index (D z) = n := by
    rw [ContinuousLinearMap.index_def, ← LinearMap.index_comp_equiv (D z).toLinearMap
      (NormedSpace.fromTangentSpace (𝕜 := 𝕜) z.1).toLinearEquiv, ← hindex z.1 z.2,
      index_sectionLinearization (hb z) (he z) (hmd z) z.2, hD,
      ContinuousLinearMap.toLinearMap_comp, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  have hsmooth : m ≠ 0 → ∀ z w : ↥{y | s y = 0}, b w.1 ∈ (e z).baseSet →
      w.1 ∈ (hf z).implicitCoordSource (LinearMap.range_eq_top.2 (hS z))
        (hF z).closedComplemented_ker →
      ContDiffAt 𝕜 m (fun y ↦ (e z ⟨b y, s y⟩).2) w.1 :=
    fun _ z w hw _ ↦ hcoord z w hw
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
  have hrange : T.range = (sectionLinearization (F := F) 𝓘(𝕜, X) b s z.1).ker :=
    range_subtypeL_comp_eq_ker_sectionLinearization (hb z) (he z)
      (hf z).hasFDerivAt.hasMFDerivAt z.2 K
  have hd := (hasMFDerivAt_coe_sectionZero hf hF hS hN hb he z).mfderiv
  have hv : mvfderiv 𝓘(𝕜, Fin n → 𝕜) (Subtype.val : ↥{y | s y = 0} → X) z = T := by
    -- The target is a normed space, so its canonical tangent identification is the identity.
    change mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, X) Subtype.val z = T
    exact hd
  exact hv.symm ▸ hrange

end TauCeti
