/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

-- Access the body of `Manifold.IsSubmersionOfComplement`, which Mathlib does not expose, to supply
-- its missing pointwise characterization.
import all Mathlib.Geometry.Manifold.Submersion

/-!
# Submersions: pointwise characterization, derivative and local sections

A map is a submersion with a fixed complement `F` exactly when it is a submersion with
complement `F` at every point (`Manifold.isSubmersionOfComplement_iff`). Mathlib states only the
forward direction, `Manifold.IsSubmersionOfComplement.isSubmersionAt`, and does not expose the
definition, so the converse is needed to build global submersions from pointwise local normal
forms, for instance with `Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt`.
The first projection of a product of manifolds is a submersion, with the second model space
as complement (`Manifold.isSubmersionOfComplement_fst`).

This file also differentiates the normal form of a `C^n` submersion `f : M → N`, `n ≠ 0`: around
every point `x` there are charts `φ` of `M` and `ψ` of `N` and a continuous linear equivalence
`L : E ≃L[𝕜] E'' × F` in which `f` reads as `u ↦ (L u).1`. On the whole source of `φ`, the
derivative of `f` read through the derivative of `ψ` is `(L (dφ v)).1`
(`Manifold.IsSubmersionAtOfComplement.mfderiv_extend_comp_mfderiv`), so `mfderiv f y` is
surjective, it has a continuous right inverse since the projection `u ↦ (L u).1` has one
(`Manifold.IsSubmersionAt.hasRightInverse_mfderiv`; Mathlib lists this as a TODO), and its kernel
is the preimage under `dφ` of the fixed subspace `L⁻¹ (0 × F)` of the model space.

When the model of the source has no boundary, a submersion at `x` has a `C^n` local section through
`x` over an open neighbourhood of `f x`, read off from the normal-form charts
(`Manifold.IsSubmersionAt.exists_contMDiffOn_section`).

## Main results

* `Manifold.isSubmersionOfComplement_iff`: a submersion with complement `F` is one at every point.
* `Manifold.IsSubmersionAtOfComplement.mfderiv_extend_comp_mfderiv`: the derivative of a
  submersion in its normal-form charts.
* `Manifold.IsSubmersionAtOfComplement.surjective_mfderiv`,
  `Manifold.IsSubmersionAt.surjective_mfderiv` and `Manifold.IsSubmersion.surjective_mfderiv`: the
  derivative of a submersion is surjective. Mathlib lists this as a TODO.
* `Manifold.IsSubmersionAtOfComplement.hasRightInverse_mfderiv`,
  `Manifold.IsSubmersionAt.hasRightInverse_mfderiv` and
  `Manifold.IsSubmersion.hasRightInverse_mfderiv`: the derivative of a submersion has a continuous
  right inverse.
* `Manifold.IsSubmersionAtOfComplement.mfderiv_eq_zero_iff`: the kernel of the derivative on the
  source of the normal-form chart.
* `Manifold.IsSubmersionAtOfComplement.exists_contMDiffOn_section`,
  `Manifold.IsSubmersionAt.exists_contMDiffOn_section`: local sections of a submersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (local form of a submersion) and Theorem 4.26 (local sections of submersions).
-/

public section

namespace Manifold

open scoped Manifold

section Pointwise

variable {𝕜 E E' F H G M N : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] {f : M → N}

/-- A map is a submersion with complement `F` exactly when it is a submersion with complement `F`
at every point. -/
theorem isSubmersionOfComplement_iff :
    IsSubmersionOfComplement F I J n f ↔ ∀ x, IsSubmersionAtOfComplement F I J n f x :=
  Iff.rfl

/-- The first projection of a product of manifolds is a submersion, with the second model
space as complement. No nonemptiness assumption on either factor is needed. -/
theorem isSubmersionOfComplement_fst [IsManifold I n M] [IsManifold J n N] :
    IsSubmersionOfComplement E' (I.prod J) I n (@Prod.fst M N) := by
  refine isSubmersionOfComplement_iff.mpr fun p ↦ ?_
  refine .mk_of_continuousAt continuous_fst.continuousAt
    (ContinuousLinearEquiv.refl 𝕜 (E × E')) (chartAt (ModelProd H G) p) (chartAt H p.1)
    (mem_chart_source _ p) (mem_chart_source _ p.1) (IsManifold.chart_mem_maximalAtlas p)
    (IsManifold.chart_mem_maximalAtlas p.1) ?_
  intro y hy
  rw [← extChartAt, ← extChartAt] at *
  rw [extChartAt_prod] at hy ⊢
  exact (extChartAt I p.1).right_inv hy.1

/-- The first projection of a product of manifolds is a submersion. -/
theorem isSubmersion_fst [IsManifold I n M] [IsManifold J n N] :
    IsSubmersion (I.prod J) I n (@Prod.fst M N) :=
  isSubmersionOfComplement_fst.isSubmersion

end Pointwise

section Derivative

open Function Filter
open scoped Manifold Topology ContDiff

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

namespace IsSubmersionAtOfComplement

variable (h : IsSubmersionAtOfComplement F I J n f x)

/-- The linear projection `u ↦ (L u).1` that a submersion reads as in its normal-form charts,
where `L` is the linear equivalence `h.equiv : E ≃L[𝕜] E'' × F`. -/
noncomputable def projection : E →L[𝕜] E'' :=
  (ContinuousLinearMap.fst 𝕜 E'' F).comp (h.equiv : E →L[𝕜] E'' × F)

/-- The normal-form projection of a submersion is the first component of `h.equiv`. -/
@[simp]
theorem projection_apply (u : E) : h.projection u = (h.equiv u).1 := (rfl)

/-- On the source of its domain chart `φ`, a submersion reads as `y ↦ (L (φ y)).1` through its
codomain chart `ψ`, where `φ` and `ψ` are taken extended. -/
theorem codChart_extend_apply {y : M} (hy : y ∈ h.domChart.source) :
    h.codChart.extend J (f y) = h.projection (h.domChart.extend I y) := by
  have hy' : y ∈ (h.domChart.extend I).source := by rwa [OpenPartialHomeomorph.extend_source]
  have := h.writtenInCharts ((h.domChart.extend I).map_source hy')
  simpa only [comp_apply, (h.domChart.extend I).left_inv hy', projection_apply] using this

private theorem isInvertible_mfderiv_codChart_extend (hn : n ≠ 0) {y : M}
    (hy : y ∈ h.domChart.source) :
    (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y)).IsInvertible :=
  isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le
    (ENat.one_le_iff_ne_zero_withTop.2 hn) h.codChart_mem_maximalAtlas)
    (h.source_subset_preimage_source hy)

private theorem isInvertible_mfderiv_domChart_extend (hn : n ≠ 0) {y : M}
    (hy : y ∈ h.domChart.source) :
    (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y).IsInvertible :=
  isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le
    (ENat.one_le_iff_ne_zero_withTop.2 hn) h.domChart_mem_maximalAtlas) hy

/-- **The derivative of a submersion in its normal-form charts.** On the source of the domain
chart `φ`, the derivative of `f` followed by the derivative of the codomain chart `ψ` is the
derivative of `φ` followed by the projection `u ↦ (L u).1`. -/
theorem mfderiv_extend_comp_mfderiv (hn : n ≠ 0) {y : M} (hy : y ∈ h.domChart.source) :
    (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y)).comp (mfderiv I J f y) =
      h.projection.comp (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y) := by
  have hfy : f y ∈ h.codChart.source := h.source_subset_preimage_source hy
  have hψ : MDifferentiableAt J 𝓘(𝕜, E'') (h.codChart.extend J) (f y) :=
    (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas hfy).mdifferentiableAt hn
  have hφ : MDifferentiableAt I 𝓘(𝕜, E) (h.domChart.extend I) y :=
    (h.domChart.contMDiffAt_extend h.domChart_mem_maximalAtlas hy).mdifferentiableAt hn
  have hf : MDifferentiableAt I J f y :=
    ((h.contMDiffOn y hy).contMDiffAt (h.domChart.open_source.mem_nhds hy)).mdifferentiableAt hn
  have heq : h.codChart.extend J ∘ f =ᶠ[𝓝 y] h.projection ∘ h.domChart.extend I :=
    eventually_of_mem (h.domChart.open_source.mem_nhds hy) fun z hz ↦ h.codChart_extend_apply hz
  exact hasMFDerivAt_unique (hψ.hasMFDerivAt.comp y hf.hasMFDerivAt)
    ((h.projection.hasMFDerivAt.comp y hφ.hasMFDerivAt).congr_of_eventuallyEq_abuse heq)

/-- The derivative of a submersion at any point of the source of its domain chart is
surjective. -/
theorem surjective_mfderiv_of_mem (hn : n ≠ 0) {y : M} (hy : y ∈ h.domChart.source) :
    Surjective (mfderiv I J f y) := by
  refine (Surjective.of_comp_iff' (h.isInvertible_mfderiv_codChart_extend hn hy).bijective _).1 ?_
  have hcomp := congrArg DFunLike.coe (h.mfderiv_extend_comp_mfderiv hn hy)
  simp only [ContinuousLinearMap.coe_comp] at hcomp
  rw [hcomp]
  exact Prod.fst_surjective.comp
    (h.equiv.surjective.comp (h.isInvertible_mfderiv_domChart_extend hn hy).surjective)

include h in
/-- **The derivative of a submersion is surjective.** -/
theorem surjective_mfderiv (hn : n ≠ 0) : Surjective (mfderiv I J f x) :=
  h.surjective_mfderiv_of_mem hn h.mem_domChart_source

/-- At any point of the source of the domain chart `φ`, the derivative of a submersion has a
continuous right inverse: read through the invertible derivatives of the charts it is the
projection `u ↦ (L u).1`, which has one. -/
theorem hasRightInverse_mfderiv_of_mem (hn : n ≠ 0) {y : M} (hy : y ∈ h.domChart.source) :
    (mfderiv I J f y).HasRightInverse := by
  obtain ⟨e, he⟩ := h.isInvertible_mfderiv_codChart_extend hn hy
  have hP : (h.projection.comp (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y)).HasRightInverse :=
    (ContinuousLinearMap.HasRightInverse.fst.comp h.equiv.hasRightInverse).comp
      (.of_isInvertible (h.isInvertible_mfderiv_domChart_extend hn hy))
  rw [← h.mfderiv_extend_comp_mfderiv hn hy, ← he] at hP
  -- Undo the invertible derivative `e` of the codomain chart.
  refine hP.continuousLinearEquivalence_comp (g := e.symm) |>.congr ?_
  ext v
  exact (e.symm_apply_apply _).symm

include h in
/-- **The derivative of a submersion has a continuous right inverse.** -/
theorem hasRightInverse_mfderiv (hn : n ≠ 0) : (mfderiv I J f x).HasRightInverse :=
  h.hasRightInverse_mfderiv_of_mem hn h.mem_domChart_source

/-- On the source of the domain chart `φ` of a submersion, a tangent vector `v` lies in the
kernel of the derivative of `f` exactly when its image `dφ v` in the model space lies in
`L⁻¹ (0 × F)`. -/
theorem mfderiv_eq_zero_iff (hn : n ≠ 0) {y : M} (hy : y ∈ h.domChart.source)
    (v : TangentSpace I y) :
    mfderiv I J f y v = 0 ↔ (h.equiv (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y v)).1 = 0 := by
  have hv : mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y) (mfderiv I J f y v) =
      h.projection (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y v) :=
    congrArg (· v) (h.mfderiv_extend_comp_mfderiv hn hy)
  rw [← (h.isInvertible_mfderiv_codChart_extend hn hy).injective.eq_iff, map_zero, hv]
  exact iff_of_eq (congrArg (· = 0) (h.projection_apply _))

end IsSubmersionAtOfComplement

/-- **The derivative of a submersion is surjective.** -/
theorem IsSubmersionAt.surjective_mfderiv (h : IsSubmersionAt I J n f x) (hn : n ≠ 0) :
    Surjective (mfderiv I J f x) :=
  h.isSubmersionAtOfComplement_complement.surjective_mfderiv hn

/-- **The derivative of a submersion is surjective** at every point. -/
theorem IsSubmersion.surjective_mfderiv (h : IsSubmersion I J n f) (hn : n ≠ 0) (x : M) :
    Surjective (mfderiv I J f x) :=
  (h.isSubmersionAt x).surjective_mfderiv hn

/-- **The derivative of a submersion has a continuous right inverse.** -/
theorem IsSubmersionAt.hasRightInverse_mfderiv (h : IsSubmersionAt I J n f x) (hn : n ≠ 0) :
    (mfderiv I J f x).HasRightInverse :=
  h.isSubmersionAtOfComplement_complement.hasRightInverse_mfderiv hn

/-- **The derivative of a submersion has a continuous right inverse** at every point. -/
theorem IsSubmersion.hasRightInverse_mfderiv (h : IsSubmersion I J n f) (hn : n ≠ 0) (x : M) :
    (mfderiv I J f x).HasRightInverse :=
  (h.isSubmersionAt x).hasRightInverse_mfderiv hn

end Derivative

section LocalSection

open Function Filter Set
open scoped Manifold Topology ContDiff

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

/-- **Local sections of a submersion.** If `f` is a `C^n` submersion at `x` and the model of `M`
has no boundary, then over an open neighbourhood `U` of `f x` there is a `C^n` section of `f`
through `x`: a map `s` with `s (f x) = x`, `f (s y) = y` for `y ∈ U`, and `C^n` on `U`. In the
normal-form charts `φ` and `ψ` it is `y ↦ φ⁻¹ (L⁻¹ (ψ y, c))`, where `c` is the second component
of `L (φ x)`. -/
theorem IsSubmersionAtOfComplement.exists_contMDiffOn_section [I.Boundaryless]
    (h : IsSubmersionAtOfComplement F I J n f x) :
    ∃ U : Set N, IsOpen U ∧ f x ∈ U ∧ ∃ s : N → M, s (f x) = x ∧ ContMDiffOn J I n s U ∧
      ∀ y ∈ U, f (s y) = y := by
  set e := h.domChart.extend I
  set c := h.codChart.extend J
  -- The affine slice `w ↦ L⁻¹ (w, z)` through `φ x` of the projection `u ↦ (L u).1`.
  set g : E'' → E := fun w ↦ h.equiv.symm (w, (h.equiv (e x)).2) with hg_def
  have hg : ContDiff 𝕜 n g :=
    h.equiv.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hxe : x ∈ e.source := by
    rw [OpenPartialHomeomorph.extend_source]
    exact h.mem_domChart_source
  have hgc : g (c (f x)) = e x := by
    simp only [hg_def, c, h.codChart_extend_apply h.mem_domChart_source, projection_apply,
      Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, e]
  refine ⟨h.codChart.source ∩ c ⁻¹' (g ⁻¹' e.target),
    h.codChart.isOpen_extend_preimage (h.domChart.isOpen_extend_target.preimage hg.continuous),
    ⟨h.mem_codChart_source, ?_⟩, e.symm ∘ g ∘ c, ?_, ?_, ?_⟩
  · rw [mem_preimage, mem_preimage, hgc]
    exact e.map_source hxe
  · rw [comp_apply, comp_apply, hgc]
    exact e.left_inv hxe
  · refine (contMDiffOn_extend_symm h.domChart_mem_maximalAtlas).comp
      (hg.contMDiff.comp_contMDiffOn
        ((h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas).mono inter_subset_left))
      fun y hy ↦ ?_
    rw [← OpenPartialHomeomorph.extend_target']
    exact hy.2
  · rintro y ⟨hy, hyt⟩
    have hsy : e.symm (g (c y)) ∈ h.domChart.source := by
      rw [← h.domChart.extend_source (I := I)]
      exact e.map_target hyt
    refine (h.codChart.extend J).injOn
      (by rw [h.codChart.extend_source]; exact h.source_subset_preimage_source hsy)
      (by rwa [h.codChart.extend_source]) ?_
    rw [comp_apply, comp_apply, h.codChart_extend_apply hsy, e.right_inv hyt, projection_apply]
    simp only [hg_def, ContinuousLinearEquiv.apply_symm_apply, c]

/-- **Local sections of a submersion.** If `f` is a `C^n` submersion at `x` and the model of `M`
has no boundary, then over an open neighbourhood `U` of `f x` there is a `C^n` section `s` of `f`
with `s (f x) = x`. -/
theorem IsSubmersionAt.exists_contMDiffOn_section [I.Boundaryless] (h : IsSubmersionAt I J n f x) :
    ∃ U : Set N, IsOpen U ∧ f x ∈ U ∧ ∃ s : N → M, s (f x) = x ∧ ContMDiffOn J I n s U ∧
      ∀ y ∈ U, f (s y) = y :=
  h.isSubmersionAtOfComplement_complement.exists_contMDiffOn_section

end LocalSection

end Manifold
