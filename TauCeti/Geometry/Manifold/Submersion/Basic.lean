/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
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
(`Manifold.IsSubmersionAt.exists_contMDiffOn_section`). Consequently smoothness descends along a
submersion: `g` is `C^m` at `f x` exactly when `g ∘ f` is `C^m` at `x`
(`Manifold.IsSubmersionAt.contMDiffAt_comp_iff`), and along a surjective submersion a `C^m` map
constant on the fibres factors through a unique `C^m` map
(`Manifold.IsSubmersion.existsUnique_contMDiff_comp_eq`). In particular, any bijection intertwining
two surjective `C^n` submersions from a common boundaryless source is a `C^n` diffeomorphism
(`Manifold.IsSubmersion.diffeomorphOfEquiv`), and two `C^n` manifold structures on the target of a
surjective map making it a `C^n` submersion have the same maximal atlas
(`Manifold.maximalAtlas_eq_of_isSubmersion`).

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
* `Manifold.IsSubmersionAt.contMDiffAt_comp_iff`, `Manifold.IsSubmersion.contMDiff_comp_iff`:
  smoothness descends along a submersion.
* `Manifold.IsSubmersion.existsUnique_contMDiff_comp_eq`: smooth maps constant on the fibres of a
  surjective submersion descend to smooth maps.
* `Manifold.IsSubmersion.diffeomorphOfEquiv`: a bijection intertwining two surjective submersions
  from a boundaryless source is a diffeomorphism.
* `Manifold.maximalAtlas_eq_of_isSubmersion`: two `C^n` manifold structures on the target of a
  surjective submersion have the same maximal atlas.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (local form of a submersion), Theorem 4.26 (local sections of submersions),
  Theorems 4.29 and 4.30 (characteristic property of surjective submersions, passing smoothly to
  the quotient) and Theorem 4.31 (uniqueness of smooth structures on quotients).
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

section Descent

variable {E''' : Type*} [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H''' : Type*}
  [TopologicalSpace H'''] {K : ModelWithCorners 𝕜 E''' H'''} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H''' P] {m : ℕ∞ω} {g : N → P}

/-- **Smoothness descends along a submersion.** If `f` is a `C^n` submersion at `x` with
boundaryless source and `m ≤ n`, a map `g` is `C^m` at `f x` exactly when `g ∘ f` is `C^m` at `x`.
Near `f x`, `g` is `g ∘ f` composed with a local section of `f`. -/
theorem IsSubmersionAt.contMDiffAt_comp_iff [I.Boundaryless] (h : IsSubmersionAt I J n f x)
    (hm : m ≤ n) : ContMDiffAt I K m (g ∘ f) x ↔ ContMDiffAt J K m g (f x) := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.comp x (h.contMDiffAt.of_le hm)⟩
  obtain ⟨U, hU, hxU, s, hsx, hs, hfs⟩ := h.exists_contMDiffOn_section
  have hgs : ContMDiffAt J K m ((g ∘ f) ∘ s) (f x) :=
    (hsx ▸ hg).comp (f x) ((hs.of_le hm).contMDiffAt (hU.mem_nhds hxU))
  exact hgs.congr_of_eventuallyEq <| eventually_of_mem (hU.mem_nhds hxU) fun y hy ↦ by
    rw [comp_apply, comp_apply, hfs y hy]

/-- **Smoothness descends along a surjective submersion.** If `f` is a surjective `C^n` submersion
with boundaryless source and `m ≤ n`, a map `g` is `C^m` exactly when `g ∘ f` is. -/
theorem IsSubmersion.contMDiff_comp_iff [I.Boundaryless] (h : IsSubmersion I J n f)
    (hsurj : Surjective f) (hm : m ≤ n) : ContMDiff I K m (g ∘ f) ↔ ContMDiff J K m g := by
  refine ⟨fun hg y ↦ ?_, fun hg ↦ hg.comp (h.contMDiff.of_le hm)⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact ((h.isSubmersionAt x).contMDiffAt_comp_iff hm).1 (hg x)

/-- **Smooth maps constant on fibres descend along a surjective submersion.** If `f` is a
surjective `C^n` submersion with boundaryless source, `m ≤ n`, and a `C^m` map `g` is constant on
the fibres of `f`, then `g` factors as `g' ∘ f` for a unique map `g'`, and `g'` is `C^m`. -/
theorem IsSubmersion.existsUnique_contMDiff_comp_eq [I.Boundaryless] (h : IsSubmersion I J n f)
    (hsurj : Surjective f) (hm : m ≤ n) {g : M → P} (hg : ContMDiff I K m g)
    (hgf : FactorsThrough g f) : ∃! g' : N → P, ContMDiff J K m g' ∧ g' ∘ f = g := by
  have hcomp : (g ∘ surjInv hsurj) ∘ f = g := funext fun x ↦ hgf (surjInv_eq hsurj (f x))
  refine ⟨g ∘ surjInv hsurj, ⟨(h.contMDiff_comp_iff hsurj hm).1 (by rwa [hcomp]), hcomp⟩,
    fun g' hg' ↦ hsurj.injective_comp_right (hg'.2.trans hcomp.symm)⟩

/-- **Uniqueness of smooth quotients by surjective submersions.** If `f₁ : M → N` and
`f₂ : M → P` are `C^n` submersions from a boundaryless manifold with `f₁` surjective, and
`e : N ≃ P` intertwines them (`e (f₁ x) = f₂ x`), then `e` is a `C^n` diffeomorphism. -/
def IsSubmersion.diffeomorphOfEquiv [I.Boundaryless] {f₁ : M → N} {f₂ : M → P}
    (h₁ : IsSubmersion I J n f₁) (h₂ : IsSubmersion I K n f₂) (hsurj : Surjective f₁)
    (e : N ≃ P) (he : ∀ x, e (f₁ x) = f₂ x) : N ≃ₘ^n⟮J, K⟯ P where
  toEquiv := e
  contMDiff_toFun :=
    (h₁.contMDiff_comp_iff hsurj le_rfl).1 (by
      have hcomp : e ∘ f₁ = f₂ := funext he
      rw [hcomp]
      exact h₂.contMDiff)
  contMDiff_invFun :=
    (h₂.contMDiff_comp_iff (by
      have hcomp : f₂ = e ∘ f₁ := (funext he).symm
      rw [hcomp]
      exact e.surjective.comp hsurj) le_rfl).1 (by
      have hcomp : e.symm ∘ f₂ = f₁ := funext fun x ↦ by
        rw [comp_apply, ← he x, e.symm_apply_apply]
      rw [hcomp]
      exact h₁.contMDiff)

/-- The underlying equivalence of `Manifold.IsSubmersion.diffeomorphOfEquiv` is `e`. -/
@[simp]
theorem IsSubmersion.diffeomorphOfEquiv_toEquiv [I.Boundaryless] {f₁ : M → N} {f₂ : M → P}
    (h₁ : IsSubmersion I J n f₁) (h₂ : IsSubmersion I K n f₂) (hsurj : Surjective f₁)
    (e : N ≃ P) (he : ∀ x, e (f₁ x) = f₂ x) :
    (h₁.diffeomorphOfEquiv h₂ hsurj e he).toEquiv = e :=
  (rfl)

/-- The diffeomorphism `Manifold.IsSubmersion.diffeomorphOfEquiv` evaluates as the underlying
equivalence. -/
@[simp]
theorem IsSubmersion.diffeomorphOfEquiv_apply [I.Boundaryless] {f₁ : M → N} {f₂ : M → P}
    (h₁ : IsSubmersion I J n f₁) (h₂ : IsSubmersion I K n f₂) (hsurj : Surjective f₁)
    (e : N ≃ P) (he : ∀ x, e (f₁ x) = f₂ x) (y : N) :
    h₁.diffeomorphOfEquiv h₂ hsurj e he y = e y :=
  (rfl)

/-- The underlying function of `Manifold.IsSubmersion.diffeomorphOfEquiv` is the underlying
equivalence. -/
theorem IsSubmersion.coe_diffeomorphOfEquiv [I.Boundaryless] {f₁ : M → N} {f₂ : M → P}
    (h₁ : IsSubmersion I J n f₁) (h₂ : IsSubmersion I K n f₂) (hsurj : Surjective f₁)
    (e : N ≃ P) (he : ∀ x, e (f₁ x) = f₂ x) :
    ⇑(h₁.diffeomorphOfEquiv h₂ hsurj e he) = e :=
  (rfl)

/-- The inverse of `Manifold.IsSubmersion.diffeomorphOfEquiv` evaluates as the inverse
equivalence. -/
@[simp]
theorem IsSubmersion.diffeomorphOfEquiv_symm_apply [I.Boundaryless]
    {f₁ : M → N} {f₂ : M → P}
    (h₁ : IsSubmersion I J n f₁) (h₂ : IsSubmersion I K n f₂) (hsurj : Surjective f₁)
    (e : N ≃ P) (he : ∀ x, e (f₁ x) = f₂ x) (z : P) :
    (h₁.diffeomorphOfEquiv h₂ hsurj e he).symm z = e.symm z :=
  (rfl)

/-- The inverse of `Manifold.IsSubmersion.diffeomorphOfEquiv` has the inverse equivalence as its
underlying function. -/
theorem IsSubmersion.coe_diffeomorphOfEquiv_symm [I.Boundaryless] {f₁ : M → N} {f₂ : M → P}
    (h₁ : IsSubmersion I J n f₁) (h₂ : IsSubmersion I K n f₂) (hsurj : Surjective f₁)
    (e : N ≃ P) (he : ∀ x, e (f₁ x) = f₂ x) :
    ⇑(h₁.diffeomorphOfEquiv h₂ hsurj e he).symm = e.symm :=
  (rfl)

end Descent

end LocalSection

section Uniqueness

open Function Set
open scoped Manifold Topology ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N]
  {n : ℕ∞ω} {f : M → N}

/-- **Uniqueness of the smooth structure on the target of a surjective submersion.** Two `C^n`
manifold structures on `N` with the same model `J` for which a surjective map `f : M → N` from a
boundaryless manifold is a `C^n` submersion have the same maximal atlas. -/
theorem maximalAtlas_eq_of_isSubmersion [I.Boundaryless] {c₁ c₂ : ChartedSpace G N}
    (h₁ : letI := c₁; IsManifold J n N) (h₂ : letI := c₂; IsManifold J n N)
    (hf₁ : letI := c₁; IsSubmersion I J n f) (hf₂ : letI := c₂; IsSubmersion I J n f)
    (hsurj : Surjective f) :
    (letI := c₁; IsManifold.maximalAtlas J n N) =
      (letI := c₂; IsManifold.maximalAtlas J n N) := by
  have sub {a b : ChartedSpace G N}
      (ha : letI := a; IsManifold J n N) (hb : letI := b; IsManifold J n N)
      (hfa : letI := a; IsSubmersion I J n f) (hfb : letI := b; IsSubmersion I J n f) :
      (letI := a; IsManifold.maximalAtlas J n N) ⊆
        (letI := b; IsManifold.maximalAtlas J n N) := by
    intro e he
    have ⟨he_to, he_symm⟩ := (letI := a; (IsManifold.mem_maximalAtlas_iff_contMDiffOn e).1 he)
    refine (letI := b; (IsManifold.mem_maximalAtlas_iff_contMDiffOn e).2
      ⟨fun y hy ↦ ?_, fun u hu ↦ ?_⟩)
    · -- Read `e` near `y = f x` as `(e ∘ f) ∘ s` using a local section `s` for `b`.
      obtain ⟨x, rfl⟩ := hsurj y
      have hef : ContMDiffAt I J n (e ∘ f) x := by
        let := a
        exact (he_to.contMDiffAt (e.open_source.mem_nhds hy)).comp x (hfa.contMDiff x)
      let := b
      obtain ⟨U, hU, hfxU, s, hsx, hs, hfs⟩ :=
        (hfb.isSubmersionAt x).exists_contMDiffOn_section
      refine (((hsx ▸ hef).comp (f x) (hs.contMDiffAt (hU.mem_nhds hfxU))).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hU.mem_nhds hfxU) fun z hz ↦ ?_)).contMDiffWithinAt
      rw [comp_apply, comp_apply, hfs z hz]
    · -- Read `e.symm` near `u` as `f ∘ (s ∘ e.symm)` using a local section `s` for `a`.
      obtain ⟨x, hx⟩ := hsurj (e.symm u)
      have hse : ∃ g : G → M, ContMDiffAt J I n g u ∧ g u = x ∧
          (e.symm : G → N) =ᶠ[𝓝 u] f ∘ g := by
        let := a
        obtain ⟨U, hU, hfxU, s, hsx, hs, hfs⟩ :=
          (hfa.isSubmersionAt x).exists_contMDiffOn_section
        rw [hx] at hfxU hsx
        have hcont := (he_symm.contMDiffAt (e.open_target.mem_nhds hu)).continuousAt
        refine ⟨s ∘ e.symm, (hs.contMDiffAt (hU.mem_nhds hfxU)).comp u
          (he_symm.contMDiffAt (e.open_target.mem_nhds hu)), hsx, ?_⟩
        filter_upwards [hcont.preimage_mem_nhds (hU.mem_nhds hfxU)] with v hv
        exact (hfs _ hv).symm
      obtain ⟨g, hg, -, hfg⟩ := hse
      let := b
      exact (((hfb.contMDiff (g u)).comp u hg).congr_of_eventuallyEq hfg).contMDiffWithinAt
  exact Subset.antisymm (sub h₁ h₂ hf₁ hf₂) (sub h₂ h₁ hf₂ hf₁)

end Uniqueness

end Manifold
