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
import TauCeti.Topology.Maps.LocalSections

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
(`Manifold.IsSubmersionAt.exists_contMDiffOn_section`). These sections can be chosen through every
point `y` near `x` at once, jointly smooth in `y`
(`Manifold.IsSubmersionAt.exists_contMDiffOn_uncurry_section`). Consequently smoothness descends
along a submersion: `g` is `C^m` at `f x` exactly when `g ∘ f` is `C^m` at `x`
(`Manifold.IsSubmersionAt.contMDiffAt_comp_iff`), and along a surjective submersion a `C^m` map
constant on the fibres factors through a unique `C^m` map
(`Manifold.IsSubmersion.existsUnique_contMDiff_comp_eq`).

## Main results

* `Manifold.isSubmersionOfComplement_iff`: a submersion with complement `F` is one at every point.
* `Manifold.IsSubmersion.of_le`, together with its `Manifold.IsSubmersionAt`,
  `Manifold.IsSubmersionOfComplement` and `Manifold.IsSubmersionAtOfComplement` forms: lowering the
  regularity order preserves submersions.
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
  `Manifold.IsSubmersionAt.exists_contMDiffOn_section`,
  `Manifold.IsSubmersion.exists_contMDiffOn_section`, and
  `Manifold.IsSubmersion.exists_contMDiffOn_section_of_surjective`: local sections of a submersion.
* `Manifold.IsSubmersionAtOfComplement.exists_contMDiffOn_uncurry_section`,
  `Manifold.IsSubmersionAt.exists_contMDiffOn_uncurry_section`: local sections through every
  nearby point of the source, depending smoothly on that point.
* `Manifold.IsSubmersion.isOpenMap`: a submersion from a boundaryless manifold is an open map.
* `Manifold.IsSubmersion.finrank_le`: a submersion out of a nonempty manifold does not raise
  dimension.
* `Manifold.IsSubmersionAt.contMDiffAt_comp_iff`, `Manifold.IsSubmersion.contMDiff_comp_iff`,
  `Manifold.IsSubmersionAt.mdifferentiableAt_comp_iff`: smoothness and differentiability descend
  along a submersion.
* `Manifold.IsSubmersion.existsUnique_contMDiff_comp_eq`: smooth maps constant on the fibres of a
  surjective submersion descend to smooth maps.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (local form of a submersion), Theorem 4.26 (local sections of submersions) and
  Theorems 4.29 and 4.30 (characteristic property of surjective submersions, passing smoothly to
  the quotient).
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

section OfLe

variable {m : WithTop ℕ∞}

/-- Lowering the regularity order preserves the submersion normal form at a point, with the same
complement. -/
theorem IsSubmersionAtOfComplement.of_le {x : M}
    (h : IsSubmersionAtOfComplement F I J m f x) (hnm : n ≤ m) :
    IsSubmersionAtOfComplement F I J n f x :=
  IsSubmersionAtOfComplement.mk_of_charts h.equiv h.domChart h.codChart
    h.mem_domChart_source h.mem_codChart_source
    (IsManifold.maximalAtlas_subset_of_le hnm h.domChart_mem_maximalAtlas)
    (IsManifold.maximalAtlas_subset_of_le hnm h.codChart_mem_maximalAtlas)
    h.source_subset_preimage_source h.writtenInCharts

/-- Lowering the regularity order preserves being a submersion at a point. -/
theorem IsSubmersionAt.of_le {x : M}
    (h : IsSubmersionAt I J m f x) (hnm : n ≤ m) :
    IsSubmersionAt I J n f x :=
  (h.isSubmersionAtOfComplement_complement.of_le hnm).isSubmersionAt

/-- Lowering the regularity order preserves submersions with a fixed complement. -/
theorem IsSubmersionOfComplement.of_le
    (h : IsSubmersionOfComplement F I J m f) (hnm : n ≤ m) :
    IsSubmersionOfComplement F I J n f :=
  fun x ↦ (h x).of_le hnm

/-- Lowering the regularity order preserves submersions. -/
theorem IsSubmersion.of_le
    (h : IsSubmersion I J m f) (hnm : n ≤ m) :
    IsSubmersion I J n f :=
  (h.isSubmersionOfComplement_complement.of_le hnm).isSubmersion

end OfLe

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

/-- **A submersion does not raise dimension**: a `C^n` submersion, `n ≠ 0`, out of a nonempty
manifold with finite-dimensional model has target model of dimension at most that of the source
model. -/
theorem IsSubmersion.finrank_le [FiniteDimensional 𝕜 E] [Nonempty M] (h : IsSubmersion I J n f)
    (hn : n ≠ 0) : Module.finrank 𝕜 E'' ≤ Module.finrank 𝕜 E := by
  obtain ⟨x⟩ := ‹Nonempty M›
  exact LinearMap.finrank_le_finrank_of_surjective (f := (mfderiv I J f x).toLinearMap)
    (h.surjective_mfderiv hn x)

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

/-- **Smooth families of local sections of a submersion.** If `f` is a `C^n` submersion at `x` and
the model of `M` has no boundary, there is a family of maps `s y : N → M`, jointly `C^n` in `(y, w)`
on an open neighbourhood `W` of `(x, f x)`, such that `f (s y w) = w` on `W` and `s y (f y) = y`
for `y` near `x`. So each `s y` is a local section of `f` through `y`, depending smoothly on `y`.
In the normal-form charts `φ` and `ψ` it is `s y w = φ⁻¹ (L⁻¹ (ψ w, c y))`, where `c y` is the
second component of `L (φ y)`. -/
theorem IsSubmersionAtOfComplement.exists_contMDiffOn_uncurry_section [I.Boundaryless]
    (h : IsSubmersionAtOfComplement F I J n f x) :
    ∃ W : Set (M × N), IsOpen W ∧ (x, f x) ∈ W ∧ ∃ s : M → N → M,
      ContMDiffOn (I.prod J) I n (uncurry s) W ∧ (∀ p ∈ W, f (s p.1 p.2) = p.2) ∧
      ∀ᶠ y in 𝓝 x, s y (f y) = y := by
  set e := h.domChart.extend I
  set c := h.codChart.extend J
  set S := h.domChart.source ×ˢ h.codChart.source
  -- The affine slice `w ↦ L⁻¹ (w, z)` through `φ y` of the projection `u ↦ (L u).1`.
  set g : M × N → E := fun p ↦ h.equiv.symm (c p.2, (h.equiv (e p.1)).2) with hg_def
  have hg : ContMDiffOn (I.prod J) 𝓘(𝕜, E) n g S :=
    h.equiv.symm.contDiff.contMDiff.comp_contMDiffOn <|
      ((h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas).comp contMDiffOn_snd
        mapsTo_snd_prod).prodMk_space <|
        ((ContinuousLinearMap.snd 𝕜 E'' F).comp (h.equiv : E →L[𝕜] E'' × F)).contMDiff
          |>.comp_contMDiffOn <|
          (h.domChart.contMDiffOn_extend h.domChart_mem_maximalAtlas).comp contMDiffOn_fst
            mapsTo_fst_prod
  have hgy {y : M} (hy : y ∈ h.domChart.source) : g (y, f y) = e y := by
    simp only [hg_def, c, h.codChart_extend_apply hy, projection_apply, Prod.mk.eta,
      ContinuousLinearEquiv.symm_apply_apply, e]
  refine ⟨S ∩ g ⁻¹' e.target, hg.continuousOn.isOpen_inter_preimage
      (h.domChart.open_source.prod h.codChart.open_source) h.domChart.isOpen_extend_target,
    ⟨⟨h.mem_domChart_source, h.mem_codChart_source⟩, ?_⟩, fun y w ↦ e.symm (g (y, w)), ?_, ?_, ?_⟩
  · rw [mem_preimage, hgy h.mem_domChart_source]
    exact e.map_source (by rw [OpenPartialHomeomorph.extend_source]; exact h.mem_domChart_source)
  · exact (contMDiffOn_extend_symm h.domChart_mem_maximalAtlas).comp (hg.mono inter_subset_left)
      fun p hp ↦ by rw [← OpenPartialHomeomorph.extend_target']; exact hp.2
  · rintro p ⟨hp, hpt⟩
    have hsp : e.symm (g p) ∈ h.domChart.source := by
      rw [← h.domChart.extend_source (I := I)]
      exact e.map_target hpt
    refine (h.codChart.extend J).injOn
      (by rw [h.codChart.extend_source]; exact h.source_subset_preimage_source hsp)
      (by rw [h.codChart.extend_source]; exact hp.2) ?_
    rw [h.codChart_extend_apply hsp, e.right_inv hpt, projection_apply]
    simp only [hg_def, ContinuousLinearEquiv.apply_symm_apply, c]
  · filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    rw [hgy hy]
    exact e.left_inv (by rw [OpenPartialHomeomorph.extend_source]; exact hy)

/-- **Local sections of a submersion.** If `f` is a `C^n` submersion at `x` and the model of `M`
has no boundary, then over an open neighbourhood `U` of `f x` there is a `C^n` section of `f`
through `x`: a map `s` with `s (f x) = x`, `f (s y) = y` for `y ∈ U`, and `C^n` on `U`. It is the
member through `x` of the family of
`Manifold.IsSubmersionAtOfComplement.exists_contMDiffOn_uncurry_section`. -/
theorem IsSubmersionAtOfComplement.exists_contMDiffOn_section [I.Boundaryless]
    (h : IsSubmersionAtOfComplement F I J n f x) :
    ∃ U : Set N, IsOpen U ∧ f x ∈ U ∧ ∃ s : N → M, s (f x) = x ∧ ContMDiffOn J I n s U ∧
      ∀ y ∈ U, f (s y) = y := by
  obtain ⟨W, hW, hxW, s, hs, hfs, hsx⟩ := h.exists_contMDiffOn_uncurry_section
  exact ⟨Prod.mk x ⁻¹' W, hW.preimage (Continuous.prodMk_right x), hxW, s x, hsx.self_of_nhds,
    hs.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun _ hw ↦ hw,
    fun w hw ↦ hfs (x, w) hw⟩

/-- **Smooth families of local sections of a submersion.** If `f` is a `C^n` submersion at `x`
and the model of `M` has no boundary, there are local sections `s y` of `f` through every `y` near
`x`, jointly `C^n` in `(y, w)` on an open neighbourhood `W` of `(x, f x)`. -/
theorem IsSubmersionAt.exists_contMDiffOn_uncurry_section [I.Boundaryless]
    (h : IsSubmersionAt I J n f x) :
    ∃ W : Set (M × N), IsOpen W ∧ (x, f x) ∈ W ∧ ∃ s : M → N → M,
      ContMDiffOn (I.prod J) I n (uncurry s) W ∧ (∀ p ∈ W, f (s p.1 p.2) = p.2) ∧
      ∀ᶠ y in 𝓝 x, s y (f y) = y :=
  h.isSubmersionAtOfComplement_complement.exists_contMDiffOn_uncurry_section

/-- **Local sections of a submersion.** If `f` is a `C^n` submersion at `x` and the model of `M`
has no boundary, then over an open neighbourhood `U` of `f x` there is a `C^n` section `s` of `f`
with `s (f x) = x`. -/
theorem IsSubmersionAt.exists_contMDiffOn_section [I.Boundaryless] (h : IsSubmersionAt I J n f x) :
    ∃ U : Set N, IsOpen U ∧ f x ∈ U ∧ ∃ s : N → M, s (f x) = x ∧ ContMDiffOn J I n s U ∧
      ∀ y ∈ U, f (s y) = y :=
  h.isSubmersionAtOfComplement_complement.exists_contMDiffOn_section

/-- **Local sections of a submersion.** If `f` is a `C^n` submersion and the model of `M` has no
boundary, then through every `x : M` there is a `C^n` local section `s` of `f` over an open
neighbourhood `U` of `f x` with `s (f x) = x`. No separation or countability assumption is
needed. -/
theorem IsSubmersion.exists_contMDiffOn_section [I.Boundaryless] (h : IsSubmersion I J n f)
    (x : M) :
    ∃ U : Set N, IsOpen U ∧ f x ∈ U ∧ ∃ s : N → M, s (f x) = x ∧ ContMDiffOn J I n s U ∧
      ∀ y ∈ U, f (s y) = y :=
  (h.isSubmersionAt x).exists_contMDiffOn_section

/-- **Local sections of a surjective submersion.** If `f` is a surjective `C^n` submersion with
boundaryless source, then every `y : N` has an open neighbourhood `U` carrying a `C^n` local
section `s` of `f`. -/
theorem IsSubmersion.exists_contMDiffOn_section_of_surjective [I.Boundaryless]
    (h : IsSubmersion I J n f) (hsurj : Surjective f) (y : N) :
    ∃ U : Set N, IsOpen U ∧ y ∈ U ∧ ∃ s : N → M, ContMDiffOn J I n s U ∧
      ∀ z ∈ U, f (s z) = z := by
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨U, hU, hxU, s, _, hs, hfs⟩ := h.exists_contMDiffOn_section x
  exact ⟨U, hU, hxU, s, hs, hfs⟩

omit [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
/-- **A submersion from a boundaryless manifold is an open map.** Every point has a continuous
local section through it by `exists_contMDiffOn_section`. -/
theorem IsSubmersion.isOpenMap [I.Boundaryless] (h : IsSubmersion I J n f) : IsOpenMap f := by
  refine .of_local_sections fun y ↦ ?_
  obtain ⟨U, hU, hyU, s, hsy, hs, hfs⟩ := h.exists_contMDiffOn_section y
  exact ⟨s, hs.continuousOn.continuousAt (hU.mem_nhds hyU), hsy,
    eventually_of_mem (hU.mem_nhds hyU) hfs⟩

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

/-- **Differentiability descends along a submersion.** If `f` is a `C^n` submersion at `x` with
boundaryless source and `n ≠ 0`, a map `g` is differentiable at `f x` exactly when `g ∘ f` is
differentiable at `x`. Near `f x`, `g` is `g ∘ f` composed with a local section of `f`. -/
theorem IsSubmersionAt.mdifferentiableAt_comp_iff [I.Boundaryless] (h : IsSubmersionAt I J n f x)
    (hn : n ≠ 0) : MDifferentiableAt I K (g ∘ f) x ↔ MDifferentiableAt J K g (f x) := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.comp x (h.contMDiffAt.mdifferentiableAt hn)⟩
  obtain ⟨U, hU, hxU, s, hsx, hs, hfs⟩ := h.exists_contMDiffOn_section
  have hgs : MDifferentiableAt J K ((g ∘ f) ∘ s) (f x) :=
    (hsx ▸ hg).comp (f x) ((hs.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt hn)
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

end Descent

end LocalSection

end Manifold
