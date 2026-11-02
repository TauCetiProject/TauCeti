/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
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

This file also differentiates the normal form of a `C^n` submersion `f : M → N`, `n ≠ 0`: around
every point `x` there are charts `φ` of `M` and `ψ` of `N` and a continuous linear equivalence
`L : E ≃L[𝕜] E'' × F` in which `f` reads as `u ↦ (L u).1`. On the whole source of `φ`, the
derivative of `f` read through the derivative of `ψ` is `(L (dφ v)).1`
(`Manifold.IsSubmersionAtOfComplement.mfderiv_extend_comp_mfderiv`), so `mfderiv f y` is
surjective and its kernel is the preimage under `dφ` of the fixed subspace `L⁻¹ (0 × F)` of the
model space.

The same normal form gives right inverses. At every point the derivative of a submersion has a
continuous linear right inverse
(`Manifold.IsSubmersionAtOfComplement.exists_rightInverse_mfderiv`), and when the model of the
source has no boundary the map `y ↦ φ⁻¹ (L⁻¹ (ψ y, v₀))` is a `C^n` local section of `f` through
`x`, defined on an open neighbourhood of `f x`
(`Manifold.IsSubmersionAtOfComplement.exists_localSection`). Local sections are what let
objects defined on the source descend along a surjective submersion.

## Main results

* `Manifold.isSubmersionOfComplement_iff`: a submersion with complement `F` is one at every point.
* `Manifold.IsSubmersionAtOfComplement.mfderiv_extend_comp_mfderiv`: the derivative of a
  submersion in its normal-form charts.
* `Manifold.IsSubmersionAtOfComplement.surjective_mfderiv`,
  `Manifold.IsSubmersionAt.surjective_mfderiv` and `Manifold.IsSubmersion.surjective_mfderiv`: the
  derivative of a submersion is surjective. Mathlib lists this as a TODO.
* `Manifold.IsSubmersionAtOfComplement.mfderiv_eq_zero_iff`: the kernel of the derivative on the
  source of the normal-form chart.
* `Manifold.IsSubmersionAt.exists_rightInverse_mfderiv`: the derivative of a submersion has a
  continuous linear right inverse.
* `Manifold.IsSubmersionAt.exists_localSection`: a submersion out of a manifold without boundary
  has smooth local sections.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorems 4.12 (local form of a submersion) and 4.26 (local sections of submersions).
-/

public section

namespace Manifold

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

end Pointwise

section Derivative

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

include h in
/-- **The derivative of a submersion has a continuous linear right inverse.** In the normal-form
charts `φ` and `ψ` it is `w ↦ (dφ)⁻¹ (L⁻¹ (dψ w, 0))`. No boundarylessness is needed. -/
theorem exists_rightInverse_mfderiv (hn : n ≠ 0) :
    ∃ R : TangentSpace J (f x) →L[𝕜] TangentSpace I x,
      RightInverse R (mfderiv I J f x) := by
  have hx := h.mem_domChart_source
  have hψ := h.isInvertible_mfderiv_codChart_extend hn hx
  have hφ := h.isInvertible_mfderiv_domChart_extend hn hx
  refine ⟨(mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) x).inverse ∘L
    (h.equiv.symm : E'' × F →L[𝕜] E) ∘L ContinuousLinearMap.inl 𝕜 E'' F ∘L
      mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f x), fun w ↦ hψ.injective ?_⟩
  -- Read through `dψ`, the derivative of `f` is the projection of the normal form after `dφ`.
  exact (ContinuousLinearMap.ext_iff.mp (h.mfderiv_extend_comp_mfderiv hn hx) _).trans
    ((congrArg h.projection (hφ.self_apply_inverse _)).trans
      (congrArg Prod.fst (h.equiv.apply_symm_apply _)))

include h in
/-- **Local sections of a submersion** (Lee, Theorem 4.26). If `f` is a `C^n` submersion at `x`
and the model of `M` has no boundary, there is a map `s`, `C^n` on an open neighbourhood `U` of
`f x`, with `s (f x) = x` and `f (s y) = y` for `y ∈ U`. In the normal-form charts `φ` and `ψ` it
is `y ↦ φ⁻¹ (L⁻¹ (ψ y, v₀))`, where `v₀` is the second normal-form coordinate of `x`. -/
theorem exists_localSection [I.Boundaryless] :
    ∃ (s : N → M) (U : Set N), IsOpen U ∧ f x ∈ U ∧ s (f x) = x ∧ ContMDiffOn J I n s U ∧
      EqOn (f ∘ s) id U := by
  -- The normal-form inclusion `u ↦ L⁻¹ (u, v₀)` of the model of `N` into the model of `M`.
  obtain ⟨g, hg⟩ : ∃ g : E'' → E,
      g = fun u ↦ h.equiv.symm (u, (h.equiv (h.domChart.extend I x)).2) := ⟨_, rfl⟩
  have hgc : ContDiff 𝕜 n g := hg ▸ h.equiv.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hx := h.mem_domChart_source
  -- The normal form sends `f x` back to `x`.
  have hgψ : g (h.codChart.extend J (f x)) = h.domChart.extend I x := by
    rw [hg, h.codChart_extend_apply hx, projection_apply]
    exact h.equiv.symm_apply_apply _
  have hsy {y : N} (hy : g (h.codChart.extend J y) ∈ (h.domChart.extend I).target) :
      (h.domChart.extend I).symm (g (h.codChart.extend J y)) ∈ h.domChart.source :=
    h.domChart.extend_source (I := I) ▸ (h.domChart.extend I).map_target hy
  refine ⟨(h.domChart.extend I).symm ∘ g ∘ h.codChart.extend J,
    h.codChart.source ∩ h.codChart.extend J ⁻¹' (g ⁻¹' (h.domChart.extend I).target),
    ?_, ⟨h.mem_codChart_source, ?_⟩, ?_, ?_, fun y hy ↦ ?_⟩
  · exact (h.codChart.extend_source (I := J) ▸ h.codChart.continuousOn_extend).isOpen_inter_preimage
      h.codChart.open_source (h.domChart.isOpen_extend_target.preimage hgc.continuous)
  · rw [mem_preimage, mem_preimage, hgψ]
    exact (h.domChart.extend I).map_source (h.domChart.extend_source (I := I) ▸ hx)
  · rw [comp_apply, comp_apply, hgψ]
    exact h.domChart.extend_left_inv hx
  · refine (contMDiffOn_extend_symm h.domChart_mem_maximalAtlas).comp
      (hgc.contMDiff.comp_contMDiffOn ((h.codChart.contMDiffOn_extend
        h.codChart_mem_maximalAtlas).mono inter_subset_left)) fun y hy ↦ ?_
    rw [mem_preimage, ← h.domChart.extend_target']
    exact hy.2
  -- Read through `ψ`, the map `f` sends the section point to `(L (L⁻¹ (ψ y, v₀))).1 = ψ y`.
  have hinj := (h.codChart.extend J).injOn
  rw [h.codChart.extend_source] at hinj
  refine hinj (h.source_subset_preimage_source (hsy hy.2)) hy.1
    ((h.codChart_extend_apply (hsy hy.2)).trans ?_)
  rw [projection_apply, (h.domChart.extend I).right_inv hy.2, hg]
  exact congrArg Prod.fst (h.equiv.apply_symm_apply _)

end IsSubmersionAtOfComplement

/-- **The derivative of a submersion has a continuous linear right inverse.** -/
theorem IsSubmersionAt.exists_rightInverse_mfderiv (h : IsSubmersionAt I J n f x) (hn : n ≠ 0) :
    ∃ R : TangentSpace J (f x) →L[𝕜] TangentSpace I x, RightInverse R (mfderiv I J f x) :=
  h.isSubmersionAtOfComplement_complement.exists_rightInverse_mfderiv hn

/-- **Local sections of a submersion** (Lee, Theorem 4.26). A `C^n` submersion at `x` out of a
manifold whose model has no boundary has a `C^n` local section through `x`, defined on an open
neighbourhood of `f x`. -/
theorem IsSubmersionAt.exists_localSection [I.Boundaryless] (h : IsSubmersionAt I J n f x) :
    ∃ (s : N → M) (U : Set N), IsOpen U ∧ f x ∈ U ∧ s (f x) = x ∧ ContMDiffOn J I n s U ∧
      EqOn (f ∘ s) id U :=
  h.isSubmersionAtOfComplement_complement.exists_localSection

/-- **The derivative of a submersion is surjective.** -/
theorem IsSubmersionAt.surjective_mfderiv (h : IsSubmersionAt I J n f x) (hn : n ≠ 0) :
    Surjective (mfderiv I J f x) :=
  h.isSubmersionAtOfComplement_complement.surjective_mfderiv hn

/-- **The derivative of a submersion is surjective** at every point. -/
theorem IsSubmersion.surjective_mfderiv (h : IsSubmersion I J n f) (hn : n ≠ 0) (x : M) :
    Surjective (mfderiv I J f x) :=
  (h.isSubmersionAt x).surjective_mfderiv hn

end Derivative

end Manifold
