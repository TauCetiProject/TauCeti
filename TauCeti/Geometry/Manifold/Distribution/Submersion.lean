/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.Distribution
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The kernel distribution of a submersion

Let `f : M → N` be a `C^n` submersion, `1 ≤ n`, in the sense of Mathlib's
`Manifold.IsSubmersionAt`: around every point `x` there are charts `φ` of `M` and `ψ` of `N` and
a continuous linear equivalence `L : E ≃L[𝕜] E'' × F` in which `f` reads as `u ↦ (L u).1`. This
file differentiates that normal form. On the whole source of `φ`, the derivative of `f` read
through the derivative of `ψ` is `(L (dφ v)).1`
(`Manifold.IsSubmersionAtOfComplement.mfderiv_extend_comp_mfderiv`), so `mfderiv f y` is
surjective and its kernel is the preimage under `dφ` of the fixed subspace `L⁻¹ (0 × F)` of the
model space.

The *kernel distribution* `x ↦ ker (mfderiv f x)` of a submersion is therefore spanned, on the
source of `φ`, by the pullbacks through `φ` of the constant vector fields `L⁻¹ (0, bᵢ)` for a basis
`b` of `F`. These are the submersion-coordinate frames. Pulling back through a `C^n` chart costs
one derivative, so for `m + 1 ≤ n` the kernel distribution of a `C^n` submersion between manifolds
modelled on finite-dimensional spaces `E` and `E''` is a `C^m` distribution of rank
`dim E - dim E''` (`Manifold.IsSubmersion.isContMDiffDistribution_ker_mfderiv`).

No Hausdorff or second-countability hypothesis is used, and the models may have boundary or
corners. For the projection of a fibre bundle the kernel distribution is its vertical
distribution.

## Main results

* `Manifold.IsSubmersionAtOfComplement.mfderiv_extend_comp_mfderiv`: the derivative of a
  submersion in its normal-form charts.
* `Manifold.IsSubmersionAtOfComplement.surjective_mfderiv`,
  `Manifold.IsSubmersionAt.surjective_mfderiv` and `Manifold.IsSubmersion.surjective_mfderiv`: the
  derivative of a submersion is surjective.
* `Manifold.IsSubmersionAtOfComplement.mfderiv_eq_zero_iff`: the kernel of the derivative on the
  source of the normal-form chart.
* `Manifold.IsSubmersionAtOfComplement.isDistributionFrameOn_ker_mfderiv`: the
  submersion-coordinate frame of the kernel distribution.
* `Manifold.IsSubmersion.isContMDiffDistribution_ker_mfderiv`: the kernel distribution of a
  `C^n` submersion is a `C^m` distribution of rank `dim E - dim E''` when `m + 1 ≤ n`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (local form of a submersion) and Chapter 19 (distributions).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer (1993), Lemma 2.2 and §9.3 (the vertical bundle of a submersion).
-/

public section

noncomputable section

open Set Function Filter Module VectorField TauCeti
open scoped Manifold Topology ContDiff

namespace Manifold

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω} {f : M → N} {x : M}

namespace IsSubmersionAtOfComplement

variable (h : IsSubmersionAtOfComplement F I J n f x)

/-- The linear projection `u ↦ (L u).1` that a submersion reads as in its normal-form charts,
where `L` is the linear equivalence `h.equiv : E ≃L[𝕜] E'' × F`. -/
def projection : E →L[𝕜] E'' :=
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

/-- The constant vectors `L⁻¹ (0, bᵢ)` of the model space, for a basis `b` of the complement `F`,
span the kernel of the normal-form projection. -/
private theorem span_range_equiv_symm_inr {ι : Type*} (b : Basis ι 𝕜 F) :
    Submodule.span 𝕜 (range fun i ↦ h.equiv.symm (0, b i)) = h.projection.ker := by
  have hrange : (range fun i ↦ h.equiv.symm (0, b i)) =
      (h.equiv.symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E'' F) '' range b :=
    range_comp (h.equiv.symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E'' F) b
  rw [hrange, Submodule.span_image, b.span_eq, Submodule.map_top]
  ext u
  simp only [LinearMap.mem_range, LinearMap.coe_comp, comp_apply, LinearMap.inr_apply,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe, projection_apply]
  refine ⟨?_, fun hu ↦ ⟨(h.equiv u).2, h.equiv.injective ?_⟩⟩
  · rintro ⟨v, rfl⟩
    simp
  · exact (h.equiv.apply_symm_apply _).trans (Prod.ext hu.symm rfl)

/-- **The submersion-coordinate frame of the kernel distribution.** Let `f` be a `C^n` submersion
at `x`, with normal-form charts `φ`, `ψ` and linear equivalence `L : E ≃L[𝕜] E'' × F`, and let `b`
be a basis of the complement `F`. On the source of `φ`, the pullbacks through `φ` of the constant
vector fields `L⁻¹ (0, bᵢ)` form a `C^m` local frame of the kernel distribution
`y ↦ ker (mfderiv f y)` when `m + 1 ≤ n`. -/
theorem isDistributionFrameOn_ker_mfderiv [CompleteSpace E] [IsManifold I 1 M] {ι : Type*}
    (b : Basis ι 𝕜 F) (hmn : m + 1 ≤ n) :
    IsDistributionFrameOn I m (fun y ↦ (mfderiv I J f y).ker)
      (fun i ↦ mpullback I 𝓘(𝕜, E) (h.domChart.extend I)
        (fun z ↦ (h.equiv.symm (0, b i) : TangentSpace 𝓘(𝕜, E) z)))
      h.domChart.source := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hmn
  refine ⟨fun i y hy ↦ ?_, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩
  · exact ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin (t := univ)
      (contMDiffAt_vectorSpace_iff_contDiffAt.2 contDiffAt_const).contMDiffWithinAt
      (h.domChart.contMDiffAt_extend h.domChart_mem_maximalAtlas hy)
      (h.isInvertible_mfderiv_domChart_extend hn hy) hmn (by simp)
  all_goals
    obtain ⟨e, he⟩ := h.isInvertible_mfderiv_domChart_extend hn hy
    have hinv : (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y).inverse = e.symm := by
      rw [← he, ContinuousLinearMap.inverse_equiv]
    have hX (i : ι) : mpullback I 𝓘(𝕜, E) (h.domChart.extend I)
        (fun z ↦ (h.equiv.symm (0, b i) : TangentSpace 𝓘(𝕜, E) z)) y =
          e.symm (h.equiv.symm (0, b i)) :=
      congrArg (· (h.equiv.symm (0, b i))) hinv
    simp only [hX]
  · have hw : LinearIndependent 𝕜 fun i ↦ h.equiv.symm (0, b i) :=
      b.linearIndependent.map' (h.equiv.symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E'' F)
        (LinearMap.ker_eq_bot.2 (h.equiv.symm.injective.comp LinearMap.inr_injective))
    exact hw.map' e.symm.toLinearMap (LinearMap.ker_eq_bot.2 e.symm.injective)
  · let w : ι → TangentSpace 𝓘(𝕜, E) (h.domChart.extend I y) := fun i ↦ h.equiv.symm (0, b i)
    have hspan : Submodule.span 𝕜 (range fun i ↦ e.symm (w i)) =
        (Submodule.span 𝕜 (range w)).map (e.symm.toLinearEquiv :
          TangentSpace 𝓘(𝕜, E) (h.domChart.extend I y) →ₗ[𝕜] TangentSpace I y) := by
      -- The two sides differ only in the coercion of `e.symm` to a function, through a continuous
      -- linear equivalence or through the underlying linear equivalence.
      rw [Submodule.map_span, ← range_comp]
      rfl
    ext v
    rw [hspan, Submodule.mem_map_equiv, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      h.mfderiv_eq_zero_iff hn hy, ← he]
    exact SetLike.ext_iff.1 (h.span_range_equiv_symm_inr b) (e v)

end IsSubmersionAtOfComplement

/-- **The derivative of a submersion is surjective.** -/
theorem IsSubmersionAt.surjective_mfderiv (h : IsSubmersionAt I J n f x) (hn : n ≠ 0) :
    Surjective (mfderiv I J f x) :=
  h.isSubmersionAtOfComplement_complement.surjective_mfderiv hn

/-- **The derivative of a submersion is surjective** at every point. -/
theorem IsSubmersion.surjective_mfderiv (h : IsSubmersion I J n f) (hn : n ≠ 0) (x : M) :
    Surjective (mfderiv I J f x) :=
  (h.isSubmersionAt x).surjective_mfderiv hn

/-- **The kernel distribution of a submersion.** For a `C^n` submersion `f : M → N` between
manifolds modelled on finite-dimensional spaces `E` and `E''`, the family
`x ↦ ker (mfderiv f x)` is a `C^m` distribution of rank `dim E - dim E''` when `m + 1 ≤ n`. Its
local frames are the submersion-coordinate frames of
`Manifold.IsSubmersionAtOfComplement.isDistributionFrameOn_ker_mfderiv`. -/
theorem IsSubmersion.isContMDiffDistribution_ker_mfderiv [FiniteDimensional 𝕜 E]
    [CompleteSpace E] [FiniteDimensional 𝕜 E''] [IsManifold I 1 M] (hf : IsSubmersion I J n f)
    (hmn : m + 1 ≤ n) :
    IsContMDiffDistribution I m (finrank 𝕜 E - finrank 𝕜 E'')
      (fun x ↦ (mfderiv I J f x).ker) := by
  refine isContMDiffDistribution_iff.2 fun x ↦ ?_
  let h := (hf.isSubmersionAt x).isSubmersionAtOfComplement_complement
  have : FiniteDimensional 𝕜 (hf.isSubmersionAt x).complement :=
    Module.Finite.of_injective (h.equiv.symm.toLinearMap ∘ₗ LinearMap.inr 𝕜 E'' _)
      (h.equiv.symm.injective.comp LinearMap.inr_injective)
  have hrank : finrank 𝕜 (hf.isSubmersionAt x).complement = finrank 𝕜 E - finrank 𝕜 E'' := by
    rw [h.equiv.toLinearEquiv.finrank_eq, Module.finrank_prod, Nat.add_sub_cancel_left]
  exact ⟨h.domChart.source, h.domChart.open_source, h.mem_domChart_source, _,
    h.isDistributionFrameOn_ker_mfderiv ((Module.finBasis 𝕜 _).reindex (finCongr hrank)) hmn⟩

end Manifold
