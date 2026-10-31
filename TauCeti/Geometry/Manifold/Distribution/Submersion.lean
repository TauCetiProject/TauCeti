/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.LinearAlgebra.Basis.RangeSpan

/-!
# The kernel distribution of a submersion

Let `f : M → N` be a `C^n` submersion, `1 ≤ n`, in the sense of Mathlib's
`Manifold.IsSubmersionAt`: around every point `x` there are charts `φ` of `M` and `ψ` of `N` and
a continuous linear equivalence `L : E ≃L[𝕜] E'' × F` in which `f` reads as `u ↦ (L u).1`. On
the whole source of `φ`, the kernel of `mfderiv f y` is the preimage under `dφ` of the fixed
subspace `L⁻¹ (0 × F)` of the model space
(`Manifold.IsSubmersionAtOfComplement.mfderiv_eq_zero_iff`).

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
  have hφ {y : M} (hy : y ∈ h.domChart.source) :
      (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y).IsInvertible :=
    isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le
      (ENat.one_le_iff_ne_zero_withTop.2 hn) h.domChart_mem_maximalAtlas) hy
  refine ⟨fun i y hy ↦ ?_, fun {y} hy ↦ ?_, fun {y} hy ↦ ?_⟩
  · exact ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin (t := univ)
      (contMDiffAt_vectorSpace_iff_contDiffAt.2 contDiffAt_const).contMDiffWithinAt
      (h.domChart.contMDiffAt_extend h.domChart_mem_maximalAtlas hy)
      (hφ hy) hmn (by simp)
  all_goals
    obtain ⟨e, he⟩ := hφ hy
    have hinv : (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y).inverse = e.symm := by
      rw [← he, ContinuousLinearMap.inverse_equiv]
    have hX (i : ι) : mpullback I 𝓘(𝕜, E) (h.domChart.extend I)
        (fun z ↦ (h.equiv.symm (0, b i) : TangentSpace 𝓘(𝕜, E) z)) y =
          e.symm (h.equiv.symm (0, b i)) :=
      mpullback_apply.trans (congrArg (· (h.equiv.symm (0, b i))) hinv)
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
    exact SetLike.ext_iff.1 (b.span_range_symm_inr_eq_ker h.equiv.toLinearEquiv) (e v)

end IsSubmersionAtOfComplement

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
