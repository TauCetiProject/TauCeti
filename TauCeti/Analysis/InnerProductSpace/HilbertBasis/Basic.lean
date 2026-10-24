/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hilbert bases

This file transfers orthogonality to every vector of a subspace from orthogonality to each
element of a Hilbert basis of that subspace.  In particular, this lets Hilbert bases of mutually
orthogonal eigenspaces be assembled into a spectral basis of the ambient space.

It also records that a continuous linear map vanishing on all but finitely many vectors of a
Hilbert basis has finite rank, since every vector is the sum of its basis expansion.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A vector orthogonal to every member of a Hilbert basis of a subspace is orthogonal to every
vector of the represented subspace. -/
theorem _root_.HilbertBasis.inner_eq_zero_of_forall_inner_eq_zero {K : Submodule 𝕜 E}
    {iota : Type*} (bK : _root_.HilbertBasis iota 𝕜 K) {x : E}
    (hx : ∀ i, ⟪x, (bK i : E)⟫_𝕜 = 0) {y : E} (hy : y ∈ K) : ⟪x, y⟫_𝕜 = 0 := by
  have hsum := ((innerSL 𝕜 x).comp K.subtypeL).hasSum (bK.hasSum_repr ⟨y, hy⟩)
  have hzero : HasSum (fun _ : iota => (0 : 𝕜)) ⟪x, y⟫_𝕜 := by
    simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.subtype_apply,
      innerSL_apply_apply, map_smul, hx, smul_zero] using hsum
  exact hzero.unique hasSum_zero

/-- A continuous linear map that vanishes on every vector of a Hilbert basis outside a finite set
of indices has finite rank: its range is spanned by the images of the remaining basis vectors. -/
theorem _root_.HilbertBasis.hasFiniteRange_of_apply_eq_zero {iota F : Type*}
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [T2Space F]
    (b : _root_.HilbertBasis iota 𝕜 E) (T : E →L[𝕜] F) (s : Finset iota)
    (hT : ∀ i ∉ s, T (b i) = 0) :
    (T : E →ₗ[𝕜] F).HasFiniteRange := by
  suffices h : (T : E →ₗ[𝕜] F).range = Submodule.span 𝕜 ((fun i ↦ T (b i)) '' s) by
    rw [LinearMap.hasFiniteRange_iff_range, h]
    exact Submodule.fg_span (s.finite_toSet.image _)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hsum := T.hasSum (b.hasSum_repr x)
    rw [ContinuousLinearMap.coe_coe, hsum.unique (hasSum_sum_of_ne_finset_zero fun i hi ↦ by
      rw [map_smul, hT i hi, smul_zero])]
    exact Submodule.sum_mem _ fun i hi ↦ by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact ⟨b i, rfl⟩

end TauCeti
