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

A space with a Hilbert basis is complete (`HilbertBasis.completeSpace`), and is finite-dimensional
iff the index type of the basis is finite (`HilbertBasis.finite_iff`, `HilbertBasis.infinite_iff`).
A Hilbert basis can be reindexed along any equivalence of index types (`HilbertBasis.reindex`).

It also expands the value of a continuous linear map in a Hilbert basis,
`T x = ∑ᵢ ⟪bᵢ, x⟫ T bᵢ` (`HilbertBasis.hasSum_inner_smul_apply`). It records that a continuous
linear map vanishing on all but finitely many vectors of a Hilbert basis has finite rank, since
every vector is the sum of its basis expansion, and that a continuous linear map is determined by
its matrix entries in Hilbert bases of its source and target (`HilbertBasis.ext_inner_apply`).
-/

public section

namespace HilbertBasis

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A space with a Hilbert basis is complete, being isometric to `ℓ²`. -/
theorem completeSpace {iota : Type*} (b : _root_.HilbertBasis iota 𝕜 E) : CompleteSpace E :=
  b.repr.toIsometryEquiv.completeSpace

/-- A space with a finite Hilbert basis is finite-dimensional. -/
theorem finiteDimensional {ι : Type*} [Finite ι] (b : _root_.HilbertBasis ι 𝕜 E) :
    FiniteDimensional 𝕜 E := by
  let _ := Fintype.ofFinite ι
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- For a Hilbert basis `b : HilbertBasis ι 𝕜 E`, the index type `ι` is finite iff `E` is
finite-dimensional. -/
theorem finite_iff {ι : Type*} (b : _root_.HilbertBasis ι 𝕜 E) :
    Finite ι ↔ FiniteDimensional 𝕜 E :=
  ⟨fun _ ↦ b.finiteDimensional, fun _ ↦ b.orthonormal.linearIndependent.finite⟩

/-- For a Hilbert basis `b : HilbertBasis ι 𝕜 E`, the index type `ι` is infinite iff `E` is
infinite-dimensional. -/
theorem infinite_iff {ι : Type*} (b : _root_.HilbertBasis ι 𝕜 E) :
    Infinite ι ↔ ¬ FiniteDimensional 𝕜 E := by
  rw [← not_finite_iff_infinite, b.finite_iff]

/-- Reindex a Hilbert basis along an equivalence of index types. -/
protected noncomputable def reindex {ι ι' : Type*} (b : _root_.HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    _root_.HilbertBasis ι' 𝕜 E :=
  letI := b.completeSpace
  _root_.HilbertBasis.mk (b.orthonormal.comp _ e.symm.injective) (by simp [b.dense_span])

@[simp]
theorem coe_reindex {ι ι' : Type*} (b : _root_.HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = b ∘ e.symm := by
  let := b.completeSpace
  exact _root_.HilbertBasis.coe_mk _ _

@[simp]
theorem reindex_apply {ι ι' : Type*} (b : _root_.HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    b.reindex e i' = b (e.symm i') :=
  congr_fun (b.coe_reindex e) i'

@[simp]
theorem repr_reindex_apply {ι ι' : Type*} (b : _root_.HilbertBasis ι 𝕜 E) (e : ι ≃ ι') (x : E)
    (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') := by
  rw [_root_.HilbertBasis.repr_apply_apply, _root_.HilbertBasis.repr_apply_apply, reindex_apply]

@[simp]
theorem reindex_refl {ι : Type*} (b : _root_.HilbertBasis ι 𝕜 E) :
    b.reindex (Equiv.refl ι) = b :=
  DFunLike.ext _ _ fun _ ↦ by simp

@[simp]
theorem reindex_reindex {ι ι' ι'' : Type*} (b : _root_.HilbertBasis ι 𝕜 E) (e : ι ≃ ι')
    (f : ι' ≃ ι'') : (b.reindex e).reindex f = b.reindex (e.trans f) :=
  DFunLike.ext _ _ fun _ ↦ by simp

theorem reindex_reindex_symm {ι ι' : Type*} (b : _root_.HilbertBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).reindex e.symm = b := by
  simp

/-- A vector orthogonal to every member of a Hilbert basis of a subspace is orthogonal to every
vector of the represented subspace. -/
theorem inner_eq_zero_of_forall_inner_eq_zero {K : Submodule 𝕜 E}
    {iota : Type*} (bK : _root_.HilbertBasis iota 𝕜 K) {x : E}
    (hx : ∀ i, ⟪x, (bK i : E)⟫_𝕜 = 0) {y : E} (hy : y ∈ K) : ⟪x, y⟫_𝕜 = 0 := by
  have hsum := ((innerSL 𝕜 x).comp K.subtypeL).hasSum (bK.hasSum_repr ⟨y, hy⟩)
  have hzero : HasSum (fun _ : iota => (0 : 𝕜)) ⟪x, y⟫_𝕜 := by
    simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.subtype_apply,
      innerSL_apply_apply, map_smul, hx, smul_zero] using hsum
  exact hzero.unique hasSum_zero

/-- Two continuous linear maps between Hilbert spaces are equal when their matrix entries
`⟪c i, A (b j)⟫` in Hilbert bases `b` of the source and `c` of the target agree. -/
theorem ext_inner_apply {iota kappa F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (b : _root_.HilbertBasis iota 𝕜 E) (c : _root_.HilbertBasis kappa 𝕜 F)
    {A B : E →L[𝕜] F} (h : ∀ i j, ⟪c i, A (b j)⟫_𝕜 = ⟪c i, B (b j)⟫_𝕜) : A = B := by
  refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span)
    ?_
  rintro _ ⟨j, rfl⟩
  exact c.repr.injective (lp.ext (funext fun i ↦ by
    simp only [_root_.HilbertBasis.repr_apply_apply, h]))

/-- **Expansion of an operator in a Hilbert basis.** `T x = ∑ᵢ ⟪bᵢ, x⟫ T bᵢ`. -/
theorem hasSum_inner_smul_apply {iota F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [TopologicalSpace F] (b : _root_.HilbertBasis iota 𝕜 E) (T : E →L[𝕜] F) (x : E) :
    HasSum (fun i ↦ ⟪b i, x⟫_𝕜 • T (b i)) (T x) := by
  simpa only [map_smul, b.repr_apply_apply] using T.hasSum (b.hasSum_repr x)

/-- A continuous linear map that vanishes on every vector of a Hilbert basis outside a finite set
of indices has finite rank: its range is spanned by the images of the remaining basis vectors. -/
theorem hasFiniteRange_of_apply_eq_zero {iota F : Type*}
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

end HilbertBasis
