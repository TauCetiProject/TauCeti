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

A space with a Hilbert basis is complete (`HilbertBasis.completeSpace`), and every nonzero vector
has a nonzero inner product with at least one basis element (`HilbertBasis.exists_inner_ne_zero`).

It also expands the value of a continuous linear map in a Hilbert basis,
`T x = ∑ᵢ ⟪bᵢ, x⟫ T bᵢ` (`HilbertBasis.hasSum_inner_smul_apply`). It records that a continuous
linear map vanishing on all but finitely many vectors of a Hilbert basis has finite rank, since
every vector is the sum of its basis expansion, and that a continuous linear map is determined by
its matrix entries in Hilbert bases of its source and target (`HilbertBasis.ext_inner_apply`).

Finally, `lp.hilbertBasisFun` bundles the standard unit coordinate vectors of `ℓ²(ι, 𝕜)` as a
Hilbert basis (the `ℓ²` analogue of `EuclideanSpace.basisFun`), with simp lemmas for its
coordinate representation (`lp.hilbertBasisFun_repr`), basis vectors (`lp.hilbertBasisFun_apply`),
and coordinate inner products (`lp.hilbertBasisFun_inner`).
-/

public section

namespace HilbertBasis

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A space with a Hilbert basis is complete, being isometric to `ℓ²`. -/
theorem completeSpace {iota : Type*} (b : _root_.HilbertBasis iota 𝕜 E) : CompleteSpace E :=
  b.repr.toIsometryEquiv.completeSpace

/-- A nonzero vector has a nonzero inner product with at least one member of any Hilbert basis. -/
theorem exists_inner_ne_zero {iota : Type*} (b : _root_.HilbertBasis iota 𝕜 E) {x : E}
    (hx : x ≠ 0) : ∃ i, ⟪b i, x⟫_𝕜 ≠ 0 := by
  by_contra! h
  refine hx (b.repr.map_eq_zero_iff.1 ?_)
  ext i
  simp [b.repr_apply_apply, h i]

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

namespace lp

open scoped InnerProductSpace lp

/-- The standard unit coordinate vectors, bundled as a Hilbert basis of `ℓ²(ι, 𝕜)`. This is the
`ℓ²` analogue of `EuclideanSpace.basisFun`. -/
noncomputable def hilbertBasisFun (ι 𝕜 : Type*) [RCLike 𝕜] : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 ℓ²(ι, 𝕜))

/-- The coordinate representation of `lp.hilbertBasisFun` is the identity isometry on `ℓ²(ι, 𝕜)`. -/
@[simp]
theorem hilbertBasisFun_repr (ι 𝕜 : Type*) [RCLike 𝕜] :
    (hilbertBasisFun ι 𝕜).repr = LinearIsometryEquiv.refl 𝕜 ℓ²(ι, 𝕜) :=
  (rfl)

/-- The `i`-th vector of `lp.hilbertBasisFun` is the unit single-coordinate vector at `i`. -/
@[simp]
theorem hilbertBasisFun_apply (ι 𝕜 : Type*) [RCLike 𝕜] [DecidableEq ι] (i : ι) :
    hilbertBasisFun ι 𝕜 i = lp.single 2 i 1 := by
  rw [← HilbertBasis.repr_symm_single, hilbertBasisFun_repr]
  exact (LinearIsometryEquiv.refl 𝕜 _).symm_apply_eq.2 rfl

/-- Inner product against the `i`-th vector of `lp.hilbertBasisFun` evaluates the `i`-th
coordinate. -/
@[simp]
theorem hilbertBasisFun_inner (ι 𝕜 : Type*) [RCLike 𝕜] (x : ℓ²(ι, 𝕜)) (i : ι) :
    ⟪hilbertBasisFun ι 𝕜 i, x⟫_𝕜 = x i := by
  rw [← (hilbertBasisFun ι 𝕜).repr_apply_apply]
  simp

end lp
