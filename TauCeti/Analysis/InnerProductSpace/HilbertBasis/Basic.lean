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

A space with a Hilbert basis is complete (`HilbertBasis.completeSpace`).

It also expands the value of a continuous linear map in a Hilbert basis: the series
`∑ᵢ ⟪bᵢ, x⟫ T bᵢ` converges to `T x` (`HilbertBasis.hasSum_inner_smul_apply`). It records that a
continuous linear map into a T1 topological module vanishing on all but finitely many vectors of a
Hilbert basis has finite rank (`HilbertBasis.hasFiniteRange_of_apply_eq_zero`), since the partial
sums of each expansion are then eventually constant. It also records that continuous
(semi)linear maps into a Hausdorff topological module, linear isometries, and linear isometric
equivalences out of `E` are determined by their values on a Hilbert basis
(`HilbertBasis.ext_continuousLinearMap`, `HilbertBasis.ext_linearIsometry`,
`HilbertBasis.ext_linearIsometryEquiv`), hence a continuous (semi)linear map between spaces with
Hilbert bases by its matrix entries in those bases (`HilbertBasis.ext_inner_apply`).

Finally, the orthogonal complement of the span of the basis vectors indexed by a set `s` is the
closed span of the basis vectors indexed by its complement (`HilbertBasis.orthogonal_span_image`).
This computes the cokernels of isometries that send a Hilbert basis into another one.
-/

public section

namespace HilbertBasis

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A space with a Hilbert basis is complete, being isometric to `ℓ²`. -/
theorem completeSpace (b : HilbertBasis ι 𝕜 E) : CompleteSpace E :=
  b.repr.toIsometryEquiv.completeSpace

/-- A vector orthogonal to every member of a Hilbert basis of a subspace is orthogonal to every
vector of the represented subspace. -/
theorem inner_eq_zero_of_forall_inner_eq_zero {K : Submodule 𝕜 E} (bK : HilbertBasis ι 𝕜 K)
    {x : E} (hx : ∀ i, ⟪x, (bK i : E)⟫_𝕜 = 0) {y : E} (hy : y ∈ K) : ⟪x, y⟫_𝕜 = 0 := by
  have hsum := ((innerSL 𝕜 x).comp K.subtypeL).hasSum (bK.hasSum_repr ⟨y, hy⟩)
  have hzero : HasSum (fun _ : ι => (0 : 𝕜)) ⟪x, y⟫_𝕜 := by
    simpa only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.subtype_apply,
      innerSL_apply_apply, map_smul, hx, smul_zero] using hsum
  exact hzero.unique hasSum_zero

/-- Two continuous semilinear maps from `E` to a Hausdorff topological module agree when they agree
on every vector of a Hilbert basis of `E`. -/
theorem ext_continuousLinearMap {𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [AddCommMonoid M] [TopologicalSpace M] [T2Space M] [Module 𝕜' M]
    (b : HilbertBasis ι 𝕜 E) {A B : E →SL[σ] M} (h : ∀ i, A (b i) = B (b i)) : A = B :=
  ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span)
    (Set.eqOn_range.2 (funext h))

/-- Two semilinear isometries out of `E` into a normed module agree when they agree on every vector
of a Hilbert basis of `E`. -/
theorem ext_linearIsometry {𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [NormedAddCommGroup M] [Module 𝕜' M] (b : HilbertBasis ι 𝕜 E)
    {f g : E →ₛₗᵢ[σ] M} (h : ∀ i, f (b i) = g (b i)) : f = g :=
  LinearIsometry.toContinuousLinearMap_injective <| b.ext_continuousLinearMap fun i ↦ by
    simpa only [LinearIsometry.coe_toContinuousLinearMap] using h i

/-- Two semilinear isometric equivalences out of `E` into a seminormed module agree when they agree
on every vector of a Hilbert basis of `E`. -/
theorem ext_linearIsometryEquiv {𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [SeminormedAddCommGroup M] [Module 𝕜' M] (b : HilbertBasis ι 𝕜 E)
    {U V : E ≃ₛₗᵢ[σ] M} (h : ∀ i, U (b i) = V (b i)) : U = V := by
  have : T2Space M := U.toHomeomorph.t2Space
  exact LinearIsometryEquiv.toLinearIsometry_injective <|
    LinearIsometry.toContinuousLinearMap_injective <|
      b.ext_continuousLinearMap fun i ↦ by
        simpa only [LinearIsometry.coe_toContinuousLinearMap,
          LinearIsometryEquiv.coe_toLinearIsometry] using h i

/-- Two continuous semilinear maps between Hilbert spaces are equal when their matrix entries
`⟪c i, A (b j)⟫` in Hilbert bases `b` of the source and `c` of the target agree. -/
theorem ext_inner_apply {𝕜' κ F : Type*} [RCLike 𝕜'] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜' F] {σ : 𝕜 →+* 𝕜'} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜' F)
    {A B : E →SL[σ] F} (h : ∀ i j, ⟪c i, A (b j)⟫_𝕜' = ⟪c i, B (b j)⟫_𝕜') : A = B :=
  b.ext_continuousLinearMap fun j ↦ c.repr.injective <| lp.ext <| funext fun i ↦ by
    simp only [HilbertBasis.repr_apply_apply, h]

/-- **Expansion of an operator in a Hilbert basis.** The series `∑ᵢ ⟪bᵢ, x⟫ T bᵢ` converges
to `T x`. No separation is assumed on the target, so this limit need not be unique. -/
theorem hasSum_inner_smul_apply {F : Type*} [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]
    (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) (x : E) :
    HasSum (fun i ↦ ⟪b i, x⟫_𝕜 • T (b i)) (T x) := by
  simpa only [map_smul, b.repr_apply_apply] using T.hasSum (b.hasSum_repr x)

/-- A continuous linear map into a T1 topological module that vanishes on every vector of a
Hilbert basis outside a finite set of indices has finite rank: its range is spanned by the images
of the remaining basis vectors. -/
theorem hasFiniteRange_of_apply_eq_zero {F : Type*}
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [T1Space F]
    (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) (s : Finset ι) (hT : ∀ i ∉ s, T (b i) = 0) :
    (T : E →ₗ[𝕜] F).HasFiniteRange := by
  suffices h : (T : E →ₗ[𝕜] F).range = Submodule.span 𝕜 ((fun i ↦ T (b i)) '' s) by
    rw [LinearMap.hasFiniteRange_iff_range, h]
    exact Submodule.fg_span (s.finite_toSet.image _)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    -- The partial sums are eventually constant, so in a T1 space their limit is that constant.
    have hx : ∑ i ∈ s, ⟪b i, x⟫_𝕜 • T (b i) = T x := by
      refine tendsto_const_nhds_iff.1 (Filter.Tendsto.congr' ?_ (b.hasSum_inner_smul_apply T x))
      filter_upwards [Filter.eventually_ge_atTop s] with t ht
      exact (Finset.sum_subset ht fun i _ hi ↦ by rw [hT i hi, smul_zero]).symm
    rw [ContinuousLinearMap.coe_coe, ← hx]
    exact Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact ⟨b i, rfl⟩

/-- The orthogonal complement of the span of the basis vectors indexed by `s` is the closed span
of the basis vectors indexed by the complement of `s`. -/
theorem orthogonal_span_image (b : HilbertBasis ι 𝕜 E) (s : Set ι) :
    (Submodule.span 𝕜 (b '' s))ᗮ = (Submodule.span 𝕜 (b '' sᶜ)).topologicalClosure := by
  apply le_antisymm
  · intro y hy
    -- The basis expansion of `y` has no terms indexed by `s`.
    have hzero : ∀ i ∈ s, ⟪b i, y⟫_𝕜 = 0 := fun i hi ↦
      Submodule.inner_right_of_mem_orthogonal (K := Submodule.span 𝕜 (b '' s))
        (Submodule.subset_span ⟨i, hi, rfl⟩) hy
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine mem_closure_of_tendsto (b.hasSum_repr y) (Filter.Eventually.of_forall fun t ↦ ?_)
    refine SetLike.mem_coe.2 (Submodule.sum_mem _ fun i _ ↦ ?_)
    by_cases hi : i ∈ s
    · rw [b.repr_apply_apply, hzero i hi, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
    rintro _ ⟨j, hj, rfl⟩ _ ⟨i, hi, rfl⟩
    exact b.orthonormal.inner_eq_zero fun hji ↦ hj (hji ▸ hi)

end HilbertBasis
