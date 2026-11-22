/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.InnerProductSpace.l2Space
import TauCeti.Topology.Algebra.Module.Span

/-!
# Hilbert bases

This file transfers orthogonality to every vector of a subspace from orthogonality to each
element of a Hilbert basis of that subspace.  In particular, this lets Hilbert bases of mutually
orthogonal eigenspaces be assembled into a spectral basis of the ambient space.

A space with a Hilbert basis is complete (`HilbertBasis.completeSpace`), and a vector orthogonal
to every vector of a Hilbert basis is zero (`HilbertBasis.eq_zero_of_forall_inner_eq_zero`). Finite
linear combinations of a Hilbert basis with coefficients from a dense set of scalars are dense
(`HilbertBasis.denseRange_finset_sum_smul`).

It also expands the value of a continuous linear map in a Hilbert basis,
`T x = ∑ᵢ ⟪bᵢ, x⟫ T bᵢ` (`HilbertBasis.hasSum_inner_smul_apply`). It records that a continuous
linear map vanishing on all but finitely many vectors of a Hilbert basis has finite rank, since
every vector is the sum of its basis expansion, and that continuous (semi)linear maps, linear
isometries, and linear isometric equivalences out of `E` are determined by their values on a
Hilbert basis (`HilbertBasis.ext_continuousLinearMap`, `HilbertBasis.ext_linearIsometry`,
`HilbertBasis.ext_linearIsometryEquiv`, `HilbertBasis.ext_inner_apply`). More generally, a
continuous semilinear map out of `E` sends every vector into a closed submodule containing the
images of the basis vectors (`HilbertBasis.apply_mem_of_forall_apply_mem`).

Finally, the orthogonal complement of the span of the basis vectors indexed by a set `s` is the
closed span of the basis vectors indexed by its complement (`HilbertBasis.orthogonal_span_image`).
This computes the cokernels of isometries that send a Hilbert basis into another one.
-/

public section

namespace HilbertBasis

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A space with a Hilbert basis is complete, being isometric to `ℓ²`. -/
theorem completeSpace {iota : Type*} (b : _root_.HilbertBasis iota 𝕜 E) : CompleteSpace E :=
  b.repr.toIsometryEquiv.completeSpace

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

/-- A vector orthogonal to every vector of a Hilbert basis is zero. -/
theorem eq_zero_of_forall_inner_eq_zero {iota : Type*} (b : _root_.HilbertBasis iota 𝕜 E) {x : E}
    (hx : ∀ i, ⟪b i, x⟫_𝕜 = 0) : x = 0 :=
  b.repr.map_eq_zero_iff.1 <| lp.ext <| funext fun i ↦ by
    rw [b.repr_apply_apply, hx i, lp.coeFn_zero, Pi.zero_apply]

/-- Two continuous semilinear maps from `E` to a Hausdorff topological module agree when they agree
on every vector of a Hilbert basis of `E`. -/
theorem ext_continuousLinearMap {ι 𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [AddCommMonoid M] [TopologicalSpace M] [T2Space M] [Module 𝕜' M]
    (b : _root_.HilbertBasis ι 𝕜 E) {A B : E →SL[σ] M} (h : ∀ i, A (b i) = B (b i)) : A = B := by
  refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span)
    ?_
  rintro _ ⟨i, rfl⟩
  exact h i

/-- A continuous semilinear map out of `E` sends every vector into a closed submodule that contains
the images of all vectors of a Hilbert basis of `E`. -/
theorem apply_mem_of_forall_apply_mem {ι 𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [AddCommMonoid M] [Module 𝕜' M] [TopologicalSpace M] (b : _root_.HilbertBasis ι 𝕜 E)
    {S : Submodule 𝕜' M} (hS : IsClosed (S : Set M)) (L : E →SL[σ] M) (h : ∀ i, L (b i) ∈ S)
    (x : E) : L x ∈ S := by
  have hle : Submodule.span 𝕜 (Set.range b) ≤ S.comap (L : E →ₛₗ[σ] M) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 h)
  have hcl := Submodule.topologicalClosure_minimal _ hle (hS.preimage L.continuous)
  rw [b.dense_span] at hcl
  exact hcl Submodule.mem_top

/-- Two semilinear isometries out of `E` into a normed module agree when they agree on every vector
of a Hilbert basis of `E`. -/
theorem ext_linearIsometry {ι 𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [NormedAddCommGroup M] [Module 𝕜' M] (b : _root_.HilbertBasis ι 𝕜 E)
    {f g : E →ₛₗᵢ[σ] M} (h : ∀ i, f (b i) = g (b i)) : f = g :=
  LinearIsometry.toContinuousLinearMap_injective <| b.ext_continuousLinearMap fun i ↦ by
    simpa only [LinearIsometry.coe_toContinuousLinearMap] using h i

/-- Two semilinear isometric equivalences out of `E` into a seminormed module agree when they agree
on every vector of a Hilbert basis of `E`. -/
theorem ext_linearIsometryEquiv {ι 𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [SeminormedAddCommGroup M] [Module 𝕜' M] (b : _root_.HilbertBasis ι 𝕜 E)
    {U V : E ≃ₛₗᵢ[σ] M} (h : ∀ i, U (b i) = V (b i)) : U = V := by
  have : T2Space M := U.toHomeomorph.t2Space
  exact LinearIsometryEquiv.toLinearIsometry_injective <|
    LinearIsometry.toContinuousLinearMap_injective <|
      b.ext_continuousLinearMap fun i ↦ by
        simpa only [LinearIsometry.coe_toContinuousLinearMap,
          LinearIsometryEquiv.coe_toLinearIsometry] using h i

/-- Two continuous linear maps between Hilbert spaces are equal when their matrix entries
`⟪c i, A (b j)⟫` in Hilbert bases `b` of the source and `c` of the target agree. -/
theorem ext_inner_apply {iota kappa F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (b : _root_.HilbertBasis iota 𝕜 E) (c : _root_.HilbertBasis kappa 𝕜 F)
    {A B : E →L[𝕜] F} (h : ∀ i j, ⟪c i, A (b j)⟫_𝕜 = ⟪c i, B (b j)⟫_𝕜) : A = B :=
  b.ext_continuousLinearMap fun j ↦ c.repr.injective <| lp.ext <| funext fun i ↦ by
    simp only [_root_.HilbertBasis.repr_apply_apply, h]

/-- Finite linear combinations of a Hilbert basis with coefficients from a dense-range scalar map
are dense in `E`. -/
theorem denseRange_finset_sum_smul {ι α : Type*} (b : _root_.HilbertBasis ι 𝕜 E)
    {g : α → 𝕜} (hg : DenseRange g) :
    DenseRange (fun t : Finset (ι × α) ↦ ∑ p ∈ t, g p.2 • b p.1) :=
  hg.finset_sum_smul (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span)

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

/-- The orthogonal complement of the span of the basis vectors indexed by `s` is the closed span
of the basis vectors indexed by the complement of `s`. -/
theorem orthogonal_span_image {iota : Type*} (b : _root_.HilbertBasis iota 𝕜 E) (s : Set iota) :
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
