/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.InnerProductSpace.l2Space
import TauCeti.Topology.Algebra.InfiniteSum.Defs

/-!
# Hilbert bases

This file transfers orthogonality to every vector of a subspace from orthogonality to each
element of a Hilbert basis of that subspace.  In particular, this lets Hilbert bases of mutually
orthogonal eigenspaces be assembled into a spectral basis of the ambient space. For the whole
space, only `0` is orthogonal to every vector of a Hilbert basis
(`HilbertBasis.eq_zero_of_forall_inner_eq_zero`).

A space with a Hilbert basis is complete (`HilbertBasis.completeSpace`).

It also expands the value of a continuous semilinear map in a Hilbert basis: the series
`∑ᵢ σ ⟪bᵢ, x⟫ • T bᵢ` converges to `T x` (`HilbertBasis.hasSum_inner_smul_apply`). A continuous
semilinear map, with a surjective scalar homomorphism `σ`, into a module with a T1 topology that
vanishes on all but finitely many vectors of a Hilbert basis has its range spanned, over the target
scalars, by the images of the remaining ones (`HilbertBasis.range_eq_span_image_of_apply_eq_zero`),
so such a map has finite rank when it is linear (`HilbertBasis.hasFiniteRange_of_apply_eq_zero`).
Among continuous semilinear maps into a module with a Hausdorff topology, semilinear isometries
into a seminormed module with a Hausdorff topology, and semilinear isometric equivalences out of
`E`, all with a fixed scalar homomorphism `σ`, each map is determined by its values on a Hilbert
basis (`HilbertBasis.ext_continuousLinearMap`, `HilbertBasis.ext_linearIsometry`,
`HilbertBasis.ext_linearIsometryEquiv`). Hence a continuous semilinear map between spaces with
Hilbert bases, for a fixed `σ`, is determined by its matrix entries in those bases
(`HilbertBasis.ext_inner_apply`).
A continuous semilinear map out of `E` also sends every vector into any closed submodule containing
the images of the basis vectors (`HilbertBasis.apply_mem_of_forall_apply_mem`).

Finally, the orthogonal complement of the span of the basis vectors indexed by a set `s` is the
closed span of the basis vectors indexed by its complement (`HilbertBasis.orthogonal_span_image`).
This computes the cokernels of isometries that send a Hilbert basis into another one.

The coordinates `⟪default i, x⟫` of a vector `x` in the standard Hilbert basis of `ℓ²(ι, 𝕜)` are
its entries `x i` (`HilbertBasis.inner_default_apply`).
-/

public section

namespace HilbertBasis

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A space with a Hilbert basis is complete, being isometric to `ℓ²`. -/
theorem completeSpace (b : HilbertBasis ι 𝕜 E) : CompleteSpace E :=
  b.repr.toIsometryEquiv.completeSpace

/-- Two continuous semilinear maps from `E` to a module with a Hausdorff topology, with the same
scalar homomorphism `σ`, agree when they agree on every vector of a Hilbert basis of `E`. -/
theorem ext_continuousLinearMap {𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [AddCommMonoid M] [TopologicalSpace M] [T2Space M] [Module 𝕜' M]
    (b : HilbertBasis ι 𝕜 E) {A B : E →SL[σ] M} (h : ∀ i, A (b i) = B (b i)) : A = B :=
  ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span)
    (Set.eqOn_range.2 (funext h))

/-- A vector orthogonal to every member of a Hilbert basis of a subspace is orthogonal to every
vector of the represented subspace. -/
theorem inner_eq_zero_of_forall_inner_eq_zero {K : Submodule 𝕜 E} (bK : HilbertBasis ι 𝕜 K)
    {x : E} (hx : ∀ i, ⟪x, (bK i : E)⟫_𝕜 = 0) {y : E} (hy : y ∈ K) : ⟪x, y⟫_𝕜 = 0 := by
  have h : (innerSL 𝕜 x).comp K.subtypeL = 0 := bK.ext_continuousLinearMap fun i ↦ by
    simpa [innerSL_apply_apply] using hx i
  simpa [innerSL_apply_apply] using DFunLike.congr_fun h ⟨y, hy⟩

/-- Only the zero vector is orthogonal to every vector of a Hilbert basis. -/
theorem eq_zero_of_forall_inner_eq_zero (b : HilbertBasis ι 𝕜 E) {x : E}
    (hx : ∀ i, ⟪x, b i⟫_𝕜 = 0) : x = 0 := by
  have h : innerSL 𝕜 x = 0 := b.ext_continuousLinearMap fun i ↦ by
    simpa [innerSL_apply_apply] using hx i
  simpa [innerSL_apply_apply] using DFunLike.congr_fun h x

/-- A continuous semilinear map out of `E` sends every vector into a closed submodule that contains
the images of all vectors of a Hilbert basis of `E`. -/
theorem apply_mem_of_forall_apply_mem {𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [AddCommMonoid M] [Module 𝕜' M] [TopologicalSpace M] (b : HilbertBasis ι 𝕜 E)
    {S : Submodule 𝕜' M} (hS : IsClosed (S : Set M)) (L : E →SL[σ] M) (h : ∀ i, L (b i) ∈ S)
    (x : E) : L x ∈ S := by
  have hle : Submodule.span 𝕜 (Set.range b) ≤ S.comap (L : E →ₛₗ[σ] M) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 h)
  have hcl := Submodule.topologicalClosure_minimal _ hle (hS.preimage L.continuous)
  rw [b.dense_span] at hcl
  exact hcl Submodule.mem_top

/-- Two semilinear isometries out of `E` into a seminormed module with a Hausdorff topology, with
the same scalar homomorphism `σ`, agree when they agree on every vector of a Hilbert basis of
`E`. -/
theorem ext_linearIsometry {𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [SeminormedAddCommGroup M] [T2Space M] [Module 𝕜' M] (b : HilbertBasis ι 𝕜 E)
    {f g : E →ₛₗᵢ[σ] M} (h : ∀ i, f (b i) = g (b i)) : f = g :=
  LinearIsometry.toContinuousLinearMap_injective <| b.ext_continuousLinearMap fun i ↦ by
    simpa only [LinearIsometry.coe_toContinuousLinearMap] using h i

/-- Two semilinear isometric equivalences out of `E` into a seminormed module, with the same scalar
homomorphism `σ`, agree when they agree on every vector of a Hilbert basis of `E`. -/
theorem ext_linearIsometryEquiv {𝕜' M : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [SeminormedAddCommGroup M] [Module 𝕜' M] (b : HilbertBasis ι 𝕜 E)
    {U V : E ≃ₛₗᵢ[σ] M} (h : ∀ i, U (b i) = V (b i)) : U = V := by
  -- The target of a linear isometric equivalence from a normed space is Hausdorff.
  have : T2Space M := U.toHomeomorph.t2Space
  exact LinearIsometryEquiv.toLinearIsometry_injective <| b.ext_linearIsometry fun i ↦ by
    simpa only [LinearIsometryEquiv.coe_toLinearIsometry] using h i

/-- Two continuous semilinear maps between Hilbert spaces, with the same scalar homomorphism `σ`,
are equal when their matrix entries `⟪c i, A (b j)⟫` in Hilbert bases `b` of the source and `c` of
the target agree. -/
theorem ext_inner_apply {𝕜' κ F : Type*} [RCLike 𝕜'] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜' F] {σ : 𝕜 →+* 𝕜'} (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜' F)
    {A B : E →SL[σ] F} (h : ∀ i j, ⟪c i, A (b j)⟫_𝕜' = ⟪c i, B (b j)⟫_𝕜') : A = B :=
  b.ext_continuousLinearMap fun j ↦ c.repr.injective <| lp.ext <| funext fun i ↦ by
    simp only [HilbertBasis.repr_apply_apply, h]

/-- **Expansion of an operator in a Hilbert basis.** For a continuous semilinear map `T`, the
series `∑ᵢ σ ⟪bᵢ, x⟫ • T bᵢ` converges to `T x`. No separation is assumed on the target, so this
limit need not be unique. -/
theorem hasSum_inner_smul_apply {𝕜' F : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'} [AddCommMonoid F]
    [Module 𝕜' F] [TopologicalSpace F] (b : HilbertBasis ι 𝕜 E) (T : E →SL[σ] F) (x : E) :
    HasSum (fun i ↦ σ ⟪b i, x⟫_𝕜 • T (b i)) (T x) := by
  simpa only [map_smulₛₗ, b.repr_apply_apply] using T.hasSum (b.hasSum_repr x)

/-- The range of a continuous semilinear map, with a surjective scalar homomorphism `σ : 𝕜 →+* 𝕜'`,
into a module with a T1 topology that vanishes on every vector of a Hilbert basis outside a finite
set `s` of indices is the `𝕜'`-span of the images of the basis vectors indexed by `s`. -/
theorem range_eq_span_image_of_apply_eq_zero {𝕜' F : Type*} [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
    [RingHomSurjective σ] [AddCommMonoid F] [Module 𝕜' F] [TopologicalSpace F] [T1Space F]
    (b : HilbertBasis ι 𝕜 E) (T : E →SL[σ] F) (s : Finset ι) (hT : ∀ i ∉ s, T (b i) = 0) :
    (T : E →ₛₗ[σ] F).range = Submodule.span 𝕜' ((fun i ↦ T (b i)) '' s) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, (b.hasSum_inner_smul_apply T x).eq_sum_of_ne_finset_zero
      fun i hi ↦ by rw [hT i hi, smul_zero]]
    exact Submodule.sum_smul_mem _ _ fun i hi ↦ Submodule.subset_span ⟨i, hi, rfl⟩
  · rw [Submodule.span_le, LinearMap.coe_range, ContinuousLinearMap.coe_coe,
      ← Set.image_image T b]
    exact Set.image_subset_range T _

/-- A continuous linear map into a module with a T1 topology that vanishes on every vector of a
Hilbert basis outside a finite set of indices has finite rank. Its range is computed by
`HilbertBasis.range_eq_span_image_of_apply_eq_zero`. -/
theorem hasFiniteRange_of_apply_eq_zero {F : Type*}
    [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [T1Space F]
    (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) (s : Finset ι) (hT : ∀ i ∉ s, T (b i) = 0) :
    (T : E →ₗ[𝕜] F).HasFiniteRange := by
  rw [LinearMap.hasFiniteRange_iff_range, b.range_eq_span_image_of_apply_eq_zero T s hT]
  exact Submodule.fg_span (s.finite_toSet.image _)

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

open scoped lp in
/-- The coordinates of `x` in the standard Hilbert basis of `ℓ²(ι, 𝕜)` are its entries. -/
@[simp]
theorem inner_default_apply (x : ℓ²(ι, 𝕜)) (i : ι) :
    ⟪(default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) i, x⟫_𝕜 = x i :=
  ((default : HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)).repr_apply_apply x i).symm

end HilbertBasis
