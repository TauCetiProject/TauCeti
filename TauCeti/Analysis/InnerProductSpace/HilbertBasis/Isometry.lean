/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic

/-!
# Linear isometries out of a Hilbert basis

A Hilbert basis `b` of `E` and an orthonormal family `v` in a complete space `F`, indexed by the
same type, determine a linear isometry `E →ₗᵢ F` sending `b i` to `v i`: identify `E` with `ℓ²`
through `b` and sum the coordinates against `v`. It is the only continuous linear map with these
values on the basis, and its range is the closed linear span of `v`.

Taking for `v` a second Hilbert basis `c` reindexed along an injection `f` of the index types
gives the isometries `b i ↦ c (f i)`, such as the unilateral shift `b n ↦ b (n + 1)` of a Hilbert
basis indexed by `ℕ`. The range of such an isometry is the orthogonal complement of the vectors
`c j` with `j` outside the range of `f`.

## Main declarations

* `HilbertBasis.linearIsometryOfOrthonormal`: the linear isometry `b i ↦ v i`.
* `HilbertBasis.hasSum_linearIsometryOfOrthonormal`: its value is `∑ᵢ ⟪b i, x⟫ • v i`.
* `HilbertBasis.eq_linearIsometryOfOrthonormal`: uniqueness among continuous linear maps.
* `HilbertBasis.range_linearIsometryOfOrthonormal`: its range is the closed span of `v`.
* `HilbertBasis.range_linearIsometryOfOrthonormal_comp`: the range of `b i ↦ c (f i)` is the
  orthogonal complement of the basis vectors `c j` with `j ∉ Set.range f`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace HilbertBasis

variable {ι 𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  (b : HilbertBasis ι 𝕜 E) {v : ι → F} (hv : Orthonormal 𝕜 v)

/-- The linear isometry sending each vector `b i` of a Hilbert basis to the vector `v i` of an
orthonormal family in a complete space: `x ↦ ∑ᵢ ⟪b i, x⟫ • v i`. -/
protected def linearIsometryOfOrthonormal : E →ₗᵢ[𝕜] F :=
  hv.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry

/-- The isometry `b i ↦ v i` takes the `ℓ²` coordinates of `x` in `b` and sums them against `v`. -/
theorem linearIsometryOfOrthonormal_apply (x : E) :
    b.linearIsometryOfOrthonormal hv x = hv.orthogonalFamily.linearIsometry (b.repr x) := by
  rw [HilbertBasis.linearIsometryOfOrthonormal]
  rfl

/-- The isometry `b i ↦ v i` is the sum `∑ᵢ ⟪b i, x⟫ • v i`. -/
theorem hasSum_linearIsometryOfOrthonormal (x : E) :
    HasSum (fun i ↦ ⟪b i, x⟫_𝕜 • v i) (b.linearIsometryOfOrthonormal hv x) := by
  simpa [linearIsometryOfOrthonormal_apply, b.repr_apply_apply] using
    hv.orthogonalFamily.hasSum_linearIsometry (b.repr x)

/-- The isometry `b i ↦ v i` sends `b i` to `v i`. -/
@[simp]
theorem linearIsometryOfOrthonormal_apply_self (i : ι) :
    b.linearIsometryOfOrthonormal hv (b i) = v i := by
  classical
  simp [linearIsometryOfOrthonormal_apply, b.repr_self]

/-- A continuous linear map sending each `b i` to `v i` is the isometry `b i ↦ v i`. -/
theorem eq_linearIsometryOfOrthonormal {T : E →L[𝕜] F} (hT : ∀ i, T (b i) = v i) :
    T = (b.linearIsometryOfOrthonormal hv).toContinuousLinearMap :=
  b.ext_continuousLinearMap fun i ↦ by simp [hT]

/-- The range of the isometry `b i ↦ v i` is the closed linear span of `v`. -/
theorem range_linearIsometryOfOrthonormal :
    LinearMap.range (b.linearIsometryOfOrthonormal hv).toLinearMap =
      (Submodule.span 𝕜 (Set.range v)).topologicalClosure := by
  have hrange : LinearMap.range (b.linearIsometryOfOrthonormal hv).toLinearMap =
      LinearMap.range hv.orthogonalFamily.linearIsometry.toLinearMap :=
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 b.repr.surjective)
  rw [hrange, hv.orthogonalFamily.range_linearIsometry]
  simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion]

/-- For Hilbert bases `b` of `E` and `c` of `F` and an injection `f` of their index types, the
range of the isometry `b i ↦ c (f i)` is the orthogonal complement of the basis vectors `c j` with
`j` outside the range of `f`. -/
theorem range_linearIsometryOfOrthonormal_comp {κ : Type*} (c : HilbertBasis κ 𝕜 F) {f : ι → κ}
    (hf : Function.Injective f) :
    LinearMap.range (b.linearIsometryOfOrthonormal (c.orthonormal.comp f hf)).toLinearMap =
      (Submodule.span 𝕜 (c '' (Set.range f)ᶜ))ᗮ := by
  rw [range_linearIsometryOfOrthonormal, orthogonal_span_image, compl_compl, Set.range_comp]

end HilbertBasis
