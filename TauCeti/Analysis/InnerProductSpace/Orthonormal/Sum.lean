/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
-- Private: `canonicalCovariantTensor_eq_sum` is used only inside `sum_apply_self_eq`.
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-!
# Expansions and contractions against orthonormal bases

Finite sums over orthonormal bases recover linear maps from their matrix coefficients and
contract tensors in orthonormal frames, for instance when tracing the Ricci tensor to scalar
curvature:

* `OrthonormalBasis.sum_apply_mul_inner`: a linear functional `ℓ` satisfies
  `∑ i, ℓ (b i) * ⟪b i, a⟫ = ℓ a`, the expansion of `a` in `b` pushed through `ℓ`.
* `OrthonormalBasis.sum_apply_mul_inner_mul_inner`: a scalar-valued bilinear map `B` satisfies
  `∑ i, ∑ j, B (u i) (v j) * ⟪u i, x⟫ * ⟪v j, y⟫ = B x y` in a pair of orthonormal bases.
* `OrthonormalBasis.sum_inner_smul_rankOne`: an operator is the sum of its matrix coefficients
  times the corresponding rank-one operators.
* `OrthonormalBasis.sum_sum_inner_mul_inner_mul_inner`: the two-basis expansion
  `⟪x, T y⟫ = ∑ᵢ ∑ⱼ ⟪x, uᵢ⟫ ⟪uᵢ, T vⱼ⟫ ⟪vⱼ, y⟫`.
* `OrthonormalBasis.inner_sum_inner_smul`: expanding two vectors in `b` and reassembling along an
  orthonormal family `e` preserves their inner product,
  `⟪∑ i, ⟪b i, x⟫ • e i, ∑ i, ⟪b i, y⟫ • e i⟫ = ⟪x, y⟫`.
* `OrthonormalBasis.sum_inner_self`: `∑ i, ⟪b i, b i⟫ = card ι`, the trace of the identity.
* `OrthonormalBasis.inner_eq_sum_repr`: the inner product in coordinates,
  `⟪x, y⟫ = ∑ i, conj (b.repr x i) * b.repr y i`.
* `OrthonormalBasis.real_inner_fin_two`: in a real plane with orthonormal basis `b`,
  `⟪x, y⟫ = ⟪x, b₀⟫ ⟪y, b₀⟫ + ⟪x, b₁⟫ ⟪y, b₁⟫`.
* `OrthonormalBasis.sum_apply_self_eq`: for orthonormal bases `b`, `b'` of a real inner product
  space and a bilinear map `B`, `∑ k, B (b k) (b k) = ∑ i, B (b' i) (b' i)`.
* `Complex.isometryOfOrthonormal_symm_apply_eq_mk`: in the same plane, the complex coordinate of
  `x` given by `Complex.isometryOfOrthonormal b` is `⟪x, b₀⟫ + i ⟪x, b₁⟫`.
-/

public section

namespace OrthonormalBasis

open InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- A linear functional is recovered from its values on an orthonormal basis:
`∑ i, ℓ (b i) * ⟪b i, a⟫ = ℓ a`. -/
theorem sum_apply_mul_inner {F : Type*} [FunLike F E 𝕜] [LinearMapClass F 𝕜 E 𝕜]
    (b : OrthonormalBasis ι 𝕜 E) (ℓ : F) (a : E) : ∑ i, ℓ (b i) * ⟪b i, a⟫_𝕜 = ℓ a := by
  conv_rhs => rw [← b.sum_repr' a]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- The vectors of an orthonormal basis have unit length, so `∑ i, ⟪b i, b i⟫ = card ι`. -/
theorem sum_inner_self (b : OrthonormalBasis ι 𝕜 E) : ∑ i, ⟪b i, b i⟫_𝕜 = Fintype.card ι := by
  simp [inner_self_eq_norm_sq_to_K, b.orthonormal.1]

/-- The inner product in the coordinates of an orthonormal basis:
`⟪x, y⟫ = ∑ i, conj (b.repr x i) * b.repr y i`. -/
theorem inner_eq_sum_repr (b : OrthonormalBasis ι 𝕜 E) (x y : E) :
    ⟪x, y⟫_𝕜 = ∑ i, conj (b.repr x i) * b.repr y i := by
  simp [← b.sum_inner_mul_inner x y, b.repr_apply_apply]

/-- The real inner product in the two coordinates of an orthonormal basis `b` of a plane:
`⟪x, y⟫ = ⟪x, b₀⟫ ⟪y, b₀⟫ + ⟪x, b₁⟫ ⟪y, b₁⟫`. -/
theorem real_inner_fin_two {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : OrthonormalBasis (Fin 2) ℝ V) (x y : V) :
    ⟪x, y⟫_ℝ = ⟪x, b 0⟫_ℝ * ⟪y, b 0⟫_ℝ + ⟪x, b 1⟫_ℝ * ⟪y, b 1⟫_ℝ := by
  rw [← b.sum_inner_mul_inner x y, Fin.sum_univ_two, real_inner_comm (b 0) y,
    real_inner_comm (b 1) y]

variable {F κ : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype κ]

/-- A scalar-valued bilinear map is recovered from its values on a pair of orthonormal bases:
`∑ i, ∑ j, B (u i) (v j) * ⟪u i, x⟫ * ⟪v j, y⟫ = B x y`. -/
theorem sum_apply_mul_inner_mul_inner (u : OrthonormalBasis ι 𝕜 E)
    (v : OrthonormalBasis κ 𝕜 F) (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (x : E) (y : F) :
    ∑ i, ∑ j, B (u i) (v j) * ⟪u i, x⟫_𝕜 * ⟪v j, y⟫_𝕜 = B x y := by
  have hj (i : ι) :
      ∑ j, B (u i) (v j) * ⟪u i, x⟫_𝕜 * ⟪v j, y⟫_𝕜 = B (u i) y * ⟪u i, x⟫_𝕜 := by
    calc ∑ j, B (u i) (v j) * ⟪u i, x⟫_𝕜 * ⟪v j, y⟫_𝕜
        = (∑ j, B (u i) (v j) * ⟪v j, y⟫_𝕜) * ⟪u i, x⟫_𝕜 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = B (u i) y * ⟪u i, x⟫_𝕜 := by rw [v.sum_apply_mul_inner]
  simp_rw [hj]
  simpa only [LinearMap.flip_apply] using u.sum_apply_mul_inner (B.flip y) x

/-- **Expansion in rank-one operators.** For orthonormal bases `(uᵢ)` of `E` and `(vⱼ)` of `F`,
every `C : F →L[𝕜] E` is the sum of its matrix coefficients `⟪uᵢ, C vⱼ⟫` times the rank-one
operators `rankOne 𝕜 uᵢ vⱼ : x ↦ ⟪vⱼ, x⟫ uᵢ`. -/
theorem sum_inner_smul_rankOne (u : OrthonormalBasis ι 𝕜 E) (v : OrthonormalBasis κ 𝕜 F)
    (C : F →L[𝕜] E) : ∑ i, ∑ j, ⟪u i, C (v j)⟫_𝕜 • rankOne 𝕜 (u i) (v j) = C := by
  have hC : C = (∑ i, rankOne 𝕜 (u i) (u i)) ∘L C ∘L ∑ j, rankOne 𝕜 (v j) (v j) := by
    simp [sum_rankOne_eq_id]
  conv_rhs => rw [hC]
  simp only [ContinuousLinearMap.comp_finsetSum, comp_rankOne, sum_apply,
    rankOne_apply, map_sum, map_smul, smul_apply]
  exact Finset.sum_comm

/-- **Matrix coefficients of an inner product.** For orthonormal bases `(uᵢ)` of `E` and `(vⱼ)` of
`F`, `⟪x, T y⟫ = ∑ᵢ ∑ⱼ ⟪x, uᵢ⟫ ⟪uᵢ, T vⱼ⟫ ⟪vⱼ, y⟫` for every linear map `T : F →ₗ[𝕜] E`. -/
theorem sum_sum_inner_mul_inner_mul_inner (u : OrthonormalBasis ι 𝕜 E)
    (v : OrthonormalBasis κ 𝕜 F) (T : F →ₗ[𝕜] E) (x : E) (y : F) :
    ∑ i, ∑ j, ⟪x, u i⟫_𝕜 * ⟪u i, T (v j)⟫_𝕜 * ⟪v j, y⟫_𝕜 = ⟪x, T y⟫_𝕜 := by
  rw [← u.sum_inner_mul_inner x (T y)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [← v.sum_repr' y]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- Expanding two vectors in an orthonormal basis `b` and reassembling their coordinates along an
orthonormal family `e` preserves their inner product. -/
theorem inner_sum_inner_smul (b : OrthonormalBasis ι 𝕜 E) {e : ι → F} (he : Orthonormal 𝕜 e)
    (x y : E) :
    ⟪∑ i, ⟪b i, x⟫_𝕜 • e i, ∑ i, ⟪b i, y⟫_𝕜 • e i⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  simp_rw [he.inner_sum, inner_conj_symm, b.sum_inner_mul_inner]

/-- **Basis independence of the trace of a real bilinear map.** For orthonormal bases `b` and `b'`
of a real inner product space `V` and a bilinear map `B : V →ₗ[ℝ] V →ₗ[ℝ] M`,
`∑ k, B (b k) (b k) = ∑ i, B (b' i) (b' i)`. -/
theorem sum_apply_self_eq {V M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [AddCommMonoid M] [Module ℝ M] (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis κ ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] M) :
    ∑ k, B (b k) (b k) = ∑ i, B (b' i) (b' i) := by
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b.toBasis
  have h := congrArg (TensorProduct.lift B)
    ((InnerProductSpace.canonicalCovariantTensor_eq_sum V b).symm.trans
      (InnerProductSpace.canonicalCovariantTensor_eq_sum V b'))
  simpa [map_sum] using h

end OrthonormalBasis

open scoped InnerProductSpace in
/-- The complex coordinate of `x` given by `Complex.isometryOfOrthonormal b` is
`⟪x, b₀⟫ + i ⟪x, b₁⟫`. -/
theorem Complex.isometryOfOrthonormal_symm_apply_eq_mk {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V) (x : V) :
    (Complex.isometryOfOrthonormal b).symm x = ⟨⟪x, b 0⟫_ℝ, ⟪x, b 1⟫_ℝ⟩ := by
  rw [Complex.isometryOfOrthonormal_symm_apply]
  apply Complex.ext <;> simp [b.coe_toBasis_repr_apply, b.repr_apply_apply, real_inner_comm]
