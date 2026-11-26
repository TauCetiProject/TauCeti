/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Expansions and contractions against orthonormal bases

Finite sums over orthonormal bases recover linear maps from their matrix coefficients and
contract tensors in orthonormal frames, for instance when tracing the Ricci tensor to scalar
curvature:

* `OrthonormalBasis.sum_apply_mul_inner`: a linear functional `ℓ` satisfies
  `∑ i, ℓ (b i) * ⟪b i, a⟫ = ℓ a`, the expansion of `a` in `b` pushed through `ℓ`.
* `OrthonormalBasis.sum_apply_mul_inner_starProjection`: replacing `⟪b i, a⟫` by
  `⟪P (b i), a⟫` in this expansion, for the orthogonal projection `P` onto a subspace `K`, while
  keeping the coefficients `ℓ (b i)`, gives `ℓ (P a)`.
* `OrthonormalBasis.sum_apply_mul_inner_sub_sum_apply_mul_inner_starProjection`: for the projection
  `P` onto `(𝕜 ∙ ν)ᗮ`, the resulting sum is tangential, and subtracting it from the original sum
  gives `ℓ (ν / ‖ν‖²) * ⟪ν, a⟫`, the part of `ℓ a` along `ν`.
* `OrthonormalBasis.sum_apply_mul_inner_mul_inner`: a scalar-valued bilinear map `B` satisfies
  `∑ i, ∑ j, B (u i) (v j) * ⟪u i, x⟫ * ⟪v j, y⟫ = B x y` in a pair of orthonormal bases.
* `OrthonormalBasis.bilin_eq_inner_mul_sum_add_sum_sum_inner_starProjection`: the same expansion
  of `B g w`, with `g` split along `ν` and the projections onto `(𝕜 ∙ ν)ᗮ` of the vectors of the
  first basis.
* `OrthonormalBasis.sum_inner_smul_rankOne`: an operator is the sum of its matrix coefficients
  times the corresponding rank-one operators.
* `OrthonormalBasis.sum_sum_inner_mul_inner_mul_inner`: the two-basis expansion
  `⟪x, T y⟫ = ∑ᵢ ∑ⱼ ⟪x, uᵢ⟫ ⟪uᵢ, T vⱼ⟫ ⟪vⱼ, y⟫`.
* `OrthonormalBasis.inner_sum_inner_smul`: expanding two vectors in `b` and reassembling along an
  orthonormal family `e` preserves their inner product,
  `⟪∑ i, ⟪b i, x⟫ • e i, ∑ i, ⟪b i, y⟫ • e i⟫ = ⟪x, y⟫`.
* `OrthonormalBasis.sum_inner_self`: `∑ i, ⟪b i, b i⟫ = card ι`, the trace of the identity.
* `OrthonormalBasis.sum_sum_inner_smul`: contracting a double frame sum against `⟪b j, b i⟫`
  leaves its diagonal, `∑ i, ∑ j, ⟪b j, b i⟫ • X i j = ∑ i, X i i`.
* `OrthonormalBasis.inner_eq_sum_repr`: the inner product in coordinates,
  `⟪x, y⟫ = ∑ i, conj (b.repr x i) * b.repr y i`.
* `OrthonormalBasis.real_sum_inner_mul_inner`: Parseval's identity over `ℝ` with both inner
  products taken against the basis vector on the right, `∑ i, ⟪x, b i⟫ ⟪y, b i⟫ = ⟪x, y⟫`.
* `OrthonormalBasis.real_inner_fin_two`: in a real plane with orthonormal basis `b`,
  `⟪x, y⟫ = ⟪x, b₀⟫ ⟪y, b₀⟫ + ⟪x, b₁⟫ ⟪y, b₁⟫`.
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

/-- **A linear functional at a projection.** Replacing `⟪b i, a⟫` by `⟪P (b i), a⟫` in the
expansion `∑ i, ℓ (b i) * ⟪b i, a⟫ = ℓ a`, where `P` is the orthogonal projection onto a subspace
`K`, and keeping the coefficients `ℓ (b i)` gives `ℓ (P a)`. -/
theorem sum_apply_mul_inner_starProjection {F : Type*} [FunLike F E 𝕜] [LinearMapClass F 𝕜 E 𝕜]
    (b : OrthonormalBasis ι 𝕜 E) (ℓ : F) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (a : E) :
    ∑ i, ℓ (b i) * ⟪K.starProjection (b i), a⟫_𝕜 = ℓ (K.starProjection a) := by
  simp only [Submodule.inner_starProjection_left_eq_right, b.sum_apply_mul_inner]

/-- **The normal part of a linear functional.** Replacing `⟪b i, a⟫` by `⟪P (b i), a⟫` in the
expansion `∑ i, ℓ (b i) * ⟪b i, a⟫ = ℓ a`, where `P` is the orthogonal projection onto
`(𝕜 ∙ ν)ᗮ`, and keeping the coefficients `ℓ (b i)` gives a tangential sum. Subtracting it from the
original sum gives `ℓ (ν / ‖ν‖²) * ⟪ν, a⟫`, the value of `ℓ` at the projection of `a` onto
`𝕜 ∙ ν`. -/
theorem sum_apply_mul_inner_sub_sum_apply_mul_inner_starProjection {F : Type*} [FunLike F E 𝕜]
    [LinearMapClass F 𝕜 E 𝕜] (b : OrthonormalBasis ι 𝕜 E) (ℓ : F) (ν a : E) :
    ∑ i, ℓ (b i) * ⟪b i, a⟫_𝕜 - ∑ i, ℓ (b i) * ⟪(𝕜 ∙ ν)ᗮ.starProjection (b i), a⟫_𝕜 =
      ℓ (((‖ν‖ : 𝕜) ^ 2)⁻¹ • ν) * ⟪ν, a⟫_𝕜 := by
  -- The two sums are `ℓ a` and `ℓ (P a)`, and `a - P a` is the projection of `a` onto `𝕜 ∙ ν`.
  rw [b.sum_apply_mul_inner, b.sum_apply_mul_inner_starProjection, ← map_sub,
    Submodule.starProjection_orthogonal_val (K := 𝕜 ∙ ν), sub_sub_cancel,
    TauCeti.apply_starProjection_singleton, smul_eq_mul, mul_comm]

/-- The vectors of an orthonormal basis have unit length, so `∑ i, ⟪b i, b i⟫ = card ι`. -/
theorem sum_inner_self (b : OrthonormalBasis ι 𝕜 E) : ∑ i, ⟪b i, b i⟫_𝕜 = Fintype.card ι := by
  simp [inner_self_eq_norm_sq_to_K, b.orthonormal.1]

/-- Contracting a double sum over an orthonormal basis against `⟪b j, b i⟫` leaves its diagonal:
`∑ i, ∑ j, ⟪b j, b i⟫ • X i j = ∑ i, X i i`. -/
theorem sum_sum_inner_smul {M : Type*} [AddCommMonoid M] [Module 𝕜 M]
    (b : OrthonormalBasis ι 𝕜 E) (X : ι → ι → M) :
    ∑ i, ∑ j, ⟪b j, b i⟫_𝕜 • X i j = ∑ i, X i i := by
  classical
  simp [orthonormal_iff_ite.mp b.orthonormal]

/-- The inner product in the coordinates of an orthonormal basis:
`⟪x, y⟫ = ∑ i, conj (b.repr x i) * b.repr y i`. -/
theorem inner_eq_sum_repr (b : OrthonormalBasis ι 𝕜 E) (x y : E) :
    ⟪x, y⟫_𝕜 = ∑ i, conj (b.repr x i) * b.repr y i := by
  simp [← b.sum_inner_mul_inner x y, b.repr_apply_apply]

/-- Parseval's identity over `ℝ` with both inner products taken against the basis vector on the
right: `∑ i, ⟪x, b i⟫ ⟪y, b i⟫ = ⟪x, y⟫`. -/
theorem real_sum_inner_mul_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : OrthonormalBasis ι ℝ V) (x y : V) : ∑ i, ⟪x, b i⟫_ℝ * ⟪y, b i⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [← b.sum_inner_mul_inner x y]
  simp_rw [real_inner_comm y]

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

/-- **Splitting a bilinear map along `ν` and the subspace orthogonal to it.** For orthonormal bases
`(uᵢ)` of `E` and `(vⱼ)` of `F`,
`B(g, w) = ⟪ν, g⟫ ∑ⱼ B(ν', vⱼ) ⟪vⱼ, w⟫ + ∑ᵢ ∑ⱼ ⟪P uᵢ, g⟫ B(uᵢ, vⱼ) ⟪vⱼ, w⟫`, where
`ν' = ν / ‖ν‖²` and `P` is the orthogonal projection onto `(𝕜 ∙ ν)ᗮ`. -/
theorem bilin_eq_inner_mul_sum_add_sum_sum_inner_starProjection (u : OrthonormalBasis ι 𝕜 E)
    (v : OrthonormalBasis κ 𝕜 F) (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (ν g : E) (w : F) :
    B g w = ⟪ν, g⟫_𝕜 * ∑ j, B (((‖ν‖ : 𝕜) ^ 2)⁻¹ • ν) (v j) * ⟪v j, w⟫_𝕜 +
      ∑ i, ∑ j, ⟪(𝕜 ∙ ν)ᗮ.starProjection (u i), g⟫_𝕜 * (B (u i) (v j) * ⟪v j, w⟫_𝕜) := by
  -- The sums over `j` evaluate `B (u i)` and `B ν'` at `w`, and the sum over `i` then evaluates
  -- `B.flip w` at the projection `P g` of `g`. Then `g` is its projection onto `𝕜 ∙ ν` plus `P g`.
  have hP : ∑ i, ∑ j, ⟪(𝕜 ∙ ν)ᗮ.starProjection (u i), g⟫_𝕜 * (B (u i) (v j) * ⟪v j, w⟫_𝕜) =
      B ((𝕜 ∙ ν)ᗮ.starProjection g) w := by
    simp only [← Finset.mul_sum, v.sum_apply_mul_inner]
    simpa only [LinearMap.flip_apply, mul_comm] using
      u.sum_apply_mul_inner_starProjection (B.flip w) (𝕜 ∙ ν)ᗮ g
  have hν := TauCeti.apply_starProjection_singleton (B.flip w) ν g
  simp only [LinearMap.flip_apply, smul_eq_mul] at hν
  rw [v.sum_apply_mul_inner, hP, ← hν, ← LinearMap.add_apply, ← map_add,
    (𝕜 ∙ ν).starProjection_add_starProjection_orthogonal g]

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

end OrthonormalBasis

open scoped InnerProductSpace in
/-- The complex coordinate of `x` given by `Complex.isometryOfOrthonormal b` is
`⟪x, b₀⟫ + i ⟪x, b₁⟫`. -/
theorem Complex.isometryOfOrthonormal_symm_apply_eq_mk {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V) (x : V) :
    (Complex.isometryOfOrthonormal b).symm x = ⟨⟪x, b 0⟫_ℝ, ⟪x, b 1⟫_ℝ⟩ := by
  rw [Complex.isometryOfOrthonormal_symm_apply]
  apply Complex.ext <;> simp [b.coe_toBasis_repr_apply, b.repr_apply_apply, real_inner_comm]
