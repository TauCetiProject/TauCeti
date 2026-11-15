/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Expansions and contractions against orthonormal bases

Finite sums over orthonormal bases recover linear maps from their matrix coefficients and
contract tensors in orthonormal frames, for instance when tracing the Ricci tensor to scalar
curvature:

* `OrthonormalBasis.sum_apply_mul_inner`: a linear functional `ℓ` satisfies
  `∑ i, ℓ (b i) * ⟪b i, a⟫ = ℓ a`, the expansion of `a` in `b` pushed through `ℓ`.
* `OrthonormalBasis.sum_conj_apply_mul_apply_eq` and `OrthonormalBasis.sum_apply_mul_apply_eq`:
  contracting two linear functionals `∑ i, conj (ℓ₁ (b i)) * ℓ₂ (b i)` does not depend on the
  orthonormal basis `b`, and `OrthonormalBasis.sum_sum_conj_apply_mul_apply_eq` and
  `OrthonormalBasis.sum_sum_apply_mul_apply_eq` give the same basis independence for double
  contractions of bilinear forms.
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

/-- Contracting two linear functionals over a finite orthonormal basis does not depend on the
basis: `∑ i, conj (ℓ₁ (b₁ i)) * ℓ₂ (b₁ i) = ∑ j, conj (ℓ₁ (b₂ j)) * ℓ₂ (b₂ j)`. -/
theorem sum_conj_apply_mul_apply_eq {ι' F₁ F₂ : Type*} [Fintype ι']
    [FunLike F₁ E 𝕜] [LinearMapClass F₁ 𝕜 E 𝕜] [FunLike F₂ E 𝕜] [LinearMapClass F₂ 𝕜 E 𝕜]
    (b₁ : OrthonormalBasis ι 𝕜 E) (b₂ : OrthonormalBasis ι' 𝕜 E) (ℓ₁ : F₁) (ℓ₂ : F₂) :
    ∑ i, conj (ℓ₁ (b₁ i)) * ℓ₂ (b₁ i) = ∑ j, conj (ℓ₁ (b₂ j)) * ℓ₂ (b₂ j) := by
  calc ∑ i, conj (ℓ₁ (b₁ i)) * ℓ₂ (b₁ i)
      = ∑ i, conj (ℓ₁ (b₁ i)) * ∑ j, ℓ₂ (b₂ j) * ⟪b₂ j, b₁ i⟫_𝕜 := by
        simp_rw [b₂.sum_apply_mul_inner ℓ₂]
    _ = ∑ j, (∑ i, conj (ℓ₁ (b₁ i)) * ⟪b₂ j, b₁ i⟫_𝕜) * ℓ₂ (b₂ j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ∑ j, conj (ℓ₁ (b₂ j)) * ℓ₂ (b₂ j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← b₁.sum_apply_mul_inner ℓ₁ (b₂ j), map_sum]
        simp_rw [map_mul, inner_conj_symm]

/-- Contracting two real linear functionals over a finite orthonormal basis does not depend on the
basis: `∑ i, ℓ₁ (b₁ i) * ℓ₂ (b₁ i) = ∑ j, ℓ₁ (b₂ j) * ℓ₂ (b₂ j)`. -/
theorem sum_apply_mul_apply_eq {V ι₁ ι₂ F₁ F₂ : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype ι₁] [Fintype ι₂]
    [FunLike F₁ V ℝ] [LinearMapClass F₁ ℝ V ℝ] [FunLike F₂ V ℝ] [LinearMapClass F₂ ℝ V ℝ]
    (b₁ : OrthonormalBasis ι₁ ℝ V) (b₂ : OrthonormalBasis ι₂ ℝ V) (ℓ₁ : F₁) (ℓ₂ : F₂) :
    ∑ i, ℓ₁ (b₁ i) * ℓ₂ (b₁ i) = ∑ j, ℓ₁ (b₂ j) * ℓ₂ (b₂ j) := by
  simpa using b₁.sum_conj_apply_mul_apply_eq b₂ ℓ₁ ℓ₂

/-- Double contraction of two bilinear forms over finite orthonormal bases does not depend on the
bases: `∑ i, ∑ j, conj (B₁ (u₁ i) (v₁ j)) * B₂ (u₁ i) (v₁ j) =
∑ p, ∑ q, conj (B₁ (u₂ p) (v₂ q)) * B₂ (u₂ p) (v₂ q)`. -/
theorem sum_sum_conj_apply_mul_apply_eq {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    (u₁ : OrthonormalBasis ι 𝕜 E) (u₂ : OrthonormalBasis ι' 𝕜 E)
    (v₁ : OrthonormalBasis κ 𝕜 F) (v₂ : OrthonormalBasis κ' 𝕜 F)
    (B₁ B₂ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    ∑ i, ∑ j, conj (B₁ (u₁ i) (v₁ j)) * B₂ (u₁ i) (v₁ j) =
      ∑ p, ∑ q, conj (B₁ (u₂ p) (v₂ q)) * B₂ (u₂ p) (v₂ q) := by
  calc ∑ i, ∑ j, conj (B₁ (u₁ i) (v₁ j)) * B₂ (u₁ i) (v₁ j)
      = ∑ i, ∑ q, conj (B₁ (u₁ i) (v₂ q)) * B₂ (u₁ i) (v₂ q) :=
        Finset.sum_congr rfl fun i _ ↦ v₁.sum_conj_apply_mul_apply_eq v₂ (B₁ (u₁ i)) (B₂ (u₁ i))
    _ = ∑ q, ∑ i, conj (B₁.flip (v₂ q) (u₁ i)) * B₂.flip (v₂ q) (u₁ i) := Finset.sum_comm
    _ = ∑ q, ∑ p, conj (B₁.flip (v₂ q) (u₂ p)) * B₂.flip (v₂ q) (u₂ p) :=
        Finset.sum_congr rfl fun q _ ↦
          u₁.sum_conj_apply_mul_apply_eq u₂ (B₁.flip (v₂ q)) (B₂.flip (v₂ q))
    _ = ∑ p, ∑ q, conj (B₁ (u₂ p) (v₂ q)) * B₂ (u₂ p) (v₂ q) := Finset.sum_comm

/-- Double contraction of two real bilinear forms over finite orthonormal bases does not depend on
the bases:
`∑ i, ∑ j, B₁ (u₁ i) (v₁ j) * B₂ (u₁ i) (v₁ j) = ∑ p, ∑ q, B₁ (u₂ p) (v₂ q) * B₂ (u₂ p) (v₂ q)`. -/
theorem sum_sum_apply_mul_apply_eq {V W ι₁ ι₂ κ₁ κ₂ : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [Fintype ι₁] [Fintype ι₂] [Fintype κ₁] [Fintype κ₂]
    (u₁ : OrthonormalBasis ι₁ ℝ V) (u₂ : OrthonormalBasis ι₂ ℝ V)
    (v₁ : OrthonormalBasis κ₁ ℝ W) (v₂ : OrthonormalBasis κ₂ ℝ W)
    (B₁ B₂ : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) :
    ∑ i, ∑ j, B₁ (u₁ i) (v₁ j) * B₂ (u₁ i) (v₁ j) =
      ∑ p, ∑ q, B₁ (u₂ p) (v₂ q) * B₂ (u₂ p) (v₂ q) := by
  simpa using u₁.sum_sum_conj_apply_mul_apply_eq u₂ v₁ v₂ B₁ B₂

end OrthonormalBasis

open scoped InnerProductSpace in
/-- The complex coordinate of `x` given by `Complex.isometryOfOrthonormal b` is
`⟪x, b₀⟫ + i ⟪x, b₁⟫`. -/
theorem Complex.isometryOfOrthonormal_symm_apply_eq_mk {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V) (x : V) :
    (Complex.isometryOfOrthonormal b).symm x = ⟨⟪x, b 0⟫_ℝ, ⟪x, b 1⟫_ℝ⟩ := by
  rw [Complex.isometryOfOrthonormal_symm_apply]
  apply Complex.ext <;> simp [b.coe_toBasis_repr_apply, b.repr_apply_apply, real_inner_comm]
