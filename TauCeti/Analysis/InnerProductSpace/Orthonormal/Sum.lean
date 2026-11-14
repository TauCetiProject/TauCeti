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
* `OrthonormalBasis.sum_apply_mul_inner_mul_inner`: a scalar-valued bilinear map `B` satisfies
  `∑ i, ∑ j, B (u i) (v j) * ⟪u i, x⟫ * ⟪v j, y⟫ = B x y` in a pair of orthonormal bases.
* `OrthonormalBasis.sum_inner_smul_rankOne`: an operator is the sum of its matrix coefficients
  times the corresponding rank-one operators.
* `OrthonormalBasis.sum_sum_inner_mul_inner_mul_inner`: the two-basis expansion
  `⟪x, T y⟫ = ∑ᵢ ∑ⱼ ⟪x, uᵢ⟫ ⟪uᵢ, T vⱼ⟫ ⟪vⱼ, y⟫`.
* `OrthonormalBasis.inner_sum_inner_smul`: expanding two vectors in `b` and reassembling along an
  orthonormal family `e` preserves their inner product,
  `⟪∑ i, ⟪b i, x⟫ • e i, ∑ i, ⟪b i, y⟫ • e i⟫ = ⟪x, y⟫`.
* `OrthonormalBasis.sum_mul_linearMap_orthonormalBasis` and
  `OrthonormalBasis.sum_mul_bilinForm_orthonormalBasis`: single and double contractions of real
  linear functionals and bilinear forms are independent of the orthonormal basis.
* `Orthonormal.norm_sum_apply_smul_le`, `Orthonormal.norm_sum_apply_mul_apply_le`, and
  `Orthonormal.norm_sum_mul_bilinForm_le`: Riesz-vector and Cauchy–Schwarz norm bounds for
  contractions of bounded linear functionals and bilinear forms along orthonormal families.
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

/-- The contraction `∑ a, φ (b₁ a) * ψ (b₁ a)` of two real linear functionals is independent of
the finite orthonormal basis. -/
theorem sum_mul_linearMap_orthonormalBasis {V α β : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype α] [Fintype β]
    (b₁ : OrthonormalBasis α ℝ V) (b₂ : OrthonormalBasis β ℝ V) (φ ψ : V →ₗ[ℝ] ℝ) :
    ∑ a, φ (b₁ a) * ψ (b₁ a) = ∑ p, φ (b₂ p) * ψ (b₂ p) := by
  calc ∑ a, φ (b₁ a) * ψ (b₁ a)
      = ∑ a, (∑ p, φ (b₂ p) * ⟪b₂ p, b₁ a⟫_ℝ) * ψ (b₁ a) := by
        simp_rw [b₂.sum_apply_mul_inner φ]
    _ = ∑ p, φ (b₂ p) * ∑ a, ψ (b₁ a) * ⟪b₁ a, b₂ p⟫_ℝ := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by rw [real_inner_comm (b₂ p)]; ring
    _ = ∑ p, φ (b₂ p) * ψ (b₂ p) := by
        simp_rw [b₁.sum_apply_mul_inner ψ]

/-- The double contraction `∑ a, ∑ b, F (b₁ a) (b₁ b) * G (b₁ a) (b₁ b)` of two real bilinear
forms is independent of the finite orthonormal basis. -/
theorem sum_mul_bilinForm_orthonormalBasis {V α β : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype α] [Fintype β]
    (b₁ : OrthonormalBasis α ℝ V) (b₂ : OrthonormalBasis β ℝ V)
    (F G : LinearMap.BilinForm ℝ V) :
    ∑ a, ∑ b, F (b₁ a) (b₁ b) * G (b₁ a) (b₁ b) =
      ∑ p, ∑ q, F (b₂ p) (b₂ q) * G (b₂ p) (b₂ q) := by
  calc ∑ a, ∑ b, F (b₁ a) (b₁ b) * G (b₁ a) (b₁ b)
      = ∑ a, ∑ q, F (b₁ a) (b₂ q) * G (b₁ a) (b₂ q) :=
        Finset.sum_congr rfl fun a _ ↦
          b₁.sum_mul_linearMap_orthonormalBasis b₂ (F (b₁ a)) (G (b₁ a))
    _ = ∑ q, ∑ a, F.flip (b₂ q) (b₁ a) * G.flip (b₂ q) (b₁ a) := by
        simp only [LinearMap.BilinForm.flip_apply]; exact Finset.sum_comm
    _ = ∑ q, ∑ p, F.flip (b₂ q) (b₂ p) * G.flip (b₂ q) (b₂ p) :=
        Finset.sum_congr rfl fun q _ ↦
          b₁.sum_mul_linearMap_orthonormalBasis b₂ (F.flip (b₂ q)) (G.flip (b₂ q))
    _ = ∑ p, ∑ q, F (b₂ p) (b₂ q) * G (b₂ p) (b₂ q) := by
        simp only [LinearMap.BilinForm.flip_apply]; exact Finset.sum_comm

end OrthonormalBasis

namespace Orthonormal

open scoped InnerProductSpace ComplexConjugate

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem norm_sum_conj_smul {b : ι → E} (hb : Orthonormal 𝕜 b) (s : Finset ι)
    (c : ι → 𝕜) : ‖∑ q ∈ s, conj (c q) • b q‖ = ‖∑ q ∈ s, c q • b q‖ := by
  have hsq : ‖∑ q ∈ s, conj (c q) • b q‖ ^ 2 = ‖∑ q ∈ s, c q • b q‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), norm_sq_eq_re_inner (𝕜 := 𝕜), hb.inner_sum, hb.inner_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ ↦ by
      rw [RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm]
  nlinarith [norm_nonneg (∑ q ∈ s, conj (c q) • b q), norm_nonneg (∑ q ∈ s, c q • b q)]

/-- For an orthonormal family `b` and a linear functional `θ` satisfying `‖θ z‖ ≤ C * ‖z‖`
(`0 ≤ C`), the partial Riesz sum `∑ q ∈ s, θ (b q) • b q` has norm at most `C`. -/
theorem norm_sum_apply_smul_le {G : Type*} [FunLike G E 𝕜] [LinearMapClass G 𝕜 E 𝕜]
    {b : ι → E} (hb : Orthonormal 𝕜 b) (s : Finset ι) {θ : G} {C : ℝ}
    (hC : 0 ≤ C) (hθ : ∀ z, ‖θ z‖ ≤ C * ‖z‖) :
    ‖∑ q ∈ s, θ (b q) • b q‖ ≤ C := by
  set w := ∑ q ∈ s, θ (b q) • b q
  set z := ∑ q ∈ s, conj (θ (b q)) • b q
  have hθz : θ z = (‖w‖ ^ 2 : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K, hb.inner_sum, map_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [map_smul, smul_eq_mul]
  have hle : ‖w‖ ^ 2 ≤ C * ‖w‖ := by
    calc ‖w‖ ^ 2 = ‖(‖w‖ ^ 2 : 𝕜)‖ := by simp
      _ = ‖θ z‖ := by rw [hθz]
      _ ≤ C * ‖z‖ := hθ z
      _ = C * ‖w‖ := by rw [norm_sum_conj_smul hb]
  nlinarith [norm_nonneg w]

/-- Cauchy–Schwarz bound on the contraction `∑ q ∈ s, φ (b q) * ψ (b q)` of two bounded linear
functionals along an orthonormal family `b`. -/
theorem norm_sum_apply_mul_apply_le {G₁ G₂ : Type*}
    [FunLike G₁ E 𝕜] [LinearMapClass G₁ 𝕜 E 𝕜]
    [FunLike G₂ E 𝕜] [LinearMapClass G₂ 𝕜 E 𝕜]
    {b : ι → E} (hb : Orthonormal 𝕜 b) (s : Finset ι) {φ : G₁} {ψ : G₂} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ A * ‖z‖) (hψ : ∀ z, ‖ψ z‖ ≤ B * ‖z‖) :
    ‖∑ q ∈ s, φ (b q) * ψ (b q)‖ ≤ A * B := by
  set x := ∑ q ∈ s, conj (φ (b q)) • b q
  set y := ∑ q ∈ s, ψ (b q) • b q
  have hxy : ∑ q ∈ s, φ (b q) * ψ (b q) = ⟪x, y⟫_𝕜 := by
    rw [hb.inner_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [RingHomCompTriple.comp_apply, RingHom.id_apply]
  have hx : ‖x‖ ≤ A := by
    rw [norm_sum_conj_smul hb]
    exact hb.norm_sum_apply_smul_le s hA hφ
  have hy : ‖y‖ ≤ B := hb.norm_sum_apply_smul_le s hB hψ
  rw [hxy]
  exact (norm_inner_le_norm x y).trans (mul_le_mul hx hy (norm_nonneg _) hA)

/-- Cauchy–Schwarz bound on the double contraction `∑ i ∈ s, ∑ j ∈ t, Φ (b i) (b j) * Ψ (b i) (b j)`
of two bounded bilinear forms along an orthonormal family `b`. -/
theorem norm_sum_mul_bilinForm_le {b : ι → E} (hb : Orthonormal 𝕜 b) (s t : Finset ι)
    {Φ Ψ : LinearMap.BilinForm 𝕜 E} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hΦ : ∀ x y, ‖Φ x y‖ ≤ A * ‖x‖ * ‖y‖) (hΨ : ∀ x y, ‖Ψ x y‖ ≤ B * ‖x‖ * ‖y‖) :
    ‖∑ i ∈ s, ∑ j ∈ t, Φ (b i) (b j) * Ψ (b i) (b j)‖ ≤ s.card * (A * B) := by
  calc ‖∑ i ∈ s, ∑ j ∈ t, Φ (b i) (b j) * Ψ (b i) (b j)‖
      ≤ ∑ i ∈ s, ‖∑ j ∈ t, Φ (b i) (b j) * Ψ (b i) (b j)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, A * B := Finset.sum_le_sum fun i _ ↦
        hb.norm_sum_apply_mul_apply_le t hA hB
          (fun z ↦ by simpa only [hb.1 i, mul_one] using hΦ (b i) z)
          (fun z ↦ by simpa only [hb.1 i, mul_one] using hΨ (b i) z)
    _ = s.card * (A * B) := by simp

end Orthonormal

open scoped InnerProductSpace in
/-- The complex coordinate of `x` given by `Complex.isometryOfOrthonormal b` is
`⟪x, b₀⟫ + i ⟪x, b₁⟫`. -/
theorem Complex.isometryOfOrthonormal_symm_apply_eq_mk {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V) (x : V) :
    (Complex.isometryOfOrthonormal b).symm x = ⟨⟪x, b 0⟫_ℝ, ⟪x, b 1⟫_ℝ⟩ := by
  rw [Complex.isometryOfOrthonormal_symm_apply]
  apply Complex.ext <;> simp [b.coe_toBasis_repr_apply, b.repr_apply_apply, real_inner_comm]
