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
* `Orthonormal.norm_sum_conj_smul`, `Orthonormal.norm_sum_apply_smul_le`,
  `Orthonormal.sum_norm_apply_sq_le`, `Orthonormal.sum_norm_apply_mul_norm_apply_le`,
  `Orthonormal.norm_sum_apply_mul_apply_le`, `Orthonormal.sum_sum_norm_apply_mul_norm_apply_le`,
  and `Orthonormal.norm_sum_sum_apply_mul_apply_le`: conjugate-coefficient norm invariance,
  Bessel-type bounds, and termwise and outer Cauchy–Schwarz norm bounds for linear functionals and
  scalar-valued bilinear maps along orthonormal families.
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

end OrthonormalBasis

namespace Orthonormal

open scoped InnerProductSpace ComplexConjugate

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Conjugating the scalar coefficients in a linear combination of an orthonormal family `b`
preserves its norm: `‖∑ q ∈ s, conj (c q) • b q‖ = ‖∑ q ∈ s, c q • b q‖`. -/
theorem norm_sum_conj_smul {b : ι → E} (hb : Orthonormal 𝕜 b) (s : Finset ι)
    (c : ι → 𝕜) : ‖∑ q ∈ s, conj (c q) • b q‖ = ‖∑ q ∈ s, c q • b q‖ := by
  have hsq : ‖∑ q ∈ s, conj (c q) • b q‖ ^ 2 = ‖∑ q ∈ s, c q • b q‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), norm_sq_eq_re_inner (𝕜 := 𝕜), hb.inner_sum, hb.inner_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [RCLike.conj_conj, mul_comm]
  nlinarith [norm_nonneg (∑ q ∈ s, conj (c q) • b q), norm_nonneg (∑ q ∈ s, c q • b q)]

/-- For an orthonormal family `b` and a linear functional `θ` satisfying `‖θ z‖ ≤ C * ‖z‖`
(`0 ≤ C`), the linear combination `∑ q ∈ s, θ (b q) • b q` (which has the same norm as the
partial Riesz vector `∑ q ∈ s, conj (θ (b q)) • b q` by `Orthonormal.norm_sum_conj_smul`) has norm
at most `C`. -/
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

/-- Bessel-type bound for a bounded linear functional `θ` (`‖θ z‖ ≤ C * ‖z‖`) along an orthonormal
family `b`: `∑ q ∈ s, ‖θ (b q)‖ ^ 2 ≤ C ^ 2`. -/
theorem sum_norm_apply_sq_le {G : Type*} [FunLike G E 𝕜] [LinearMapClass G 𝕜 E 𝕜]
    {b : ι → E} (hb : Orthonormal 𝕜 b) (s : Finset ι) {θ : G} {C : ℝ}
    (hθ : ∀ z, ‖θ z‖ ≤ C * ‖z‖) :
    ∑ q ∈ s, ‖θ (b q)‖ ^ 2 ≤ C ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨q₀, _⟩
  · simpa using sq_nonneg C
  · have hC : 0 ≤ C := (norm_nonneg _).trans ((hθ (b q₀)).trans_eq (by simp [hb.1 q₀]))
    have hnorm : ∑ q ∈ s, ‖θ (b q)‖ ^ 2 = ‖∑ q ∈ s, θ (b q) • b q‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hb.inner_sum, map_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by rw [RCLike.conj_mul]; norm_cast
    rw [hnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb.norm_sum_apply_smul_le s hC hθ) 2

/-- Cauchy–Schwarz bound on the termwise-norm contraction `∑ q ∈ s, ‖φ (u q)‖ * ‖ψ (v q)‖` of two
bounded linear functionals along orthonormal families `u` in `E` and `v` in `F`. -/
theorem sum_norm_apply_mul_norm_apply_le {F G₁ G₂ : Type*}
    [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FunLike G₁ E 𝕜] [LinearMapClass G₁ 𝕜 E 𝕜]
    [FunLike G₂ F 𝕜] [LinearMapClass G₂ 𝕜 F 𝕜]
    {u : ι → E} (hu : Orthonormal 𝕜 u) {v : ι → F} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) {φ : G₁} {ψ : G₂} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ A * ‖z‖) (hψ : ∀ z, ‖ψ z‖ ≤ B * ‖z‖) :
    ∑ q ∈ s, ‖φ (u q)‖ * ‖ψ (v q)‖ ≤ A * B := by
  have hsq : (∑ q ∈ s, ‖φ (u q)‖ * ‖ψ (v q)‖) ^ 2 ≤ (A * B) ^ 2 := by
    calc (∑ q ∈ s, ‖φ (u q)‖ * ‖ψ (v q)‖) ^ 2
        ≤ (∑ q ∈ s, ‖φ (u q)‖ ^ 2) * (∑ q ∈ s, ‖ψ (v q)‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq s (fun q ↦ ‖φ (u q)‖) (fun q ↦ ‖ψ (v q)‖)
      _ ≤ A ^ 2 * B ^ 2 :=
          mul_le_mul (hu.sum_norm_apply_sq_le s hφ) (hv.sum_norm_apply_sq_le s hψ)
            (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg A)
      _ = (A * B) ^ 2 := by ring
  exact (sq_le_sq₀ (Finset.sum_nonneg fun _ _ ↦ by positivity) (mul_nonneg hA hB)).1 hsq

/-- Cauchy–Schwarz bound on the contraction `∑ q ∈ s, φ (u q) * ψ (v q)` of two bounded linear
functionals along orthonormal families `u` in `E` and `v` in `F`. -/
theorem norm_sum_apply_mul_apply_le {F G₁ G₂ : Type*}
    [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FunLike G₁ E 𝕜] [LinearMapClass G₁ 𝕜 E 𝕜]
    [FunLike G₂ F 𝕜] [LinearMapClass G₂ 𝕜 F 𝕜]
    {u : ι → E} (hu : Orthonormal 𝕜 u) {v : ι → F} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) {φ : G₁} {ψ : G₂} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hφ : ∀ z, ‖φ z‖ ≤ A * ‖z‖) (hψ : ∀ z, ‖ψ z‖ ≤ B * ‖z‖) :
    ‖∑ q ∈ s, φ (u q) * ψ (v q)‖ ≤ A * B := by
  calc ‖∑ q ∈ s, φ (u q) * ψ (v q)‖
      ≤ ∑ q ∈ s, ‖φ (u q) * ψ (v q)‖ := norm_sum_le _ _
    _ = ∑ q ∈ s, ‖φ (u q)‖ * ‖ψ (v q)‖ := Finset.sum_congr rfl fun _ _ ↦ norm_mul _ _
    _ ≤ A * B := hu.sum_norm_apply_mul_norm_apply_le hv s hA hB hφ hψ

/-- Cauchy–Schwarz bound on the termwise-norm double contraction
`∑ i ∈ s, ∑ j ∈ t, ‖Φ (u i) (v j)‖ * ‖Ψ (u i) (v j)‖` of two bounded scalar-valued bilinear maps
along orthonormal families `u` in `E` and `v` in `F`. -/
theorem sum_sum_norm_apply_mul_norm_apply_le {F κ : Type*}
    [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {u : ι → E} (hu : Orthonormal 𝕜 u) {v : κ → F} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) (t : Finset κ) {Φ Ψ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {A B : ℝ}
    (hΦ : ∀ x y, ‖Φ x y‖ ≤ A * ‖x‖ * ‖y‖) (hΨ : ∀ x y, ‖Ψ x y‖ ≤ B * ‖x‖ * ‖y‖) :
    ∑ i ∈ s, ∑ j ∈ t, ‖Φ (u i) (v j)‖ * ‖Ψ (u i) (v j)‖ ≤
      (min s.card t.card : ℕ) * (A * B) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, _⟩
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ⟨j₀, _⟩
  · simp
  have hA : 0 ≤ A :=
    (norm_nonneg _).trans ((hΦ (u i₀) (v j₀)).trans_eq (by simp [hu.1 i₀, hv.1 j₀]))
  have hB : 0 ≤ B :=
    (norm_nonneg _).trans ((hΨ (u i₀) (v j₀)).trans_eq (by simp [hu.1 i₀, hv.1 j₀]))
  have hleft : ∑ i ∈ s, ∑ j ∈ t, ‖Φ (u i) (v j)‖ * ‖Ψ (u i) (v j)‖ ≤ s.card * (A * B) := by
    calc ∑ i ∈ s, ∑ j ∈ t, ‖Φ (u i) (v j)‖ * ‖Ψ (u i) (v j)‖
        ≤ ∑ _i ∈ s, A * B := Finset.sum_le_sum fun i _ ↦
            hv.sum_norm_apply_mul_norm_apply_le hv t hA hB
              (fun z ↦ by simpa only [hu.1 i, mul_one] using hΦ (u i) z)
              (fun z ↦ by simpa only [hu.1 i, mul_one] using hΨ (u i) z)
      _ = s.card * (A * B) := by simp
  have hright : ∑ i ∈ s, ∑ j ∈ t, ‖Φ (u i) (v j)‖ * ‖Ψ (u i) (v j)‖ ≤ t.card * (A * B) := by
    rw [Finset.sum_comm]
    calc ∑ j ∈ t, ∑ i ∈ s, ‖Φ (u i) (v j)‖ * ‖Ψ (u i) (v j)‖
        ≤ ∑ _j ∈ t, A * B := Finset.sum_le_sum fun j _ ↦ by
            simpa only [LinearMap.flip_apply] using
              hu.sum_norm_apply_mul_norm_apply_le hu s hA hB
                (φ := Φ.flip (v j)) (ψ := Ψ.flip (v j))
                (fun z ↦ by simpa only [LinearMap.flip_apply, hv.1 j, mul_one] using hΦ z (v j))
                (fun z ↦ by simpa only [LinearMap.flip_apply, hv.1 j, mul_one] using hΨ z (v j))
      _ = t.card * (A * B) := by simp
  rw [Nat.cast_min, min_mul_of_nonneg _ _ (mul_nonneg hA hB)]
  exact le_min hleft hright

/-- Cauchy–Schwarz bound on the double contraction
`∑ i ∈ s, ∑ j ∈ t, Φ (u i) (v j) * Ψ (u i) (v j)` of two bounded scalar-valued bilinear maps along
orthonormal families `u` in `E` and `v` in `F`. -/
theorem norm_sum_sum_apply_mul_apply_le {F κ : Type*}
    [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {u : ι → E} (hu : Orthonormal 𝕜 u) {v : κ → F} (hv : Orthonormal 𝕜 v)
    (s : Finset ι) (t : Finset κ) {Φ Ψ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {A B : ℝ}
    (hΦ : ∀ x y, ‖Φ x y‖ ≤ A * ‖x‖ * ‖y‖) (hΨ : ∀ x y, ‖Ψ x y‖ ≤ B * ‖x‖ * ‖y‖) :
    ‖∑ i ∈ s, ∑ j ∈ t, Φ (u i) (v j) * Ψ (u i) (v j)‖ ≤
      (min s.card t.card : ℕ) * (A * B) := by
  calc ‖∑ i ∈ s, ∑ j ∈ t, Φ (u i) (v j) * Ψ (u i) (v j)‖
      ≤ ∑ i ∈ s, ‖∑ j ∈ t, Φ (u i) (v j) * Ψ (u i) (v j)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖Φ (u i) (v j) * Ψ (u i) (v j)‖ :=
        Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _
    _ = ∑ i ∈ s, ∑ j ∈ t, ‖Φ (u i) (v j)‖ * ‖Ψ (u i) (v j)‖ :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ norm_mul _ _
    _ ≤ (min s.card t.card : ℕ) * (A * B) :=
        hu.sum_sum_norm_apply_mul_norm_apply_le hv s t hΦ hΨ

end Orthonormal

open scoped InnerProductSpace in
/-- The complex coordinate of `x` given by `Complex.isometryOfOrthonormal b` is
`⟪x, b₀⟫ + i ⟪x, b₁⟫`. -/
theorem Complex.isometryOfOrthonormal_symm_apply_eq_mk {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V) (x : V) :
    (Complex.isometryOfOrthonormal b).symm x = ⟨⟪x, b 0⟫_ℝ, ⟪x, b 1⟫_ℝ⟩ := by
  rw [Complex.isometryOfOrthonormal_symm_apply]
  apply Complex.ext <;> simp [b.coe_toBasis_repr_apply, b.repr_apply_apply, real_inner_comm]
