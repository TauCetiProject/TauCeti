/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
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
* `OrthonormalBasis.sum_inner_self`: `∑ i, ⟪b i, b i⟫ = card ι`, the trace of the identity.
* `OrthonormalBasis.inner_eq_sum_repr`: the inner product in coordinates,
  `⟪x, y⟫ = ∑ i, conj (b.repr x i) * b.repr y i`.
* `OrthonormalBasis.real_inner_fin_two`: in a real plane with orthonormal basis `b`,
  `⟪x, y⟫ = ⟪x, b₀⟫ ⟪y, b₀⟫ + ⟪x, b₁⟫ ⟪y, b₁⟫`.
* `Complex.isometryOfOrthonormal_symm_apply_eq_mk`: in the same plane, the complex coordinate of
  `x` given by `Complex.isometryOfOrthonormal b` is `⟪x, b₀⟫ + i ⟪x, b₁⟫`.

A finite family of line projections comes from an orthonormal basis exactly when the projections
sum to the identity (`TauCeti.exists_orthonormalBasis_eq_rankOne_iff`). The forward implication
is Mathlib's `OrthonormalBasis.sum_rankOne_eq_id`.

Two unit vectors defining the same line projection differ by a scalar of norm one. Thus a
phase-invariant function on unit vectors has a well-defined value on each line projection, and
the characterization expresses its basis-sum condition in terms of projections. For this
frame-function condition, see A. M. Gleason, *Measures on the Closed Subspaces of a Hilbert
Space*, 1957, §1.
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

open scoped InnerProductSpace in
/-- The complex coordinate of `x` given by `Complex.isometryOfOrthonormal b` is
`⟪x, b₀⟫ + i ⟪x, b₁⟫`. -/
theorem Complex.isometryOfOrthonormal_symm_apply_eq_mk {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : OrthonormalBasis (Fin 2) ℝ V) (x : V) :
    (Complex.isometryOfOrthonormal b).symm x = ⟨⟪x, b 0⟫_ℝ, ⟪x, b 1⟫_ℝ⟩ := by
  rw [Complex.isometryOfOrthonormal_symm_apply]
  apply Complex.ext <;> simp [b.coe_toBasis_repr_apply, b.repr_apply_apply, real_inner_comm]

open InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An operator is a star projection with one-dimensional range exactly when it is the
rank-one operator of a unit vector. -/
theorem ContinuousLinearMap.isStarProjection_finrank_range_eq_one_iff [CompleteSpace E]
    {p : E →L[𝕜] E} :
    IsStarProjection p ∧ Module.finrank 𝕜 p.range = 1 ↔
      ∃ v : E, ‖v‖ = 1 ∧ p = rankOne 𝕜 v v := by
  constructor
  · rintro ⟨hp, hrank⟩
    have hpos : 0 < Module.finrank 𝕜 p.range := by simp [hrank]
    let : FiniteDimensional 𝕜 p.range := Module.finite_of_finrank_pos hpos
    let : Nontrivial p.range := Module.finrank_pos_iff.mp hpos
    let : NormedSpace ℝ p.range := NormedSpace.restrictScalars ℝ 𝕜 p.range
    obtain ⟨v, hv⟩ := exists_norm_eq p.range zero_le_one
    have hv0 : (v : E) ≠ 0 := by
      intro h
      have h' : v = 0 := Subtype.ext h
      simp [h'] at hv
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hrank v.property hv0
    have hproj : p = (𝕜 ∙ (v : E)).starProjection := by
      apply ContinuousLinearMap.IsStarProjection.ext hp isStarProjection_starProjection
      rwa [Submodule.range_starProjection]
    refine ⟨v, hv, hproj.trans ?_⟩
    ext x
    exact (Submodule.starProjection_unit_singleton 𝕜 (v := (v : E)) hv x).trans
      (rankOne_apply (𝕜 := 𝕜) (v : E) (v : E) x).symm
  · rintro ⟨v, hv, rfl⟩
    have hv0 : v ≠ 0 := by
      intro h
      simp [h] at hv
    exact ⟨isStarProjection_rankOne_self hv,
      Module.rank_eq_one_iff_finrank_eq_one.mp (rank_rankOne hv0 hv0)⟩

namespace TauCeti

/-- A finite family consists of the projections onto the lines of an orthonormal basis exactly
when each term is the rank-one projection of a unit vector and the terms sum to the identity. -/
theorem exists_orthonormalBasis_eq_rankOne_iff [Fintype ι] {p : ι → E →L[𝕜] E} :
    (∃ b : OrthonormalBasis ι 𝕜 E, ∀ i, p i = rankOne 𝕜 (b i) (b i)) ↔
      (∀ i, ∃ v : E, ‖v‖ = 1 ∧ p i = rankOne 𝕜 v v) ∧ (∑ i, p i = 1) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨fun i ↦ ⟨b i, b.norm_eq_one i, hb i⟩,
      (Finset.sum_congr rfl fun i _ ↦ hb i).trans b.sum_rankOne_eq_id⟩
  · rintro ⟨hunit, hsum⟩
    classical
    choose v hv hp using hunit
    have hsum_apply (x : E) : ∑ i, ⟪v i, x⟫_𝕜 • v i = x := by
      simpa only [sum_apply, hp, rankOne_apply, one_apply_eq_self] using
        DFunLike.congr_fun hsum x
    have hon : Orthonormal 𝕜 v := by
      refine ⟨hv, fun i j hij ↦ ?_⟩
      -- The inner product with `v j` leaves no contribution outside the diagonal term.
      have hsq := congrArg (fun x ↦ RCLike.re ⟪x, v j⟫_𝕜) (hsum_apply (v j))
      simp only [sum_inner, inner_smul_left, RCLike.conj_mul, map_sum, ← RCLike.ofReal_pow,
        RCLike.ofReal_re, inner_self_eq_norm_sq, hv j, one_pow] at hsq
      have hdiag : ‖⟪v j, v j⟫_𝕜‖ ^ 2 = 1 := by
        rw [inner_self_eq_one_of_norm_eq_one (hv j), norm_one, one_pow]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hdiag, add_eq_right] at hsq
      have hi := (Finset.sum_sq_eq_zero_iff _ _).mp hsq i
        (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
      exact norm_eq_zero.mp hi
    have hspan : ⊤ ≤ Submodule.span 𝕜 (Set.range v) := by
      intro x _
      exact (Submodule.mem_span_range_iff_exists_fun 𝕜).mpr ⟨_, hsum_apply x⟩
    refine ⟨OrthonormalBasis.mk hon hspan, fun i ↦ ?_⟩
    simpa only [OrthonormalBasis.coe_mk] using hp i

end TauCeti
