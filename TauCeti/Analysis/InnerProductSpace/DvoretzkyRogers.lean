/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.InnerProductSpace.JohnEllipsoid

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# The Dvoretzky–Rogers lemma

Let `T : E ≃L[𝕜] F` be a maximal-volume ellipsoid (`ContinuousLinearEquiv.IsMaxVolumeEllipsoid`)
from an `n`-dimensional inner product space `E` over `ℝ` or `ℂ` into a normed space `F`, so that
the norm `x ↦ ‖T x‖` on `E` is in John's position: it is at most the Euclidean norm, and the
Euclidean unit ball is the inscribed ellipsoid of maximal volume. The **Dvoretzky–Rogers lemma**
says that such a norm cannot be much smaller than the Euclidean norm in many orthogonal directions:
there is an orthonormal basis `e₀, …, eₙ₋₁` of `E` with

`2 ^ (-n / (2 (n - j))) ≤ ‖T eⱼ‖` for every `j < n`.

In particular the first `⌊n / 2⌋` basis vectors have `‖T eⱼ‖ ≥ 1 / 2`. On their span the norm
`‖T ·‖` is therefore at least `1 / 2` on every vector of an orthonormal basis, which is the
hypothesis of the lower bound `c √(log m / m) / 32` on its average over the Euclidean sphere
(`LinearMap.mul_sqrt_log_finrank_div_le_integral_norm_comp_uniformSphereMeasure`) in the proof of
Dvoretzky's theorem.

The basis is built one vector at a time. If `K` is a subspace of `E` and `‖T z‖ ≤ a ‖z‖` for every
`z ∈ Kᗮ`, then rescaling `K` by `1 / √2` and `Kᗮ` by `1 / (√2 a)` gives the contraction
`y + z ↦ T (y / √2 + z / (√2 a))`, since `‖y‖ + ‖z‖ ≤ √2 ‖y + z‖`; its determinant relative to
`T` is `(1 / √2) ^ dim K (1 / (√2 a)) ^ dim Kᗮ`, so maximality of the volume forces
`2⁻¹ ^ n ≤ a ^ (2 dim Kᗮ)`
(`ContinuousLinearEquiv.IsMaxVolumeEllipsoid.inv_two_pow_finrank_le_pow_of_norm_apply_le`).
Taking for `a` the largest value of `‖T z‖` on the unit sphere of `Kᗮ`, where `K` is the span of
the vectors chosen so far, gives the next vector.

The bound `2 ^ (-n / (n - j))` often stated instead comes from the cruder estimate
`‖y‖ + ‖z‖ ≤ 2 ‖y + z‖`; the Pythagorean bound gives the stronger exponent.

## Main results

* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.inv_two_pow_finrank_le_pow_of_norm_apply_le`: if
  `T` shrinks the orthogonal complement of `K` by the factor `a`, then `2⁻¹ ^ n ≤ a ^ (2 dim Kᗮ)`.
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.exists_mem_orthogonal_inv_two_pow_finrank_le`: for
  every proper subspace `K` there is a unit vector `u ∈ Kᗮ` with
  `2⁻¹ ^ n ≤ ‖T u‖ ^ (2 dim Kᗮ)`.
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.exists_orthonormalBasis_rpow_le_norm_apply`: the
  **Dvoretzky–Rogers lemma**, an orthonormal basis with `2 ^ (-n / (2 (n - j))) ≤ ‖T eⱼ‖`.
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.exists_orthonormal_half_le_norm_apply`: there are
  `⌊n / 2⌋` orthonormal vectors `eⱼ` with `1 / 2 ≤ ‖T eⱼ‖`.

## References

* A. Dvoretzky and C. A. Rogers, *Absolute and unconditional convergence in normed linear spaces*,
  Proc. Nat. Acad. Sci. U.S.A. **36** (1950), 192–197.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Lemma 13.3.5.
-/

public section

open Module Metric
open scoped InnerProductSpace

namespace ContinuousLinearEquiv.IsMaxVolumeEllipsoid

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {T : E ≃L[𝕜] F}

/-- If `T` is a contraction with `‖T z‖ ≤ a ‖z‖` on `Kᗮ`, then `T` composed with the map scaling
`K` by `1 / √2` and `Kᗮ` by `1 / (√2 a)` is again a contraction, because
`‖y‖ + ‖z‖ ≤ √2 ‖y + z‖` for orthogonal `y` and `z`. -/
private theorem norm_comp_ofIsCompl_le_one (hT : ‖(T : E →L[𝕜] F)‖ ≤ 1) (K : Submodule 𝕜 E)
    {a : ℝ} (ha : 0 < a) (hK : ∀ z ∈ Kᗮ, ‖T z‖ ≤ a * ‖z‖) :
    ‖(T : E →L[𝕜] F).comp (LinearMap.toContinuousLinearMap <|
      LinearMap.ofIsCompl K.isCompl_orthogonal (K.subtype ∘ₗ ((((√2)⁻¹ : ℝ) : 𝕜) • LinearMap.id))
        (Kᗮ.subtype ∘ₗ ((((√2)⁻¹ / a : ℝ) : 𝕜) • LinearMap.id)))‖ ≤ 1 := by
  set β : ℝ := (√2)⁻¹ with hβ
  have hβ0 : 0 < β := by positivity
  have hβa : 0 < β / a := by positivity
  have hβ2 : β ^ 2 = 2⁻¹ := by rw [hβ, inv_pow, Real.sq_sqrt zero_le_two]
  set D : E →L[𝕜] E := LinearMap.toContinuousLinearMap <|
    LinearMap.ofIsCompl K.isCompl_orthogonal (K.subtype ∘ₗ ((β : 𝕜) • LinearMap.id))
      (Kᗮ.subtype ∘ₗ (((β / a : ℝ) : 𝕜) • LinearMap.id)) with hD_def
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  obtain ⟨y, z, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl K.isCompl_orthogonal x
  have hD : D (y + z) = (β : 𝕜) • (y : E) + ((β / a : ℝ) : 𝕜) • (z : E) := by simp [hD_def]
  have hTy : ‖T y‖ ≤ ‖(y : E)‖ := by
    simpa using (T : E →L[𝕜] F).le_of_opNorm_le hT (y : E)
  have hTz : β / a * ‖T z‖ ≤ β * ‖(z : E)‖ := by
    calc β / a * ‖T z‖ ≤ β / a * (a * ‖(z : E)‖) := by gcongr; exact hK z z.2
      _ = β * ‖(z : E)‖ := by field_simp
  have hyz := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (y : E) z
    (Submodule.inner_right_of_mem_orthogonal y.2 z.2)
  rw [ContinuousLinearMap.comp_apply, hD, ContinuousLinearEquiv.coe_coe, map_add, map_smul,
    map_smul, one_mul]
  calc _ ≤ β * ‖T y‖ + β / a * ‖T z‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_pos hβ0,
          abs_of_pos hβa]
    _ ≤ β * (‖(y : E)‖ + ‖(z : E)‖) := by nlinarith [mul_le_mul_of_nonneg_left hTy hβ0.le]
    _ ≤ ‖(y : E) + z‖ := by
        refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
        rw [mul_pow, hβ2]
        nlinarith [sq_nonneg (‖(y : E)‖ - ‖(z : E)‖)]

/-- If a maximal-volume ellipsoid `T` shrinks the orthogonal complement of a subspace `K` by the
factor `a`, that is `‖T z‖ ≤ a ‖z‖` for `z ∈ Kᗮ`, then `2⁻¹ ^ n ≤ a ^ (2 dim Kᗮ)`, where `n` is the
dimension of `E`. -/
theorem inv_two_pow_finrank_le_pow_of_norm_apply_le (hT : T.IsMaxVolumeEllipsoid)
    (K : Submodule 𝕜 E) {a : ℝ} (hK : ∀ z ∈ Kᗮ, ‖T z‖ ≤ a * ‖z‖) :
    (2⁻¹ : ℝ) ^ finrank 𝕜 E ≤ a ^ (2 * finrank 𝕜 Kᗮ) := by
  rcases eq_or_ne (finrank 𝕜 Kᗮ) 0 with h0 | h0
  · rw [h0, mul_zero, pow_zero]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  -- A nonzero vector of `Kᗮ` shows `0 < a`.
  have ha : 0 < a := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.finrank_eq_zero.not.1 h0)
    have h1 : 0 < ‖T z‖ := norm_pos_iff.2 ((map_ne_zero_iff T T.injective).2 hz0)
    have h2 : 0 < ‖z‖ := norm_pos_iff.2 hz0
    nlinarith [hK z hz]
  -- Scaling `K` by `β = 1 / √2` and `Kᗮ` by `β / a` keeps `T` a contraction, and multiplies its
  -- volume by `β ^ dim K * (β / a) ^ dim Kᗮ = β ^ n / a ^ dim Kᗮ`, which is therefore at most `1`.
  have hβ0 : 0 < (√2)⁻¹ := by positivity
  have hβa : 0 < (√2)⁻¹ / a := by positivity
  have hdet := hT.norm_det_le_one _ (norm_comp_ofIsCompl_le_one hT.norm_le_one K ha hK)
  rw [← ContinuousLinearMap.comp_assoc, T.coe_symm_comp_coe, ContinuousLinearMap.id_comp,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_ofIsCompl] at hdet
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, norm_mul, norm_pow,
    RCLike.norm_ofReal, abs_of_pos hβ0, abs_of_pos hβa, div_pow] at hdet
  rw [mul_div_assoc', ← pow_add, K.finrank_add_finrank_orthogonal, div_le_one (by positivity)]
    at hdet
  -- Squaring `β ^ n ≤ a ^ dim Kᗮ` gives the claim.
  calc (2⁻¹ : ℝ) ^ finrank 𝕜 E = ((√2)⁻¹ ^ finrank 𝕜 E) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul, inv_pow (√2), Real.sq_sqrt zero_le_two]
    _ ≤ (a ^ finrank 𝕜 Kᗮ) ^ 2 := pow_le_pow_left₀ (by positivity) hdet 2
    _ = a ^ (2 * finrank 𝕜 Kᗮ) := by rw [← pow_mul, mul_comm]

/-- **The Dvoretzky–Rogers step.** For a maximal-volume ellipsoid `T` and a proper subspace `K` of
`E`, some unit vector `u` orthogonal to `K` satisfies `2⁻¹ ^ n ≤ ‖T u‖ ^ (2 dim Kᗮ)`, where `n` is
the dimension of `E`. -/
theorem exists_mem_orthogonal_inv_two_pow_finrank_le (hT : T.IsMaxVolumeEllipsoid)
    {K : Submodule 𝕜 E} (hK : K ≠ ⊤) :
    ∃ u ∈ Kᗮ, ‖u‖ = 1 ∧ (2⁻¹ : ℝ) ^ finrank 𝕜 E ≤ ‖T u‖ ^ (2 * finrank 𝕜 Kᗮ) := by
  have : Nontrivial Kᗮ := Submodule.nontrivial_iff_ne_bot.2 (K.orthogonal_eq_bot_iff.not.2 hK)
  have : ProperSpace Kᗮ := FiniteDimensional.proper_rclike 𝕜 Kᗮ
  -- Take a unit vector `u` of `Kᗮ` on which `‖T u‖` is largest.
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : Kᗮ) 1).exists_isMaxOn
    (Set.nonempty_coe_sort.1 (NormedSpace.sphere_nonempty_rclike 𝕜 zero_le_one))
    (T.continuous.comp continuous_subtype_val).norm.continuousOn
  rw [mem_sphere_zero_iff_norm] at hu
  refine ⟨u, u.2, by simpa using hu, hT.inv_two_pow_finrank_le_pow_of_norm_apply_le K
    fun z hz ↦ ?_⟩
  -- Then `‖T z‖ ≤ ‖T u‖ ‖z‖` on `Kᗮ`.
  have hnorm : ‖(T : E →L[𝕜] F).comp Kᗮ.subtypeL‖ ≤ ‖T u‖ :=
    ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun x hx ↦
      hmax (mem_sphere_zero_iff_norm.2 hx)
  simpa using ((T : E →L[𝕜] F).comp Kᗮ.subtypeL).le_of_opNorm_le hnorm ⟨z, hz⟩

/-- The greedy construction: for every `k ≤ n` there are `k` orthonormal vectors `vᵢ` with
`2⁻¹ ^ n ≤ ‖T vᵢ‖ ^ (2 (n - i))`. -/
private theorem exists_orthonormal_inv_two_pow_finrank_le (hT : T.IsMaxVolumeEllipsoid) :
    ∀ k ≤ finrank 𝕜 E, ∃ v : Fin k → E, Orthonormal 𝕜 v ∧
      ∀ i, (2⁻¹ : ℝ) ^ finrank 𝕜 E ≤ ‖T (v i)‖ ^ (2 * (finrank 𝕜 E - i)) := by
  intro k hk
  induction k with
  | zero => exact ⟨Fin.elim0, orthonormal_iff_ite.2 (Fin.elim0 ·), (Fin.elim0 ·)⟩
  | succ k ih =>
    obtain ⟨v, hv, hvT⟩ := ih (Nat.le_of_succ_le hk)
    -- Add a vector orthogonal to the span `K` of the first `k` vectors.
    set K := Submodule.span 𝕜 (Set.range v)
    have hKk : finrank 𝕜 K = k := by
      simpa using finrank_span_eq_card hv.linearIndependent
    have hK : K ≠ ⊤ := fun h ↦ by
      rw [h, finrank_top] at hKk
      omega
    obtain ⟨u, huK, hu, huT⟩ := hT.exists_mem_orthogonal_inv_two_pow_finrank_le hK
    have hKu : finrank 𝕜 Kᗮ = finrank 𝕜 E - k := by
      have := K.finrank_add_finrank_orthogonal
      omega
    have hvu (i : Fin k) : ⟪v i, u⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i)) huK
    refine ⟨Fin.snoc v u, orthonormal_iff_ite.2 fun i j ↦ ?_, fun i ↦ ?_⟩
    · induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
        simp [inner_self_eq_norm_sq_to_K, hu, hvu, inner_eq_zero_symm.1 (hvu _),
          orthonormal_iff_ite.1 hv, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne']
    · induction i using Fin.lastCases with
      | last => simpa [hKu] using huT
      | cast i => simpa using hvT i

/-- **The Dvoretzky–Rogers lemma.** If `T : E ≃L[𝕜] F` is a maximal-volume ellipsoid from an
`n`-dimensional inner product space, then `E` has an orthonormal basis `e₀, …, eₙ₋₁` with
`2 ^ (-n / (2 (n - j))) ≤ ‖T eⱼ‖` for every `j`. In other words, a norm in John's position is at
least `2 ^ (-n / (2 (n - j)))` on the `j`-th vector of some orthonormal basis. -/
theorem exists_orthonormalBasis_rpow_le_norm_apply (hT : T.IsMaxVolumeEllipsoid) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E, ∀ j : Fin (finrank 𝕜 E),
      (2 : ℝ) ^ (-(finrank 𝕜 E : ℝ) / (2 * (finrank 𝕜 E - j : ℝ))) ≤ ‖T (b j)‖ := by
  set n := finrank 𝕜 E
  obtain ⟨v, hv, hvT⟩ := exists_orthonormal_inv_two_pow_finrank_le hT n le_rfl
  refine ⟨OrthonormalBasis.mk hv
    (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [n])).ge, fun j ↦ ?_⟩
  rw [OrthonormalBasis.coe_mk]
  -- Take the `2 (n - j)`-th root of `2⁻¹ ^ n ≤ ‖T eⱼ‖ ^ (2 (n - j))`.
  have hm : 2 * (n - j) ≠ 0 := by omega
  have hmR : ((2 * (n - j) : ℕ) : ℝ) = 2 * (n - j : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub j.2.le, Nat.cast_ofNat]
  calc (2 : ℝ) ^ (-(n : ℝ) / (2 * (n - j : ℝ)))
      = ((2⁻¹ : ℝ) ^ n) ^ (((2 * (n - j) : ℕ) : ℝ)⁻¹) := by
        rw [hmR, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
    _ ≤ (‖T (v j)‖ ^ (2 * (n - j))) ^ (((2 * (n - j) : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) (hvT j) (by positivity)
    _ = ‖T (v j)‖ := Real.pow_rpow_inv_natCast (norm_nonneg _) hm

/-- **Dvoretzky–Rogers on half the dimension.** A maximal-volume ellipsoid `T` from an
`n`-dimensional inner product space maps some `⌊n / 2⌋` orthonormal vectors to vectors of norm at
least `1 / 2`. -/
theorem exists_orthonormal_half_le_norm_apply (hT : T.IsMaxVolumeEllipsoid) :
    ∃ v : Fin (finrank 𝕜 E / 2) → E, Orthonormal 𝕜 v ∧ ∀ i, 1 / 2 ≤ ‖T (v i)‖ := by
  set n := finrank 𝕜 E
  obtain ⟨b, hb⟩ := hT.exists_orthonormalBasis_rpow_le_norm_apply
  refine ⟨b ∘ Fin.castLE (Nat.div_le_self n 2),
    b.orthonormal.comp _ (Fin.castLE_injective _), fun i ↦ ?_⟩
  refine le_trans ?_ (hb _)
  -- For `2 i < n` the exponent `-n / (2 (n - i))` is at least `-1`.
  have hi : 2 * (i : ℕ) < n := by omega
  have hiR : 2 * (i : ℝ) < n := by exact_mod_cast hi
  have hpos : 0 < 2 * ((n : ℝ) - i) := by linarith
  rw [one_div, ← Real.rpow_neg_one]
  refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
  rw [Fin.val_castLE, le_div_iff₀ hpos]
  linarith

end ContinuousLinearEquiv.IsMaxVolumeEllipsoid
