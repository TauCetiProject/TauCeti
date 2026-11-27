/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.Analysis.InnerProductSpace.Orthonormal.TangentialPart

/-!
# Recovering an endomorphism from its tangential values and one contraction

Let `w` be a unit vector of `ℝᵐ`, write `τⱼ = eⱼ - ⟪eⱼ, w⟫ w` for the parts of the coordinate
vectors orthogonal to `w`, and let `A` be a matrix with `λ ≤ ⟪A w, w⟫`, `λ > 0`. An endomorphism
`S` which is symmetric between `w` and each `τⱼ` is controlled by its values `S τⱼ` up to its
component `⟪S w, w⟫` (`ContinuousLinearMap.norm_sub_smul_smulRight_le`), and that component is
recovered from the contraction `∑ᵢⱼ Aᵢⱼ ⟪S eᵢ, eⱼ⟫` with `A`:

* `TauCeti.PDE.norm_le_sum_norm_apply_sub_add_abs_contraction`:
  `‖S‖ ≤ (2 + 2 m ‖A‖ / λ) ∑ⱼ ‖S τⱼ‖ + |∑ᵢⱼ Aᵢⱼ ⟪S eᵢ, eⱼ⟫| / λ`;
* `TauCeti.PDE.norm_sq_le_sum_norm_apply_sub_sq_add_contraction_sq`: its squared form, for
  `‖A‖ ≤ Λ`.

For `S` a Hessian at a flat boundary with unit normal `w`, the `S τⱼ` are the tangential columns and
the contraction is the non-divergence-form operator with coefficients `A`, so the equation recovers
the normal-normal second derivative.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace PDE

variable {m : ℕ}

/-- **An endomorphism is controlled by its tangential values and one contraction.** Let `w` be a
unit vector of `ℝᵐ`, write `τⱼ = eⱼ - ⟪eⱼ, w⟫ w` for the parts of the coordinate vectors
orthogonal to `w`, and let `A` be a matrix with `λ ≤ ⟪A w, w⟫`. If `S` is symmetric between `w` and
each `τⱼ`, then `S` is bounded by its values `S τⱼ` and by its contraction `∑ᵢⱼ Aᵢⱼ ⟪S eᵢ, eⱼ⟫`
with `A`: the component `⟪S w, w⟫`, which the `S τⱼ` do not see, is recovered from the
contraction. -/
theorem norm_le_sum_norm_apply_sub_add_abs_contraction
    {A : Matrix (Fin m) (Fin m) ℝ} {lam : ℝ} (hlam : 0 < lam)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) (hAw : lam ≤ matrixBilinearForm A w w)
    {τ : Fin m → EuclideanSpace ℝ (Fin m)}
    (hτ : ∀ j, τ j = EuclideanSpace.single j 1 - ⟪EuclideanSpace.single j 1, w⟫_ℝ • w)
    (S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hS : ∀ j, ⟪S w, τ j⟫_ℝ = ⟪S (τ j), w⟫_ℝ) :
    ‖S‖ ≤ (2 + 2 * m * ‖matrixBilinearForm A‖ / lam) * ∑ j, ‖S (τ j)‖ +
      |Matrix.contraction A S| / lam := by
  have hS₁norm := S.norm_sub_smul_smulRight_le (EuclideanSpace.basisFun (Fin m) ℝ) hw
    (fun j => by rw [hτ j, EuclideanSpace.basisFun_apply]) hS
  set Q := ∑ j, ‖S (τ j)‖
  set σ := ⟪S w, w⟫_ℝ
  set N : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (innerSL ℝ w).smulRight w with hN
  have hNnorm : ‖N‖ ≤ 1 := by
    rw [hN, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, hw, one_mul]
  set S₁ := S - σ • N with hS₁
  -- The contraction with `w ⊗ w` is `⟪A w, w⟫`.
  have hcN : Matrix.contraction A N = matrixBilinearForm A w w := by
    rw [Matrix.contraction_apply, matrixBilinearForm_apply_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hN, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, PiLp.smul_apply,
      smul_eq_mul]
    ring
  have hc : Matrix.contraction A S = Matrix.contraction A S₁ + σ * matrixBilinearForm A w w := by
    rw [← hcN, ← smul_eq_mul, ← map_smul, ← map_add, hS₁, sub_add_cancel]
  have hmb : 0 < matrixBilinearForm A w w := hlam.trans_le hAw
  have hσle : lam * |σ| ≤ |Matrix.contraction A S| + m * ‖matrixBilinearForm A‖ * (2 * Q) := by
    have h1 : |σ| * matrixBilinearForm A w w =
        |Matrix.contraction A S - Matrix.contraction A S₁| := by
      rw [hc, add_sub_cancel_left, abs_mul, abs_of_pos hmb]
    calc lam * |σ| ≤ |σ| * matrixBilinearForm A w w := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hAw (abs_nonneg σ)
      _ ≤ |Matrix.contraction A S| + |Matrix.contraction A S₁| := h1 ▸ abs_sub _ _
      _ ≤ _ := by
          gcongr
          exact (Matrix.abs_contraction_le_mul_norm_matrixBilinearForm_mul_norm A S₁).trans
            (mul_le_mul_of_nonneg_left hS₁norm (by positivity))
  have hSle : ‖S‖ ≤ 2 * Q + |σ| := by
    calc ‖S‖ = ‖S₁ + σ • N‖ := by rw [hS₁, sub_add_cancel]
      _ ≤ ‖S₁‖ + ‖σ • N‖ := norm_add_le _ _
      _ ≤ 2 * Q + |σ| * 1 := by
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
      _ = 2 * Q + |σ| := by rw [mul_one]
  have hσ' : |σ| ≤ (|Matrix.contraction A S| + m * ‖matrixBilinearForm A‖ * (2 * Q)) / lam :=
    (le_div_iff₀ hlam).2 (by rw [mul_comm]; exact hσle)
  calc ‖S‖ ≤ 2 * Q + (|Matrix.contraction A S| +
        m * ‖matrixBilinearForm A‖ * (2 * Q)) / lam := hSle.trans (by gcongr)
    _ = _ := by field_simp; ring

/-- The squared form of `TauCeti.PDE.norm_le_sum_norm_apply_sub_add_abs_contraction`, with
`‖A‖ ≤ Λ`: `‖S‖² ≤ 2 m (2 + 2 m Λ / λ)² ∑ⱼ ‖S τⱼ‖² + 2 / λ² (∑ᵢⱼ Aᵢⱼ ⟪S eᵢ, eⱼ⟫)²`. -/
theorem norm_sq_le_sum_norm_apply_sub_sq_add_contraction_sq
    {A : Matrix (Fin m) (Fin m) ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hΛ : ‖matrixBilinearForm A‖ ≤ Lam)
    {w : EuclideanSpace ℝ (Fin m)} (hw : ‖w‖ = 1) (hAw : lam ≤ matrixBilinearForm A w w)
    {τ : Fin m → EuclideanSpace ℝ (Fin m)}
    (hτ : ∀ j, τ j = EuclideanSpace.single j 1 - ⟪EuclideanSpace.single j 1, w⟫_ℝ • w)
    (S : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hS : ∀ j, ⟪S w, τ j⟫_ℝ = ⟪S (τ j), w⟫_ℝ) :
    ‖S‖ ^ 2 ≤ 2 * m * (2 + 2 * m * Lam / lam) ^ 2 * ∑ j, ‖S (τ j)‖ ^ 2 +
      2 / lam ^ 2 * Matrix.contraction A S ^ 2 := by
  set Q := ∑ j, ‖S (τ j)‖
  have hQ2 : Q ^ 2 ≤ m * ∑ j, ‖S (τ j)‖ ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖S (τ j)‖)
  have h1 : ‖S‖ ≤ (2 + 2 * m * Lam / lam) * Q + |Matrix.contraction A S| / lam :=
    (norm_le_sum_norm_apply_sub_add_abs_contraction hlam hw hAw hτ S hS).trans (by gcongr)
  calc ‖S‖ ^ 2 ≤ ((2 + 2 * m * Lam / lam) * Q + |Matrix.contraction A S| / lam) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ 2 * ((2 + 2 * m * Lam / lam) * Q) ^ 2 + 2 * (|Matrix.contraction A S| / lam) ^ 2 := by
        nlinarith [sq_nonneg ((2 + 2 * m * Lam / lam) * Q - |Matrix.contraction A S| / lam)]
    _ = 2 * (2 + 2 * m * Lam / lam) ^ 2 * Q ^ 2 + 2 / lam ^ 2 * Matrix.contraction A S ^ 2 := by
        rw [div_pow, sq_abs]
        ring
    _ ≤ 2 * (2 + 2 * m * Lam / lam) ^ 2 * (m * ∑ j, ‖S (τ j)‖ ^ 2) +
          2 / lam ^ 2 * Matrix.contraction A S ^ 2 := by gcongr
    _ = _ := by ring

end PDE

end TauCeti
