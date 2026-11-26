/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Hua's integral bound for complex matrices

This file proves Hua's integral bound for negative powers of `‖det (M + Yᴴ Y)‖` over spaces of
complex matrices, where `M` is positive definite.

## Main results

* `TauCeti.norm_det_star_mul_self_add_vecMulVec`: for any complex square matrix `C` and row vector
  `y`, `‖det (Cᴴ C + (y C)ᴴ (y C))‖ = ‖det C‖² (1 + ∑ j, ‖y j‖²)`.
* `TauCeti.lintegral_one_add_sum_norm_sq_inv_pow`: the integral of `(1 + ∑ j, ‖y j‖²) ^ (-(k + 1))`
  over `ℂ ^ κ` (`k = Fintype.card κ`) equals `π ^ k / k!`.
* `TauCeti.lintegral_norm_det_add_vecMulVec_inv_pow_le`: one-row Hua bound.
* `TauCeti.hua_integral_le`: iterated marginal Hua bound over a finite set of rows `s`.
* `TauCeti.lintegral_comp_mul_add`: change of variables `A ↦ S A + c` on `ι → κ → ℂ`.
* `TauCeti.lintegral_norm_det_add_conjTranspose_mul_inv_pow_le`: Hua's bound over `ι → κ → ℂ`
  matrices, for any `S` with `S.det ≠ 0` and positive definite `G`.
-/

public section

open Fintype Function Matrix MeasureTheory Real
open scoped ComplexOrder MatrixOrder

namespace TauCeti

/-- For a square complex matrix `C` and a row vector `y`,
`‖det (star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C))‖ = ‖det C‖² (1 + ∑ j, ‖y j‖²)`. -/
theorem norm_det_star_mul_self_add_vecMulVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : Matrix κ κ ℂ) (y : κ → ℂ) :
    ‖(star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C)).det‖ =
      ‖C.det‖ ^ 2 * (1 + ∑ j : κ, ‖y j‖ ^ 2) := by
  have h_factor : star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C) =
      star C * (1 + vecMulVec (star y) y) * C := by
    simp [mul_add, add_mul, star_vecMul, mul_vecMulVec, vecMulVec_mul, star_eq_conjTranspose]
  have h_det : (1 + vecMulVec (star y) y).det = (1 + ∑ j, ‖y j‖ ^ 2 : ℝ) := by
    simp [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct, RCLike.mul_conj]
  rw [h_factor, det_mul, det_mul, h_det, star_eq_conjTranspose, det_conjTranspose, norm_mul,
    norm_mul, norm_star, Complex.norm_of_nonneg (by positivity)]
  ring

/-- The Gamma integral as a lower Lebesgue integral on `(0, ∞)`. -/
private lemma lintegral_const_mul_rpow_mul_exp_neg_mul_Ioi {b r K : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hK : 0 < K) :
    ∫⁻ t : ℝ in Set.Ioi 0, ENNReal.ofReal (K * (t ^ (b - 1) * rexp (-(r * t)))) =
      ENNReal.ofReal (K * ((1 / r) ^ b * Gamma b)) := by
  have h_int : ∫ t : ℝ in Set.Ioi 0, K * (t ^ (b - 1) * rexp (-(r * t))) =
      K * ((1 / r) ^ b * Gamma b) := by
    rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi hb hr]
  have h_ne : K * ((1 / r) ^ b * Gamma b) ≠ 0 := by
    have := Gamma_pos_of_pos hb
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (h_int.trans_ne h_ne))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦ by positivity), h_int]

/-- The Gaussian integral of `exp (-t ∑ j, ‖y j‖²)` over `y : κ → ℂ` for `t > 0` is
`(π / t) ^ card κ`. -/
private lemma integral_rexp_neg_mul_sum_norm_sq {κ : Type*} [Fintype κ] {t : ℝ} (ht : 0 < t) :
    ∫ y : κ → ℂ, rexp (-t * ∑ j : κ, ‖y j‖ ^ 2) = (π / t) ^ card κ := by
  have h_eq (y : κ → ℂ) : rexp (-t * ∑ j : κ, ‖y j‖ ^ 2) = ∏ j : κ, rexp (-t * ‖y j‖ ^ 2) := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h_eq]
  rw [integral_fintype_prod_volume_eq_prod (f := fun (_ : κ) (z : ℂ) ↦ rexp (-t * ‖z‖ ^ 2))]
  have h1 : ∫ z : ℂ, rexp (-t * ‖z‖ ^ 2) = π / t := by
    simpa [Complex.finrank_real_complex] using
      GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) ht
  rw [Finset.prod_const, Finset.card_univ, h1]

/-- The integral of `(1 + ∑ j, ‖y j‖²) ^ (-(k + 1))` over `y : κ → ℂ` (`k = card κ`) is
`π ^ k / k!`. -/
theorem lintegral_one_add_sum_norm_sq_inv_pow {κ : Type*} [Fintype κ] :
    ∫⁻ y : κ → ℂ, ENNReal.ofReal ((1 + ∑ j : κ, ‖y j‖ ^ 2)⁻¹ ^ (card κ + 1)) =
      ENNReal.ofReal (π ^ card κ / (card κ).factorial) := by
  set k : ℕ := card κ
  let F (y : κ → ℂ) (t : ℝ) : ℝ :=
    (Gamma (k + 1))⁻¹ * (t ^ (k : ℝ) * rexp (-((1 + ∑ j : κ, ‖y j‖ ^ 2) * t)))
  have h_gpos : 0 < Gamma ((k : ℝ) + 1) := Gamma_pos_of_pos (by positivity)
  have h_point (y : κ → ℂ) :
      ENNReal.ofReal ((1 + ∑ j : κ, ‖y j‖ ^ 2)⁻¹ ^ (k + 1)) =
        ∫⁻ t : ℝ in Set.Ioi 0, ENNReal.ofReal (F y t) := by
    have h_pos : 0 < 1 + ∑ j : κ, ‖y j‖ ^ 2 := by positivity
    have h_eq : (1 + ∑ j : κ, ‖y j‖ ^ 2)⁻¹ ^ (k + 1) =
        (Gamma (k + 1))⁻¹ * ((1 / (1 + ∑ j : κ, ‖y j‖ ^ 2)) ^ ((k : ℝ) + 1) * Gamma (k + 1)) := by
      rw [one_div, rpow_add_one (by positivity), rpow_natCast, pow_succ]
      field_simp [k]
    rw [h_eq, ← lintegral_const_mul_rpow_mul_exp_neg_mul_Ioi (b := (k : ℝ) + 1) (by positivity)
      h_pos (inv_pos.2 h_gpos)]
    simp [F]
  have h_slice (t : ℝ) (ht : 0 < t) :
      ∫⁻ y : κ → ℂ, ENNReal.ofReal (F y t) =
        ENNReal.ofReal (π ^ k / Gamma (k + 1) * (t ^ ((1 : ℝ) - 1) * rexp (-(1 * t)))) := by
    have h_int : ∫ y : κ → ℂ, F y t =
        π ^ k / Gamma (k + 1) * (t ^ ((1 : ℝ) - 1) * rexp (-(1 * t))) := by
      have h_split (y : κ → ℂ) :
          F y t = (Gamma (k + 1))⁻¹ * t ^ (k : ℝ) * rexp (-t) * rexp (-t * ∑ j : κ, ‖y j‖ ^ 2) := by
        simp only [F, mul_assoc, ← Real.exp_add]
        ring_nf
      simp_rw [h_split]
      rw [integral_const_mul, integral_rexp_neg_mul_sum_norm_sq ht, rpow_natCast, div_pow,
        sub_self, rpow_zero, one_mul, one_mul]
      dsimp only [k]
      field_simp
    have h_ne : π ^ k / Gamma (k + 1) * (t ^ ((1 : ℝ) - 1) * rexp (-(1 * t))) ≠ 0 := by positivity
    rw [← ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (h_int.trans_ne h_ne))
      (.of_forall fun y ↦ show 0 ≤ F y t by positivity), h_int]
  rw [lintegral_congr h_point, lintegral_lintegral_swap (by fun_prop),
    setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ h_slice t (Set.mem_Ioi.1 ht),
    lintegral_const_mul_rpow_mul_exp_neg_mul_Ioi one_pos one_pos (by positivity)]
  simp [Gamma_nat_eq_factorial, k]

/-- Change of variables on `κ → ℂ` for an invertible complex matrix `u`. -/
private lemma lintegral_eq_norm_det_sq_mul_lintegral_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    (u : Matrix κ κ ℂ) (hu : u.det ≠ 0) (g : (κ → ℂ) → ENNReal) :
    ∫⁻ y : κ → ℂ, g y = ENNReal.ofReal (‖u.det‖ ^ 2) * ∫⁻ y : κ → ℂ, g (u *ᵥ y) := by
  let f : (κ → ℂ) →ₗ[ℝ] (κ → ℂ) := u.toLin'.restrictScalars ℝ
  have h_det : LinearMap.det f = ‖u.det‖ ^ 2 := by
    simp [f, LinearMap.det_restrictScalars, Algebra.norm_complex_eq, ← Complex.sq_norm]
  have h_emb : MeasurableEmbedding (fun y : κ → ℂ ↦ u *ᵥ y) :=
    Continuous.measurableEmbedding (by fun_prop) (mulVec_injective_of_det_ne_zero hu)
  have h_map : (volume : Measure (κ → ℂ)).map f = (ENNReal.ofReal (‖u.det‖ ^ 2))⁻¹ • volume := by
    simp [Measure.map_linearMap_addHaar_eq_smul_addHaar, h_det, hu]
  rw [← h_emb.lintegral_map]
  change _ = ENNReal.ofReal (‖u.det‖ ^ 2) * ∫⁻ y, g y ∂volume.map f
  rw [h_map]
  simp [ENNReal.mul_inv_cancel_left, hu]

/-- One row of Hua's bound: for positive definite `M`, invertible `S`, and `r ≥ card κ`,
`∫⁻ v, ‖det (M + (v S + a)ᴴ (v S + a))‖⁻¹ ^ (r + 1) ≤ (π^k / (k! ‖det S‖²)) ‖det M‖⁻¹ ^ r`. -/
theorem lintegral_norm_det_add_vecMulVec_inv_pow_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M S : Matrix κ κ ℂ} (hM : M.PosDef) (hS : det S ≠ 0) (a : κ → ℂ) {r : ℕ} (hr : card κ ≤ r) :
    ∫⁻ v : κ → ℂ,
        ENNReal.ofReal (‖(M + vecMulVec (star (v ᵥ* S + a)) (v ᵥ* S + a)).det‖⁻¹ ^ (r + 1)) ≤
      ENNReal.ofReal (π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2 * ‖M.det‖⁻¹ ^ r) := by
  obtain ⟨C, hC_unit, rfl⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hM.isStrictlyPositive
  have hC : C.det ≠ 0 := (C.isUnit_iff_isUnit_det.1 hC_unit).ne_zero
  have h_subst (y : κ → ℂ) : ((C * S⁻¹)ᵀ *ᵥ y + -a ᵥ* S⁻¹) ᵥ* S + a = y ᵥ* C := by
    rw [mulVec_transpose]
    simp [add_vecMul, hS]
  let B : ℝ := ‖(star C * C).det‖⁻¹ ^ r / ‖S.det‖ ^ 2
  have h_jacobian (u : ℝ) :
      ‖(C * S⁻¹)ᵀ.det‖ ^ 2 * (‖C.det‖ ^ 2 * u)⁻¹ ^ (r + 1) = B * u⁻¹ ^ (r + 1) := by
    simp [B, pow_succ _ r, star_eq_conjTranspose, mul_pow, field, ← pow_mul, mul_comm 2 r]
  calc
    _ = ∫⁻ y : κ → ℂ, ENNReal.ofReal (‖(C * S⁻¹)ᵀ.det‖ ^ 2) *
          ENNReal.ofReal ((‖C.det‖ ^ 2 * (1 + ∑ j, ‖y j‖ ^ 2))⁻¹ ^ (r + 1)) := by
      rw [← lintegral_add_right_eq_self _ (-a ᵥ* S⁻¹),
        lintegral_eq_norm_det_sq_mul_lintegral_mulVec (C * S⁻¹)ᵀ (by simp [hC, hS]),
        ← lintegral_const_mul' _ _ (by finiteness)]
      simp_rw [h_subst, norm_det_star_mul_self_add_vecMulVec]
    _ ≤ ∫⁻ y : κ → ℂ,
          ENNReal.ofReal B * ENNReal.ofReal ((1 + ∑ j, ‖y j‖ ^ 2)⁻¹ ^ (card κ + 1)) := by
      refine lintegral_mono fun y ↦ ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), h_jacobian]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))) (Nat.succ_le_succ hr)
    _ = ENNReal.ofReal
          (π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2 * ‖(star C * C).det‖⁻¹ ^ r) := by
      rw [lintegral_const_mul' _ _ (by finiteness), lintegral_one_add_sum_norm_sq_inv_pow,
        ← ENNReal.ofReal_mul (by positivity)]
      simp only [B]
      ring_nf

/-- **Hua's integral bound** (iterated marginal form): for positive definite `M`, invertible `S`,
`c ≥ 0`, `r ≥ card κ`, and a finite set of rows `s`, the iterated lower Lebesgue integral of
`c ‖det (M + ∑ i ∈ s, (y i S + a i)ᴴ (y i S + a i))‖⁻¹ ^ (s.card + r)` over `i ∈ s` is at most
`c (π^k / (k! ‖det S‖²)) ^ s.card ‖det M‖⁻¹ ^ r`. -/
theorem hua_integral_le {ι κ : Type} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {M : Matrix κ κ ℂ} (S : Matrix κ κ ℂ) (hS : det S ≠ 0) (a : ι → κ → ℂ) (hM : M.PosDef) {c : ℝ}
    (hc : 0 ≤ c) (s : Finset ι) {r : ℕ} (hr : card κ ≤ r) (x : ι → κ → ℂ) :
    (∫⋯∫⁻_s, fun y : ι → κ → ℂ ↦ ENNReal.ofReal (c *
        ‖(M + ∑ i ∈ s, vecMulVec (star (y i ᵥ* S + a i)) (y i ᵥ* S + a i)).det‖⁻¹ ^
          (s.card + r))) x ≤
      ENNReal.ofReal
        (c * ((π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2) ^ s.card * ‖M.det‖⁻¹ ^ r)) := by
  set K : ℝ := π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2
  have hK : 0 ≤ K := by positivity
  induction s using Finset.induction generalizing M r x with
  | empty => simp
  | insert i s hi ih =>
    let F (A : Matrix κ κ ℂ) (t : Finset ι) (n : ℕ) (x' : ι → κ → ℂ) : ENNReal :=
      ENNReal.ofReal (c *
        ‖(A + ∑ j ∈ t, vecMulVec (star (x' j ᵥ* S + a j)) (x' j ᵥ* S + a j)).det‖⁻¹ ^ n)
    let M' (v : κ → ℂ) : Matrix κ κ ℂ := M + vecMulVec (star (v ᵥ* S + a i)) (v ᵥ* S + a i)
    have h_pos (v : κ → ℂ) : (M' v).PosDef := hM.add_posSemidef (posSemidef_vecMulVec_star_self _)
    have inner_eq (v : κ → ℂ) :
        (∫⋯∫⁻_s, F M (insert i s) ((insert i s).card + r)) (update x i v) =
          (∫⋯∫⁻_s, F (M' v) s (s.card + (r + 1))) (update x i v) :=
      lintegral_congr fun y ↦ by simp [F, M', updateFinset, hi, add_assoc, add_comm 1 r]
    have h_meas : Measurable (F M (insert i s) ((insert i s).card + r)) := by
      have h_entry (p q : κ) : Measurable fun x' : ι → κ → ℂ ↦
          (M + ∑ j ∈ insert i s, vecMulVec (star (x' j ᵥ* S + a j)) (x' j ᵥ* S + a j)) p q := by
        simp only [Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply,
          Pi.add_apply, vecMul, dotProduct]
        fun_prop
      have h_det : Measurable fun x' : ι → κ → ℂ ↦
          (M + ∑ j ∈ insert i s, vecMulVec (star (x' j ᵥ* S + a j)) (x' j ᵥ* S + a j)).det := by
        simp only [Matrix.det_apply']
        exact Finset.measurable_sum _ fun σ _ ↦
          measurable_const.mul (Finset.measurable_prod _ fun p _ ↦ h_entry (σ p) p)
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul (h_det.norm.inv.pow_const _))
    calc
      _ = ∫⁻ v : κ → ℂ, (∫⋯∫⁻_s, F M (insert i s) ((insert i s).card + r)) (update x i v) :=
        lmarginal_insert _ h_meas hi x
      _ ≤ ∫⁻ v : κ → ℂ, ENNReal.ofReal (c * (K ^ s.card * ‖(M' v).det‖⁻¹ ^ (r + 1))) :=
        lintegral_mono fun v ↦ (inner_eq v).trans_le
          (ih (h_pos v) (Nat.le_succ_of_le hr) (update x i v))
      _ = ENNReal.ofReal (c * K ^ s.card) *
            ∫⁻ v : κ → ℂ, ENNReal.ofReal (‖(M' v).det‖⁻¹ ^ (r + 1)) := by
        simp_rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hc (pow_nonneg hK s.card))]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (c * K ^ s.card) * ENNReal.ofReal (K * ‖M.det‖⁻¹ ^ r) := by
        gcongr
        exact lintegral_norm_det_add_vecMulVec_inv_pow_le hM hS (a i) hr
      _ = ENNReal.ofReal (c * (K ^ (insert i s).card * ‖M.det‖⁻¹ ^ r)) := by
        rw [← ENNReal.ofReal_mul (by positivity), Finset.card_insert_of_notMem hi]
        ring_nf

/-- For an invertible matrix `S` and a measurable function `g`, the affine substitution
`A ↦ S A + c` on `ι → κ → ℂ` multiplies `∫⁻ g` by `‖det S‖⁻¹ ^ (2 * card κ)`. -/
theorem lintegral_comp_mul_add {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {S : Matrix ι ι ℂ} (hS : S.det ≠ 0) (c : Matrix ι κ ℂ) {g : (ι → κ → ℂ) → ENNReal}
    (hg : Measurable g) :
    ∫⁻ A : ι → κ → ℂ, g (S * of A + c) =
      ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) * ∫⁻ A : ι → κ → ℂ, g A := by
  classical
  let e : (ι × κ → ℂ) ≃ₗ[ℂ] (ι → κ → ℂ) := LinearEquiv.curry ℂ ℂ ι κ
  let f : (ι → κ → ℂ) →ₗ[ℂ] (ι → κ → ℂ) :=
    e.toLinearMap ∘ₗ (kroneckerMap (· * ·) S (1 : Matrix κ κ ℂ)).toLin' ∘ₗ e.symm.toLinearMap
  have hf (A : ι → κ → ℂ) : f A = S * of A := by
    ext a b
    simp [f, e, mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]
  have h_det : LinearMap.det (f.restrictScalars ℝ) = ‖S.det‖ ^ (2 * card κ) := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_conj]
    simp [det_kronecker, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, ← pow_mul, mul_comm]
  have h_pos : 0 < ‖S.det‖ ^ (2 * card κ) := pow_pos (norm_pos_iff.2 hS) _
  calc
    _ = ∫⁻ A : ι → κ → ℂ, g (f.restrictScalars ℝ A + of.symm c) :=
      lintegral_congr fun A ↦ congrArg g (congrArg (· + c) (hf A).symm)
    _ = ∫⁻ A, g (A + of.symm c) ∂(Measure.map (f.restrictScalars ℝ) volume) :=
      (lintegral_map (hg.comp (measurable_add_const _))
        (f.restrictScalars ℝ).continuous_of_finiteDimensional.measurable).symm
    _ = _ := by
      have : (volume : Measure (κ → ℂ)).IsAddHaarMeasure := ⟨⟩
      have : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := ⟨⟩
      rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → κ → ℂ))
          (h_det.trans_ne h_pos.ne'),
        lintegral_smul_measure, lintegral_add_right_eq_self, h_det,
        abs_of_pos (inv_pos.2 h_pos), inv_pow, smul_eq_mul]

/-- **Hua's integral bound over matrices**: for invertible `S : Matrix ι ι ℂ`, positive definite
`G : Matrix κ κ ℂ`, and `C ≥ 0`, the integral of `C ‖det (G + (S A + c)ᴴ (S A + c))‖⁻¹ ^ (#κ + #ι)`
over `A : ι → κ → ℂ` is at most
`C (π ^ #κ / #κ!) ^ #ι ‖det S‖⁻¹ ^ (2 #κ) ‖det G‖⁻¹ ^ #κ`. -/
theorem lintegral_norm_det_add_conjTranspose_mul_inv_pow_le {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {S : Matrix ι ι ℂ} (hS : S.det ≠ 0) (c : Matrix ι κ ℂ)
    {G : Matrix κ κ ℂ} (hG : G.PosDef) {C : ℝ} (hC : 0 ≤ C) :
    ∫⁻ A : ι → κ → ℂ,
        ENNReal.ofReal (C * ‖(G + (S * of A + c)ᴴ * (S * of A + c)).det‖⁻¹ ^ (card κ + card ι)) ≤
      ENNReal.ofReal (C * ((π ^ card κ / (card κ).factorial) ^ card ι *
        (‖S.det‖⁻¹ ^ (2 * card κ) * ‖G.det‖⁻¹ ^ card κ))) := by
  let g (v : ι → κ → ℂ) : ENNReal :=
    ENNReal.ofReal (C * ‖(G + (of v)ᴴ * of v).det‖⁻¹ ^ (card κ + card ι))
  have hg : Measurable g := by
    have h_det : Continuous fun v : ι → κ → ℂ ↦ (G + (of v)ᴴ * of v).det := by fun_prop
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul (h_det.measurable.norm.inv.pow_const _))
  have h_rows (v : ι → κ → ℂ) : (of v)ᴴ * of v = ∑ i, vecMulVec (star (v i)) (v i) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply]
  have h_hua : ∫⁻ v, g v ≤
      ENNReal.ofReal (C * ((π ^ card κ / (card κ).factorial) ^ card ι * ‖G.det‖⁻¹ ^ card κ)) := by
    have h := hua_integral_le (ι := ι) (1 : Matrix κ κ ℂ) (by simp) 0 hG hC Finset.univ le_rfl 0
    simpa [g, h_rows, lmarginal_univ, add_comm, volume_pi] using h
  change ∫⁻ A : ι → κ → ℂ, g (S * of A + c) ≤ _
  rw [lintegral_comp_mul_add hS c hg]
  calc
    ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) * ∫⁻ v, g v
      ≤ ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) *
          ENNReal.ofReal
            (C * ((π ^ card κ / (card κ).factorial) ^ card ι * ‖G.det‖⁻¹ ^ card κ)) := by
        gcongr
    _ = ENNReal.ofReal (C * ((π ^ card κ / (card κ).factorial) ^ card ι *
          (‖S.det‖⁻¹ ^ (2 * card κ) * ‖G.det‖⁻¹ ^ card κ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf

end TauCeti
