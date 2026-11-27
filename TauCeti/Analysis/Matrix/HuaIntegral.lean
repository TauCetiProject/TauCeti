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
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Complex
import TauCeti.LinearAlgebra.Matrix.Determinant.StarRankOne
import TauCeti.MeasureTheory.Measure.Haar.Matrix.Complex

/-!
# Hua's integral bound for complex matrices

This file proves Hua's integral bound for negative powers of `‖det (M + Yᴴ Y)‖` over spaces of
complex matrices, where `M` is positive definite.

## Main results

* `Matrix.PosDef.lintegral_norm_det_add_vecMulVec_inv_pow_le`: one-row Hua bound.
* `Matrix.lmarginal_norm_det_add_sum_vecMulVec_inv_pow_le`: iterated marginal Hua bound over a
  finite set of rows `s`.
* `TauCeti.lintegral_norm_det_add_conjTranspose_mul_inv_pow_le`: two-sided affine Hua bound over
  `ι → κ → ℂ` matrices for any exponent `r + card ι` (`r ≥ card κ`), invertible `S` and `T`, and
  positive definite `G`.

## References

* L. K. Hua, *Harmonic Analysis of Functions of Several Complex Variables in the Classical Domains*,
  AMS Transl. Math. Monographs **6**, 1963, §2.
* Adapted from `New.lintegral_norm_det_add_inv_pow_le` in
  `src/New/Spanning/RemainingTerms/OneRealPlace.lean` of grh-lean
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Fintype Function Matrix MeasureTheory Real
open scoped ComplexOrder MatrixOrder

namespace Matrix.PosDef

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
  have h_cv : ∫⁻ v : κ → ℂ,
        ENNReal.ofReal (‖(star C * C + vecMulVec (star (v ᵥ* S + a))
          (v ᵥ* S + a)).det‖⁻¹ ^ (r + 1)) =
      ENNReal.ofReal (‖(C * S⁻¹)ᵀ.det‖ ^ 2) * ∫⁻ y : κ → ℂ,
        ENNReal.ofReal ((‖C.det‖ ^ 2 * (1 + ∑ j, ‖y j‖ ^ 2))⁻¹ ^ (r + 1)) := by
    rw [← lintegral_add_right_eq_self _ (-a ᵥ* S⁻¹)]
    have h_det_ne : (C * S⁻¹)ᵀ.det ≠ 0 := by simp [hC, hS]
    have h_mul := lintegral_comp_mulVec (u := (C * S⁻¹)ᵀ) h_det_ne
      (fun v ↦ ENNReal.ofReal (‖(star C * C + vecMulVec (star ((v + -a ᵥ* S⁻¹) ᵥ* S + a))
        ((v + -a ᵥ* S⁻¹) ᵥ* S + a)).det‖⁻¹ ^ (r + 1)))
    have h_solved := congrArg (ENNReal.ofReal (‖(C * S⁻¹)ᵀ.det‖ ^ 2) * ·) h_mul
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_pow,
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul] at h_solved
    rw [← h_solved]
    congr 1
    exact lintegral_congr fun y ↦ by rw [h_subst, norm_det_star_mul_self_add_vecMulVec]
  calc
    _ = ∫⁻ y : κ → ℂ, ENNReal.ofReal (‖(C * S⁻¹)ᵀ.det‖ ^ 2) *
          ENNReal.ofReal ((‖C.det‖ ^ 2 * (1 + ∑ j, ‖y j‖ ^ 2))⁻¹ ^ (r + 1)) := by
      rw [h_cv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y : κ → ℂ,
          ENNReal.ofReal B * ENNReal.ofReal ((1 + ∑ j, ‖y j‖ ^ 2)⁻¹ ^ (card κ + 1)) := by
      refine lintegral_mono fun y ↦ ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), h_jacobian]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))) (Nat.succ_le_succ hr)
    _ = ENNReal.ofReal
          (π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2 * ‖(star C * C).det‖⁻¹ ^ r) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        TauCeti.lintegral_one_add_sum_norm_sq_inv_pow, ← ENNReal.ofReal_mul (by positivity)]
      simp only [B]
      congr 1
      ring

end Matrix.PosDef

namespace Matrix

/-- **Hua's integral bound** (iterated marginal form): for positive definite `M`, invertible `S`,
`r ≥ card κ`, and a finite set of rows `s`, the iterated lower Lebesgue integral of
`‖det (M + ∑ i ∈ s, (y i S + a i)ᴴ (y i S + a i))‖⁻¹ ^ (r + s.card)` over `i ∈ s` is at most
`(π^k / (k! ‖det S‖²)) ^ s.card ‖det M‖⁻¹ ^ r`. -/
theorem lmarginal_norm_det_add_sum_vecMulVec_inv_pow_le {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {M : Matrix κ κ ℂ} (S : Matrix κ κ ℂ) (hS : det S ≠ 0) (a : ι → κ → ℂ)
    (hM : M.PosDef) (s : Finset ι) {r : ℕ} (hr : card κ ≤ r) (x : ι → κ → ℂ) :
    (∫⋯∫⁻_s, fun y : ι → κ → ℂ ↦ ENNReal.ofReal (
        ‖(M + ∑ i ∈ s, vecMulVec (star (y i ᵥ* S + a i)) (y i ᵥ* S + a i)).det‖⁻¹ ^
          (r + s.card))) x ≤
      ENNReal.ofReal
        ((π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2) ^ s.card * ‖M.det‖⁻¹ ^ r) := by
  set K : ℝ := π ^ card κ / (card κ).factorial / ‖S.det‖ ^ 2
  have hK : 0 ≤ K := by positivity
  induction s using Finset.induction generalizing M r x with
  | empty => simp
  | insert i s hi ih =>
    let F (A : Matrix κ κ ℂ) (t : Finset ι) (n : ℕ) (x' : ι → κ → ℂ) : ENNReal :=
      ENNReal.ofReal (
        ‖(A + ∑ j ∈ t, vecMulVec (star (x' j ᵥ* S + a j)) (x' j ᵥ* S + a j)).det‖⁻¹ ^ n)
    let M' (v : κ → ℂ) : Matrix κ κ ℂ := M + vecMulVec (star (v ᵥ* S + a i)) (v ᵥ* S + a i)
    have h_pos (v : κ → ℂ) : (M' v).PosDef := hM.add_posSemidef (posSemidef_vecMulVec_star_self _)
    have inner_eq (v : κ → ℂ) :
        (∫⋯∫⁻_s, F M (insert i s) (r + (insert i s).card)) (update x i v) =
          (∫⋯∫⁻_s, F (M' v) s ((r + 1) + s.card)) (update x i v) :=
      lintegral_congr fun y ↦ by simp [F, M', updateFinset, hi, add_assoc, add_comm 1]
    have h_meas : Measurable (F M (insert i s) (r + (insert i s).card)) := by
      have h_mat : Measurable fun x' : ι → κ → ℂ ↦
          of.symm (M + ∑ j ∈ insert i s, vecMulVec (star (x' j ᵥ* S + a j)) (x' j ᵥ* S + a j)) := by
        rw [measurable_pi_iff]
        intro p
        rw [measurable_pi_iff]
        intro q
        simp only [of_symm_apply, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply,
          Pi.star_apply, Pi.add_apply, vecMul, dotProduct]
        fun_prop
      have h_det : Continuous fun A : κ → κ → ℂ ↦ (of A).det := by fun_prop
      exact ENNReal.measurable_ofReal.comp ((h_det.measurable.comp h_mat).norm.inv.pow_const _)
    calc
      _ = ∫⁻ v : κ → ℂ, (∫⋯∫⁻_s, F M (insert i s) (r + (insert i s).card)) (update x i v) :=
        lmarginal_insert _ h_meas hi x
      _ ≤ ∫⁻ v : κ → ℂ, ENNReal.ofReal (K ^ s.card * ‖(M' v).det‖⁻¹ ^ (r + 1)) :=
        lintegral_mono fun v ↦ (inner_eq v).trans_le
          (ih (h_pos v) (Nat.le_succ_of_le hr) (update x i v))
      _ = ENNReal.ofReal (K ^ s.card) *
            ∫⁻ v : κ → ℂ, ENNReal.ofReal (‖(M' v).det‖⁻¹ ^ (r + 1)) := by
        simp_rw [ENNReal.ofReal_mul (pow_nonneg hK s.card)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (K ^ s.card) * ENNReal.ofReal (K * ‖M.det‖⁻¹ ^ r) := by
        gcongr
        exact hM.lintegral_norm_det_add_vecMulVec_inv_pow_le hS (a i) hr
      _ = ENNReal.ofReal (K ^ (insert i s).card * ‖M.det‖⁻¹ ^ r) := by
        rw [← ENNReal.ofReal_mul (by positivity), Finset.card_insert_of_notMem hi, pow_succ]
        congr 1
        ring

end Matrix

namespace TauCeti

/-- **Hua's integral bound over matrices** (two-sided affine form): for invertible
`S : Matrix ι ι ℂ` and `T : Matrix κ κ ℂ`, positive definite `G : Matrix κ κ ℂ`, and `r ≥ card κ`,
the integral of `‖det (G + (S A T + c)ᴴ (S A T + c))‖⁻¹ ^ (r + #ι)` over `A : ι → κ → ℂ` is at most
`(π ^ #κ / #κ!) ^ #ι ‖det S‖⁻¹ ^ (2 #κ) ‖det T‖⁻¹ ^ (2 #ι) ‖det G‖⁻¹ ^ r`. -/
theorem lintegral_norm_det_add_conjTranspose_mul_inv_pow_le {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] {S : Matrix ι ι ℂ} (hS : S.det ≠ 0)
    {T : Matrix κ κ ℂ} (hT : T.det ≠ 0) (c : Matrix ι κ ℂ) {G : Matrix κ κ ℂ} (hG : G.PosDef)
    {r : ℕ} (hr : card κ ≤ r) :
    ∫⁻ A : ι → κ → ℂ,
        ENNReal.ofReal (‖(G + (S * of A * T + c)ᴴ * (S * of A * T + c)).det‖⁻¹ ^ (r + card ι)) ≤
      ENNReal.ofReal ((π ^ card κ / (card κ).factorial) ^ card ι *
        (‖S.det‖⁻¹ ^ (2 * card κ) * (‖T.det‖⁻¹ ^ (2 * card ι) * ‖G.det‖⁻¹ ^ r))) := by
  let g (v : ι → κ → ℂ) : ENNReal :=
    ENNReal.ofReal (‖(G + (of v * T + c)ᴴ * (of v * T + c)).det‖⁻¹ ^ (r + card ι))
  have h_rows (v : ι → κ → ℂ) :
      (of v * T + c)ᴴ * (of v * T + c) =
        ∑ i, vecMulVec (star (v i ᵥ* T + c i)) (v i ᵥ* T + c i) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, vecMul, dotProduct, mul_comm]
  have h_integrand (v : ι → κ → ℂ) :
      ENNReal.ofReal (‖(G + ∑ i ∈ (Finset.univ : Finset ι),
          vecMulVec (star (v i ᵥ* T + c i)) (v i ᵥ* T + c i)).det‖⁻¹ ^
          (r + (Finset.univ : Finset ι).card)) = g v := by
    simp only [g, h_rows, Finset.card_univ]
  have h_hua : ∫⁻ v, g v ≤
      ENNReal.ofReal
        ((π ^ card κ / (card κ).factorial / ‖T.det‖ ^ 2) ^ card ι * ‖G.det‖⁻¹ ^ r) := by
    have h := Matrix.lmarginal_norm_det_add_sum_vecMulVec_inv_pow_le (ι := ι)
      T hT (fun i ↦ c i) hG Finset.univ hr 0
    rw [lmarginal_univ, ← volume_pi, lintegral_congr h_integrand] at h
    simpa only [Finset.card_univ] using h
  have h_comp (A : ι → κ → ℂ) :
      ENNReal.ofReal (‖(G + (S * of A * T + c)ᴴ * (S * of A * T + c)).det‖⁻¹ ^ (r + card ι)) =
        g (of.symm (S * of A + 0)) := by
    simp only [g, add_zero, Equiv.apply_symm_apply]
  rw [lintegral_congr h_comp, lintegral_comp_matrix_mul_add hS 0 g]
  calc
    ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) * ∫⁻ v, g v
      ≤ ENNReal.ofReal (‖S.det‖⁻¹ ^ (2 * card κ)) *
          ENNReal.ofReal
            ((π ^ card κ / (card κ).factorial / ‖T.det‖ ^ 2) ^ card ι * ‖G.det‖⁻¹ ^ r) := by
        gcongr
    _ = ENNReal.ofReal ((π ^ card κ / (card κ).factorial) ^ card ι *
          (‖S.det‖⁻¹ ^ (2 * card κ) * (‖T.det‖⁻¹ ^ (2 * card ι) * ‖G.det‖⁻¹ ^ r))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [div_pow, inv_pow, ← pow_mul]
        field_simp

end TauCeti
