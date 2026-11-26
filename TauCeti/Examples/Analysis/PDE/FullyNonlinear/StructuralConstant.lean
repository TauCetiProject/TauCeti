/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FullyNonlinear.AdmissiblePair
public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Esymm
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Checks: structural constants of the Hessian and the pure quotient pairs

The structural condition with constant `γ` asks `∏_j ∂_j f ≥ γ` on the cone
(`TauCeti.HasStructuralConstant`). These examples test it on the Hessian pair and on the pure
quotient pairs, with and without an added multiple of `σ₁`.

* The Hessian pair `(σ₂^{1/2}, Γ₂)` in `ℝ³`: at `e = (1, 1, 1)` every partial derivative of
  `σ₂^{1/2}` is `3^{-1/2}` (`fderiv_sqrtEsymmTwo_single`), which is `binom(3, 2)^{1/2} / 3`
  (`sqrt_choose_div_three`).
* The pure quotient `σ₂/σ₁` in `ℝ²`: `∏_j ∂_j f = λ₁²λ₂²/(λ₁ + λ₂)⁴`
  (`prod_fderiv_quotTwo_single`), which is `1/16` at `e` (`prod_fderiv_quotTwo_one_single`) and
  `ε²/(1 + ε)⁴` at `(ε, 1)`, so no positive structural constant holds on `Γ₂`
  (`not_hasStructuralConstant_quotTwo`).
* The pure quotient `σ₂/σ₁` in `ℝ³` at `(M, 1, 1)`: `∂₁ f = 3/(M + 2)²` and
  `∂₂ f = ∂₃ f = (M² + M + 1)/(M + 2)²` (`fderiv_quotThree_single_zero`,
  `fderiv_quotThree_single_of_ne_zero`), so the product
  `3(M² + M + 1)²/(M + 2)⁶` is at most `3/(M + 2)²` and no positive structural constant holds on
  `Γ₂` (`not_hasStructuralConstant_quotThree`). Adding `c σ₁` raises every partial derivative by
  `c` and restores the bound `c³` at these points (`pow_three_le_prod_fderiv_quotThree_add`).

## References

* B. Guo, D. H. Phong and F. Tong, *On L∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), §1.
* B. Guo and D. H. Phong, *On L∞ estimates for fully nonlinear partial differential equations*,
  Ann. of Math. 200 (2024), arXiv:2204.12549, the examples after (1.2).
-/

public section

noncomputable section

open Finset MvPolynomial

namespace TauCeti.Examples.StructuralConstant

/-! ### The Hessian pair `(σ₂^{1/2}, Γ₂)` in `ℝ³` at `e` -/

/-- `σ₂^{1/2}` in three variables. -/
def sqrtEsymmTwo (μ : Fin 3 → ℝ) : ℝ := √(μ 0 * μ 1 + μ 0 * μ 2 + μ 1 * μ 2)

/-- **The partial derivatives of `σ₂^{1/2}` at `e = (1, 1, 1)` are `3^{-1/2}`.** -/
theorem fderiv_sqrtEsymmTwo_single (j : Fin 3) :
    fderiv ℝ sqrtEsymmTwo 1 (Pi.single j 1) = (√3)⁻¹ := by
  have hd : DifferentiableAt ℝ sqrtEsymmTwo 1 := by
    unfold sqrtEsymmTwo
    exact (by fun_prop : DifferentiableAt ℝ
      (fun μ : Fin 3 → ℝ ↦ μ 0 * μ 1 + μ 0 * μ 2 + μ 1 * μ 2) 1).sqrt (by norm_num)
  rw [← hd.lineDeriv_eq_fderiv]
  refine HasLineDerivAt.lineDeriv ?_
  -- On the line through `e` in a coordinate direction, `σ₂ = 3 + 2t`.
  have hline : (fun t : ℝ ↦ sqrtEsymmTwo (1 + t • Pi.single j 1)) = fun t ↦ √(3 + 2 * t) := by
    ext t
    fin_cases j <;> simp [sqrtEsymmTwo] <;> ring_nf
  rw [HasLineDerivAt, hline]
  have h := (((hasDerivAt_id' (0 : ℝ)).const_mul 2).const_add 3).sqrt (by norm_num)
  convert h using 1
  rw [show (3 : ℝ) + 2 * 0 = 3 by norm_num]
  field_simp

/-- The constant `binom(3, 2)^{1/2} / 3` of the Hessian pair `(σ₂^{1/2}, Γ₂)` in `ℝ³` is
`3^{-1/2}`. -/
theorem sqrt_choose_div_three : √(Nat.choose 3 2 : ℝ) / 3 = (√3)⁻¹ := by
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  rw [show (Nat.choose 3 2 : ℝ) = 3 by norm_num [Nat.choose]]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

/-! ### The pure quotient `σ₂/σ₁` in `ℝ²` -/

/-- The pure quotient `σ₂/σ₁ = λ₁λ₂/(λ₁ + λ₂)` in two variables. -/
def quotTwo (μ : Fin 2 → ℝ) : ℝ := μ 0 * μ 1 / (μ 0 + μ 1)

/-- `σ₂/σ₁` is differentiable where `σ₁ ≠ 0`. -/
theorem differentiableAt_quotTwo {μ : Fin 2 → ℝ} (hμ : μ 0 + μ 1 ≠ 0) :
    DifferentiableAt ℝ quotTwo μ := by
  unfold quotTwo
  fun_prop (disch := exact hμ)

/-- `∂₁(σ₂/σ₁) = λ₂²/(λ₁ + λ₂)²`. -/
theorem fderiv_quotTwo_single_zero {μ : Fin 2 → ℝ} (hμ : μ 0 + μ 1 ≠ 0) :
    fderiv ℝ quotTwo μ (Pi.single 0 1) = μ 1 ^ 2 / (μ 0 + μ 1) ^ 2 := by
  rw [← (differentiableAt_quotTwo hμ).lineDeriv_eq_fderiv]
  refine HasLineDerivAt.lineDeriv ?_
  have hline : (fun t : ℝ ↦ quotTwo (μ + t • Pi.single 0 1)) =
      fun t ↦ (μ 0 + t) * μ 1 / (μ 0 + t + μ 1) := by
    ext t
    simp [quotTwo]
  rw [HasLineDerivAt, hline]
  have h := HasDerivAt.fun_div ((((hasDerivAt_id' (0 : ℝ)).const_add (μ 0)).mul_const (μ 1)))
    (((hasDerivAt_id' (0 : ℝ)).const_add (μ 0)).add_const (μ 1)) (by simpa using hμ)
  convert h using 1
  simp only [add_zero]
  field_simp
  ring

/-- `∂₂(σ₂/σ₁) = λ₁²/(λ₁ + λ₂)²`. -/
theorem fderiv_quotTwo_single_one {μ : Fin 2 → ℝ} (hμ : μ 0 + μ 1 ≠ 0) :
    fderiv ℝ quotTwo μ (Pi.single 1 1) = μ 0 ^ 2 / (μ 0 + μ 1) ^ 2 := by
  rw [← (differentiableAt_quotTwo hμ).lineDeriv_eq_fderiv]
  refine HasLineDerivAt.lineDeriv ?_
  have hline : (fun t : ℝ ↦ quotTwo (μ + t • Pi.single 1 1)) =
      fun t ↦ μ 0 * (μ 1 + t) / (μ 0 + (μ 1 + t)) := by
    ext t
    simp [quotTwo]
  rw [HasLineDerivAt, hline]
  have h := HasDerivAt.fun_div ((((hasDerivAt_id' (0 : ℝ)).const_add (μ 1)).const_mul (μ 0)))
    (((hasDerivAt_id' (0 : ℝ)).const_add (μ 1)).const_add (μ 0)) (by simpa using hμ)
  convert h using 1
  simp only [add_zero]
  field_simp
  ring

/-- **The structural product of `σ₂/σ₁` in `ℝ²`**: `∏_j ∂_j f = λ₁²λ₂²/(λ₁ + λ₂)⁴`. -/
theorem prod_fderiv_quotTwo_single {μ : Fin 2 → ℝ} (hμ : μ 0 + μ 1 ≠ 0) :
    ∏ j, fderiv ℝ quotTwo μ (Pi.single j 1) = μ 0 ^ 2 * μ 1 ^ 2 / (μ 0 + μ 1) ^ 4 := by
  rw [Fin.prod_univ_two, fderiv_quotTwo_single_zero hμ, fderiv_quotTwo_single_one hμ]
  field_simp

/-- At `e = (1, 1)` the structural product of `σ₂/σ₁` is `1/16`. -/
theorem prod_fderiv_quotTwo_one_single :
    ∏ j, fderiv ℝ quotTwo 1 (Pi.single j 1) = 1 / 16 := by
  rw [prod_fderiv_quotTwo_single (by norm_num)]
  norm_num

/-- **The pure quotient `σ₂/σ₁` has no positive structural constant on `Γ₂ ⊂ ℝ²`**: at `(ε, 1)`
its structural product is `ε²/(1 + ε)⁴ ≤ ε²`. -/
theorem not_hasStructuralConstant_quotTwo {γ : ℝ} (hγ : 0 < γ) :
    ¬ HasStructuralConstant (gardingCone (esymm (Fin 2) ℝ 2) 1) quotTwo γ := by
  rintro ⟨h⟩
  have hcone : gardingCone (esymm (Fin 2) ℝ 2) 1 = {μ : Fin 2 → ℝ | ∀ i, 0 < μ i} := by
    have h := gardingCone_esymm_card (σ := Fin 2)
    rw [Fintype.card_fin] at h
    exact h
  set ε := min (1 / 2) (γ / 2)
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hmem : (![ε, 1] : Fin 2 → ℝ) ∈ gardingCone (esymm (Fin 2) ℝ 2) 1 := by
    rw [hcone]
    intro i
    fin_cases i <;> simp [hε0]
  have := h hmem
  rw [prod_fderiv_quotTwo_single (by simp; linarith)] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one] at this
  have h1 : ε ^ 2 / (ε + 1) ^ 4 ≤ ε ^ 2 :=
    div_le_self (by positivity) (one_le_pow₀ (by linarith))
  have h2 : ε ^ 2 < γ := by
    have hε1 : ε ≤ 1 / 2 := min_le_left _ _
    have hεγ : ε ≤ γ / 2 := min_le_right _ _
    nlinarith
  linarith

/-! ### The pure quotient `σ₂/σ₁` in `ℝ³` at `(M, 1, 1)` -/

/-- The pure quotient `σ₂/σ₁` in three variables. -/
def quotThree (μ : Fin 3 → ℝ) : ℝ :=
  (μ 0 * μ 1 + μ 0 * μ 2 + μ 1 * μ 2) / (μ 0 + μ 1 + μ 2)

/-- `σ₂/σ₁` is differentiable where `σ₁ ≠ 0`. -/
theorem differentiableAt_quotThree {μ : Fin 3 → ℝ} (hμ : μ 0 + μ 1 + μ 2 ≠ 0) :
    DifferentiableAt ℝ quotThree μ := by
  unfold quotThree
  fun_prop (disch := exact hμ)

/-- The point `(M, 1, 1)`. -/
abbrev pointM (M : ℝ) : Fin 3 → ℝ := ![M, 1, 1]

/-- `∂₁(σ₂/σ₁)(M, 1, 1) = 3/(M + 2)²`. -/
theorem fderiv_quotThree_single_zero {M : ℝ} (hM : 0 < M) :
    fderiv ℝ quotThree (pointM M) (Pi.single 0 1) = 3 / (M + 2) ^ 2 := by
  have hM2 : M + 2 ≠ 0 := by linarith
  rw [← (differentiableAt_quotThree (by simp; linarith)).lineDeriv_eq_fderiv]
  refine HasLineDerivAt.lineDeriv ?_
  have hline : (fun t : ℝ ↦ quotThree (pointM M + t • Pi.single 0 1)) =
      fun t ↦ (2 * (M + t) + 1) / (M + t + 2) := by
    ext t
    simp [quotThree]
    ring_nf
  rw [HasLineDerivAt, hline]
  have h := HasDerivAt.fun_div ((((hasDerivAt_id' (0 : ℝ)).const_add M).const_mul 2).add_const 1)
    (((hasDerivAt_id' (0 : ℝ)).const_add M).add_const 2) (by simpa using hM2)
  convert h using 1
  simp only [add_zero]
  field_simp
  ring

/-- `∂₂(σ₂/σ₁)(M, 1, 1) = ∂₃(σ₂/σ₁)(M, 1, 1) = (M² + M + 1)/(M + 2)²`. -/
theorem fderiv_quotThree_single_of_ne_zero {M : ℝ} (hM : 0 < M) {j : Fin 3} (hj : j ≠ 0) :
    fderiv ℝ quotThree (pointM M) (Pi.single j 1) = (M ^ 2 + M + 1) / (M + 2) ^ 2 := by
  have hM2 : M + 2 ≠ 0 := by linarith
  rw [← (differentiableAt_quotThree (by simp; linarith)).lineDeriv_eq_fderiv]
  refine HasLineDerivAt.lineDeriv ?_
  have hline : (fun t : ℝ ↦ quotThree (pointM M + t • Pi.single j 1)) =
      fun t ↦ ((M + 1) * (1 + t) + M) / (M + 2 + t) := by
    ext t
    fin_cases j
    · exact absurd rfl hj
    all_goals simp [quotThree]; ring_nf
  rw [HasLineDerivAt, hline]
  have h := HasDerivAt.fun_div
    ((((hasDerivAt_id' (0 : ℝ)).const_add 1).const_mul (M + 1)).add_const M)
    ((hasDerivAt_id' (0 : ℝ)).const_add (M + 2)) (by simpa using hM2)
  convert h using 1
  simp only [add_zero]
  field_simp
  ring

/-- The structural product of `σ₂/σ₁` at `(M, 1, 1)` is `3(M² + M + 1)²/(M + 2)⁶`. -/
theorem prod_fderiv_quotThree_single {M : ℝ} (hM : 0 < M) :
    ∏ j, fderiv ℝ quotThree (pointM M) (Pi.single j 1) =
      3 * (M ^ 2 + M + 1) ^ 2 / (M + 2) ^ 6 := by
  rw [Fin.prod_univ_three, fderiv_quotThree_single_zero hM,
    fderiv_quotThree_single_of_ne_zero hM (by decide),
    fderiv_quotThree_single_of_ne_zero hM (by decide)]
  have hM2 : M + 2 ≠ 0 := by linarith
  field_simp

/-- The structural product of `σ₂/σ₁` at `(M, 1, 1)` is at most `3/(M + 2)²`. -/
theorem prod_fderiv_quotThree_single_le {M : ℝ} (hM : 0 < M) :
    ∏ j, fderiv ℝ quotThree (pointM M) (Pi.single j 1) ≤ 3 / (M + 2) ^ 2 := by
  rw [prod_fderiv_quotThree_single hM, div_le_div_iff₀ (by positivity) (by positivity)]
  have h : M ^ 2 + M + 1 ≤ (M + 2) ^ 2 := by nlinarith
  have h' : (M ^ 2 + M + 1) ^ 2 ≤ ((M + 2) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  nlinarith [pow_pos (show (0 : ℝ) < M + 2 by linarith) 2]

/-- **The pure quotient `σ₂/σ₁` has no positive structural constant on `Γ₂ ⊂ ℝ³`**: its
structural product at `(M, 1, 1) ∈ Γ₃ ⊆ Γ₂` is at most `3/(M + 2)²`. -/
theorem not_hasStructuralConstant_quotThree {γ : ℝ} (hγ : 0 < γ) :
    ¬ HasStructuralConstant (gardingCone (esymm (Fin 3) ℝ 2) 1) quotThree γ := by
  rintro ⟨h⟩
  have hsub : {μ : Fin 3 → ℝ | ∀ i, 0 < μ i} ⊆ gardingCone (esymm (Fin 3) ℝ 2) 1 := by
    have h3 := gardingCone_esymm_card (σ := Fin 3)
    rw [Fintype.card_fin] at h3
    rw [← h3]
    exact gardingCone_esymm_subset (by norm_num)
  set M := 3 / γ with hMdef
  have hM : 0 < M := by positivity
  have hmem : pointM M ∈ gardingCone (esymm (Fin 3) ℝ 2) 1 :=
    hsub fun i ↦ by fin_cases i <;> simp [hM]
  have hle := (h hmem).trans (prod_fderiv_quotThree_single_le hM)
  have hlt : 3 / (M + 2) ^ 2 < γ := by
    rw [div_lt_iff₀ (by positivity)]
    have : 3 = γ * M := by rw [hMdef]; field_simp
    nlinarith
  linarith

/-- **Adding `c σ₁` restores the bound `c³` at `(M, 1, 1)`**: every partial derivative of
`σ₂/σ₁ + c σ₁` is that of `σ₂/σ₁`, which is positive there, plus `c`. -/
theorem pow_three_le_prod_fderiv_quotThree_add {M c : ℝ} (hM : 0 < M) (hc : 0 ≤ c) :
    c ^ 3 ≤ ∏ j, fderiv ℝ (fun μ ↦ quotThree μ + c * ∑ i, μ i) (pointM M) (Pi.single j 1) := by
  have hd := differentiableAt_quotThree (μ := pointM M) (by simp; linarith)
  have hpart (j : Fin 3) :
      fderiv ℝ (fun μ ↦ quotThree μ + c * ∑ i, μ i) (pointM M) (Pi.single j 1) =
        fderiv ℝ quotThree (pointM M) (Pi.single j 1) + c := by
    rw [fderiv_fun_add hd (by fun_prop), fderiv_const_mul (by fun_prop)]
    simp
  rw [Fin.prod_univ_three, hpart, hpart, hpart, fderiv_quotThree_single_zero hM,
    fderiv_quotThree_single_of_ne_zero hM (by decide),
    fderiv_quotThree_single_of_ne_zero hM (by decide)]
  have h0 : c ≤ 3 / (M + 2) ^ 2 + c := le_add_of_nonneg_left (by positivity)
  have h1 : c ≤ (M ^ 2 + M + 1) / (M + 2) ^ 2 + c := le_add_of_nonneg_left (by positivity)
  calc c ^ 3 = c * c * c := by ring
    _ ≤ _ := by gcongr

end TauCeti.Examples.StructuralConstant
