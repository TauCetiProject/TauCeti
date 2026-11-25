/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Hyperbolic.Esymm
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Real.Sqrt

/-!
# Checks for hyperbolic polynomials and their Gårding cones

Worked examples of hyperbolic polynomials and their Gårding cones that need only the elementary
theory of `MvPolynomial.IsHyperbolic` and `MvPolynomial.gardingCone`, all on `ℝ²` in the
direction `e = (1, 1)` unless stated otherwise.

* `xy` is hyperbolic of degree `2`, with the open quadrant as cone; at `x = (2, -1)` the roots of
  `t ↦ p(x + t e)` are `-2` and `1`, so `x` is not in the cone.
* `x + y` is hyperbolic of degree `1`, with the half-plane `x + y > 0` as cone; its derivative
  `D_e p = 2` is a positive constant, whose cone is the whole plane.
* Degree zero: a positive constant is hyperbolic of degree `0` in every direction, with the whole
  space as cone (which contains `-a`), and its directional derivatives vanish, so they are not
  positive (the zero polynomial is not hyperbolic).
* The index range of `σ_k`: in one variable, `σ_1` is hyperbolic in `e`, while `σ_2 = 0` is not.
* The family `p_c = (x₁ + x₂)² - c (x₁ - x₂)²`, `c ≥ 0`: `p_c` is hyperbolic of degree `2`, with
  cone `{x₁ + x₂ > √c |x₁ - x₂|}`; the coordinate vector `e₁` lies in the closure of the cone
  exactly when `c ≤ 1`, and the open quadrant `Γ_2` lies in the cone exactly when `c ≤ 1`.
  At `c = 1/4`, `∂₁ p_c > 0` on the cone; at `c = 1`, `p_1 = 4 x₁ x₂` has cone `Γ_2`.
* The polynomial `p = 2xy - 0.9 (x² + y²) = p_{19} / 20` is symmetric and hyperbolic in `e`, but
  its cone misses the point `(1, 0.1)` of `Γ_2`, `p(e₁) < 0` and `e₁` is not in the closure of
  the cone, and at the point `(1, 0.7)` of the cone `∂ₓ p = -0.4 < 0`: without `e_i` in the
  closure of the cone, the partial derivatives need not be positive there.
-/

public section

noncomputable section

open MvPolynomial Set

namespace TauCeti.HyperbolicExamples

/-! ### `xy` and `x + y` -/

/-- `xy` on `ℝ²` is the elementary symmetric polynomial `σ_2` in two variables. -/
theorem X_mul_X_eq_esymm_card :
    (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) = esymm (Fin 2) ℝ (Fintype.card (Fin 2)) := by
  rw [esymm_card, Fin.prod_univ_two]

/-- `xy` on `ℝ²` is hyperbolic of degree `2` in the direction `e = (1, 1)`. -/
theorem isHyperbolic_X_mul_X : IsHyperbolic (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) 2 1 := by
  rw [X_mul_X_eq_esymm_card]
  simpa using isHyperbolic_esymm_card (σ := Fin 2)

/-- The Gårding cone of `xy` in the direction `(1, 1)` is the open quadrant. -/
theorem gardingCone_X_mul_X :
    gardingCone (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) 1 = {x | 0 < x 0 ∧ 0 < x 1} := by
  rw [X_mul_X_eq_esymm_card, gardingCone_esymm_card]
  ext x
  simp [Fin.forall_fin_two]

/-- At `x = (2, -1)`, `t ↦ xy(x + t e)` vanishes at `t = -2`. -/
theorem eval_X_mul_X_neg_two : eval (![2, -1] + (-2 : ℝ) • 1) (X 0 * X 1 : MvPolynomial (Fin 2) ℝ)
    = 0 := by
  simp [Matrix.vecHead, Matrix.vecTail]

/-- At `x = (2, -1)`, `t ↦ xy(x + t e)` vanishes at `t = 1`. -/
theorem eval_X_mul_X_one : eval (![2, -1] + (1 : ℝ) • 1) (X 0 * X 1 : MvPolynomial (Fin 2) ℝ)
    = 0 := by
  simp [Matrix.vecHead, Matrix.vecTail]

/-- The point `(2, -1)`, whose roots `-2` and `1` are not both negative, is not in the cone of
`xy`. -/
example : ![(2 : ℝ), -1] ∉ gardingCone (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) 1 :=
  fun h ↦ mem_gardingCone.1 h 1 zero_le_one eval_X_mul_X_one

/-- `x + y` on `ℝ²` is hyperbolic of degree `1` in the direction `(1, 1)`. -/
theorem isHyperbolic_X_add_X : IsHyperbolic (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) 1 1 where
  isHomogeneous := (isHomogeneous_X ℝ 0).add (isHomogeneous_X ℝ 1)
  eval_pos := by norm_num
  splits x := Polynomial.Splits.of_natDegree_le_one <|
    natDegree_aeval_C_add_C_mul_X_le_of_isHomogeneous
      ((isHomogeneous_X ℝ 0).add (isHomogeneous_X ℝ 1)) x 1

/-- The Gårding cone of `x + y` in the direction `(1, 1)` is the half-plane `x + y > 0`. -/
theorem gardingCone_X_add_X :
    gardingCone (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) 1 = {x | 0 < x 0 + x 1} := by
  ext x
  simp only [mem_gardingCone, map_add, eval_X, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one, mem_ofPred_eq]
  refine ⟨fun h ↦ ?_, fun h t ht h' ↦ by linarith⟩
  by_contra! hle
  exact h (-(x 0 + x 1) / 2) (by linarith) (by ring)

/-- The derivative `D_e (x + y)` is the constant `2`. -/
theorem sum_smul_pderiv_X_add_X :
    ∑ i, (1 : Fin 2 → ℝ) i • pderiv i (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) = C 2 := by
  simp [Fin.sum_univ_two, pderiv_X, one_add_one_eq_two, map_ofNat]

/-! ### Degree zero -/

/-- The constant `2` is hyperbolic of degree `0` in the direction `(1, 1)`, with the whole plane
as cone. -/
example : IsHyperbolic (C 2 : MvPolynomial (Fin 2) ℝ) 0 1 ∧
    gardingCone (C 2 : MvPolynomial (Fin 2) ℝ) 1 = univ :=
  ⟨isHyperbolic_C two_pos 1, gardingCone_C two_ne_zero 1⟩

/-- The cone of the constant `1` contains `-a`. -/
example {σ : Type*} (a : σ → ℝ) : -a ∈ gardingCone (C 1 : MvPolynomial σ ℝ) a := by
  simp

/-- The cone of `D_e (x + y) = 2` is the whole plane. -/
example : gardingCone
    (∑ i, (1 : Fin 2 → ℝ) i • pderiv i (X 0 + X 1 : MvPolynomial (Fin 2) ℝ)) 1 = univ := by
  rw [sum_smul_pderiv_X_add_X, gardingCone_C two_ne_zero]

/-- The cone of `x + y` lies in the cone of its derivative `D_e (x + y)`. -/
example : gardingCone (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) 1 ⊆
    gardingCone (∑ i, (1 : Fin 2 → ℝ) i • pderiv i (X 0 + X 1 : MvPolynomial (Fin 2) ℝ)) 1 :=
  isHyperbolic_X_add_X.gardingCone_subset_sum_smul_pderiv le_rfl

/-- The positive-degree conclusions fail in degree `0`: `D_b 1 = 0` is not hyperbolic. -/
example {σ : Type*} [Fintype σ] (b : σ → ℝ) :
    ¬ IsHyperbolic (∑ i, b i • pderiv i (C 1 : MvPolynomial σ ℝ)) 0 b :=
  fun h ↦ h.ne_zero (by simp)

/-- The independence of the direction survives in degree `0`: `1` is hyperbolic in every `b`,
with the same cone as in any other direction `a`. -/
example {σ : Type*} (a b : σ → ℝ) : IsHyperbolic (C 1 : MvPolynomial σ ℝ) 0 b ∧
    gardingCone (C 1 : MvPolynomial σ ℝ) b = gardingCone (C 1) a := by
  rw [gardingCone_C one_ne_zero, gardingCone_C one_ne_zero]
  exact ⟨isHyperbolic_C one_pos b, rfl⟩

/-! ### The index range of `σ_k` -/

/-- `σ_1` in one variable is hyperbolic of degree `1` in the direction `e`. -/
example : IsHyperbolic (esymm (Fin 1) ℝ 1) 1 1 := by
  simpa using isHyperbolic_esymm_card (σ := Fin 1)

/-- `σ_2` in one variable is the zero polynomial. -/
theorem esymm_fin_one_two : esymm (Fin 1) ℝ 2 = 0 := by
  rw [esymm, Finset.powersetCard_eq_empty.2 (by simp), Finset.sum_empty]

/-- `σ_2` in one variable is not hyperbolic in any direction. -/
example (m : ℕ) (b : Fin 1 → ℝ) : ¬ IsHyperbolic (esymm (Fin 1) ℝ 2) m b := by
  rw [esymm_fin_one_two]
  exact fun h ↦ h.ne_zero rfl

/-! ### The family `p_c = (x₁ + x₂)² - c (x₁ - x₂)²` -/

/-- The polynomial `p_c = (x₁ + x₂)² - c (x₁ - x₂)²` on `ℝ²`. -/
def familyPoly (c : ℝ) : MvPolynomial (Fin 2) ℝ :=
  (X 0 + X 1) ^ 2 - C c * (X 0 - X 1) ^ 2

/-- The values of `p_c`. -/
@[simp]
theorem eval_familyPoly (c : ℝ) (x : Fin 2 → ℝ) :
    eval x (familyPoly c) = (x 0 + x 1) ^ 2 - c * (x 0 - x 1) ^ 2 := by
  simp [familyPoly]

/-- `p_c` is homogeneous of degree `2`. -/
theorem isHomogeneous_familyPoly (c : ℝ) : (familyPoly c).IsHomogeneous 2 := by
  have h1 : (X 0 + X 1 : MvPolynomial (Fin 2) ℝ).IsHomogeneous 1 :=
    (isHomogeneous_X ℝ 0).add (isHomogeneous_X ℝ 1)
  have h2 : (X 0 - X 1 : MvPolynomial (Fin 2) ℝ).IsHomogeneous 1 :=
    (isHomogeneous_X ℝ 0).sub (isHomogeneous_X ℝ 1)
  rw [familyPoly, sq, sq]
  exact (h1.mul h1).sub ((h2.mul h2).C_mul c)

/-- For `c ≥ 0`, `p_c` is hyperbolic of degree `2` in the direction `(1, 1)`: its line
restriction is `(x₁ + x₂ + 2t)² - (√c (x₁ - x₂))²`, a product of two linear factors. -/
theorem isHyperbolic_familyPoly {c : ℝ} (hc : 0 ≤ c) : IsHyperbolic (familyPoly c) 2 1 where
  isHomogeneous := isHomogeneous_familyPoly c
  eval_pos := by norm_num
  splits x := by
    have hs : Polynomial.C √c * Polynomial.C √c = Polynomial.C c := by
      rw [← Polynomial.C_mul, Real.mul_self_sqrt hc]
    have h : aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C ((1 : Fin 2 → ℝ) i) *
        Polynomial.X) (familyPoly c) =
        (Polynomial.C (x 0 + x 1 - √c * (x 0 - x 1)) + 2 * Polynomial.X) *
        (Polynomial.C (x 0 + x 1 + √c * (x 0 - x 1)) + 2 * Polynomial.X) := by
      simp only [familyPoly, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
        Pi.one_apply, Polynomial.algebraMap_eq,
        Polynomial.C_1, one_mul]
      linear_combination (Polynomial.C (x 0) - Polynomial.C (x 1)) ^ 2 * hs
    rw [h]
    exact (Polynomial.Splits.of_natDegree_le_one (by compute_degree!)).mul
      (Polynomial.Splits.of_natDegree_le_one (by compute_degree!))

/-- For `c ≥ 0`, the Gårding cone of `p_c` in the direction `(1, 1)` is
`{x₁ + x₂ > √c |x₁ - x₂|}`. -/
theorem gardingCone_familyPoly {c : ℝ} (hc : 0 ≤ c) :
    gardingCone (familyPoly c) 1 = {x | √c * |x 0 - x 1| < x 0 + x 1} := by
  ext x
  simp only [mem_gardingCone, eval_familyPoly, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one, mem_ofPred_eq]
  have key (t : ℝ) : (x 0 + t + (x 1 + t)) ^ 2 - c * (x 0 + t - (x 1 + t)) ^ 2 =
      (x 0 + x 1 + 2 * t) ^ 2 - (√c * |x 0 - x 1|) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc, sq_abs]
    ring
  simp only [key]
  have h0 : 0 ≤ √c * |x 0 - x 1| := by positivity
  refine ⟨fun h ↦ ?_, fun h t ht ↦ ?_⟩
  · by_contra! hle
    exact h ((√c * |x 0 - x 1| - (x 0 + x 1)) / 2) (by linarith) (by ring)
  · have hlt : √c * |x 0 - x 1| < x 0 + x 1 + 2 * t := by linarith
    exact (sub_pos.2 (pow_lt_pow_left₀ hlt h0 two_ne_zero)).ne'

/-- The closure of the cone of `p_c` lies in `{x₁ + x₂ ≥ √c |x₁ - x₂|}`. -/
theorem closure_gardingCone_familyPoly_subset {c : ℝ} (hc : 0 ≤ c) :
    closure (gardingCone (familyPoly c) 1) ⊆ {x | √c * |x 0 - x 1| ≤ x 0 + x 1} := by
  rw [gardingCone_familyPoly hc]
  exact closure_lt_subset_le (by fun_prop) (by fun_prop)

/-- The coordinate vector `e₁ = (1, 0)` lies in the closure of the cone of `p_c` exactly when
`c ≤ 1`. -/
theorem mem_closure_gardingCone_familyPoly_iff {c : ℝ} (hc : 0 ≤ c) :
    ![1, 0] ∈ closure (gardingCone (familyPoly c) 1) ↔ c ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := closure_gardingCone_familyPoly_subset hc h
    norm_num at h'
    nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c]
  · have hs : √c ≤ 1 := Real.sqrt_le_one.2 h
    have ht : Filter.Tendsto (fun ε : ℝ ↦ (![1, 0] : Fin 2 → ℝ) + ε • 1)
        (nhdsWithin 0 (Ioi 0)) (nhds ![1, 0]) := by
      have hcont : Continuous fun ε : ℝ ↦ (![1, 0] : Fin 2 → ℝ) + ε • 1 := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦ ?_)
    rw [gardingCone_familyPoly hc]
    norm_num [Matrix.vecHead, Matrix.vecTail]
    linarith

/-- The open quadrant `Γ_2` lies in the cone of `p_c` exactly when `c ≤ 1`. -/
theorem quadrant_subset_gardingCone_familyPoly_iff {c : ℝ} (hc : 0 ≤ c) :
    {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 < x 1} ⊆ gardingCone (familyPoly c) 1 ↔ c ≤ 1 := by
  rw [gardingCone_familyPoly hc]
  refine ⟨fun h ↦ ?_, fun h x ⟨h0, h1⟩ ↦ ?_⟩
  · by_contra! hlt
    have hs : 1 < √c := (Real.lt_sqrt zero_le_one).2 (by simpa using hlt)
    have hmem : ![√c + 1, √c - 1] ∈ {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 < x 1} := by
      norm_num
      constructor <;> linarith
    have h' := h hmem
    norm_num at h'
    linarith
  · have hs : √c ≤ 1 := Real.sqrt_le_one.2 h
    have habs : |x 0 - x 1| < x 0 + x 1 := abs_lt.2 ⟨by linarith, by linarith⟩
    calc √c * |x 0 - x 1| ≤ 1 * |x 0 - x 1| := by gcongr
      _ < x 0 + x 1 := by rwa [one_mul]

/-- The partial derivative `∂₁ p_c = 2 (x₁ + x₂) - 2c (x₁ - x₂)`. -/
theorem eval_pderiv_zero_familyPoly (c : ℝ) (x : Fin 2 → ℝ) :
    eval x (pderiv 0 (familyPoly c)) = 2 * (x 0 + x 1) - 2 * c * (x 0 - x 1) := by
  simp [familyPoly, pderiv_X]
  ring

/-- At `c = 1/4`, `∂₁ p_c > 0` on the cone. -/
example {x : Fin 2 → ℝ} (hx : x ∈ gardingCone (familyPoly (1 / 4)) 1) :
    0 < eval x (pderiv 0 (familyPoly (1 / 4))) := by
  have hs : √(1 / 4 : ℝ) = 1 / 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [gardingCone_familyPoly (by norm_num), mem_ofPred_eq, hs] at hx
  rw [eval_pderiv_zero_familyPoly]
  linarith [le_abs_self (x 0 - x 1), neg_abs_le (x 0 - x 1)]

/-- At `c = 1`, `p_1 = 4 x₁ x₂`. -/
example (x : Fin 2 → ℝ) : eval x (familyPoly 1) = 4 * x 0 * x 1 := by
  simp only [eval_familyPoly]
  ring

/-- At `c = 1`, the cone of `p_1` is the open quadrant `Γ_2`. -/
example : gardingCone (familyPoly 1) 1 = {x | 0 < x 0 ∧ 0 < x 1} := by
  rw [gardingCone_familyPoly zero_le_one]
  ext x
  simp only [Real.sqrt_one, one_mul, mem_ofPred_eq, abs_lt]
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith

/-! ### A symmetric hyperbolic polynomial whose cone misses part of `Γ_2` -/

/-- The polynomial `p = 2xy - 0.9 (x² + y²)` on `ℝ²`. -/
def sectorPoly : MvPolynomial (Fin 2) ℝ :=
  C 2 * X 0 * X 1 - C (9 / 10) * (X 0 ^ 2 + X 1 ^ 2)

/-- The values of `p = 2xy - 0.9 (x² + y²)`. -/
@[simp]
theorem eval_sectorPoly (x : Fin 2 → ℝ) :
    eval x sectorPoly = 2 * x 0 * x 1 - 9 / 10 * (x 0 ^ 2 + x 1 ^ 2) := by
  simp [sectorPoly]

/-- `p = p_{19} / 20`. -/
theorem sectorPoly_eq : sectorPoly = (1 / 20 : ℝ) • familyPoly 19 := by
  refine MvPolynomial.funext fun x ↦ ?_
  simp only [eval_sectorPoly, smul_eval, eval_familyPoly]
  ring

/-- `p` is symmetric. -/
example : rename (Equiv.swap 0 1) sectorPoly = sectorPoly := by
  refine MvPolynomial.funext fun x ↦ ?_
  simp only [eval_rename, eval_sectorPoly, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  ring

/-- `p` is hyperbolic of degree `2` in the direction `(1, 1)`. -/
theorem isHyperbolic_sectorPoly : IsHyperbolic sectorPoly 2 1 := by
  rw [sectorPoly_eq]
  exact (isHyperbolic_familyPoly (by norm_num)).smul_left (by norm_num)

/-- The cone of `p` is the sector `{x₁ + x₂ > √19 |x₁ - x₂|}`. -/
theorem gardingCone_sectorPoly :
    gardingCone sectorPoly 1 = {x | √19 * |x 0 - x 1| < x 0 + x 1} := by
  rw [sectorPoly_eq, gardingCone_smul_left (by norm_num), gardingCone_familyPoly (by norm_num)]

/-- The point `(1, 0.1)` of `Γ_2` has `p(1, 0.1) = -0.709` and is not in the cone of `p`. -/
example : eval ![1, 1 / 10] sectorPoly = -709 / 1000 ∧
    ![(1 : ℝ), 1 / 10] ∉ gardingCone sectorPoly 1 := by
  refine ⟨by norm_num, ?_⟩
  have h4 : (4 : ℝ) ≤ √19 := Real.le_sqrt_of_sq_le (by norm_num)
  rw [gardingCone_sectorPoly]
  norm_num
  linarith

/-- `p(e₁) = -0.9 < 0`, and `e₁` is not in the closure of the cone of `p`. -/
example : eval ![1, 0] sectorPoly = -9 / 10 ∧
    ![(1 : ℝ), 0] ∉ closure (gardingCone sectorPoly 1) := by
  refine ⟨by norm_num, ?_⟩
  rw [sectorPoly_eq, gardingCone_smul_left (by norm_num),
    mem_closure_gardingCone_familyPoly_iff (by norm_num)]
  norm_num

/-- The point `(1, 0.7)` lies in the cone of `p`, with `p(1, 0.7) = 0.059`, but there
`∂ₓ p = -0.4 < 0`. -/
example : ![(1 : ℝ), 7 / 10] ∈ gardingCone sectorPoly 1 ∧
    eval ![1, 7 / 10] sectorPoly = 59 / 1000 ∧
    eval ![1, 7 / 10] (pderiv 0 sectorPoly) = -2 / 5 := by
  refine ⟨?_, by norm_num, ?_⟩
  · have h5 : √19 < 5 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    rw [gardingCone_sectorPoly]
    norm_num
    linarith
  · simp [sectorPoly, pderiv_X]
    norm_num

end TauCeti.HyperbolicExamples
