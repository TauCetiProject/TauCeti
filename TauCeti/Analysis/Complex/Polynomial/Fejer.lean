/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.DirichletSineSum

/-!
# Fejér polynomials

For each natural number `m`, the `m`-th **Fejér polynomial** is

`fejerPoly m w = ∑ j ∈ Finset.Icc 1 m, (w ^ (m - j) - w ^ (m + j)) / j`.

Its degree is at most `2 * m` and its real coefficients `fejerPolyCoeff m n` satisfy:

* `|fejerPolyCoeff m n| ≤ 1` for all `n`;
* the first `m` coefficients sum to the harmonic number `harmonic m`;
* all `2 * m + 1` coefficients sum to `fejerPoly m 1 = 0`;
* on the unit circle `w = exp (θ * I)`, `fejerPoly m w` factors as
  `-2 * I * exp (m * θ * I) * ∑ j ∈ Icc 1 m, sin (j * θ) / j`, so the uniform Gibbs–Fejér bound
  (`TauCeti.abs_sum_Icc_sin_div_le`) and the maximum modulus principle yield
  `‖fejerPoly m w‖ ≤ 2 * (1 + 2 * π)` on the closed unit disc `Metric.closedBall 0 1`, uniformly
  in `m`.

## Main declarations

* `TauCeti.fejerPoly`: the `m`-th Fejér polynomial.
* `TauCeti.fejerPolyCoeff`: its `n`-th real Taylor coefficient.
* `TauCeti.fejerPoly_eq_sum_range`: expansion of `fejerPoly m w` in powers of `w`.
* `TauCeti.sum_range_fejerPolyCoeff`: the partial sum of the first `m` coefficients is `harmonic m`.
* `TauCeti.norm_fejerPoly_le_of_norm_le_one`: uniform bound `2 * (1 + 2 * π)` on the closed unit
  disc.

## References

* L. Fejér, *Sur les singularités de la série de Fourier des fonctions continues*, Ann. Sci.
  École Norm. Sup. (3) 28 (1911), 63–104.
* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Ch. II, §2.
* A. Zygmund, *Trigonometric Series*, 3rd ed., Vol. I, Ch. VIII, §1.
-/

public section

open Filter Finset Metric Complex
open scoped Topology Real

namespace TauCeti

private noncomputable def fejerRealPoly (m : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Icc 1 m,
    (Polynomial.monomial (m - j) (j : ℝ)⁻¹ - Polynomial.monomial (m + j) (j : ℝ)⁻¹)

private theorem natDegree_fejerRealPoly_le (m : ℕ) : (fejerRealPoly m).natDegree ≤ 2 * m := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
  have hj_le : j ≤ m := (mem_Icc.mp hj).2
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le ((Polynomial.natDegree_monomial_le _).trans (by omega))
      ((Polynomial.natDegree_monomial_le _).trans (by omega)))

/-- The `m`-th Fejér polynomial `∑ j ∈ Icc 1 m, (w ^ (m - j) - w ^ (m + j)) / j`. -/
noncomputable def fejerPoly (m : ℕ) (w : ℂ) : ℂ :=
  (fejerRealPoly m).eval₂ Complex.ofRealHom w

theorem fejerPoly_def (m : ℕ) (w : ℂ) :
    fejerPoly m w = ∑ j ∈ Icc 1 m, (w ^ (m - j) - w ^ (m + j)) / (j : ℂ) := by
  simp only [fejerPoly, fejerRealPoly, Polynomial.eval₂_finsetSum, Polynomial.eval₂_sub,
    Polynomial.eval₂_monomial, Complex.ofRealHom_eq_coe, ofReal_inv, ofReal_natCast]
  refine sum_congr rfl fun j _ ↦ ?_
  ring

/-- The `n`-th real Taylor coefficient of `fejerPoly m`: it is `(m - n)⁻¹` for `n < m`,
`-(n - m)⁻¹` for `m < n ≤ 2 * m`, and `0` otherwise. -/
noncomputable def fejerPolyCoeff (m n : ℕ) : ℝ :=
  (fejerRealPoly m).coeff n

private theorem fejerPolyCoeff_eq_sub_sum (m n : ℕ) :
    fejerPolyCoeff m n =
      (∑ j ∈ Icc 1 m, if m - j = n then (j : ℝ)⁻¹ else 0) -
        ∑ j ∈ Icc 1 m, if m + j = n then (j : ℝ)⁻¹ else 0 := by
  simp only [fejerPolyCoeff, fejerRealPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_sub,
    Polynomial.coeff_monomial, Finsupp.single_apply, sum_sub_distrib]

private theorem sum_Icc_ite_inv_eq {p : ℕ → Prop} [DecidablePred p] (m k : ℕ)
    (hk : k ∈ Icc 1 m) (hp : ∀ j ∈ Icc 1 m, p j ↔ j = k) :
    (∑ j ∈ Icc 1 m, if p j then (j : ℝ)⁻¹ else 0) = (k : ℝ)⁻¹ := by
  rw [sum_congr rfl fun j hj ↦ if_congr (hp j hj) rfl rfl, sum_ite_eq' _ k _]
  simp [hk]

@[simp]
theorem fejerPoly_zero (w : ℂ) : fejerPoly 0 w = 0 := by
  simp [fejerPoly, fejerRealPoly]

@[simp]
theorem fejerPoly_one (m : ℕ) : fejerPoly m 1 = 0 := by
  simp [fejerPoly_def]

@[simp]
theorem fejerPolyCoeff_zero_left (n : ℕ) : fejerPolyCoeff 0 n = 0 := by
  simp [fejerPolyCoeff, fejerRealPoly]

theorem fejerPolyCoeff_of_lt {m n : ℕ} (h : n < m) :
    fejerPolyCoeff m n = ((m - n : ℕ) : ℝ)⁻¹ := by
  rw [fejerPolyCoeff_eq_sub_sum,
    sum_Icc_ite_inv_eq m (m - n) (mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun j hj ↦ by have := mem_Icc.mp hj; omega),
    sum_eq_zero fun j hj ↦ by have := mem_Icc.mp hj; simp [show m + j ≠ n by omega],
    sub_zero]

@[simp]
theorem fejerPolyCoeff_self (m : ℕ) : fejerPolyCoeff m m = 0 := by
  rw [fejerPolyCoeff_eq_sub_sum,
    sum_eq_zero fun j hj ↦ by have := mem_Icc.mp hj; simp [show m - j ≠ m by omega],
    sum_eq_zero fun j hj ↦ by simp [Nat.ne_of_gt (mem_Icc.mp hj).1],
    sub_zero]

theorem fejerPolyCoeff_of_gt_of_le {m n : ℕ} (h₁ : m < n) (h₂ : n ≤ 2 * m) :
    fejerPolyCoeff m n = -((n - m : ℕ) : ℝ)⁻¹ := by
  rw [fejerPolyCoeff_eq_sub_sum,
    sum_eq_zero fun j hj ↦ by have := mem_Icc.mp hj; simp [show m - j ≠ n by omega],
    sum_Icc_ite_inv_eq m (n - m) (mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun j hj ↦ by have := mem_Icc.mp hj; omega),
    zero_sub]

theorem fejerPolyCoeff_of_gt {m n : ℕ} (h : 2 * m < n) : fejerPolyCoeff m n = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt ((natDegree_fejerRealPoly_le m).trans_lt h)

theorem fejerPolyCoeff_def (m n : ℕ) :
    fejerPolyCoeff m n =
      if n < m then ((m - n : ℕ) : ℝ)⁻¹
      else if m < n ∧ n ≤ 2 * m then -((n - m : ℕ) : ℝ)⁻¹
      else 0 := by
  rcases lt_trichotomy n m with h | rfl | h
  · simp [h, fejerPolyCoeff_of_lt h]
  · simp
  · by_cases h2 : n ≤ 2 * m
    · have hnot : ¬ n < m := not_lt.mpr h.le
      simp [hnot, h, h2, fejerPolyCoeff_of_gt_of_le h h2]
    · have hgt : 2 * m < n := by omega
      have hnot1 : ¬ n < m := by omega
      have hnot2 : ¬ (m < n ∧ n ≤ 2 * m) := by omega
      simp [hnot1, hnot2, fejerPolyCoeff_of_gt hgt]

/-- Every coefficient of a Fejér polynomial has absolute value at most `1`. -/
theorem abs_fejerPolyCoeff_le_one (m n : ℕ) : |fejerPolyCoeff m n| ≤ 1 := by
  rw [fejerPolyCoeff_def]
  split_ifs with h₁ h₂
  · rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.sub_pos_of_lt h₁)
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.sub_pos_of_lt h₂.1)
  · simp

/-- Power-series expansion of `fejerPoly m w` in terms of `fejerPolyCoeff m`. -/
theorem fejerPoly_eq_sum_range (m : ℕ) (w : ℂ) :
    fejerPoly m w = ∑ n ∈ range (2 * m + 1), (fejerPolyCoeff m n : ℂ) * w ^ n := by
  simpa [fejerPoly, fejerPolyCoeff] using
    Polynomial.eval₂_eq_sum_range' Complex.ofRealHom
      (Nat.lt_succ_of_le (natDegree_fejerRealPoly_le m)) w

/-- The sum of the first `m` coefficients of `fejerPoly m` equals the `m`-th harmonic number. -/
theorem sum_range_fejerPolyCoeff (m : ℕ) :
    ∑ n ∈ range m, fejerPolyCoeff m n = (harmonic m : ℝ) := by
  have href := (Finset.sum_Ico_reflect (fejerPolyCoeff m) 1 (m := m + 1) (n := m) le_rfl).symm
  simp only [Nat.sub_self, Nat.add_sub_cancel, Nat.Ico_zero_eq_range,
    Ico_add_one_right_eq_Icc] at href
  rw [harmonic_eq_sum_Icc, href]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  refine sum_congr rfl fun j hj ↦ ?_
  have hmem := mem_Icc.mp hj
  rw [fejerPolyCoeff_of_lt (by omega : m - j < m), Nat.sub_sub_self hmem.2]

/-- The sum of all coefficients of `fejerPoly m` vanishes. -/
theorem sum_range_two_mul_add_one_fejerPolyCoeff (m : ℕ) :
    ∑ n ∈ range (2 * m + 1), fejerPolyCoeff m n = 0 := by
  apply ofReal_injective
  have h := fejerPoly_eq_sum_range m 1
  rw [fejerPoly_one] at h
  simpa [ofReal_sum] using h.symm

/-- On the unit circle `w = exp (θ * I)`, `fejerPoly m w` factors as `-2 * I * exp (m * θ * I)`
times the `m`-th Dirichlet sine sum. -/
theorem fejerPoly_exp_mul_I (m : ℕ) (θ : ℝ) :
    fejerPoly m (exp ((θ : ℂ) * I)) =
      -2 * I * exp ((m : ℂ) * θ * I) * ((∑ j ∈ Icc 1 m, Real.sin (j * θ) / j : ℝ) : ℂ) := by
  rw [fejerPoly_def, ofReal_sum, mul_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  have hjm : j ≤ m := (mem_Icc.mp hj).2
  have h1 : exp ((θ : ℂ) * I) ^ (m - j) = exp ((m : ℂ) * θ * I) * exp (-((j : ℂ) * θ * I)) := by
    rw [← exp_natCast_mul, ← exp_add, Nat.cast_sub hjm]
    congr 1
    ring
  have h2 : exp ((θ : ℂ) * I) ^ (m + j) = exp ((m : ℂ) * θ * I) * exp ((j : ℂ) * θ * I) := by
    rw [← exp_natCast_mul, ← exp_add, Nat.cast_add]
    congr 1
    ring
  have hsin : exp (-((j : ℂ) * θ * I)) - exp ((j : ℂ) * θ * I) =
      -2 * I * ((Real.sin (j * θ) : ℝ) : ℂ) := by
    have htwo := congrArg (· * (-I)) (Complex.two_sin ((j * θ : ℝ) : ℂ))
    simp only [mul_assoc, neg_mul, mul_neg, Complex.I_mul_I, neg_neg, mul_one] at htwo
    rw [← Complex.ofReal_sin] at htwo
    push_cast at htwo ⊢
    linear_combination -htwo
  rw [h1, h2, ← mul_sub, hsin, ofReal_div, ofReal_natCast]
  ring

theorem differentiable_fejerPoly (m : ℕ) : Differentiable ℂ (fejerPoly m) := by
  have h : fejerPoly m = fun w ↦ ((fejerRealPoly m).map Complex.ofRealHom).eval w :=
    funext fun w ↦ by simp only [fejerPoly, Polynomial.eval₂_eq_eval_map]
  exact h ▸ ((fejerRealPoly m).map Complex.ofRealHom).differentiable

theorem continuous_fejerPoly (m : ℕ) : Continuous (fejerPoly m) :=
  (differentiable_fejerPoly m).continuous

/-- **Uniform bound on Fejér polynomials on the closed unit disc.** By `fejerPoly_exp_mul_I`,
`abs_sum_Icc_sin_div_le`, and the maximum modulus principle, `‖fejerPoly m w‖ ≤ 2 * (1 + 2 * π)`
for every `m : ℕ` and `‖w‖ ≤ 1`. -/
theorem norm_fejerPoly_le_of_norm_le_one (m : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖fejerPoly m w‖ ≤ 2 * (1 + 2 * π) := by
  have hmem : w ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall_zero_iff]
    exact hw
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (differentiable_fejerPoly m).diffContOnCl (fun z hz ↦ ?_) hmem
  rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hz
  have hz_exp : z = exp ((arg z : ℂ) * I) := by
    simpa [hz] using (norm_mul_exp_arg_mul_I z).symm
  have hexp : ‖exp ((m : ℂ) * (arg z : ℂ) * I)‖ = 1 := by
    have harg : (m : ℂ) * (arg z : ℂ) * I = (((m : ℝ) * arg z : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg, norm_exp_ofReal_mul_I]
  rw [hz_exp, fejerPoly_exp_mul_I, norm_mul, norm_mul, norm_mul, norm_neg,
    Complex.norm_ofNat, norm_I, mul_one, hexp, mul_one, norm_real, Real.norm_eq_abs]
  gcongr
  exact abs_sum_Icc_sin_div_le m (arg z)

end TauCeti
