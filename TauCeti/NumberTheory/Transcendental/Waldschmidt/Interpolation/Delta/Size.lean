/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Delta.Operator
public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.EntryPolynomial
import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# The size of the delta-row entries of Waldschmidt's interpolation matrix

In the homogeneous rational case of Waldschmidt's lower bound for linear forms in logarithms,
the linear form is `a₁ λ₁ + ⋯ + aₘ λₘ` with integers `aⱼ`, `aₘ ≠ 0`, so the normalized
coefficients `β₀ = 0`, `βⱼ = -aⱼ / aₘ` are rational, and the rows of the interpolation matrix are
Baker's delta polynomials `∏ᵢ Δ(q zᵢ; τᵢ)` with `q = aₘ`
(`TauCeti.waldschmidtDelta`), `Δ(X; k) = (X + 1) ⋯ (X + k) / k!`. At rational coefficients `b`,
an entry is a rational number times the exponential factor `α₁^(t s₁) ⋯ αₘ^(t sₘ)`
(`TauCeti.waldschmidtOperatorEntry_map_algebraMap` and `TauCeti.map_waldschmidtDelta`):
the rational number is the value at `b` of `TauCeti.waldschmidtEntryPolynomial`.
Liouville's inequality
for a nonzero minor of the matrix then needs the denominators of these rational numbers, given by
`Subring.mul_waldschmidtOperatorEntry_waldschmidtDelta_mem`, and their absolute values, which this
file bounds.

By the formula `TauCeti.waldschmidtOperatorEntry_prod_aeval_X` for separated rows, the rational
factor of the entry of the operator `P(∂/∂z₀)` at the grid point `x = s · y` is

`(∑ₖ k! P^{[k]}(t) q ^ k Δ^{[k]}(q x₀; τ₀)) Δ(q x₁; τ₁) ⋯ Δ(q x_{m-1}; τ_{m-1})`,

where `^{[k]}` denotes the `k`-th Hasse derivative and the factor `q ^ k` comes from the rescaling
`z₀ ↦ q z₀` (`Polynomial.eval_hasseDeriv_comp_C_mul_X`). If `|q xᵢ| ≤ Nᵢ`, Baker's size bound
`TauCeti.abs_eval_hasseDeriv_multichoose_X_add_one_pow_le` bounds each value of `Δ` and of its
Hasse derivatives by `2 ^ (Nᵢ + τᵢ + 1)`, and the factorial-weighted sum `∑_{k ≤ τ₀} k! |q| ^ k`
is at most `(1 + τ₀ |q|) ^ τ₀` (`Nat.sum_range_factorial_mul_pow_le`). In the homogeneous rational
case `q x₀ = 0` and `q xⱼ = aₘ sⱼ - aⱼ sₘ`
(`TauCeti.mul_waldschmidtPoint_waldschmidtNormalize_zero` and
`TauCeti.mul_waldschmidtPoint_waldschmidtNormalize_succ`), so `|sⱼ| ≤ Sⱼ` allows
`N₀ = 0` and `Nⱼ = |aₘ| Sⱼ + |aⱼ| Sₘ`
(`TauCeti.abs_intCast_mul_waldschmidtPoint_waldschmidtNormalize_le`). For the delta-operator
columns `δ_k(∂/∂z₀; σ)` and `|t| ≤ T₁`, the Hasse derivatives of the operator are bounded by
`TauCeti.abs_eval_hasseDeriv_waldschmidtDeltaOperator_le`. All the integer grid, derivative,
degree and denominator parameters are kept separate.

## Main results

* `TauCeti.abs_intCast_mul_waldschmidtPoint_waldschmidtNormalize_le`: the bounds `Nᵢ` on the
  grid coordinates for integer coefficients.
* `TauCeti.abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_le`: if
  `|P^{[k]}(t)| ≤ H` for `k ≤ τ₀` and `|q xᵢ| ≤ Nᵢ`, this rational number has absolute value at
  most `H (1 + τ₀ |q|) ^ τ₀ 2 ^ (∑ᵢ (Nᵢ + τᵢ + 1))`.
* `TauCeti.abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_waldschmidtDeltaOperator_le`: the
  same with `H = 2 ^ (⌊σ / k⌋ (T₁ + k + 1) + (T₁ + (σ mod k) + 1))` for the delta-operator
  columns.

* `TauCeti.l1Norm_waldschmidtDelta_le`: the coefficient-length bound for the delta rows.
* `TauCeti.l1Norm_waldschmidtEntryPolynomial_waldschmidtDelta_le`: a parameter-only bound
  on the coefficient length of the entry polynomial in the normalized coefficients.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.1, Lemma 9.11, and §9.3.2.
* A. Baker, *A sharpening of the bounds for linear forms in logarithms*, Acta Arith. **21**
  (1972), 117–129.
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable {n : ℕ}

/-- **The grid in the rational case.** Let the linear form `a₀ + a₁ λ₁ + ⋯ + aₘ λₘ` have
integer coefficients with `aₘ ≠ 0`, normalized to the coefficients `β₀ = -a₀ / aₘ`,
`βⱼ = -aⱼ / aₘ`, and let `|sⱼ| ≤ Sⱼ`. Then the coordinates of `aₘ (s · y)` are bounded by
`|a₀| Sₘ` for `z₀` and by `|aₘ| Sⱼ + |aⱼ| Sₘ` for `zⱼ`, so `q = aₘ` and these bounds are admissible
in `TauCeti.abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_le`. -/
theorem abs_intCast_mul_waldschmidtPoint_waldschmidtNormalize_le (a₀ : ℤ) {a : Fin (n + 1) → ℤ}
    (ha : a (Fin.last n) ≠ 0) {s : Fin (n + 1) → ℤ} {S : Fin (n + 1) → ℕ}
    (hs : ∀ j, (s j).natAbs ≤ S j) (i : Fin (n + 1)) :
    |(a (Fin.last n) : ℚ) * waldschmidtPoint (waldschmidtNormalize (a₀ : ℚ) fun j ↦ (a j : ℚ)) s i|
      ≤ (Fin.cons (a₀.natAbs * S (Fin.last n)) fun k ↦
          (a (Fin.last n)).natAbs * S k.castSucc + (a k.castSucc).natAbs * S (Fin.last n) :
        Fin (n + 1) → ℕ) i := by
  have ha' : ((a (Fin.last n) : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.2 ha
  have habs (z : ℤ) : |(z : ℚ)| = z.natAbs := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
  have hs' (j : Fin (n + 1)) : |(s j : ℚ)| ≤ S j := by
    rw [habs]
    exact_mod_cast hs j
  cases i using Fin.cases with
  | zero =>
    rw [mul_waldschmidtPoint_waldschmidtNormalize_zero (c := fun j ↦ (a j : ℚ)) ha', Fin.cons_zero,
      abs_neg, abs_mul, habs a₀, Nat.cast_mul, mul_comm]
    gcongr
    exact hs' _
  | succ k =>
    rw [mul_waldschmidtPoint_waldschmidtNormalize_succ (c := fun j ↦ (a j : ℚ)) ha',
      Fin.cons_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · rw [habs]
      gcongr
      exact hs' _
    · rw [habs (a k.castSucc), mul_comm]
      gcongr
      exact hs' _

/-- The rational factor of the entry of `P(∂/∂z₀)` on the delta row `∏ᵢ Δ(q zᵢ; τᵢ)`, by the
formula `TauCeti.waldschmidtOperatorEntry_prod_aeval_X` for separated rows with `α = 1`. -/
private theorem eval_waldschmidtEntryPolynomial_waldschmidtDelta (b : Fin (n + 1) → ℚ) (t : ℤ)
    (s : Fin (n + 1) → ℤ) (q : ℤ) (τ : Fin (n + 1) →₀ ℕ) (P : Polynomial ℚ) :
    eval b (waldschmidtEntryPolynomial t s P (waldschmidtDelta q τ)) =
      (∑ k ∈ range (P.natDegree + 1), (Polynomial.derivative^[k] P).eval (t : ℚ) *
        (Polynomial.hasseDeriv k ((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) (τ 0)).comp
          (Polynomial.C (q : ℚ) * Polynomial.X))).eval (waldschmidtPoint b s 0)) *
        ∏ i : Fin n, ((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) (τ i.succ)).comp
          (Polynomial.C (q : ℚ) * Polynomial.X)).eval (waldschmidtPoint b s i.succ) := by
  have h₁ : waldschmidtOperatorEntry (fun _ ↦ (1 : ℚ)) b t s (waldschmidtDelta q τ) P =
      eval b (waldschmidtEntryPolynomial t s P (waldschmidtDelta q τ)) := by
    simp [waldschmidtOperatorEntry_eq_aeval]
  rw [← h₁, waldschmidtDelta_def, waldschmidtOperatorEntry_prod_aeval_X]
  simp only [Algebra.algebraMap_self, Polynomial.map_id, one_zpow, prod_const_one, mul_one]

/-- **The size of the delta-row entries.** Let the coefficients `b` be rational, let `q` be an
integer with `|q xᵢ| ≤ Nᵢ` for the coordinates of the grid point `x = s · y`, and let the
operator `P` satisfy `|P^{[k]}(t)| ≤ H` for its Hasse derivatives of order `k ≤ τ₀`. Then the
rational factor of the entry of `P(∂/∂z₀)` on the delta row `∏ᵢ Δ(q zᵢ; τᵢ)` has absolute value
at most `H (1 + τ₀ |q|) ^ τ₀ 2 ^ (∑ᵢ (Nᵢ + τᵢ + 1))`. -/
theorem abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_le {b : Fin (n + 1) → ℚ} {t : ℤ}
    {s : Fin (n + 1) → ℤ} {q : ℤ} {N : Fin (n + 1) → ℕ}
    (hx : ∀ i, |(q : ℚ) * waldschmidtPoint b s i| ≤ N i) {τ : Fin (n + 1) →₀ ℕ}
    {P : Polynomial ℚ} {H : ℚ} (hP : ∀ k ≤ τ 0, |(Polynomial.hasseDeriv k P).eval (t : ℚ)| ≤ H) :
    |eval b (waldschmidtEntryPolynomial t s P (waldschmidtDelta q τ))| ≤
      H * (1 + τ 0 * |(q : ℚ)|) ^ τ 0 * 2 ^ ∑ i, (N i + τ i + 1) := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hP 0 (Nat.zero_le _))
  -- The factors `Δ(q xᵢ; τᵢ)` of the coordinates other than `z₀`.
  have hprod : |∏ i : Fin n, ((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) (τ i.succ)).comp
      (Polynomial.C (q : ℚ) * Polynomial.X)).eval (waldschmidtPoint b s i.succ)| ≤
      ∏ i : Fin n, (2 : ℚ) ^ (N i.succ + τ i.succ + 1) := by
    rw [abs_prod]
    exact prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ by
      simpa only [Polynomial.hasseDeriv_zero', pow_zero, pow_one, one_mul] using
        abs_eval_hasseDeriv_multichoose_X_add_one_pow_comp_C_mul_X_le (hx i.succ) (τ i.succ) 1 0
  rw [eval_waldschmidtEntryPolynomial_waldschmidtDelta, abs_mul, Fin.sum_univ_succ, pow_add,
    ← mul_assoc]
  exact mul_le_mul (abs_sum_eval_iterate_derivative_mul_eval_hasseDeriv_le (hx 0) hP)
    (hprod.trans_eq (prod_pow_eq_pow_sum _ _ _)) (abs_nonneg _) (by positivity)

/-- **The coefficient length of the delta rows.** The product `∏ᵢ Δ(q Xᵢ; τᵢ)` has length at
most `∏ᵢ (τᵢ + 1) max(1, ‖q‖) ^ τᵢ`. -/
theorem l1Norm_waldschmidtDelta_le (q : ℤ) (τ : Fin (n + 1) →₀ ℕ) :
    (waldschmidtDelta (K := ℚ) q τ).l1Norm ≤
      ∏ i, ((τ i + 1 : ℝ) * max 1 ‖(q : ℚ)‖ ^ τ i) := by
  rw [waldschmidtDelta_def]
  refine (l1Norm_prod_le _ _).trans (prod_le_prod₀ (fun _ _ ↦ l1Norm_nonneg _) fun i _ ↦ ?_)
  simp only [Algebra.algebraMap_self, Polynomial.map_id]
  refine (Polynomial.l1Norm_toMvPolynomial_le i _).trans
    ((Polynomial.l1Norm_comp_le _ _).trans ?_)
  have hΔ : (Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) (τ i)).l1Norm ≤ τ i + 1 := by
    simpa using l1Norm_taylor_multichoose_X_add_one_le (x := 0) (n := 0) (by simp) (τ i)
  rw [natDegree_multichoose_X_add_one, Polynomial.C_mul_X_eq_monomial,
    Polynomial.l1Norm_monomial]
  exact mul_le_mul_of_nonneg_right hΔ (by positivity)

/-- **The coefficient length of the delta-row entries.** If `|sⱼ| ≤ S` and the Hasse derivatives
of `P` at `t` have norm at most `H`, then the entry polynomial in the normalized coefficients has
length at most `H ∏ᵢ ((τᵢ + 1) max(1, ‖q‖) ^ τᵢ) (|τ| + 2 S + 1) ^ |τ|`.
This bound depends only on the grid, row degrees, rescaling, and operator bound. -/
theorem l1Norm_waldschmidtEntryPolynomial_waldschmidtDelta_le {t : ℤ} {P : Polynomial ℚ} {H : ℝ}
    (hP : ∀ k, ‖(Polynomial.hasseDeriv k P).eval (t : ℚ)‖ ≤ H)
    {s : Fin (n + 1) → ℤ} {S : ℕ} (hs : ∀ j, (s j).natAbs ≤ S)
    (q : ℤ) (τ : Fin (n + 1) →₀ ℕ) :
    (waldschmidtEntryPolynomial t s P (waldschmidtDelta q τ)).l1Norm ≤
      H * (∏ i, ((τ i + 1 : ℝ) * max 1 ‖(q : ℚ)‖ ^ τ i)) *
        (τ.degree + 2 * S + 1 : ℝ) ^ τ.degree := by
  have hH : 0 ≤ H := (norm_nonneg _).trans (hP 0)
  have hs' (j : Fin (n + 1)) : ‖(s j : ℚ)‖ ≤ S := by
    rw [Int.norm_cast_rat, Int.norm_eq_abs, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast hs j
  have hdeg : (waldschmidtDelta (K := ℚ) q τ).totalDegree ≤ τ.degree :=
    (mem_restrictTotalDegree _ _ _).1 (waldschmidtDelta_mem_restrictTotalDegree q le_rfl)
  have hweight (μ : Fin (n + 1) →₀ ℕ) (hμ : μ ∈ (waldschmidtDelta (K := ℚ) q τ).support) :
      (μ 0 + ‖(s (Fin.last n) : ℚ)‖) ^ μ 0 *
        ∏ i : Fin n, (‖(s i.castSucc : ℚ)‖ + ‖(s (Fin.last n) : ℚ)‖) ^ μ i.succ ≤
          (τ.degree + 2 * S + 1 : ℝ) ^ τ.degree := by
    have hμ0 : μ 0 ≤ τ.degree :=
      (monomial_le_degreeOf 0 hμ).trans ((degreeOf_le_totalDegree _ _).trans hdeg)
    have hμd : ∑ i, μ i ≤ τ.degree := by
      simpa only [μ.sum_fintype (fun _ e ↦ e) (fun _ ↦ rfl)] using
        (le_totalDegree hμ).trans hdeg
    calc _ ≤ (τ.degree + 2 * S + 1 : ℝ) ^ μ 0 *
          ∏ i : Fin n, (τ.degree + 2 * S + 1 : ℝ) ^ μ i.succ := by
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · refine pow_le_pow_left₀ (by positivity) ?_ _
              have : (μ 0 : ℝ) ≤ τ.degree := by exact_mod_cast hμ0
              linarith [hs' (Fin.last n)]
            · refine prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ ?_
              refine pow_le_pow_left₀ (by positivity) ?_ _
              linarith [hs' i.castSucc, hs' (Fin.last n)]
      _ = (τ.degree + 2 * S + 1 : ℝ) ^ (∑ i, μ i) := by
        rw [prod_pow_eq_pow_sum, ← pow_add, Fin.sum_univ_succ]
      _ ≤ (τ.degree + 2 * S + 1 : ℝ) ^ τ.degree := by
        apply pow_le_pow_right₀ _ hμd
        linarith [Nat.cast_nonneg (α := ℝ) τ.degree, Nat.cast_nonneg (α := ℝ) S]
  refine (l1Norm_waldschmidtEntryPolynomial_le hP s _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hH
  exact (sum_le_sum fun μ hμ ↦ mul_le_mul_of_nonneg_left (hweight μ hμ) (norm_nonneg _)).trans
    (by rw [← sum_mul, ← l1Norm_def]; gcongr; exact l1Norm_waldschmidtDelta_le q τ)

/-- **The size of the delta-row entries with delta-operator columns.** Let the coefficients `b`
be rational, let `q` be an integer with `|q xᵢ| ≤ Nᵢ` for the coordinates of the grid point
`x = s · y`, and let `|t| ≤ T₁`. Write `σ = k p + r` with `0 ≤ r < k`. Then the rational factor
of the entry of the operator `δ_k(∂/∂z₀; σ)` on the delta row `∏ᵢ Δ(q zᵢ; τᵢ)` has absolute value
at most `2 ^ (p (T₁ + k + 1) + (T₁ + r + 1)) (1 + τ₀ |q|) ^ τ₀ 2 ^ (∑ᵢ (Nᵢ + τᵢ + 1))`. -/
theorem abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_waldschmidtDeltaOperator_le
    {b : Fin (n + 1) → ℚ} {t : ℤ} {s : Fin (n + 1) → ℤ} {q : ℤ} {N : Fin (n + 1) → ℕ}
    (hx : ∀ i, |(q : ℚ) * waldschmidtPoint b s i| ≤ N i) {T₁ : ℕ} (ht : t.natAbs ≤ T₁)
    (k σ : ℕ) (τ : Fin (n + 1) →₀ ℕ) :
    |eval b (waldschmidtEntryPolynomial t s (waldschmidtDeltaOperator k σ) (waldschmidtDelta q τ))|
      ≤ 2 ^ (σ / k * (T₁ + k + 1) + (T₁ + σ % k + 1)) * (1 + τ 0 * |(q : ℚ)|) ^ τ 0 *
        2 ^ ∑ i, (N i + τ i + 1) := by
  have htT : |(t : ℚ)| ≤ T₁ := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast ht
  exact abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_le hx
    fun κ _ ↦ abs_eval_hasseDeriv_waldschmidtDeltaOperator_le htT k σ κ

end TauCeti
