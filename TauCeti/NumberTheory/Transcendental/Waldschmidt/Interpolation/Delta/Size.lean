/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Delta.Operator
public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.EntryPolynomial
import Mathlib.RingTheory.MvPolynomial.Tower
import TauCeti.Algebra.Polynomial.HasseDeriv
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Data.Nat.Choose.Bounds

/-!
# The size of the delta-row entries of Waldschmidt's interpolation matrix

In the homogeneous rational case of Waldschmidt's lower bound for linear forms in logarithms,
the linear form is `a₁ λ₁ + ⋯ + aₘ λₘ` with integers `aⱼ`, `aₘ ≠ 0`, so the normalized
coefficients `β₀ = 0`, `βⱼ = -aⱼ / aₘ` are rational, and the rows of the interpolation matrix are
Baker's delta polynomials `∏ᵢ Δ(q zᵢ; τᵢ)` with `q = aₘ`
(`TauCeti.waldschmidtDelta`), `Δ(X; k) = (X + 1) ⋯ (X + k) / k!`. At rational coefficients `b`,
an entry is a rational number times the exponential factor `α₁^(t s₁) ⋯ αₘ^(t sₘ)`
(`TauCeti.waldschmidtOperatorEntry_waldschmidtDelta_eq_ratCast_mul`): the rational number is the
value at `b` of the entry polynomial `TauCeti.waldschmidtEntryPolynomial`. Liouville's inequality
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

* `TauCeti.waldschmidtOperatorEntry_waldschmidtDelta_eq_ratCast_mul`: at rational coefficients
  the entry of a delta row is a rational number times `α₁^(t s₁) ⋯ αₘ^(t sₘ)`.
* `TauCeti.abs_intCast_mul_waldschmidtPoint_waldschmidtNormalize_le`: the bounds `Nᵢ` on the
  grid coordinates for integer coefficients.
* `TauCeti.abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_le`: if
  `|P^{[k]}(t)| ≤ H` for `k ≤ τ₀` and `|q xᵢ| ≤ Nᵢ`, this rational number has absolute value at
  most `H (1 + τ₀ |q|) ^ τ₀ 2 ^ (∑ᵢ (Nᵢ + τᵢ + 1))`.
* `TauCeti.abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_waldschmidtDeltaOperator_le`: the
  same with `H = 2 ^ (⌊σ / k⌋ (T₁ + k + 1) + (T₁ + (σ mod k) + 1))` for the delta-operator
  columns.

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

/-- **The entries of the delta rows at rational coefficients.** Let `K` be a field of
characteristic zero and let the coefficients `β = b` and the operator `P` be rational. Then the
entry of the operator `P(∂/∂z₀)` on the delta row `∏ᵢ Δ(q zᵢ; τᵢ)` is the rational number obtained
by evaluating the entry polynomial at `b`, times `α₁^(t s₁) ⋯ αₘ^(t sₘ)`. -/
theorem waldschmidtOperatorEntry_waldschmidtDelta_eq_ratCast_mul {K : Type*} [Field K]
    [CharZero K] (α : Fin (n + 1) → K) (b : Fin (n + 1) → ℚ) (t : ℤ) (s : Fin (n + 1) → ℤ)
    (q : ℤ) (τ : Fin (n + 1) →₀ ℕ) (P : Polynomial ℚ) :
    waldschmidtOperatorEntry α (fun i ↦ (b i : K)) t s (waldschmidtDelta q τ)
        (P.map (algebraMap ℚ K)) =
      (eval b (waldschmidtEntryPolynomial t s P (waldschmidtDelta q τ)) : K) *
        ∏ j, α j ^ (t * s j) := by
  rw [← map_waldschmidtDelta (algebraMap ℚ K), waldschmidtOperatorEntry_map_algebraMap]
  have hb : (fun i ↦ (b i : K)) = algebraMap ℚ K ∘ b := funext fun i ↦ (eq_ratCast _ _).symm
  rw [hb, aeval_algebraMap_apply, eq_ratCast, aeval_eq_eval]

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
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
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

/-- The first factor of the rational factor: if `|q x| ≤ N` and `|P^{[k]}(t)| ≤ H` for `k ≤ τ`,
then `|∑ₖ P⁽ᵏ⁾(t) (Δ(q X; τ))^{[k]}(x)| ≤ H (1 + τ |q|) ^ τ 2 ^ (N + τ + 1)`. -/
private theorem abs_sum_eval_iterate_derivative_mul_eval_hasseDeriv_le {q : ℤ} {x : ℚ} {N : ℕ}
    (hx : |(q : ℚ) * x| ≤ N) {τ : ℕ} {t : ℤ} {P : Polynomial ℚ} {H : ℚ}
    (hP : ∀ k ≤ τ, |(Polynomial.hasseDeriv k P).eval (t : ℚ)| ≤ H) :
    |∑ k ∈ range (P.natDegree + 1), (Polynomial.derivative^[k] P).eval (t : ℚ) *
      (Polynomial.hasseDeriv k ((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) τ).comp
        (Polynomial.C (q : ℚ) * Polynomial.X))).eval x| ≤
      H * (1 + τ * |(q : ℚ)|) ^ τ * 2 ^ (N + τ + 1) := by
  set Q := (Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) τ).comp
    (Polynomial.C (q : ℚ) * Polynomial.X)
  set f := fun k ↦ (Polynomial.derivative^[k] P).eval (t : ℚ) *
    (Polynomial.hasseDeriv k Q).eval x with hfdef
  have hH : 0 ≤ H := (abs_nonneg _).trans (hP 0 (Nat.zero_le _))
  -- The Hasse derivatives of `Q` of order above `τ` vanish.
  have hf (k : ℕ) (hk : k ∉ range (τ + 1)) : |f k| = 0 := by
    have hQ : Polynomial.hasseDeriv k Q = 0 := by
      refine Polynomial.hasseDeriv_eq_zero_of_lt_natDegree _ _
        (lt_of_le_of_lt ?_ (by simpa [Nat.lt_succ_iff] using hk))
      exact natDegree_multichoose_X_add_one_comp_C_mul_X_le τ _
    simp [f, hQ]
  calc |∑ k ∈ range (P.natDegree + 1), f k|
      ≤ ∑ k ∈ range (P.natDegree + 1) ∪ range (τ + 1), |f k| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum_of_subset_of_nonneg subset_union_left
          fun _ _ _ ↦ abs_nonneg _)
    _ = ∑ k ∈ range (τ + 1), |f k| :=
        (sum_subset subset_union_right fun k _ hk ↦ hf k hk).symm
    _ ≤ ∑ k ∈ range (τ + 1), (k.factorial : ℚ) * |(q : ℚ)| ^ k * (H * 2 ^ (N + τ + 1)) := by
        refine sum_le_sum fun k hk ↦ ?_
        simp only [hfdef]
        rw [Polynomial.eval_iterate_derivative_eq_factorial_mul, abs_mul, abs_mul, Nat.abs_cast]
        have h₁ := hP k (Nat.lt_succ_iff.1 (mem_range.1 hk))
        have h₂ : |(Polynomial.hasseDeriv k Q).eval x| ≤ |(q : ℚ)| ^ k * 2 ^ (N + τ + 1) := by
          simpa only [pow_one, one_mul] using
            abs_eval_hasseDeriv_multichoose_X_add_one_pow_comp_C_mul_X_le hx τ 1 k
        calc (k.factorial : ℚ) * |(Polynomial.hasseDeriv k P).eval (t : ℚ)| *
              |(Polynomial.hasseDeriv k Q).eval x|
            ≤ k.factorial * H * (|(q : ℚ)| ^ k * 2 ^ (N + τ + 1)) := by gcongr
          _ = _ := by ring
    _ = (∑ k ∈ range (τ + 1), (k.factorial : ℚ) * |(q : ℚ)| ^ k) * (H * 2 ^ (N + τ + 1)) := by
        rw [sum_mul]
    _ ≤ (1 + τ * |(q : ℚ)|) ^ τ * (H * 2 ^ (N + τ + 1)) :=
        mul_le_mul_of_nonneg_right (Nat.sum_range_factorial_mul_pow_le _ (abs_nonneg _))
          (by positivity)
    _ = _ := by ring

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
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast ht
  exact abs_eval_waldschmidtEntryPolynomial_waldschmidtDelta_le hx
    fun κ _ ↦ abs_eval_hasseDeriv_waldschmidtDeltaOperator_le htT k σ κ

end TauCeti
