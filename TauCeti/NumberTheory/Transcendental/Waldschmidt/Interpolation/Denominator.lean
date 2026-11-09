/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Baker.Delta
public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Matrix
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.Subring.Basic

/-!
# Denominators of Waldschmidt's interpolation matrix

The entries of Waldschmidt's interpolation matrix are the coefficient-field factors

`γ_P = (∑ₖ P^{[k]}(t) (∂ᵏF/∂z₀ᵏ)(s · y)) α₁^(t s₁) ⋯ αₘ^(t sₘ)`

of the differential operators `P(∂/∂z₀)` applied to the auxiliary functions
`F(z) exp(t (z₀ + λ₁ z₁ + ⋯))` at the grid points `s · y`
(`TauCeti.waldschmidtOperatorEntry_eq_sum_hasseDeriv`). For the lower bound of Liouville type on
a nonzero minor of the matrix, these algebraic numbers are made integral by a common denominator.
This file computes such a denominator, relative to an arbitrary subring `A` of the coefficient
field `K` (in the application, the ring of integers of a number field). It is a product of three
factors, one for each part of the entry.

* **The polynomial.** If `F` has coefficients in `A` and total degree at most `T`, and `d ∈ A` is
  a common denominator of `β₀, …, β_{m-1}`, then `d` is a common denominator of the coordinates
  `sₘ β₀` and `sⱼ + sₘ βⱼ` of the grid point, so `d ^ T` clears the denominators of all the
  values `(∂ᵏF/∂z₀ᵏ)(s · y)`, which vanish for `k > T`.
* **The operator.** If `c P^{[k]}(t) ∈ A` for `k ≤ T`, then `c` clears the denominators of the
  operator. For the iterated derivatives `P = X^σ` the values `P^{[k]}(t) = (σ choose k) t^(σ - k)`
  are integers and `c = 1`. For powers of Baker's binomial polynomial `P = Δ(X; k) ^ l` one may
  take `c = L ^ T` with `L` any integer divisible by `1, …, k`, by Baker's denominator bound
  `TauCeti.pow_mul_eval_hasseDeriv_multichoose_X_add_one_pow_mem_range_intCast`.
* **The exponential factor.** If `aⱼ ∈ A` is a common denominator of `αⱼ` and `αⱼ⁻¹` and
  `|t sⱼ| ≤ Nⱼ`, then `∏ⱼ aⱼ ^ Nⱼ` clears the denominator of `α₁^(t s₁) ⋯ αₘ^(t sₘ)`
  (`Subring.prod_pow_mul_prod_zpow_mem`).

When the rows have `|t| ≤ T₁` and the columns have `|sⱼ| ≤ Sⱼ`, the exponents `Nⱼ = T₁ Sⱼ`
serve for all entries at once, so a single element of `A` clears the denominators of every entry
of the matrix (`Subring.mul_waldschmidtInterpolationMatrix_mem`).

## Main results

* `Subring.mul_waldschmidtOperatorEntry_mem`: `c d ^ T e γ_P ∈ A`, for denominators `c` of the
  operator, `d` of the coefficients `βᵢ` and `e` of the exponential factor.
* `Subring.mul_waldschmidtEntry_mem`: for the iterated derivatives, `d ^ T e γ ∈ A`.
* `Subring.mul_waldschmidtOperatorEntry_prod_aeval_X_mem`: denominators of the entries of a
  separated row `∏ᵢ Qᵢ(zᵢ)`, in terms of the denominators of the operator and of the factors `Qᵢ`.
* `Subring.pow_mul_waldschmidtOperatorEntry_multichoose_mem`: for the operators `Δ(∂/∂z₀; k) ^ l`
  built from Baker's binomial polynomial, `L ^ T d ^ T e γ ∈ A`.
* `Subring.mul_waldschmidtInterpolationMatrix_mem`: a common denominator of all the entries of
  the interpolation matrix.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §§9.2.1, 9.3.2.
* A. Baker, *A sharpening of the bounds for linear forms in logarithms*, Acta Arith. **21**
  (1972), 117–129.
-/

public section

open Finset MvPolynomial TauCeti

namespace Subring

variable {n : ℕ}

/-- A common denominator `d` of the coefficients `β₀, …, β_{m-1}` is a common denominator of the
coordinates `sₘ β₀` and `sⱼ + sₘ βⱼ` of every grid point `s · y`. -/
theorem mul_waldschmidtPoint_mem {R : Type*} [CommRing R] (A : Subring R) {b : Fin (n + 1) → R}
    {d : R} (hd : d ∈ A) (hb : ∀ i, d * b i ∈ A) (s : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    d * waldschmidtPoint b s i ∈ A := by
  cases i using Fin.cases with
  | zero =>
    rw [waldschmidtPoint_apply_zero, mul_left_comm]
    exact mul_mem (intCast_mem A _) (hb 0)
  | succ k =>
    rw [waldschmidtPoint_apply_succ, mul_add, mul_comm d, mul_left_comm]
    exact add_mem (mul_mem (intCast_mem A _) hd) (mul_mem (intCast_mem A _) (hb k.succ))

variable {K : Type*} [Field K] (A : Subring K)

/-- **Denominators of the operator entries.** Let `F` have coefficients in the subring `A` and
total degree at most `T`, let `d ∈ A` with `d βᵢ ∈ A` for all `i`, let `c` clear the
denominators of the Hasse derivatives of the operator at `t`, in the sense that
`c P^{[k]}(t) ∈ A` for `k ≤ T`, and let `e` clear the denominator of the exponential factor
`α₁^(t s₁) ⋯ αₘ^(t sₘ)`. Then `c d ^ T e γ_P ∈ A`. -/
theorem mul_waldschmidtOperatorEntry_mem {α b : Fin (n + 1) → K} {t : ℤ} {s : Fin (n + 1) → ℤ}
    {F : MvPolynomial (Fin (n + 1)) K} {P : Polynomial K} {T : ℕ} {c d e : K}
    (hF : ∀ m, F.coeff m ∈ A) (hFT : F.totalDegree ≤ T) (hd : d ∈ A) (hb : ∀ i, d * b i ∈ A)
    (hP : ∀ k ≤ T, c * (Polynomial.hasseDeriv k P).eval (t : K) ∈ A)
    (he : e * ∏ j, α j ^ (t * s j) ∈ A) :
    c * d ^ T * e * waldschmidtOperatorEntry α b t s F P ∈ A := by
  have h (x y : K) : c * d ^ T * e * (x * y) = c * d ^ T * x * (e * y) := by ring
  rw [waldschmidtOperatorEntry_eq_sum_hasseDeriv, h, Finset.mul_sum]
  refine mul_mem (sum_mem fun k _ ↦ ?_) he
  rw [mul_mul_mul_comm]
  rcases le_or_gt k T with hk | hk
  · exact mul_mem (hP k hk) (pow_mul_eval_mem (coeff_iterate_pderiv_mem hF 0 k)
      ((totalDegree_iterate_pderiv_le 0 k F).trans ((Nat.sub_le _ _).trans hFT)) hd
      (mul_waldschmidtPoint_mem A hd hb s))
  · rw [iterate_pderiv_eq_zero_of_totalDegree_lt (hFT.trans_lt hk), map_zero, mul_zero,
      mul_zero]
    exact zero_mem A

/-- **Denominators of the derivative entries.** For the iterated derivatives `∂^σ/∂z₀^σ`, the
Hasse derivatives `(σ choose k) t^(σ - k)` of `X^σ` at `t` are integers, so `d ^ T e γ ∈ A`
under the hypotheses of `Subring.mul_waldschmidtOperatorEntry_mem` on `F`, `d` and `e`. -/
theorem mul_waldschmidtEntry_mem {α b : Fin (n + 1) → K} {t : ℤ} {s : Fin (n + 1) → ℤ}
    {F : MvPolynomial (Fin (n + 1)) K} {T : ℕ} {d e : K} (hF : ∀ m, F.coeff m ∈ A)
    (hFT : F.totalDegree ≤ T) (hd : d ∈ A) (hb : ∀ i, d * b i ∈ A)
    (he : e * ∏ j, α j ^ (t * s j) ∈ A) (σ : ℕ) :
    d ^ T * e * waldschmidtEntry α b F t σ s ∈ A := by
  have h := mul_waldschmidtOperatorEntry_mem A (c := 1) (P := Polynomial.X ^ σ) hF hFT hd hb
    (fun k _ ↦ ?_) he
  · rwa [one_mul, waldschmidtOperatorEntry_X_pow] at h
  rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.hasseDeriv_monomial,
    Polynomial.eval_monomial, one_mul, mul_one]
  exact mul_mem (natCast_mem A _) (pow_mem (intCast_mem A _) _)

/-- **Denominators of the entries of a separated row.** Let `x = s · y`. Suppose that `u` clears
the denominators of the derivatives of the operator, `u P⁽ᵏ⁾(t) ∈ A`, and `c` those of the Hasse
derivatives of the first factor, `c Q₀^{[k]}(x₀) ∈ A`, for `k ≤ deg Q₀`; that `dᵢ Qᵢ(xᵢ) ∈ A` for
the other factors; and that `e` clears the denominator of the exponential factor
`α₁^(t s₁) ⋯ αₘ^(t sₘ)`. Then `u c (∏ᵢ dᵢ) e γ_P ∈ A` for the entry `γ_P` of the operator
`P(∂/∂z₀)` on the row `∏ᵢ Qᵢ(zᵢ)`. -/
theorem mul_waldschmidtOperatorEntry_prod_aeval_X_mem {α b : Fin (n + 1) → K} {t : ℤ}
    {s : Fin (n + 1) → ℤ} {Q : Fin (n + 1) → Polynomial K} {P : Polynomial K} {u c e : K}
    {d : Fin n → K}
    (hP : ∀ k ≤ (Q 0).natDegree, u * (Polynomial.derivative^[k] P).eval (t : K) ∈ A)
    (hQ₀ : ∀ k ≤ (Q 0).natDegree,
      c * (Polynomial.hasseDeriv k (Q 0)).eval (waldschmidtPoint b s 0) ∈ A)
    (hQ : ∀ i : Fin n, d i * (Q i.succ).eval (waldschmidtPoint b s i.succ) ∈ A)
    (he : e * ∏ j, α j ^ (t * s j) ∈ A) :
    u * c * (∏ i, d i) * e *
      waldschmidtOperatorEntry α b t s (∏ i, Polynomial.aeval (X i) (Q i)) P ∈ A := by
  have h (x y z : K) : u * c * (∏ i, d i) * e * (x * y * z) =
      u * c * x * ((∏ i, d i) * y) * (e * z) := by ring
  rw [waldschmidtOperatorEntry_prod_aeval_X, h, mul_sum, ← prod_mul_distrib]
  refine mul_mem (mul_mem (sum_mem fun k _ ↦ ?_) (prod_mem fun i _ ↦ hQ i)) he
  rcases le_or_gt k (Q 0).natDegree with hk | hk
  · rw [mul_mul_mul_comm]
    exact mul_mem (hP k hk) (hQ₀ k hk)
  · rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree _ _ hk, Polynomial.eval_zero, mul_zero,
      mul_zero]
    exact zero_mem A

/-- **Denominators of Baker's operator entries.** Let `L` be an integer divisible by each of
`1, …, k`. For the operator `Δ(∂/∂z₀; k) ^ l`, the `l`-th power of Baker's binomial polynomial
`Δ(X; k) = (X + 1) ⋯ (X + k) / k!`, the number `L ^ T` clears the denominators of the operator,
so `L ^ T d ^ T e γ ∈ A` under the hypotheses of `Subring.mul_waldschmidtOperatorEntry_mem` on
`F`, `d` and `e`. -/
theorem pow_mul_waldschmidtOperatorEntry_multichoose_mem [CharZero K] {α b : Fin (n + 1) → K}
    {t : ℤ} {s : Fin (n + 1) → ℤ} {F : MvPolynomial (Fin (n + 1)) K} {T : ℕ} {d e : K}
    (hF : ∀ m, F.coeff m ∈ A) (hFT : F.totalDegree ≤ T) (hd : d ∈ A) (hb : ∀ i, d * b i ∈ A)
    (he : e * ∏ j, α j ^ (t * s j) ∈ A) {k : ℕ} {L : ℤ}
    (hL : ∀ j ∈ Finset.Icc 1 k, (j : ℤ) ∣ L) (l : ℕ) :
    (L : K) ^ T * d ^ T * e * waldschmidtOperatorEntry α b t s F
      ((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) k ^ l).map (algebraMap ℚ K)) ∈ A := by
  refine mul_waldschmidtOperatorEntry_mem A hF hFT hd hb (fun κ hκ ↦ ?_) he
  obtain ⟨z, hz⟩ := pow_mul_eval_hasseDeriv_multichoose_X_add_one_pow_mem_range_intCast hL l κ t
  have hz' : (L : K) ^ κ * algebraMap ℚ K ((Polynomial.hasseDeriv κ
      (Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) k ^ l)).eval (t : ℚ)) = z := by
    rw [← map_intCast (algebraMap ℚ K) z, hz, map_mul, (algebraMap ℚ K).map_pow, map_intCast]
  rw [Polynomial.hasseDeriv_map, Polynomial.eval_map, ← map_intCast (algebraMap ℚ K) t,
    Polynomial.eval₂_at_apply, ← Nat.sub_add_cancel hκ, pow_add, mul_assoc, hz']
  exact mul_mem (pow_mem (intCast_mem A _) _) (intCast_mem A _)

/-- **A common denominator of the interpolation matrix.** Let the rows have polynomials `F r`
with coefficients in `A` and total degree at most `T` and exponents `|t r| ≤ T₁`, let the columns
have grid points with `|sⱼ| ≤ Sⱼ`, and let `u` clear the denominators of the operators of all
columns at all the exponents of the rows, in the sense that `u (P c)^{[k]}(t r) ∈ A` for
`k ≤ T`. If `d ∈ A` is a common denominator of the `βᵢ` and `aⱼ ∈ A` a common denominator of `αⱼ`
and `αⱼ⁻¹`, then `u d ^ T ∏ⱼ aⱼ ^ (T₁ Sⱼ)` times every entry of the interpolation matrix lies
in `A`. -/
theorem mul_waldschmidtInterpolationMatrix_mem {ι κ : Type*} {α a b : Fin (n + 1) → K}
    {F : ι → MvPolynomial (Fin (n + 1)) K} {t : ι → ℤ} {P : κ → Polynomial K}
    {s : κ → Fin (n + 1) → ℤ} {T T₁ : ℕ} {S : Fin (n + 1) → ℕ} {u d : K}
    (hF : ∀ r m, (F r).coeff m ∈ A) (hFT : ∀ r, (F r).totalDegree ≤ T) (ht : ∀ r, (t r).natAbs ≤ T₁)
    (hs : ∀ c j, (s c j).natAbs ≤ S j) (hd : d ∈ A) (hb : ∀ i, d * b i ∈ A)
    (hP : ∀ r c, ∀ k ≤ T, u * (Polynomial.hasseDeriv k (P c)).eval (t r : K) ∈ A)
    (ha : ∀ j, a j ∈ A) (hα : ∀ j, a j * α j ∈ A) (hα' : ∀ j, a j * (α j)⁻¹ ∈ A) (r : ι)
    (c : κ) :
    u * d ^ T * (∏ j, a j ^ (T₁ * S j)) * waldschmidtInterpolationMatrix α b F t P s r c ∈ A := by
  rw [waldschmidtInterpolationMatrix_apply]
  refine mul_waldschmidtOperatorEntry_mem A (hF r) (hFT r) hd hb (hP r c)
    (A.prod_pow_mul_prod_zpow_mem (fun j _ ↦ ha j) (fun j _ ↦ hα j) (fun j _ ↦ hα' j)
      fun j _ ↦ ?_)
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (ht r) (hs c j)

end Subring
