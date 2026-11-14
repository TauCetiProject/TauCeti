/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Delta.Basic
import TauCeti.Algebra.Polynomial.Lifts

/-!
# The delta operators of Waldschmidt's interpolation matrix

In the arithmetic estimate of Waldschmidt's interpolation determinant, the columns of iterated
derivatives `∂^σ/∂z₀^σ`, `σ < N`, are replaced by the columns of the differential operators
`δ_k(∂/∂z₀; σ)`, built from Baker's binomial polynomial `Δ(X; k) = (X + 1) ⋯ (X + k) / k!`:
writing `σ = k q + r` with `0 ≤ r < k`,

`δ_k(X; σ) = Δ(X; k) ^ q Δ(X; r)`

(`TauCeti.waldschmidtDeltaOperator k σ`; in the proof `k` is the parameter `S₀♯`). These
polynomials have degree `σ`, so they form a polynomial sequence
(`TauCeti.waldschmidtDeltaSequence`), and the columns of the operators `δ_k(∂/∂z₀; σ)`, `σ < N`,
span the same space as the columns of the iterated derivatives
(`TauCeti.span_image_waldschmidtOperatorEntry_waldschmidtDeltaOperator`); the interpolation
matrix keeps its rank.

The point of the change of basis is arithmetic. By the Leibniz formula
`TauCeti.waldschmidtOperatorEntry_eq_sum_hasseDeriv`, the entries of the operator `P(∂/∂z₀)` on
the auxiliary function with exponent `t` involve the numbers `P^{[κ]}(t)`, the Hasse derivatives
of `P` at the integer `t`. For the iterated derivatives these are the binomial numbers
`(σ choose κ) t^(σ - κ)`, as large as `|t| ^ σ`, whereas for `δ_k(X; σ)` the exponent `σ` is
replaced by the quotient `q = σ / k`: if `|x| ≤ n` then
`|δ_k^{[κ]}(x; σ)| ≤ 2 ^ (q (n + k + 1) + (n + r + 1))`
(`TauCeti.abs_eval_hasseDeriv_waldschmidtDeltaOperator_le`). The price is a denominator: if
`L` is an integer divisible by each of `1, …, k`, then `L ^ κ δ_k^{[κ]}(x; σ)` is an integer for
every integer `x` (`TauCeti.pow_mul_eval_hasseDeriv_waldschmidtDeltaOperator_mem_range_intCast`).
These give common denominators of the interpolation matrices with delta-operator columns, both
with rows of polynomials with integral coefficients
(`Subring.pow_mul_waldschmidtInterpolationMatrix_waldschmidtDeltaOperator_mem`) and with Baker's
delta rows `∏ᵢ Δ(q zᵢ; τᵢ)` of the homogeneous rational case
(`Subring.pow_mul_waldschmidtInterpolationMatrix_waldschmidtDelta_waldschmidtDeltaOperator_mem`).

## Main definitions

* `TauCeti.waldschmidtDeltaOperator k σ`: the polynomial `δ_k(X; σ) = Δ(X; k) ^ q Δ(X; r)`.
* `TauCeti.waldschmidtDeltaSequence K k`: the polynomials `δ_k(X; σ)` as a polynomial sequence
  over a field `K` of characteristic zero.

## Main results

* `TauCeti.natDegree_waldschmidtDeltaOperator`: `δ_k(X; σ)` has degree `σ`.
* `TauCeti.span_image_waldschmidtOperatorEntry_waldschmidtDeltaOperator`: the columns of the
  operators `δ_k(∂/∂z₀; σ)`, `σ < N`, span the same space as those of the iterated derivatives.
* `TauCeti.pow_mul_eval_hasseDeriv_waldschmidtDeltaOperator_mem_range_intCast`: the denominator
  bound `L ^ κ δ_k^{[κ]}(x; σ) ∈ ℤ` for integral `x`.
* `TauCeti.abs_eval_hasseDeriv_waldschmidtDeltaOperator_le`: the size bound.
* `Subring.pow_mul_waldschmidtInterpolationMatrix_waldschmidtDeltaOperator_mem` and
  `Subring.pow_mul_waldschmidtInterpolationMatrix_waldschmidtDelta_waldschmidtDeltaOperator_mem`:
  common denominators of the interpolation matrices with delta-operator columns.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §§9.2.1, 9.3.2.
* A. Baker, *A sharpening of the bounds for linear forms in logarithms*, Acta Arith. **21**
  (1972), 117–129.
-/

public section

open Finset Polynomial

namespace TauCeti

/-- Waldschmidt's delta polynomial `δ_k(X; σ) = Δ(X; k) ^ q Δ(X; r)`, where `σ = k q + r` with
`0 ≤ r < k` and `Δ(X; k) = (X + 1) ⋯ (X + k) / k!` is Baker's binomial polynomial. For `k = 0` it
is `Δ(X; σ)`. Used as the differential operator `δ_k(∂/∂z₀; σ)`, it replaces the iterated
derivative `∂^σ/∂z₀^σ` in the columns of the interpolation matrix. -/
noncomputable def waldschmidtDeltaOperator (k σ : ℕ) : ℚ[X] :=
  Ring.multichoose (X + 1 : ℚ[X]) k ^ (σ / k) * Ring.multichoose (X + 1 : ℚ[X]) (σ % k)

/-- The defining formula of `waldschmidtDeltaOperator k σ`. -/
theorem waldschmidtDeltaOperator_def (k σ : ℕ) :
    waldschmidtDeltaOperator k σ =
      Ring.multichoose (X + 1 : ℚ[X]) k ^ (σ / k) * Ring.multichoose (X + 1 : ℚ[X]) (σ % k) :=
  (rfl)

/-- Below the block length, `δ_k(X; σ)` is Baker's binomial polynomial `Δ(X; σ)`. -/
@[simp]
theorem waldschmidtDeltaOperator_of_lt {k σ : ℕ} (h : σ < k) :
    waldschmidtDeltaOperator k σ = Ring.multichoose (X + 1 : ℚ[X]) σ := by
  rw [waldschmidtDeltaOperator_def, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, pow_zero, one_mul]

/-- `δ_k(X; 0) = 1`. -/
@[simp]
theorem waldschmidtDeltaOperator_zero (k : ℕ) : waldschmidtDeltaOperator k 0 = 1 := by
  simp [waldschmidtDeltaOperator_def]

/-- **The recursion of the delta polynomials.**
`δ_k(X; σ + k) = Δ(X; k) δ_k(X; σ)`. For `k > 0`, together with
`TauCeti.waldschmidtDeltaOperator_of_lt` this determines `δ_k(X; σ)` for all `σ`. -/
theorem waldschmidtDeltaOperator_add (k σ : ℕ) :
    waldschmidtDeltaOperator k (σ + k) =
      Ring.multichoose (X + 1 : ℚ[X]) k * waldschmidtDeltaOperator k σ := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  rw [waldschmidtDeltaOperator_def, waldschmidtDeltaOperator_def, Nat.add_div_right _ hk,
    Nat.add_mod_right, pow_succ']
  ring

/-- The delta polynomial `δ_k(X; σ)` has natural degree `σ`. -/
@[simp]
theorem natDegree_waldschmidtDeltaOperator (k σ : ℕ) :
    (waldschmidtDeltaOperator k σ).natDegree = σ := by
  rw [waldschmidtDeltaOperator_def, natDegree_mul (pow_ne_zero _ (multichoose_X_add_one_ne_zero k))
    (multichoose_X_add_one_ne_zero _), natDegree_pow, natDegree_multichoose_X_add_one,
    natDegree_multichoose_X_add_one, mul_comm, Nat.div_add_mod]

/-- The delta polynomial `δ_k(X; σ)` is nonzero. -/
theorem waldschmidtDeltaOperator_ne_zero (k σ : ℕ) : waldschmidtDeltaOperator k σ ≠ 0 := by
  rw [waldschmidtDeltaOperator_def]
  exact mul_ne_zero (pow_ne_zero _ (multichoose_X_add_one_ne_zero k))
    (multichoose_X_add_one_ne_zero _)

/-- The delta polynomial `δ_k(X; σ)` has degree `σ`. -/
@[simp]
theorem degree_waldschmidtDeltaOperator (k σ : ℕ) : (waldschmidtDeltaOperator k σ).degree = σ := by
  rw [degree_eq_natDegree (waldschmidtDeltaOperator_ne_zero k σ),
    natDegree_waldschmidtDeltaOperator]

/-- The delta polynomials `δ_k(X; σ)`, mapped to `K[X]` for a field `K` of characteristic zero,
form a polynomial sequence: `δ_k(X; σ)` has degree `σ`. -/
noncomputable def waldschmidtDeltaSequence (K : Type*) [Field K] [CharZero K] (k : ℕ) :
    Polynomial.Sequence K where
  elems' σ := (waldschmidtDeltaOperator k σ).map (algebraMap ℚ K)
  degree_eq' σ := by
    rw [degree_map_eq_of_injective (algebraMap ℚ K).injective, degree_waldschmidtDeltaOperator]

/-- The `σ`-th term of `TauCeti.waldschmidtDeltaSequence K k` is `δ_k(X; σ)`. -/
@[simp]
theorem waldschmidtDeltaSequence_apply (K : Type*) [Field K] [CharZero K] (k σ : ℕ) :
    waldschmidtDeltaSequence K k σ = (waldschmidtDeltaOperator k σ).map (algebraMap ℚ K) :=
  (rfl)

/-- **Change of basis to the delta operators.** Fix a family of rows, the `r`-th built from the
polynomial `F r` and the integer `t r`, and a grid point `s`. The columns of entries of the
operators `δ_k(∂/∂z₀; σ)`, `σ < N`, span the same space as the columns of entries of the iterated
derivatives `∂^σ/∂z₀^σ`, `σ < N`. -/
theorem span_image_waldschmidtOperatorEntry_waldschmidtDeltaOperator {n : ℕ} {K : Type*}
    [Field K] [CharZero K] {ι : Type*} (α b : Fin (n + 1) → K)
    (F : ι → MvPolynomial (Fin (n + 1)) K) (t : ι → ℤ) (s : Fin (n + 1) → ℤ) (k N : ℕ) :
    Submodule.span K ((fun σ r ↦ waldschmidtOperatorEntry α b (t r) s (F r)
        ((waldschmidtDeltaOperator k σ).map (algebraMap ℚ K))) '' Set.Iio N) =
      Submodule.span K ((fun σ r ↦ waldschmidtEntry α b (F r) (t r) σ s) '' Set.Iio N) := by
  simpa only [waldschmidtDeltaSequence_apply] using
    span_image_waldschmidtOperatorEntry_sequence α b F t s (waldschmidtDeltaSequence K k) N

/-- **The denominator bound for the delta polynomials.** Let `k > 0` and let `L` be an integer
divisible by each of `1, …, k`. Then for every integer `x` and every `κ`,
`L ^ κ (1 / κ!) (d / dx) ^ κ δ_k(x; σ)` is an integer. -/
theorem pow_mul_eval_hasseDeriv_waldschmidtDeltaOperator_mem_range_intCast {k : ℕ} (hk : 0 < k)
    {L : ℤ} (hL : ∀ j ∈ Icc 1 k, (j : ℤ) ∣ L) (σ κ : ℕ) (x : ℤ) :
    (L : ℚ) ^ κ * (hasseDeriv κ (waldschmidtDeltaOperator k σ)).eval (x : ℚ) ∈
      Set.range (Int.cast : ℤ → ℚ) := by
  refine pow_mul_eval_hasseDeriv_mem_range_intCast_of_comp_mem_lifts ?_ κ
  rw [waldschmidtDeltaOperator_def, mul_comp, pow_comp]
  -- The remainder `σ % k` is below `k`, so `1, …, σ % k` also divide `L`.
  refine mul_mem (pow_mem (multichoose_X_add_one_comp_C_add_C_mul_X_mem_lifts hL x) _)
    (multichoose_X_add_one_comp_C_add_C_mul_X_mem_lifts (fun j hj ↦ hL j ?_) x)
  rw [mem_Icc] at hj ⊢
  exact ⟨hj.1, hj.2.trans (Nat.mod_lt σ hk).le⟩

/-- **The size bound for the delta polynomials.** If `x` is rational with `|x| ≤ n`, then for
`σ = k q + r` with `0 ≤ r < k` and every `κ`,
`|(1 / κ!) (d / dx) ^ κ δ_k(x; σ)| ≤ 2 ^ (q (n + k + 1) + (n + r + 1))`. -/
theorem abs_eval_hasseDeriv_waldschmidtDeltaOperator_le {x : ℚ} {n : ℕ} (hx : |x| ≤ n)
    (k σ κ : ℕ) :
    |(hasseDeriv κ (waldschmidtDeltaOperator k σ)).eval x| ≤
      2 ^ (σ / k * (n + k + 1) + (n + σ % k + 1)) := by
  have hlen (j : ℕ) : (taylor x (Ring.multichoose (X + 1 : ℚ[X]) j)).l1Norm ≤ 2 ^ (n + j + 1) :=
    (l1Norm_taylor_multichoose_X_add_one_le hx j).trans
      (by exact_mod_cast Nat.choose_le_two_pow _ _)
  have h : ‖(hasseDeriv κ (waldschmidtDeltaOperator k σ)).eval x‖ ≤
      2 ^ (σ / k * (n + k + 1) + (n + σ % k + 1)) := by
    rw [← taylor_coeff, waldschmidtDeltaOperator_def, taylor_mul, taylor_pow, pow_add, pow_mul']
    refine (norm_coeff_le_l1Norm _ κ).trans ((l1Norm_mul_le _ _).trans ?_)
    exact mul_le_mul ((l1Norm_pow_le _ _).trans (pow_le_pow_left₀ (l1Norm_nonneg _) (hlen k) _))
      (hlen _) (l1Norm_nonneg _) (by positivity)
  rw [← Rat.cast_le (K := ℝ)]
  simpa [← Rat.norm_cast_real, Real.norm_eq_abs] using h

end TauCeti

namespace Subring

open TauCeti

variable {n : ℕ} {K : Type*} [Field K] [CharZero K] (A : Subring K)

/-- **A common denominator of the interpolation matrix with delta-operator columns.** Let the
rows have polynomials `F r` with coefficients in `A` and total degree at most `T` and exponents
`|t r| ≤ T₁`, and let the columns be the operators `δ_k(∂/∂z₀; σ c)` at grid points with
`|sⱼ| ≤ Sⱼ`. Let `k > 0` and let `L` be an integer divisible by each of `1, …, k`. If `d ∈ A` is a
common denominator of the `βᵢ` and `aⱼ ∈ A` a common denominator of `αⱼ` and `αⱼ⁻¹`, then
`L ^ T d ^ T ∏ⱼ aⱼ ^ (T₁ Sⱼ)` times every entry of the interpolation matrix lies in `A`. -/
theorem pow_mul_waldschmidtInterpolationMatrix_waldschmidtDeltaOperator_mem {ι κ : Type*}
    {α a b : Fin (n + 1) → K} {F : ι → MvPolynomial (Fin (n + 1)) K} {t : ι → ℤ}
    {σ : κ → ℕ} {s : κ → Fin (n + 1) → ℤ} {T T₁ : ℕ} {S : Fin (n + 1) → ℕ} {d : K} {k : ℕ}
    (hk : 0 < k) {L : ℤ} (hL : ∀ j ∈ Icc 1 k, (j : ℤ) ∣ L) (hF : ∀ r m, (F r).coeff m ∈ A)
    (hFT : ∀ r, (F r).totalDegree ≤ T) (ht : ∀ r, (t r).natAbs ≤ T₁)
    (hs : ∀ c j, (s c j).natAbs ≤ S j) (hd : d ∈ A) (hb : ∀ i, d * b i ∈ A)
    (ha : ∀ j, a j ∈ A) (hα : ∀ j, a j * α j ∈ A) (hα' : ∀ j, a j * (α j)⁻¹ ∈ A) (r : ι)
    (c : κ) :
    (L : K) ^ T * d ^ T * (∏ j, a j ^ (T₁ * S j)) * waldschmidtInterpolationMatrix α b F t
      (fun c ↦ (waldschmidtDeltaOperator k (σ c)).map (algebraMap ℚ K)) s r c ∈ A :=
  mul_waldschmidtInterpolationMatrix_mem A hF hFT ht hs hd hb
    (fun r c _ hκ ↦ pow_mul_eval_hasseDeriv_map_mem A
      (pow_mul_eval_hasseDeriv_waldschmidtDeltaOperator_mem_range_intCast hk hL (σ c) _ (t r))
      hκ) ha hα hα' r c

/-- **A common denominator of the interpolation matrix with delta rows and delta-operator
columns.** Let the rows be the delta polynomials `∏ᵢ Δ(q zᵢ; τᵢ)` with `τ₀ ≤ T` and exponents
`|t| ≤ T₁`, and let the columns be the operators `δ_k(∂/∂z₀; σ c)` at grid points with
`|sⱼ| ≤ Sⱼ`. Let `q βᵢ ∈ ℤ` for every coefficient `βᵢ`, let `L` be an integer divisible by each of
`1, …, T`, let `k > 0` and let `L'` be an integer divisible by each of `1, …, k`. If `aⱼ ∈ A` is a
common denominator of `αⱼ` and `αⱼ⁻¹`, then `L' ^ T L ^ T ∏ⱼ aⱼ ^ (T₁ Sⱼ)` times every entry of
the interpolation matrix lies in `A`. -/
theorem pow_mul_waldschmidtInterpolationMatrix_waldschmidtDelta_waldschmidtDeltaOperator_mem
    {ι κ : Type*} {α a b : Fin (n + 1) → K} {q : ℤ} {τ : ι → Fin (n + 1) →₀ ℕ} {t : ι → ℤ}
    {σ : κ → ℕ} {s : κ → Fin (n + 1) → ℤ} {T T₁ : ℕ} {S : Fin (n + 1) → ℕ} {L : ℤ} {k : ℕ}
    (hk : 0 < k) {L' : ℤ} (hL' : ∀ j ∈ Icc 1 k, (j : ℤ) ∣ L') (hτ : ∀ r, τ r 0 ≤ T)
    (ht : ∀ r, (t r).natAbs ≤ T₁) (hs : ∀ c j, (s c j).natAbs ≤ S j)
    (hb : ∀ i, (q : K) * b i ∈ Set.range (Int.cast : ℤ → K)) (hL : ∀ j ∈ Icc 1 T, (j : ℤ) ∣ L)
    (ha : ∀ j, a j ∈ A) (hα : ∀ j, a j * α j ∈ A) (hα' : ∀ j, a j * (α j)⁻¹ ∈ A) (r : ι)
    (c : κ) :
    (L' : K) ^ T * (L : K) ^ T * (∏ j, a j ^ (T₁ * S j)) *
      waldschmidtInterpolationMatrix α b (fun r ↦ waldschmidtDelta q (τ r)) t
        (fun c ↦ (waldschmidtDeltaOperator k (σ c)).map (algebraMap ℚ K)) s r c ∈ A := by
  refine mul_waldschmidtInterpolationMatrix_waldschmidtDelta_mem A hτ ht hs hb hL
    (fun r c j hj ↦ ?_) ha hα hα' r c
  -- The `j`-th derivative is `j!` times the `j`-th Hasse derivative.
  rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul, nsmul_eq_mul, mul_left_comm]
  exact mul_mem (natCast_mem A _)
    (pow_mul_eval_hasseDeriv_map_mem A
      (pow_mul_eval_hasseDeriv_waldschmidtDeltaOperator_mem_range_intCast hk hL' (σ c) _ (t r)) hj)

end Subring
