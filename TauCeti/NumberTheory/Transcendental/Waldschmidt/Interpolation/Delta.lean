/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Denominator
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Algebra.MvPolynomial.Polynomial
import TauCeti.RingTheory.Subring.Basic

/-!
# The delta-polynomial rows of Waldschmidt's interpolation matrix

In the arithmetic estimate of Waldschmidt's interpolation determinant the monomial rows `z^τ` are
replaced by integer-valued polynomials, so that the entries of the matrix acquire small
denominators. For an integer `q` and an exponent `τ ∈ ℕᵐ` these are the products

`∏ᵢ Δ(q zᵢ; τᵢ)`,   `Δ(X; k) = (X + 1) (X + 2) ⋯ (X + k) / k!`,

of Baker's binomial polynomials (`TauCeti.waldschmidtDelta q τ`). When the coordinates `q xᵢ` of
a point `x` are integers, the values `Δ(q xᵢ; τᵢ)` are integers, and the divided derivatives
`(1 / k!) (d / dz₀)ᵏ Δ(q z₀; τ₀)` at `x` have denominators dividing `L ^ k`, for any integer `L`
divisible by `1, …, τ₀`, by Baker's denominator bound
`TauCeti.pow_mul_eval_hasseDeriv_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast`.
This applies to all grid points `s · y` as soon as `q βᵢ` is an integer for every coefficient
`βᵢ`; for instance in the homogeneous rational case `β₀ = 0`, `βⱼ = -bⱼ / bₘ` with `bⱼ ∈ ℤ`, with
`q = bₘ`. For the iterated derivatives `∂^σ/∂z₀^σ` the only denominators of the entries are
then `L ^ τ₀` and the denominator of the exponential factor `α₁^(t s₁) ⋯ αₘ^(t sₘ)`: unlike the
monomial rows, whose values at the grid points have the denominator `q ^ |τ|`, the delta rows
involve no power of `q`.

The rows `∏ᵢ Qᵢ(zᵢ)` separate the variables, so the derivatives in `z₀` only see the first
factor, and the entry of the operator `P(∂/∂z₀)` is
(`TauCeti.waldschmidtOperatorEntry_prod_aeval_X`)

`γ_P = (∑ₖ P⁽ᵏ⁾(t) Q₀^{[k]}(x₀)) Q₁(x₁) ⋯ Q_{m-1}(x_{m-1}) α₁^(t s₁) ⋯ αₘ^(t sₘ)`,   `x = s · y`,

with `P⁽ᵏ⁾` the `k`-th derivative and `Q₀^{[k]}` the `k`-th Hasse derivative. For `q ≠ 0` the
polynomials `Δ(q X; k)` form a polynomial sequence, so the delta rows with `τ` of degree at most
`T` span the same space of rows of the interpolation matrix as the monomial rows
(`TauCeti.span_image_waldschmidtOperatorEntry_waldschmidtDelta`). Each of them has total degree
at most the degree of `τ`.

## Main definitions

* `TauCeti.waldschmidtDelta q τ`: the delta polynomial `∏ᵢ Δ(q zᵢ; τᵢ)`.

## Main results

* `TauCeti.eval_waldschmidtDelta_mem_range_intCast`: the delta polynomials are integer-valued at
  the points `x` with all `q xᵢ` integral.
* `TauCeti.waldschmidtOperatorEntry_prod_aeval_X`: the entry of a separated row `∏ᵢ Qᵢ(zᵢ)`.
* `Subring.mul_waldschmidtOperatorEntry_prod_aeval_X_mem`: denominators of the entries of a
  separated row, in terms of the denominators of the operator and of the factors `Qᵢ`.
* `TauCeti.waldschmidtDelta_mem_restrictTotalDegree` and
  `TauCeti.span_image_waldschmidtOperatorEntry_waldschmidtDelta`: the delta rows have total degree
  at most `|τ|`, and they span the same rows as the monomials.
* `Subring.mul_waldschmidtOperatorEntry_waldschmidtDelta_mem`: if `q βᵢ ∈ ℤ` for all `i`,
  then `u L ^ τ₀ e γ_P ∈ A` for the delta row `∏ᵢ Δ(q zᵢ; τᵢ)`, where `u` clears the
  denominators of the derivatives of the operator at `t` and `e` that of the exponential factor.
* `Subring.mul_waldschmidtEntry_waldschmidtDelta_mem`: for the iterated derivatives
  `∂^σ/∂z₀^σ`, `L ^ τ₀ e γ ∈ A`.
* `Subring.mul_waldschmidtInterpolationMatrix_waldschmidtDelta_mem`: a common denominator of
  all the entries of the interpolation matrix with delta rows.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §§9.2.1, 9.3.2.
* A. Baker, *A sharpening of the bounds for linear forms in logarithms*, Acta Arith. **21**
  (1972), 117–129.
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable {n : ℕ} {K : Type*} [Field K]

/-- **The entry of a separated row.** For one-variable polynomials `Q₀, …, Q_{m-1}`, the entry of
the operator `P(∂/∂z₀)` on the row `∏ᵢ Qᵢ(zᵢ)` at the grid point `x = s · y` is
`(∑ₖ P⁽ᵏ⁾(t) Q₀^{[k]}(x₀)) Q₁(x₁) ⋯ Q_{m-1}(x_{m-1}) α₁^(t s₁) ⋯ αₘ^(t sₘ)`, where `P⁽ᵏ⁾` is the
`k`-th derivative of `P` and `Q₀^{[k]}` the `k`-th Hasse derivative of `Q₀`. -/
theorem waldschmidtOperatorEntry_prod_aeval_X (α b : Fin (n + 1) → K) (t : ℤ)
    (s : Fin (n + 1) → ℤ) (Q : Fin (n + 1) → Polynomial K) (P : Polynomial K) :
    waldschmidtOperatorEntry α b t s (∏ i, Polynomial.aeval (X i) (Q i)) P =
      (∑ k ∈ range (P.natDegree + 1), (Polynomial.derivative^[k] P).eval (t : K) *
          (Polynomial.hasseDeriv k (Q 0)).eval (waldschmidtPoint b s 0)) *
        (∏ i : Fin n, (Q i.succ).eval (waldschmidtPoint b s i.succ)) * ∏ j, α j ^ (t * s j) := by
  classical
  have herase : ∏ i ∈ univ.erase (0 : Fin (n + 1)), (Q i).eval (waldschmidtPoint b s i) =
      ∏ i : Fin n, (Q i.succ).eval (waldschmidtPoint b s i.succ) := by
    simp only [Fin.univ_succ, erase_cons, prod_map, Function.Embedding.coeFn_mk]
  rw [waldschmidtOperatorEntry_eq_sum_hasseDeriv]
  congr 1
  rw [sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  have hd (p : Polynomial K) (x : K) :
      (Polynomial.derivative^[k] p).eval x = k.factorial * (Polynomial.hasseDeriv k p).eval x := by
    rw [← Polynomial.factorial_smul_hasseDeriv, LinearMap.smul_apply, Polynomial.eval_smul,
      nsmul_eq_mul]
  rw [iterate_pderiv_prod_aeval_X (mem_univ (0 : Fin (n + 1)))]
  simp only [map_mul, map_prod, eval_polynomial_aeval, eval_X, hd, ← herase]
  ring

variable [CharZero K]

/-- The integer-valued delta polynomial `∏ᵢ Δ(q zᵢ; τᵢ)` on `Kᵐ`, for an integer `q` and an
exponent `τ ∈ ℕᵐ`, where `Δ(X; k) = (X + 1) (X + 2) ⋯ (X + k) / k!` is Baker's binomial
polynomial. It takes integer values wherever all the coordinates `q zᵢ` are integers. -/
noncomputable def waldschmidtDelta (q : ℤ) (τ : Fin (n + 1) →₀ ℕ) :
    MvPolynomial (Fin (n + 1)) K :=
  ∏ i, Polynomial.aeval (X i) (((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) (τ i)).comp
    (Polynomial.C (q : ℚ) * Polynomial.X)).map (algebraMap ℚ K))

/-- The defining formula of `waldschmidtDelta q τ`. -/
theorem waldschmidtDelta_def (q : ℤ) (τ : Fin (n + 1) →₀ ℕ) :
    waldschmidtDelta (K := K) q τ =
      ∏ i, Polynomial.aeval (X i) (((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ)
        (τ i)).comp (Polynomial.C (q : ℚ) * Polynomial.X)).map (algebraMap ℚ K)) :=
  (rfl)

/-- **The delta polynomials are integer-valued.** If `q xᵢ` is an integer for every coordinate
of the point `x`, then `∏ᵢ Δ(q xᵢ; τᵢ)` is an integer. -/
theorem eval_waldschmidtDelta_mem_range_intCast {q : ℤ} {x : Fin (n + 1) → K}
    (hx : ∀ i, (q : K) * x i ∈ Set.range (Int.cast : ℤ → K)) (τ : Fin (n + 1) →₀ ℕ) :
    eval x (waldschmidtDelta q τ) ∈ Set.range (Int.cast : ℤ → K) := by
  rw [waldschmidtDelta_def, map_prod]
  simp only [eval_polynomial_aeval, eval_X]
  exact Subring.mem_bot.1 (prod_mem fun i _ ↦ Subring.mem_bot.2
    (eval_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast (τ i) q (hx i)))

/-- The delta polynomial of the zero exponent is `1`. -/
@[simp]
theorem waldschmidtDelta_zero (q : ℤ) : waldschmidtDelta (K := K) (n := n) q 0 = 1 := by
  simp [waldschmidtDelta_def]

/-- For `q ≠ 0`, the polynomials `Δ(q X; k)`, mapped to `K[X]`, form a polynomial sequence. -/
private noncomputable def deltaSequence {q : ℤ} (hq : q ≠ 0) : Polynomial.Sequence K where
  elems' k := ((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) k).comp
    (Polynomial.C (q : ℚ) * Polynomial.X)).map (algebraMap ℚ K)
  degree_eq' k := by
    have hlin : (Polynomial.C (q : ℚ) * Polynomial.X).degree = 1 :=
      Polynomial.degree_C_mul_X (Int.cast_ne_zero.2 hq)
    rw [Polynomial.degree_map_eq_of_injective (algebraMap ℚ K).injective,
      Polynomial.degree_comp (by rw [hlin]; exact zero_lt_one), hlin,
      TauCeti.degree_multichoose_X_add_one, mul_one]

/-- The leading coefficients of the polynomials `Δ(q X; k)` are units of `K`. -/
private theorem isUnit_leadingCoeff_deltaSequence {q : ℤ} (hq : q ≠ 0) (k : ℕ) :
    IsUnit ((deltaSequence (K := K) hq) k).leadingCoeff :=
  isUnit_iff_ne_zero.2 (Polynomial.leadingCoeff_ne_zero.2 ((deltaSequence hq).ne_zero k))

/-- The delta polynomial `∏ᵢ Δ(q zᵢ; τᵢ)` has total degree at most the degree
`τ₀ + ⋯ + τ_{m-1}` of `τ`. -/
theorem waldschmidtDelta_mem_restrictTotalDegree (q : ℤ) {τ : Fin (n + 1) →₀ ℕ} {T : ℕ}
    (hτ : τ.degree ≤ T) :
    waldschmidtDelta (K := K) q τ ∈ restrictTotalDegree (Fin (n + 1)) K T := by
  rcases eq_or_ne q 0 with rfl | hq
  · -- For `q = 0` the delta polynomial is a constant.
    simp [waldschmidtDelta_def, mem_restrictTotalDegree, ← map_prod]
  rw [← (deltaSequence hq).span_prod_aeval_X_eq_restrictTotalDegree fun k _ ↦
    isUnit_leadingCoeff_deltaSequence hq k]
  exact Submodule.subset_span ⟨τ, hτ, rfl⟩

/-- **Change of basis to the delta polynomials.** Fix a family of columns, the `c`-th built from
the operator `P c` and the grid point `s c`, an integer `t` and an integer `q ≠ 0`. The rows of
entries of the delta polynomials `∏ᵢ Δ(q zᵢ; τᵢ)` with `τ` of degree at most `T` span the same
space as the rows of entries of the monomials `z^τ` with `τ` of degree at most `T`. -/
theorem span_image_waldschmidtOperatorEntry_waldschmidtDelta {κ : Type*}
    (α b : Fin (n + 1) → K) (P : κ → Polynomial K) (t : ℤ) (s : κ → Fin (n + 1) → ℤ) {q : ℤ}
    (hq : q ≠ 0) (T : ℕ) :
    Submodule.span K ((fun (τ : Fin (n + 1) →₀ ℕ) c ↦ waldschmidtOperatorEntry α b t (s c)
        (waldschmidtDelta q τ) (P c)) '' {τ | τ.degree ≤ T}) =
      Submodule.span K ((fun (τ : Fin (n + 1) →₀ ℕ) c ↦ waldschmidtOperatorEntry α b t (s c)
        (monomial τ 1) (P c)) '' {τ | τ.degree ≤ T}) :=
  span_image_waldschmidtOperatorEntry_prod_sequence α b P t s (deltaSequence hq) T

end TauCeti

namespace Subring

open TauCeti

variable {n : ℕ} {K : Type*} [Field K] (A : Subring K)

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

variable [CharZero K]

/-- **Denominators of the delta-polynomial entries.** Let `q` be an integer with `q βᵢ ∈ ℤ` for
every coefficient `βᵢ`, so that every grid point `x = s · y` has integral coordinates `q xᵢ`, and
let `L` be an integer divisible by each of `1, …, τ₀`. If `u` clears the denominators of the
derivatives of the operator at `t`, `u P⁽ᵏ⁾(t) ∈ A` for `k ≤ τ₀`, and `e` clears the denominator
of the exponential factor `α₁^(t s₁) ⋯ αₘ^(t sₘ)`, then `u L ^ τ₀ e γ_P ∈ A` for the entry `γ_P`
of the operator `P(∂/∂z₀)` on the delta row `∏ᵢ Δ(q zᵢ; τᵢ)`. -/
theorem mul_waldschmidtOperatorEntry_waldschmidtDelta_mem {α b : Fin (n + 1) → K} {t : ℤ}
    {s : Fin (n + 1) → ℤ} {P : Polynomial K} {q : ℤ} {τ : Fin (n + 1) →₀ ℕ} {L : ℤ} {u e : K}
    (hb : ∀ i, (q : K) * b i ∈ Set.range (Int.cast : ℤ → K))
    (hL : ∀ j ∈ Icc 1 (τ 0), (j : ℤ) ∣ L)
    (hP : ∀ k ≤ τ 0, u * (Polynomial.derivative^[k] P).eval (t : K) ∈ A)
    (he : e * ∏ j, α j ^ (t * s j) ∈ A) :
    u * (L : K) ^ τ 0 * e * waldschmidtOperatorEntry α b t s (waldschmidtDelta q τ) P ∈ A := by
  -- The coordinates `q xᵢ` of the grid point are integers.
  have hx (i : Fin (n + 1)) : (q : K) * waldschmidtPoint b s i ∈ Set.range (Int.cast : ℤ → K) :=
    mem_bot.1 (mul_waldschmidtPoint_mem ⊥ (intCast_mem ⊥ q) (fun i ↦ mem_bot.2 (hb i)) s i)
  have hdeg : (((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) (τ 0)).comp
      (Polynomial.C (q : ℚ) * Polynomial.X)).map (algebraMap ℚ K)).natDegree ≤ τ 0 :=
    Polynomial.natDegree_map_le.trans (Polynomial.natDegree_comp_le.trans (by
      rw [TauCeti.natDegree_multichoose_X_add_one]
      exact (Nat.mul_le_mul_left _ ((Polynomial.natDegree_C_mul_le _ _).trans
        Polynomial.natDegree_X_le)).trans (by rw [mul_one])))
  have h := mul_waldschmidtOperatorEntry_prod_aeval_X_mem A (b := b) (d := fun _ ↦ 1)
    (Q := fun i ↦ ((Ring.multichoose (Polynomial.X + 1 : Polynomial ℚ) (τ i)).comp
      (Polynomial.C (q : ℚ) * Polynomial.X)).map (algebraMap ℚ K))
    (c := (L : K) ^ τ 0) (fun k hk ↦ hP k (hk.trans hdeg)) (fun k hk ↦ ?_) (fun i ↦ ?_) he
  · simpa [waldschmidtDelta_def] using h
  · obtain ⟨z, hz⟩ :=
      pow_mul_eval_hasseDeriv_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast hL q (hx 0) k
    rw [← pow_sub_mul_pow (L : K) (hk.trans hdeg), mul_assoc, ← hz]
    exact mul_mem (pow_mem (intCast_mem A L) _) (intCast_mem A z)
  · obtain ⟨z, hz⟩ :=
      eval_map_multichoose_X_add_one_comp_C_mul_X_mem_range_intCast (τ i.succ) q (hx i.succ)
    rw [one_mul, ← hz]
    exact intCast_mem A z

/-- **Denominators of the delta-polynomial derivative entries.** For the iterated derivatives
`∂^σ/∂z₀^σ`, whose derivatives `σ! / (σ - k)! t^(σ - k)` at `t` are integers,
`L ^ τ₀ e γ ∈ A` under the hypotheses of
`Subring.mul_waldschmidtOperatorEntry_waldschmidtDelta_mem` on `q`, `L` and `e`. -/
theorem mul_waldschmidtEntry_waldschmidtDelta_mem {α b : Fin (n + 1) → K} {t : ℤ}
    {s : Fin (n + 1) → ℤ} {q : ℤ} {τ : Fin (n + 1) →₀ ℕ} {L : ℤ} {e : K}
    (hb : ∀ i, (q : K) * b i ∈ Set.range (Int.cast : ℤ → K))
    (hL : ∀ j ∈ Icc 1 (τ 0), (j : ℤ) ∣ L) (he : e * ∏ j, α j ^ (t * s j) ∈ A) (σ : ℕ) :
    (L : K) ^ τ 0 * e * waldschmidtEntry α b (waldschmidtDelta q τ) t σ s ∈ A := by
  have h := mul_waldschmidtOperatorEntry_waldschmidtDelta_mem A (u := 1)
    (P := Polynomial.X ^ σ) hb hL (fun k _ ↦ ?_) he
  · rwa [one_mul, waldschmidtOperatorEntry_X_pow] at h
  rw [Polynomial.iterate_derivative_X_pow_eq_smul, Polynomial.eval_smul, Polynomial.eval_pow,
    Polynomial.eval_X, one_mul, smul_eq_mul]
  exact mul_mem (natCast_mem A _) (pow_mem (intCast_mem A t) _)

/-- **A common denominator of the interpolation matrix with delta rows.** Let the rows be the
delta polynomials `∏ᵢ Δ(q zᵢ; τᵢ)` with `τ₀ ≤ T` and exponents `|t| ≤ T₁`, and let the columns
have grid points with `|sⱼ| ≤ Sⱼ`. Let `q βᵢ ∈ ℤ` for every coefficient `βᵢ`, let `L` be an
integer divisible by each of `1, …, T`, let `u` clear the denominators of the derivatives of the
operators of all columns at all the exponents of the rows, in the sense that
`u (P c)⁽ᵏ⁾(t r) ∈ A` for `k ≤ T`, and let `aⱼ ∈ A` be a common denominator of `αⱼ` and `αⱼ⁻¹`.
Then `u L ^ T ∏ⱼ aⱼ ^ (T₁ Sⱼ)` times every entry of the interpolation matrix lies in `A`. -/
theorem mul_waldschmidtInterpolationMatrix_waldschmidtDelta_mem {ι κ : Type*}
    {α a b : Fin (n + 1) → K} {q : ℤ} {τ : ι → Fin (n + 1) →₀ ℕ} {t : ι → ℤ}
    {P : κ → Polynomial K} {s : κ → Fin (n + 1) → ℤ} {T T₁ : ℕ} {S : Fin (n + 1) → ℕ} {L : ℤ}
    {u : K} (hτ : ∀ r, τ r 0 ≤ T) (ht : ∀ r, (t r).natAbs ≤ T₁)
    (hs : ∀ c j, (s c j).natAbs ≤ S j) (hb : ∀ i, (q : K) * b i ∈ Set.range (Int.cast : ℤ → K))
    (hL : ∀ j ∈ Icc 1 T, (j : ℤ) ∣ L)
    (hP : ∀ r c, ∀ k ≤ T, u * (Polynomial.derivative^[k] (P c)).eval (t r : K) ∈ A)
    (ha : ∀ j, a j ∈ A) (hα : ∀ j, a j * α j ∈ A) (hα' : ∀ j, a j * (α j)⁻¹ ∈ A) (r : ι)
    (c : κ) :
    u * (L : K) ^ T * (∏ j, a j ^ (T₁ * S j)) *
      waldschmidtInterpolationMatrix α b (fun r ↦ waldschmidtDelta q (τ r)) t P s r c ∈ A := by
  have he : (∏ j, a j ^ (T₁ * S j)) * ∏ j, α j ^ (t r * s c j) ∈ A :=
    A.prod_pow_mul_prod_zpow_mem (fun j _ ↦ ha j) (fun j _ ↦ hα j) (fun j _ ↦ hα' j)
      fun j _ ↦ by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (ht r) (hs c j)
  have h := mul_waldschmidtOperatorEntry_waldschmidtDelta_mem A hb
    (fun j hj ↦ hL j (mem_Icc.2 ⟨(mem_Icc.1 hj).1, (mem_Icc.1 hj).2.trans (hτ r)⟩))
    (fun k hk ↦ hP r c k (hk.trans (hτ r))) he
  rw [waldschmidtInterpolationMatrix_apply, ← pow_sub_mul_pow (L : K) (hτ r)]
  have e (x y z w : K) : u * (x * y) * z * w = x * (u * y * z * w) := by ring
  rw [e]
  exact mul_mem (pow_mem (intCast_mem A L) _) h

end Subring
