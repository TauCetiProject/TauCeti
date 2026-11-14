/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.L1Norm
public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Delta.Operator
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Data.Nat.Choose.Bounds

/-!
# The entries of Waldschmidt's interpolation matrix as polynomials in the coefficients

The entry of the operator `P(∂/∂z₀)` on Waldschmidt's auxiliary function
`F(z) exp(t (z₀ + λ₁ z₁ + ⋯ + λ_{m-1} z_{m-1}))` at the grid point `s · y` is

`γ_P = (∑ₖ P^{[k]}(t) (∂ᵏF/∂z₀ᵏ)(s · y)) α₁^(t s₁) ⋯ αₘ^(t sₘ)`

(`TauCeti.waldschmidtOperatorEntry_eq_sum_hasseDeriv`). The coordinates `sₘ β₀` and
`sⱼ + sₘ βⱼ` of the grid point are polynomials of degree at most one in the coefficients
`β = (β₀, …, β_{m-1})` of the normalized linear form, so the first factor is the value at `β` of
a polynomial `E_P` in `m` variables: the polynomial obtained by substituting
`X₀ ↦ sₘ X₀` and `Xⱼ ↦ sⱼ + sₘ Xⱼ` into `∑ₖ P^{[k]}(t) ∂ᵏF/∂X₀ᵏ`
(`TauCeti.waldschmidtEntryPolynomial t s P F`). For the arithmetic lower bound on a nonzero minor
of the interpolation matrix, Liouville's inequality is applied to polynomials in `β` and the
`αⱼ` (`Height.logHeight₁_aeval_le`); it needs the total degree, a common denominator and the
length (the sum of the absolute values of the coefficients) of `E_P`. This file supplies the
three, following Waldschmidt's Lemma 9.11:

* **degree:** `E_P` has total degree at most that of `F`
  (`TauCeti.totalDegree_waldschmidtEntryPolynomial_le`);
* **denominator:** if `F` has coefficients in a subring `A` and degree at most `T` in `X₀`, and
  `c P^{[k]}(t) ∈ A` for `k ≤ T`, then `c E_P` has coefficients in `A`
  (`Subring.coeff_smul_waldschmidtEntryPolynomial_mem`);
* **length:** over a seminormed ring, if `‖P^{[k]}(t)‖ ≤ H` for all `k`, then
  `ℓ(E_P) ≤ H ∑_μ ‖F_μ‖ (μ₀ + ‖sₘ‖) ^ μ₀ ∏_{1 ≤ j < m} (‖sⱼ‖ + ‖sₘ‖) ^ μⱼ`
  (`TauCeti.l1Norm_waldschmidtEntryPolynomial_le`).

The degree and the length do not depend on the coefficients `β`, which enter Liouville's
inequality only through their heights.

For the columns `δ_k(∂/∂z₀; σ)` built from Baker's binomial polynomials, the Hasse derivatives
`δ_k^{[κ]}(t; σ)` are bounded by `TauCeti.abs_eval_hasseDeriv_waldschmidtDeltaOperator_le` and
have the denominators of
`TauCeti.pow_mul_eval_hasseDeriv_waldschmidtDeltaOperator_mem_range_intCast`; combining gives the
length and denominator of the entry polynomials of the general case of the measure, whose rows are
polynomials with integral coefficients, such as the monomials `z^τ`
(`TauCeti.l1Norm_waldschmidtEntryPolynomial_waldschmidtDeltaOperator_le` and
`TauCeti.coeff_pow_smul_waldschmidtEntryPolynomial_waldschmidtDeltaOperator_mem_range_intCast`).

## Main definitions

* `TauCeti.waldschmidtEntryPolynomial t s P`: the linear map `F ↦ E_P`.

## Main results

* `TauCeti.waldschmidtOperatorEntry_map_algebraMap`: the entry is `E_P(β) α₁^(t s₁) ⋯ αₘ^(t sₘ)`.
* `TauCeti.totalDegree_waldschmidtEntryPolynomial_le`: the total degree bound.
* `Subring.coeff_smul_waldschmidtEntryPolynomial_mem`: the denominator bound.
* `TauCeti.l1Norm_waldschmidtEntryPolynomial_le`: the length bound.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.1, Lemma 9.11, and §9.3.2.
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable {n : ℕ}

section CommRing

variable {R : Type*} [CommRing R]

/-- The entry of the operator `P(∂/∂z₀)` of Waldschmidt's interpolation matrix, on the row of the
polynomial `F` with exponent `t` and at the grid point `s · y`, as a polynomial in the
coefficients `β = (β₀, …, β_{m-1})`: the polynomial `∑ₖ P^{[k]}(t) (∂ᵏF/∂X₀ᵏ)(s · X)`, where
`s · X = (sₘ X₀, s₁ + sₘ X₁, …, s_{m-1} + sₘ X_{m-1})` is the grid point with indeterminate
coefficients. It is linear in `F`. Its value at `β`, times `α₁^(t s₁) ⋯ αₘ^(t sₘ)`, is the entry
`TauCeti.waldschmidtOperatorEntry` (`TauCeti.waldschmidtOperatorEntry_map_algebraMap`). -/
noncomputable def waldschmidtEntryPolynomial (t : ℤ) (s : Fin (n + 1) → ℤ) (P : Polynomial R) :
    MvPolynomial (Fin (n + 1)) R →ₗ[R] MvPolynomial (Fin (n + 1)) R :=
  ∑ k ∈ range (P.natDegree + 1), (Polynomial.hasseDeriv k P).eval (t : R) •
    ((bind₁ (waldschmidtPoint X s)).toLinearMap ∘ₗ (pderiv 0).toLinearMap ^ k)

/-- The defining formula of `waldschmidtEntryPolynomial t s P F`. -/
theorem waldschmidtEntryPolynomial_apply (t : ℤ) (s : Fin (n + 1) → ℤ) (P : Polynomial R)
    (F : MvPolynomial (Fin (n + 1)) R) :
    waldschmidtEntryPolynomial t s P F = ∑ k ∈ range (P.natDegree + 1),
      (Polynomial.hasseDeriv k P).eval (t : R) •
        bind₁ (waldschmidtPoint X s) ((pderiv 0)^[k] F) := by
  simp [waldschmidtEntryPolynomial, pow_apply_eq_iterate]

/-- The coordinates of the grid point with indeterminate coefficients have total degree at most
one. -/
private theorem totalDegree_waldschmidtPoint_X_le (s : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    (waldschmidtPoint (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) s i).totalDegree ≤ 1 := by
  have hX (j : Fin (n + 1)) : (X j : MvPolynomial (Fin (n + 1)) R).totalDegree ≤ 1 := by
    rw [X]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  have hz (z : ℤ) : (z : MvPolynomial (Fin (n + 1)) R).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial (Fin (n + 1)) R), totalDegree_C]
  have hCX (z : ℤ) (j : Fin (n + 1)) :
      ((z : MvPolynomial (Fin (n + 1)) R) * X j).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by rw [hz, zero_add]; exact hX j)
  cases i using Fin.cases with
  | zero =>
    rw [waldschmidtPoint_apply_zero]
    exact hCX _ 0
  | succ k =>
    rw [waldschmidtPoint_apply_succ]
    exact (totalDegree_add _ _).trans (max_le ((hz _).trans_le zero_le_one) (hCX _ k.succ))

/-- **The degree of the entry polynomials.** The entry polynomial of `F` has total degree at most
that of `F`. -/
theorem totalDegree_waldschmidtEntryPolynomial_le (t : ℤ) (s : Fin (n + 1) → ℤ)
    (P : Polynomial R) (F : MvPolynomial (Fin (n + 1)) R) :
    (waldschmidtEntryPolynomial t s P F).totalDegree ≤ F.totalDegree := by
  rw [← mem_restrictTotalDegree, waldschmidtEntryPolynomial_apply]
  refine Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ ?_
  rw [← aeval_eq_bind₁]
  exact aeval_mem_restrictTotalDegree (totalDegree_waldschmidtPoint_X_le s)
    ((mem_restrictTotalDegree _ _ _).2 ((totalDegree_iterate_pderiv_le 0 k F).trans tsub_le_self))

/-- **The entry as a value of the entry polynomial.** Let `K` be a field that is an algebra over
`R`. The entry of the operator `P(∂/∂z₀)` on the row of `F` with exponent `t`, at the grid point
`s · y` built from `b = (β₀, …, β_{m-1})`, is the value at `b` of the entry polynomial of `F`
times `α₁^(t s₁) ⋯ αₘ^(t sₘ)`. -/
theorem waldschmidtOperatorEntry_map_algebraMap {K : Type*} [Field K] [Algebra R K]
    (α b : Fin (n + 1) → K) (t : ℤ) (s : Fin (n + 1) → ℤ) (F : MvPolynomial (Fin (n + 1)) R)
    (P : Polynomial R) :
    waldschmidtOperatorEntry α b t s (F.map (algebraMap R K)) (P.map (algebraMap R K)) =
      aeval b (waldschmidtEntryPolynomial t s P F) * ∏ j, α j ^ (t * s j) := by
  set φ := algebraMap R K
  -- The grid point with indeterminate coefficients specializes to the grid point at `b`.
  have hpt : (fun i ↦ aeval b (waldschmidtPoint
      (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) s i)) = waldschmidtPoint b s := by
    simpa using (waldschmidtPoint_map (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
      (aeval b).toRingHom s).symm
  have hpderiv (k : ℕ) : (pderiv 0)^[k] (F.map φ) = ((pderiv 0)^[k] F).map φ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, pderiv_map, Function.iterate_succ_apply']
  rw [waldschmidtOperatorEntry_eq_sum_hasseDeriv, waldschmidtEntryPolynomial_apply, map_sum]
  congr 1
  -- The sum over the degree of `P.map φ` extends to the degree of `P`.
  refine (sum_subset (range_subset_range.2 (Nat.succ_le_succ (Polynomial.natDegree_map_le)))
    fun k _ hk ↦ ?_).trans (sum_congr rfl fun k _ ↦ ?_)
  · rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree _ _ (by simpa using hk),
      Polynomial.eval_zero, zero_mul]
  · rw [map_smul, aeval_bind₁, hpt, Algebra.smul_def, Polynomial.hasseDeriv_map,
      Polynomial.eval_map_algebraMap, hpderiv, eval_map, ← aeval_def]
    simp [Polynomial.aeval_def, Polynomial.eval₂_at_intCast]

/-- The entry of the operator `P(∂/∂z₀)` on the row of `F` with exponent `t`, at the grid point
`s · y` built from `b = (β₀, …, β_{m-1})`, is the value at `b` of the entry polynomial of `F`
times `α₁^(t s₁) ⋯ αₘ^(t sₘ)`. -/
theorem waldschmidtOperatorEntry_eq_aeval {K : Type*} [Field K] (α b : Fin (n + 1) → K) (t : ℤ)
    (s : Fin (n + 1) → ℤ) (F : MvPolynomial (Fin (n + 1)) K) (P : Polynomial K) :
    waldschmidtOperatorEntry α b t s F P =
      aeval b (waldschmidtEntryPolynomial t s P F) * ∏ j, α j ^ (t * s j) := by
  simpa [MvPolynomial.map_id] using waldschmidtOperatorEntry_map_algebraMap α b t s F P

end CommRing

section Length

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R]

/-- The length of the entry polynomial of a monomial `X^μ`, given a bound `H` on the Hasse
derivatives of the operator at `t`. -/
private theorem l1Norm_waldschmidtEntryPolynomial_monomial_le {t : ℤ} {P : Polynomial R} {H : ℝ}
    (hP : ∀ k, ‖(Polynomial.hasseDeriv k P).eval (t : R)‖ ≤ H) (s : Fin (n + 1) → ℤ)
    (μ : Fin (n + 1) →₀ ℕ) :
    (waldschmidtEntryPolynomial t s P (monomial μ 1)).l1Norm ≤
      H * ((μ 0 + ‖(s (Fin.last n) : R)‖) ^ μ 0 *
        ∏ i : Fin n, (‖(s i.castSucc : R)‖ + ‖(s (Fin.last n) : R)‖) ^ μ i.succ) := by
  set g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R := waldschmidtPoint X s with hg
  set a := ‖(s (Fin.last n) : R)‖
  set B := ∏ i : Fin n, (‖(s i.castSucc : R)‖ + a) ^ μ i.succ
  have hH : 0 ≤ H := (norm_nonneg _).trans (hP 0)
  have hB : 0 ≤ B := prod_nonneg fun _ _ ↦ by positivity
  -- The lengths of the coordinates of the grid point with indeterminate coefficients.
  have hint (z : ℤ) : (z : MvPolynomial (Fin (n + 1)) R).l1Norm = ‖(z : R)‖ := by
    rw [← map_intCast (C : R →+* MvPolynomial (Fin (n + 1)) R), l1Norm_C]
  have hCX (z : ℤ) (j : Fin (n + 1)) :
      ((z : MvPolynomial (Fin (n + 1)) R) * X j).l1Norm ≤ ‖(z : R)‖ := by
    simpa [hint] using l1Norm_mul_le (z : MvPolynomial (Fin (n + 1)) R) (X j)
  have hg0 : (g 0).l1Norm ≤ a := by
    rw [hg, waldschmidtPoint_apply_zero]
    exact hCX _ 0
  have hgs (j : Fin n) : (g j.succ).l1Norm ≤ ‖(s j.castSucc : R)‖ + a := by
    rw [hg, waldschmidtPoint_apply_succ]
    exact (l1Norm_add_le _ _).trans (add_le_add (hint _).le (hCX _ j.succ))
  -- The `k`-th term is at most `H (μ₀ ⋯ (μ₀ - k + 1)) a ^ (μ₀ - k) B`.
  have hterm (k : ℕ) : ((Polynomial.hasseDeriv k P).eval (t : R) •
      bind₁ g ((pderiv 0)^[k] (monomial μ 1))).l1Norm ≤
      H * ((μ 0).descFactorial k * (a ^ (μ 0 - k) * B)) := by
    refine (l1Norm_smul_le _ _).trans (mul_le_mul (hP k) ?_ (l1Norm_nonneg _) hH)
    rw [iterate_pderiv_monomial, one_mul]
    refine (l1Norm_bind₁_monomial_le _ _ _).trans ?_
    rw [Finsupp.prod_fintype _ _ fun i ↦ pow_zero _, Fin.prod_univ_succ]
    have hν (i : Fin n) : Finsupp.single (0 : Fin (n + 1)) k i.succ = 0 :=
      Finsupp.single_eq_of_ne (Fin.succ_ne_zero i)
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, hν, tsub_zero]
    refine mul_le_mul (by simpa using Nat.norm_cast_le (α := R) ((μ 0).descFactorial k))
      (mul_le_mul (pow_le_pow_left₀ (l1Norm_nonneg _) hg0 _)
        (prod_le_prod₀ (fun i _ ↦ pow_nonneg (l1Norm_nonneg _) _)
          fun i _ ↦ pow_le_pow_left₀ (l1Norm_nonneg _) (hgs i) _)
        (prod_nonneg fun i _ ↦ pow_nonneg (l1Norm_nonneg _) _) (by positivity))
      (mul_nonneg (pow_nonneg (l1Norm_nonneg _) _)
        (prod_nonneg fun i _ ↦ pow_nonneg (l1Norm_nonneg _) _)) (Nat.cast_nonneg _)
  rw [waldschmidtEntryPolynomial_apply]
  refine (l1Norm_sum_le _ _).trans ((sum_le_sum fun k _ ↦ hterm k).trans ?_)
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hH
  calc ∑ k ∈ range (P.natDegree + 1), ((μ 0).descFactorial k : ℝ) * (a ^ (μ 0 - k) * B)
      = (∑ k ∈ range (P.natDegree + 1), ((μ 0).descFactorial k : ℝ) * a ^ (μ 0 - k)) * B := by
        rw [sum_mul]
        exact sum_congr rfl fun _ _ ↦ (mul_assoc _ _ _).symm
    _ ≤ (μ 0 + a) ^ μ 0 * B :=
        mul_le_mul_of_nonneg_right (Nat.sum_range_descFactorial_mul_pow_le _ _ (norm_nonneg _)) hB

/-- **The length of the entry polynomials.** If the Hasse derivatives of the operator `P` at `t`
have norm at most `H`, then the entry polynomial of `F = ∑_μ F_μ X^μ` has length at most
`H ∑_μ ‖F_μ‖ (μ₀ + ‖sₘ‖) ^ μ₀ ∏_{1 ≤ j < m} (‖sⱼ‖ + ‖sₘ‖) ^ μⱼ`. -/
theorem l1Norm_waldschmidtEntryPolynomial_le {t : ℤ} {P : Polynomial R} {H : ℝ}
    (hP : ∀ k, ‖(Polynomial.hasseDeriv k P).eval (t : R)‖ ≤ H) (s : Fin (n + 1) → ℤ)
    (F : MvPolynomial (Fin (n + 1)) R) :
    (waldschmidtEntryPolynomial t s P F).l1Norm ≤
      H * ∑ μ ∈ F.support, ‖F.coeff μ‖ * ((μ 0 + ‖(s (Fin.last n) : R)‖) ^ μ 0 *
        ∏ i : Fin n, (‖(s i.castSucc : R)‖ + ‖(s (Fin.last n) : R)‖) ^ μ i.succ) := by
  have hF : waldschmidtEntryPolynomial t s P F =
      ∑ μ ∈ F.support, F.coeff μ • waldschmidtEntryPolynomial t s P (monomial μ 1) := by
    conv_lhs => rw [F.as_sum, map_sum]
    refine sum_congr rfl fun μ _ ↦ ?_
    rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [hF, mul_sum]
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun μ _ ↦ ?_)
  rw [mul_left_comm]
  exact (l1Norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
    (l1Norm_waldschmidtEntryPolynomial_monomial_le hP s μ) (norm_nonneg _))

end Length

end TauCeti

namespace Subring

open TauCeti

variable {n : ℕ} {R : Type*} [CommRing R] (A : Subring R)

/-- **The denominator of the entry polynomials.** Let `F` have coefficients in the subring `A`
and degree at most `T` in `X₀`, and let `c` clear the denominators of the Hasse derivatives of the
operator at `t`, in the sense that `c P^{[k]}(t) ∈ A` for `k ≤ T`. Then `c` times the entry
polynomial of `F` has coefficients in `A`. -/
theorem coeff_smul_waldschmidtEntryPolynomial_mem {t : ℤ} {s : Fin (n + 1) → ℤ}
    {P : Polynomial R} {F : MvPolynomial (Fin (n + 1)) R} {T : ℕ} {c : R}
    (hF : ∀ m, F.coeff m ∈ A) (hFT : F.degreeOf 0 ≤ T)
    (hP : ∀ k ≤ T, c * (Polynomial.hasseDeriv k P).eval (t : R) ∈ A) (m : Fin (n + 1) →₀ ℕ) :
    (c • waldschmidtEntryPolynomial t s P F).coeff m ∈ A := by
  -- The polynomials with coefficients in `A` form the subring `S`.
  set S := (MvPolynomial.map (σ := Fin (n + 1)) A.subtype).range
  have hC {x : R} (hx : x ∈ A) : C x ∈ S := ⟨C ⟨x, hx⟩, by simp⟩
  have hpt (i : Fin (n + 1)) : waldschmidtPoint X s i ∈ S := by
    have hX (j : Fin (n + 1)) : (X j : MvPolynomial (Fin (n + 1)) R) ∈ S := ⟨X j, by simp⟩
    cases i using Fin.cases with
    | zero =>
      rw [waldschmidtPoint_apply_zero]
      exact mul_mem (intCast_mem S _) (hX 0)
    | succ j =>
      rw [waldschmidtPoint_apply_succ]
      exact add_mem (intCast_mem S _) (mul_mem (intCast_mem S _) (hX j.succ))
  suffices h : c • waldschmidtEntryPolynomial t s P F ∈ S by
    obtain ⟨p, hp⟩ := h
    rw [← hp, coeff_map]
    exact (p.coeff m).2
  rw [waldschmidtEntryPolynomial_apply, smul_sum]
  refine sum_mem fun k _ ↦ ?_
  rw [smul_smul, smul_eq_C_mul]
  rcases le_or_gt k T with hk | hk
  · refine mul_mem (hC (hP k hk)) ?_
    rw [← aeval_eq_bind₁, aeval_def]
    exact eval₂_mem (fun μ _ ↦ hC (coeff_iterate_pderiv_mem hF 0 k μ)) hpt
  · rw [iterate_pderiv_eq_zero_of_degreeOf_lt (hFT.trans_lt hk), map_zero, mul_zero]
    exact zero_mem S

end Subring

namespace TauCeti

variable {n : ℕ}

/-- **The denominator of the entry polynomials with delta-operator columns.** Let `F` have
integral coefficients and degree at most `T` in `X₀`, let `k > 0` and let `L` be an integer
divisible by each of `1, …, k`. Then `L ^ T` times the entry polynomial of `F` for the operator
`δ_k(∂/∂z₀; σ)` has integral coefficients. -/
theorem coeff_pow_smul_waldschmidtEntryPolynomial_waldschmidtDeltaOperator_mem_range_intCast
    {k : ℕ} (hk : 0 < k) {L : ℤ} (hL : ∀ j ∈ Icc 1 k, (j : ℤ) ∣ L)
    {F : MvPolynomial (Fin (n + 1)) ℚ} (hF : ∀ m, F.coeff m ∈ Set.range (Int.cast : ℤ → ℚ))
    {T : ℕ} (hFT : F.degreeOf 0 ≤ T) (σ : ℕ) (t : ℤ) (s : Fin (n + 1) → ℤ)
    (m : Fin (n + 1) →₀ ℕ) :
    ((L : ℚ) ^ T • waldschmidtEntryPolynomial t s (waldschmidtDeltaOperator k σ) F).coeff m ∈
      Set.range (Int.cast : ℤ → ℚ) := by
  have hA {x : ℚ} : x ∈ (Int.castRingHom ℚ).range ↔ x ∈ Set.range (Int.cast : ℤ → ℚ) := by
    simp
  refine hA.1 (Subring.coeff_smul_waldschmidtEntryPolynomial_mem _ (fun m ↦ hA.2 (hF m)) hFT
    (fun κ hκ ↦ ?_) m)
  rw [← Nat.sub_add_cancel hκ, pow_add, mul_assoc]
  exact mul_mem (pow_mem (intCast_mem _ _) _) (hA.2
    (pow_mul_eval_hasseDeriv_waldschmidtDeltaOperator_mem_range_intCast hk hL σ κ t))

/-- **The length of the entry polynomials with delta-operator columns.** Let `|t| ≤ N` and write
`σ = k q + r` with `0 ≤ r < k`. Then the entry polynomial of `F = ∑_μ F_μ X^μ` for the operator
`δ_k(∂/∂z₀; σ)` has length at most
`2 ^ (q (N + k + 1) + (N + r + 1)) ∑_μ ‖F_μ‖ (μ₀ + ‖sₘ‖) ^ μ₀ ∏_{1 ≤ j < m} (‖sⱼ‖ + ‖sₘ‖) ^ μⱼ`,
where `‖·‖` is the absolute value of `ℚ`. -/
theorem l1Norm_waldschmidtEntryPolynomial_waldschmidtDeltaOperator_le {N : ℕ} {t : ℤ}
    (ht : t.natAbs ≤ N) (k σ : ℕ) (s : Fin (n + 1) → ℤ) (F : MvPolynomial (Fin (n + 1)) ℚ) :
    (waldschmidtEntryPolynomial t s (waldschmidtDeltaOperator k σ) F).l1Norm ≤
      2 ^ (σ / k * (N + k + 1) + (N + σ % k + 1)) *
        ∑ μ ∈ F.support, ‖F.coeff μ‖ * ((μ 0 + ‖(s (Fin.last n) : ℚ)‖) ^ μ 0 *
          ∏ i : Fin n, (‖(s i.castSucc : ℚ)‖ + ‖(s (Fin.last n) : ℚ)‖) ^ μ i.succ) := by
  refine l1Norm_waldschmidtEntryPolynomial_le (fun κ ↦ ?_) s F
  have htN : |(t : ℚ)| ≤ N := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast ht
  have h := abs_eval_hasseDeriv_waldschmidtDeltaOperator_le htN k σ κ
  rw [← Rat.norm_cast_real, Real.norm_eq_abs, ← Rat.cast_abs]
  exact_mod_cast h

end TauCeti
