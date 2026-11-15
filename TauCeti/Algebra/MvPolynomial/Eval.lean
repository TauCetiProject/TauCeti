/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Variables

import Mathlib.Tactic.Ring

/-!
# Denominators and congruences in the values of multivariate polynomials

Mathlib's `MvPolynomial.eval_mem` says that a polynomial with coefficients in a subsemiring takes
values in it at points with coordinates in it. If instead only the multiples `c xᵢ` of the
coordinates by a common denominator `c` lie in the subsemiring, then a polynomial of total degree
at most `T` has its value at `x` there after multiplication by `c ^ T`. This is the form in which
the denominators of algebraic numbers enter Liouville-type estimates: for a polynomial with
algebraic-integer coefficients evaluated at algebraic numbers with denominator `c`, the value has
denominator dividing `c ^ T`.

Over a commutative ring, evaluation also respects congruences: if `d ∣ xᵢ - tᵢ` for every `i`, then
`d ∣ p(x) - p(t)`.

We also define `MvPolynomial.evalZeroAt v`, the `R`-algebra endomorphism setting a single variable
`X v` to `0`, together with its evaluation, coefficient-map, monomial, coefficient, support, and
variable-set lemmas.

## Main definitions and results

* `MvPolynomial.pow_mul_eval_mem`: `c ^ T p(x)` lies in a subsemiring containing `c`, the
  coefficients of `p` and the `c xᵢ`, when `p` has total degree at most `T`.
* `MvPolynomial.dvd_eval_sub_eval`: values at points congruent modulo `d` are congruent modulo `d`.
* `MvPolynomial.evalZeroAt`: the algebra endomorphism specializing a single variable `X v` to `0`.
-/

public section

namespace MvPolynomial

section Eval

variable {σ S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

/-- **Clearing denominators in a polynomial value.** If the coefficients of `p` lie in a
subsemiring `s`, `p` has total degree at most `T`, and `c ∈ s` is a common denominator of the
coordinates of `x`, that is `c xᵢ ∈ s` for all `i`, then `c ^ T p(x) ∈ s`. -/
theorem pow_mul_eval_mem {s : subS} {p : MvPolynomial σ S} (hp : ∀ m, p.coeff m ∈ s) {T : ℕ}
    (hT : p.totalDegree ≤ T) {c : S} (hc : c ∈ s) {x : σ → S} (hx : ∀ i, c * x i ∈ s) :
    c ^ T * eval x p ∈ s := by
  rw [eval_eq, Finset.mul_sum]
  refine sum_mem fun m hm ↦ ?_
  have hm' : ∑ i ∈ m.support, m i ≤ T := (le_totalDegree hm).trans hT
  -- Split `c ^ T` as `c ^ (T - |m|) c ^ |m|` and distribute `c ^ |m|` over the monomial.
  have h : c ^ T * (p.coeff m * ∏ i ∈ m.support, x i ^ m i) =
      c ^ (T - ∑ i ∈ m.support, m i) * p.coeff m * ∏ i ∈ m.support, (c * x i) ^ m i := by
    conv_lhs => rw [← Nat.sub_add_cancel hm', pow_add, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_congr rfl fun i _ ↦ mul_pow c (x i) (m i), Finset.prod_mul_distrib]
    ring
  rw [h]
  exact mul_mem (mul_mem (pow_mem hc _) (hp m)) (prod_mem fun i _ ↦ pow_mem (hx i) _)

/-- The values of a polynomial at points that agree modulo `d` agree modulo `d`. -/
theorem dvd_eval_sub_eval {R : Type*} [CommRing R] (p : MvPolynomial σ R) {d : R} {x t : σ → R}
    (h : ∀ i, d ∣ x i - t i) : d ∣ eval x p - eval t p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa [add_sub_add_comm] using dvd_add hp hq
  | mul_X p i hp =>
    convert dvd_add (dvd_mul_of_dvd_left hp (x i)) (dvd_mul_of_dvd_right (h i) (eval t p))
      using 1
    simp only [map_mul, eval_X]
    ring

end Eval

section EvalZeroAt

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] [DecidableEq σ]

/-- Specialize a single variable `X v` of a multivariate polynomial to `0`. -/
noncomputable def evalZeroAt (v : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (Function.update X v 0)

/-- `evalZeroAt v` unfolds to `aeval (Function.update X v 0)`. -/
theorem evalZeroAt_eq_aeval (v : σ) :
    evalZeroAt (R := R) v = aeval (Function.update X v 0) := (rfl)

/-- `evalZeroAt v` sends `X v` to `0`. -/
@[simp]
theorem evalZeroAt_X_self (v : σ) : evalZeroAt (R := R) v (X v) = 0 := by
  simp [evalZeroAt]

/-- `evalZeroAt v` leaves `X w` unchanged when `w ≠ v`. -/
@[simp]
theorem evalZeroAt_X_of_ne {v w : σ} (h : w ≠ v) :
    evalZeroAt (R := R) v (X w) = X w := by
  simp [evalZeroAt, h]

/-- Evaluating `evalZeroAt v P` in an `R`-algebra updates the evaluation point at `v` to `0`. -/
@[simp]
theorem aeval_evalZeroAt [Algebra R S] (v : σ) (P : MvPolynomial σ R) (a : σ → S) :
    aeval a (evalZeroAt v P) = aeval (Function.update a v 0) P := by
  have h : (aeval a).comp (evalZeroAt (R := R) v) = aeval (Function.update a v 0) := by
    ext w
    by_cases hw : w = v <;> simp [hw]
  exact AlgHom.congr_fun h P

/-- Evaluating `evalZeroAt v P` at `a : σ → R` updates `a` at `v` to `0`. -/
@[simp]
theorem eval_evalZeroAt (v : σ) (P : MvPolynomial σ R) (a : σ → R) :
    eval a (evalZeroAt v P) = eval (Function.update a v 0) P :=
  aeval_evalZeroAt v P a

/-- Mapping coefficients along a ring homomorphism commutes with `evalZeroAt v`. -/
@[simp]
theorem map_evalZeroAt (f : R →+* S) (v : σ) (P : MvPolynomial σ R) :
    map f (evalZeroAt v P) = evalZeroAt v (map f P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp =>
    by_cases hw : w = v <;> simp [hw, hp]

/-- Specializing `X v` to `0` preserves a monomial if `v` has exponent `0` and kills it
otherwise. -/
@[simp]
theorem evalZeroAt_monomial (v : σ) (n : σ →₀ ℕ) (c : R) :
    evalZeroAt v (monomial n c) = if n v = 0 then monomial n c else 0 := by
  rw [evalZeroAt, aeval_monomial, algebraMap_eq]
  by_cases hv : n v = 0
  · simp only [hv, ↓reduceIte, monomial_eq]
    congr 1
    rw [Finsupp.prod]
    refine Finset.prod_congr rfl fun w hw ↦ ?_
    have hne : w ≠ v := fun h ↦ Finsupp.mem_support_iff.mp hw (h ▸ hv)
    simp [Function.update_of_ne hne]
  · simp only [hv, ↓reduceIte, Finsupp.prod]
    have hmem : v ∈ n.support := Finsupp.mem_support_iff.mpr hv
    rw [Finset.prod_eq_zero hmem (by simp [hv]), mul_zero]

/-- The `n`-coefficient of `evalZeroAt v P` equals `P.coeff n` when `n v = 0` and `0` otherwise. -/
@[simp]
theorem coeff_evalZeroAt (v : σ) (P : MvPolynomial σ R) (n : σ →₀ ℕ) :
    (evalZeroAt v P).coeff n = if n v = 0 then P.coeff n else 0 := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
  simp_rw [evalZeroAt_monomial]
  by_cases hn : n v = 0
  · simp only [hn, ↓reduceIte]
    rw [Finset.sum_eq_single n]
    · simp [hn]
    · intro m _ hne
      split_ifs <;> simp [coeff_monomial, hne]
    · intro h
      simp [notMem_support_iff.mp h]
  · simp only [hn, ↓reduceIte]
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    split_ifs with hm
    · rw [coeff_monomial]
      split_ifs with hmn
      · exact absurd (hmn ▸ hm) hn
      · rfl
    · simp

/-- The support of `evalZeroAt v P` consists of the exponents in `P.support` vanishing at `v`. -/
theorem mem_support_evalZeroAt_iff (v : σ) (P : MvPolynomial σ R) (n : σ →₀ ℕ) :
    n ∈ (evalZeroAt v P).support ↔ n v = 0 ∧ n ∈ P.support := by
  simp only [mem_support_iff, coeff_evalZeroAt]
  split_ifs with hn <;> simp [hn]

/-- The eliminated variable `v` never belongs to `(evalZeroAt v P).vars`. -/
@[simp]
theorem notMem_vars_evalZeroAt_self (v : σ) (P : MvPolynomial σ R) :
    v ∉ (evalZeroAt v P).vars := by
  classical
  intro hv
  obtain ⟨n, hn, hnv⟩ := (mem_vars_iff_mem_support v).mp hv
  have h0 : n v = 0 := ((mem_support_evalZeroAt_iff v P n).mp hn).1
  exact Finsupp.mem_support_iff.mp hnv h0

/-- Specializing `X v` to `0` does not introduce any new variables into `vars`. -/
theorem notMem_vars_evalZeroAt_of_notMem {v w : σ} {P : MvPolynomial σ R} (hw : w ∉ P.vars) :
    w ∉ (evalZeroAt v P).vars := by
  classical
  intro hmem
  obtain ⟨n, hn, hnw⟩ := (mem_vars_iff_mem_support w).mp hmem
  exact hw ((mem_vars_iff_mem_support w).mpr ⟨n, ((mem_support_evalZeroAt_iff v P n).mp hn).2, hnw⟩)

end EvalZeroAt

end MvPolynomial
