/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.FieldDivision
import TauCeti.Algebra.Polynomial.Degree.Operations
import TauCeti.RingTheory.Polynomial.CyclicInvariants.Basic

/-!
# The norm of a polynomial under the `e`-th roots of unity

Let `ζ` be a primitive `e`-th root of unity in a domain `R` and let `p ∈ R[X]`. The product
`N(p) = ∏_{k < e} p(ζᵏ X)` is invariant under `X ↦ ζ X`, so its coefficients vanish outside the
multiples of `e`, and `N(p) = Q(Xᵉ)` for `Q = contract e N(p)`. When `e ≠ 0` and
`N(p) = Q(Xᵉ)`, the value `p(u)` divides `Q(uᵉ)`, since `p(u)` is the factor `k = 0` of `N(p)(u)`.
Over a domain `K`, if `Xᵉ - w` is prime, `ζ ≠ 0`, `deg p < e` and `Q(w) = 0`, then `p = 0`:
the prime `Xᵉ - w` divides `Q(Xᵉ) = N(p)`, so it divides some factor `p(ζᵏ X)`, of degree less
than `e`.

Stepanov's method for `y^e = f(x)` uses this norm in place of the squaring of the case `e = 2`.

## Main results

* `Polynomial.coeff_prod_comp_C_mul_X_eq_zero`: the coefficients of `∏_{k < e} p(ζᵏ X)` vanish
  outside the multiples of `e`.
* `Polynomial.expand_contract_prod_comp_C_mul_X`: `∏_{k < e} p(ζᵏ X)` is `Q(Xᵉ)` for its
  contraction `Q`.
* `Polynomial.eval_dvd_eval_pow_of_prod_comp_C_mul_X_eq_expand`: if `e ≠ 0` and
  `∏_{k < e} p(ζᵏ X) = Q(Xᵉ)`, then `p(u) ∣ Q(uᵉ)`.
* `Polynomial.eq_zero_of_prod_comp_C_mul_X_eq_expand`: over a domain, if `Xᵉ - w` is prime,
  `ζ ≠ 0`, `deg p < e`, `∏_{k < e} p(ζᵏ X) = Q(Xᵉ)` and `Q(w) = 0`, then `p = 0`.
-/

public section

open Polynomial

namespace Polynomial

section Domain

variable {R : Type*} [CommSemiring R] [IsDomain R]

omit [IsDomain R] in
/-- For a primitive `e`-th root of unity `ζ`, the norm `∏_{k < e} p(ζᵏ X)` is invariant under
`X ↦ ζ X`. For `e = 0` it is the empty product `1`. -/
private theorem prod_comp_C_mul_X_comp_C_mul_X {ζ : R} {e : ℕ} (hζ : IsPrimitiveRoot ζ e)
    (p : R[X]) : (∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X)).comp (C ζ * X) =
      ∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X) := by
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · rw [Finset.range_zero, Finset.prod_empty, one_comp]
  have hstep : ∀ k, (p.comp (C (ζ ^ k) * X)).comp (C ζ * X) = p.comp (C (ζ ^ (k + 1)) * X) :=
    fun k ↦ by simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, pow_succ]
  rw [prod_comp]
  simp_rw [hstep]
  obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by lia⟩
  rw [he', Finset.prod_range_succ, Finset.prod_range_succ' (fun k ↦ p.comp (C (ζ ^ k) * X))]
  congr 1
  rw [← he', hζ.pow_eq_one, pow_zero]

/-- For a primitive `e`-th root of unity `ζ` in a domain, the coefficients of the norm
`∏_{k < e} p(ζᵏ X)` vanish outside the multiples of `e`, since the norm is invariant under
`X ↦ ζ X`. -/
theorem coeff_prod_comp_C_mul_X_eq_zero {ζ : R} {e : ℕ} (hζ : IsPrimitiveRoot ζ e) (p : R[X])
    {n : ℕ} (hn : ¬e ∣ n) : (∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X)).coeff n = 0 :=
  (comp_C_mul_X_eq_self_iff _ hζ).1 (prod_comp_C_mul_X_comp_C_mul_X hζ p) n hn

/-- For a primitive `e`-th root of unity `ζ` in a domain, the norm `∏_{k < e} p(ζᵏ X)` is
`Q(Xᵉ)` for its contraction `Q = contract e (∏_{k < e} p(ζᵏ X))`. -/
theorem expand_contract_prod_comp_C_mul_X {ζ : R} {e : ℕ} (hζ : IsPrimitiveRoot ζ e) (p : R[X]) :
    expand R e (contract e (∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X))) =
      ∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X) :=
  expand_contract_of_comp_C_mul_X_eq_self _ hζ (prod_comp_C_mul_X_comp_C_mul_X hζ p)

end Domain

/-- If `∏_{k < e} p(ζᵏ X) = Q(Xᵉ)` with `e ≠ 0`, then `p(u)` divides `Q(uᵉ)`: it is the factor
`k = 0` of the product at `u`. -/
theorem eval_dvd_eval_pow_of_prod_comp_C_mul_X_eq_expand {R : Type*} [CommSemiring R] {e : ℕ}
    (he : e ≠ 0) {ζ : R} {p Q : R[X]}
    (hNQ : ∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X) = expand R e Q) (u : R) :
    p.eval u ∣ Q.eval (u ^ e) := by
  rw [← expand_eval, ← hNQ, eval_prod]
  have h0 : (p.comp (C (ζ ^ 0) * X)).eval u = p.eval u := by
    rw [pow_zero, C_1, one_mul, comp_X]
  rw [← h0]
  exact Finset.dvd_prod_of_mem (fun k ↦ (p.comp (C (ζ ^ k) * X)).eval u)
    (Finset.mem_range.2 (Nat.pos_of_ne_zero he))

/-- Over a domain `K`, if `Xᵉ - w` is prime, `ζ ≠ 0`, `deg p < e` and
`∏_{k < e} p(ζᵏ X) = Q(Xᵉ)` with `Q(w) = 0`, then `p = 0`. -/
theorem eq_zero_of_prod_comp_C_mul_X_eq_expand {K : Type*} [CommRing K] [IsDomain K] {e : ℕ}
    {w ζ : K} (hprime : Prime (X ^ e - C w)) (hζ : ζ ≠ 0) {p Q : K[X]} (hpdeg : p.natDegree < e)
    (hNQ : ∏ k ∈ Finset.range e, p.comp (C (ζ ^ k) * X) = expand K e Q) (hQ : Q.eval w = 0) :
    p = 0 := by
  -- `X - w` divides `Q`, so the prime `Xᵉ - w` divides `Q(Xᵉ)`, hence some factor `p(ζᵏ X)`.
  have hdvd : X ^ e - C w ∣ expand K e Q := by
    simpa using _root_.map_dvd (expand K e) (dvd_iff_isRoot.2 hQ)
  rw [← hNQ] at hdvd
  obtain ⟨k, -, hk⟩ := hprime.exists_mem_finset_dvd hdvd
  rw [← comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k hζ))]
  refine eq_zero_of_dvd_of_natDegree_lt hk ?_
  rw [natDegree_X_pow_sub_C]
  exact (natDegree_comp_C_mul_X_le _ _).trans_lt hpdeg

end Polynomial
