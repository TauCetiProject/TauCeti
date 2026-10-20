/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.SumIteratedDerivative
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.Algebra.Polynomial.Derivative

/-!
# The auxiliary polynomials of the Lindemann–Weierstrass theorem

For a finite set `S` of `t` elements of a field `K`, natural numbers `l` and `p`, and `γ ∈ K`,
`auxPoly S l p γ` is the polynomial
`f = l ^ (t p) / (p - 1)! * (X - γ) ^ (p - 1) * ∏_{γ' ∈ S, γ' ≠ γ} (X - γ') ^ p`.
In Hermite's proof of the Lindemann–Weierstrass theorem `S` is the support of a vanishing
exponential sum `∑ δ_γ' exp γ'` with algebraic `δ_γ'` and `γ'`, `l` is a common denominator of the
exponents and `p` is a large prime. The number `∑_γ' δ_γ' (sumIDeriv f)(γ')` is then a nonzero
algebraic integer all of whose conjugates have absolute value less than one, which is impossible.

This file proves the algebraic half of that argument: the values of the derivatives of `f` at the
points of `S`. With `A = l ^ t ∏_{γ' ∈ S, γ' ≠ γ} (γ - γ')`,

* `eval_iterate_derivative_auxPoly_self`: `f⁽ᵖ⁻¹⁾(γ) = A ^ p`;
* `eval_iterate_derivative_auxPoly_self_of_lt`, `eval_iterate_derivative_auxPoly_of_ne`: all other
  derivatives of order `< p` vanish at the points of `S`;
* `isIntegral_eval_iterate_derivative_auxPoly_div`: if `l γ'` is an algebraic integer for every
  `γ' ∈ S` and `γ ∈ S`, then for `j ≥ p` the value `f⁽ʲ⁾(z) / p` is an algebraic integer whenever
  `l z` is;
* `exists_eval_sumIDeriv_auxPoly_eq`: consequently `(sumIDeriv f)(γ')` is `A ^ p` at `γ' = γ`, and
  `0` at the other points of `S`, up to `p` times an algebraic integer.

We also record the degree `t p - 1` of `f` (`natDegree_auxPoly`) and the compatibility of `auxPoly`
with field homomorphisms (`auxPoly_map`), used to conjugate it by Galois automorphisms.

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 4, §4.2, the proof of Theorem 4.11 and
  Lemma 4.13.
-/

public section

open Finset Polynomial
open scoped Nat

namespace TauCeti.LindemannWeierstrass

variable {K : Type*} [Field K] [DecidableEq K]

/-- The auxiliary polynomial `l ^ (t p) / (p - 1)! * (X - γ) ^ (p - 1) * ∏ (X - γ') ^ p` of
Hermite's proof of the Lindemann–Weierstrass theorem, where `t` is the cardinality of `S` and the
product runs over the elements `γ' ≠ γ` of `S`. -/
noncomputable def auxPoly (S : Finset K) (l p : ℕ) (γ : K) : K[X] :=
  C ((l : K) ^ (#S * p) / (p - 1)!) * (X - C γ) ^ (p - 1) * ∏ γ' ∈ S.erase γ, (X - C γ') ^ p

/-- The defining formula of `auxPoly S l p γ`. -/
theorem auxPoly_def (S : Finset K) (l p : ℕ) (γ : K) :
    auxPoly S l p γ =
      C ((l : K) ^ (#S * p) / (p - 1)!) * (X - C γ) ^ (p - 1) * ∏ γ' ∈ S.erase γ, (X - C γ') ^ p :=
  (rfl)

/-- Applying a field homomorphism to the coefficients of `auxPoly S l p γ` replaces `S` and `γ` by
their images. -/
@[simp]
theorem auxPoly_map {L : Type*} [Field L] [DecidableEq L] (φ : K →+* L) (S : Finset K)
    (l p : ℕ) (γ : K) : (auxPoly S l p γ).map φ = auxPoly (S.image φ) l p (φ γ) := by
  simp [auxPoly, Polynomial.map_prod, card_image_of_injective _ φ.injective,
    ← image_erase φ.injective, prod_image φ.injective.injOn]

/-- For `γ ∈ S` and nonzero `l`, the polynomial `auxPoly S l p γ` has natural degree `t p - 1`,
where `t` is the cardinality of `S`. This includes `p = 0`, when the polynomial is `1`. -/
theorem natDegree_auxPoly [CharZero K] {S : Finset K} {l p : ℕ} {γ : K} (hγ : γ ∈ S)
    (hl : l ≠ 0) : (auxPoly S l p γ).natDegree = #S * p - 1 := by
  by_cases hp : p = 0
  · simp [auxPoly, hp]
  have hc : (l : K) ^ (#S * p) / (p - 1)! ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hl))
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  rw [auxPoly, mul_assoc, natDegree_C_mul hc,
    natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero γ))
      (prod_ne_zero_iff.2 fun _ _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)),
    natDegree_prod _ _ fun _ _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one, sum_const, card_erase_of_mem hγ,
    smul_eq_mul]
  have : p ≤ #S * p := Nat.le_mul_of_pos_left p (card_pos.2 ⟨γ, hγ⟩)
  rw [Nat.sub_mul, one_mul]
  omega

/-- The `(p - 1)`-st derivative of `auxPoly S l p γ` at `γ` is
`(l ^ t ∏_{γ' ∈ S, γ' ≠ γ} (γ - γ')) ^ p`. -/
theorem eval_iterate_derivative_auxPoly_self [CharZero K] (S : Finset K) (l p : ℕ) (γ : K) :
    (derivative^[p - 1] (auxPoly S l p γ)).eval γ =
      ((l : K) ^ #S * ∏ γ' ∈ S.erase γ, (γ - γ')) ^ p := by
  have h := aeval_iterate_derivative_self (auxPoly S l p γ) (p - 1) γ
    (p' := C ((l : K) ^ (#S * p) / (p - 1)!) * ∏ γ' ∈ S.erase γ, (X - C γ') ^ p)
    (by rw [Algebra.algebraMap_self, Polynomial.map_id, auxPoly]; ring)
  rw [coe_aeval_eq_eval] at h
  rw [h, nsmul_eq_mul, eval_mul, eval_C, eval_prod]
  simp only [eval_pow, eval_sub, eval_X, eval_C, prod_pow, mul_pow, pow_mul]
  have : ((p - 1)! : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp

/-- The derivatives of `auxPoly S l p γ` of order less than `p - 1` vanish at `γ`. -/
theorem eval_iterate_derivative_auxPoly_self_of_lt (S : Finset K) (l : ℕ) {p j : ℕ} (γ : K)
    (hj : j < p - 1) : (derivative^[j] (auxPoly S l p γ)).eval γ = 0 := by
  have h := aeval_iterate_derivative_of_lt (auxPoly S l p γ) (p - 1) γ
    (p' := C ((l : K) ^ (#S * p) / (p - 1)!) * ∏ γ' ∈ S.erase γ, (X - C γ') ^ p)
    (by rw [Algebra.algebraMap_self, Polynomial.map_id, auxPoly]; ring) hj
  rwa [coe_aeval_eq_eval] at h

/-- The derivatives of `auxPoly S l p γ` of order less than `p` vanish at every point of `S` other
than `γ`. -/
theorem eval_iterate_derivative_auxPoly_of_ne {S : Finset K} (l : ℕ) {p j : ℕ} {γ γ' : K}
    (hγ' : γ' ∈ S) (hne : γ' ≠ γ) (hj : j < p) :
    (derivative^[j] (auxPoly S l p γ)).eval γ' = 0 := by
  have h := aeval_iterate_derivative_of_lt (auxPoly S l p γ) p γ'
    (p' := C ((l : K) ^ (#S * p) / (p - 1)!) * (X - C γ) ^ (p - 1) *
      ∏ γ'' ∈ (S.erase γ).erase γ', (X - C γ'') ^ p)
    (by
      rw [Algebra.algebraMap_self, Polynomial.map_id, auxPoly,
        ← mul_prod_erase _ _ (mem_erase.2 ⟨hne, hγ'⟩)]
      ring) hj
  rwa [coe_aeval_eq_eval] at h

/-- The key computation behind the integrality of the derivatives of `auxPoly S l p γ`: every
derivative satisfies `(p - 1)! f⁽ʲ⁾(z) = j! y` for an algebraic integer `y`, provided that `l z` is
an algebraic integer. -/
private theorem exists_isIntegral_factorial_mul_eval_iterate_derivative_auxPoly [CharZero K]
    {S : Finset K} {l p : ℕ} {γ : K} (hγ : γ ∈ S) (hp : p ≠ 0)
    (hS : ∀ γ' ∈ S, IsIntegral ℤ ((l : K) * γ')) {z : K} (hz : IsIntegral ℤ ((l : K) * z))
    (j : ℕ) : ∃ y : K, IsIntegral ℤ y ∧
      ((p - 1)! : K) * (derivative^[j] (auxPoly S l p γ)).eval z = j ! * y := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp
  obtain ⟨t, ht⟩ : ∃ t, #S = t + 1 := ⟨_, (card_erase_add_one hγ).symm⟩
  set R := integralClosure ℤ K
  -- Multiplying by `(p - 1)!` clears the denominator of `auxPoly`, leaving a power of `l` times the
  -- denominator-free polynomial `h` below. The polynomial `q` with `q (l X) = l ^ _ * h` has
  -- algebraic integer coefficients, and the `j`-th derivative of such a polynomial is `j!` times
  -- another one.
  set h : K[X] := (X - C γ) ^ p * ∏ γ' ∈ S.erase γ, (X - C γ') ^ (p + 1) with hh
  set q : K[X] := (X - C ((l : K) * γ)) ^ p * ∏ γ' ∈ S.erase γ, (X - C ((l : K) * γ')) ^ (p + 1)
    with hq
  have hlin (c : K) : (X - C ((l : K) * c)).comp (C (l : K) * X) = C (l : K) * (X - C c) := by
    rw [sub_comp, X_comp, C_comp, C_mul]
    ring
  have hcomp : q.comp (C (l : K) * X) = C ((l : K) ^ (t * (p + 1) + p)) * h := by
    rw [hq, hh, mul_comp, pow_comp, Polynomial.prod_comp]
    simp_rw [pow_comp, hlin, mul_pow, prod_mul_distrib, prod_const, card_erase_of_mem hγ, ht,
      add_tsub_cancel_right, C_pow]
    ring
  -- The coefficients of `q` are algebraic integers.
  obtain ⟨Q, hQ⟩ : ∃ Q : R[X], Q.map (algebraMap R K) = q := by
    rw [← mem_lifts, lifts_iff_liftsRing]
    have hlift (c : K) (hc : IsIntegral ℤ ((l : K) * c)) :
        X - C ((l : K) * c) ∈ liftsRing (algebraMap R K) :=
      sub_mem ((lifts_iff_liftsRing _ _).1 (X_mem_lifts _))
        ((lifts_iff_liftsRing _ _).1 (C'_mem_lifts ⟨⟨_, hc⟩, rfl⟩))
    exact mul_mem (pow_mem (hlift γ (hS γ hγ)) _)
      (prod_mem fun γ' hγ' ↦ pow_mem (hlift γ' (hS γ' (mem_of_mem_erase hγ'))) _)
  obtain ⟨g, -, hg⟩ := exists_iterate_derivative_eq_factorial_smul Q j
  set w : R := ⟨_, hz⟩
  have hw : IsIntegral ℤ (algebraMap R K (g.eval w)) := (g.eval w).2
  refine ⟨(l : K) ^ (j + 1) * algebraMap R K (g.eval w), ((isIntegral_natCast l).pow _).mul hw, ?_⟩
  -- Differentiate `q (l X) = l ^ (t (p + 1) + p) h` `j` times and evaluate at `z`.
  have hder := congrArg (fun P ↦ (derivative^[j] P).eval z) hcomp
  simp only [iterate_derivative_comp_C_mul_X, iterate_derivative_C_mul, eval_mul, eval_C,
    eval_comp, eval_X] at hder
  -- `w` is `l z`, viewed in the integral closure.
  have hlz : (l : K) * z = algebraMap R K w := rfl
  rw [← hQ, iterate_derivative_map, hg, nsmul_eq_mul, Polynomial.map_mul,
    Polynomial.map_natCast, eval_mul, eval_natCast, eval_map, hlz, eval₂_at_apply] at hder
  have hf : auxPoly S l (p + 1) γ = C ((l : K) ^ (#S * (p + 1)) / p !) * h := by
    rw [auxPoly, hh, add_tsub_cancel_right, mul_assoc]
  rw [hf, iterate_derivative_C_mul, eval_mul, eval_C, ht, add_tsub_cancel_right]
  have : (p ! : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero p)
  field_simp
  linear_combination -(l : K) * hder

/-- If `γ ∈ S` and `l γ'` is an algebraic integer for every `γ' ∈ S`, then for `j ≥ p` the `j`-th
derivative of `auxPoly S l p γ` takes values in `p` times the algebraic integers at every `z` for
which `l z` is an algebraic integer. -/
theorem isIntegral_eval_iterate_derivative_auxPoly_div [CharZero K] {S : Finset K} {l p : ℕ}
    {γ : K} (hγ : γ ∈ S) (hS : ∀ γ' ∈ S, IsIntegral ℤ ((l : K) * γ')) {z : K}
    (hz : IsIntegral ℤ ((l : K) * z)) {j : ℕ} (hj : p ≤ j) :
    IsIntegral ℤ ((derivative^[j] (auxPoly S l p γ)).eval z / p) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simpa using isIntegral_zero
  obtain ⟨y, hy, hfy⟩ :=
    exists_isIntegral_factorial_mul_eval_iterate_derivative_auxPoly hγ hp hS hz j
  -- `j! = p * (p - 1)! * m`, so `f⁽ʲ⁾(z) / p = m y`.
  obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hj
  have hjm : (j ! : K) = p * (p - 1)! * m := by
    rw [hm, ← Nat.mul_factorial_pred hp]
    push_cast
    ring
  rw [hjm] at hfy
  have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hfac : ((p - 1)! : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have : (derivative^[j] (auxPoly S l p γ)).eval z / p = m * y := by
    rw [div_eq_iff hp']
    apply mul_left_cancel₀ hfac
    linear_combination hfy
  rw [this]
  exact (isIntegral_natCast m).mul hy

/-- If `γ ∈ S`, `p ≠ 0` and `l γ'` is an algebraic integer for every `γ' ∈ S`, then at every point
`γ'` of `S` the sum of all derivatives of `auxPoly S l p γ` is, up to `p` times an algebraic
integer, equal to `(l ^ t ∏_{γ'' ∈ S, γ'' ≠ γ} (γ - γ'')) ^ p` if `γ' = γ` and to `0` otherwise. -/
theorem exists_eval_sumIDeriv_auxPoly_eq [CharZero K] {S : Finset K} {l p : ℕ} {γ : K}
    (hγ : γ ∈ S) (hp : p ≠ 0) (hS : ∀ γ' ∈ S, IsIntegral ℤ ((l : K) * γ')) {γ' : K}
    (hγ' : γ' ∈ S) :
    ∃ y : K, IsIntegral ℤ y ∧ (sumIDeriv (auxPoly S l p γ)).eval γ' =
      (if γ' = γ then ((l : K) ^ #S * ∏ γ'' ∈ S.erase γ, (γ - γ'')) ^ p else 0) + p * y := by
  set f := auxPoly S l p γ
  set A := ((l : K) ^ #S * ∏ γ'' ∈ S.erase γ, (γ - γ'')) ^ p
  set n := f.natDegree + p
  have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp
  refine ⟨∑ j ∈ range n, if p ≤ j then (derivative^[j] f).eval γ' / p else 0,
    IsIntegral.sum _ fun j _ ↦ ?_, ?_⟩
  · split_ifs with hj
    · exact isIntegral_eval_iterate_derivative_auxPoly_div hγ hS (hS γ' hγ') hj
    · exact isIntegral_zero
  -- Each derivative of order `j` contributes `A` if `(j, γ') = (p - 1, γ)` and a multiple of `p`
  -- otherwise.
  have hterm (j : ℕ) : (derivative^[j] f).eval γ' =
      (if j = p - 1 ∧ γ' = γ then A else 0) +
        p * if p ≤ j then (derivative^[j] f).eval γ' / p else 0 := by
    split_ifs with h hj hj
    · exact absurd h.1 (by omega)
    · obtain ⟨rfl, rfl⟩ := h
      rw [mul_zero, add_zero]
      exact eval_iterate_derivative_auxPoly_self S l p γ'
    · rw [mul_div_cancel₀ _ hp', zero_add]
    · rw [mul_zero, add_zero]
      rcases eq_or_ne γ' γ with rfl | hne
      · exact eval_iterate_derivative_auxPoly_self_of_lt S l γ'
          (by have : j ≠ p - 1 := fun hj' ↦ h ⟨hj', rfl⟩; omega)
      · exact eval_iterate_derivative_auxPoly_of_ne l hγ' hne (by omega)
  rw [sumIDeriv_apply_of_lt (show f.natDegree < n by omega), eval_finsetSum, mul_sum,
    sum_congr rfl fun j _ ↦ hterm j, sum_add_distrib]
  congr 1
  by_cases h : γ' = γ
  · simp [h, A, show p - 1 < n by omega]
  · simp [h]

end TauCeti.LindemannWeierstrass

end

/-! ### Examples -/

open Finset Polynomial
open scoped Nat

namespace TauCeti.LindemannWeierstrass

/- For a single point the product is empty. -/
example {K : Type*} [Field K] [DecidableEq K] (l p : ℕ) (γ : K) :
    auxPoly {γ} l p γ = C ((l : K) ^ p / (p - 1)!) * (X - C γ) ^ (p - 1) := by
  simp [auxPoly]

/- `auxPoly {0, 1} 1 2 0 = X (X - 1) ^ 2`. -/
example : auxPoly ({0, 1} : Finset ℚ) 1 2 0 = X ^ 3 - 2 * X ^ 2 + X := by
  simp [auxPoly]
  ring

/- The factor `1 / (p - 1)!` makes the coefficients non-integral: `auxPoly {0} 1 3 0 = X ^ 2 / 2`,
not `X ^ 2 / 3!`. -/
example : auxPoly ({0} : Finset ℚ) 1 3 0 = C (1 / 2) * X ^ 2 := by
  simp [auxPoly]

end TauCeti.LindemannWeierstrass
