/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Derivation.Ideal

/-!
# Partial derivatives of products of multivariate polynomials in ideal powers

For a variable `s` and a point `a`, if every iterated partial derivative `(pderiv s)^[k]` of order
at most `K` of each of `n` multivariate polynomials evaluates into an ideal `J` at `a`, then so
does every such derivative of their product, times an arbitrary cofactor, into `J ^ n`. This is
the instance of `Derivation.iterate_mul_prod_mem_ideal_pow` for `pderiv s` and evaluation at `a`;
the univariate forms are in `TauCeti.RingTheory.Polynomial.DerivativeIdealPow`.

## Main results

* `MvPolynomial.pderiv_prod_mem_ideal_pow`: iterated partial derivatives of multivariate
  polynomials, in an arbitrary variable.
* `MvPolynomial.pow_dvd_aeval_iterate_pderiv_mul_X_pow_sub_X_pow`: divisibility of ordinary
  jets at points satisfying a Frobenius congruence, using
  `Derivation.iterate_mul_prod_mem_ideal_pow`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Lemma 11.14 and (11.22), p. 283, prove
  the analogue for Hasse derivatives of univariate polynomials; the argument here adapts it to
  iterated partial derivatives.
-/

public section

open Finset

namespace MvPolynomial

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] in
/-- All ordinary jets in `X i` of `g * (X i ^ p - X j)^e` are divisible by `p ^ e` at
a point satisfying `a i ^ p ≡ a j (mod p)`, when `i ≠ j`. See Green, *On Landau–Siegel zeros*. -/
theorem pow_dvd_aeval_iterate_pderiv_mul_X_pow_sub_X_pow {σ : Type*} {i j : σ}
    (g : MvPolynomial σ R) (hij : j ≠ i) {p : ℕ} {a : σ → S}
    (ha : (p : S) ∣ a i ^ p - a j) (e k : ℕ) :
    (p : S) ^ e ∣ aeval a ((pderiv i)^[k] (g * (X i ^ p - X j) ^ e)) := by
  let d : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) := pderiv i
  have hfactor (t : ℕ) : aeval a (d^[t] (X i ^ p - X j)) ∈ Ideal.span {(p : S)} := by
    rw [Ideal.mem_span_singleton]
    cases t with
    | zero =>
      simpa only [Function.iterate_zero_apply, map_sub, map_pow, aeval_X] using ha
    | succ t =>
      have hd : d (X i ^ p - X j) = p • X i ^ (p - 1) := by
        simp only [d, map_sub, pderiv_pow, pderiv_X_self, pderiv_X_of_ne hij, mul_one,
          sub_zero, nsmul_eq_mul]
      rw [Function.iterate_succ_apply, hd]
      have hmap (f : MvPolynomial σ R) : d^[t] (p • f) = p • d^[t] f := by
        simpa only [pow_apply_eq_iterate, Derivation.coeFn_coe] using
          map_nsmul (d.toLinearMap ^ t) p f
      rw [hmap, map_nsmul, nsmul_eq_mul]
      exact dvd_mul_right _ _
  have hprod := d.iterate_mul_prod_mem_ideal_pow (RingHomClass.toRingHom (aeval a))
    (fun _ : Fin e ↦ X i ^ p - X j) g (Ideal.span {(p : S)}) k (fun _ t _ ↦ hfactor t) k le_rfl
  simpa only [prod_const, card_univ, Fintype.card_fin, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, RingHom.coe_coe, d] using hprod

variable {R σ ι : Type*} [CommSemiring R]

/-- **Partial derivatives of a product in an ideal power**: for a variable `s` and a point
`a : σ → R`, if every iterated partial derivative `(pderiv s)^[k]` of order at most `K` of each of
the `card ι` factors `f i` evaluates into `J` at `a`, so does every such derivative of the product
with an arbitrary cofactor `g`, into `J ^ card ι`. The bivariate form is `σ = Fin 2`. -/
theorem pderiv_prod_mem_ideal_pow [Fintype ι] (s : σ) (f : ι → MvPolynomial σ R)
    (g : MvPolynomial σ R) (a : σ → R) (J : Ideal R) (K : ℕ)
    (hf : ∀ i, ∀ k ≤ K, eval a ((pderiv s)^[k] (f i)) ∈ J) :
    ∀ k ≤ K, eval a ((pderiv s)^[k] (g * ∏ i, f i)) ∈ J ^ Fintype.card ι :=
  (pderiv s).iterate_mul_prod_mem_ideal_pow (eval a) f g J K hf

end MvPolynomial
