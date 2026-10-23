/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Polynomial.Roots
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Analysis.Calculus.LocalExtr.Rolle

/-!
# Real zeros of exponential polynomials

A real *exponential polynomial* is a function `f(x) = ∑ₖ pₖ(x) exp(γₖ x)` with real polynomials
`pₖ` and real exponents `γₖ`, indexed by a finite set. If the index set is nonempty, the
exponents are pairwise distinct and the `pₖ` are nonzero, then `f` has fewer than
`∑ₖ (deg pₖ + 1)` real zeros (`TauCeti.card_lt_of_sum_eval_mul_exp_eq_zero`); in particular its
zero set is finite. Nonemptiness is needed: the empty sum vanishes everywhere.
For a single term this is the bound on the number of roots of a polynomial.

The proof is by induction on the number of terms. Multiplying `f` by `exp(-γ x)` for one of
the exponents `γ`, with polynomial `p`, does not change the zeros and makes the exponent of `p`
equal to `0`. Differentiating `deg p + 1` times removes this term, while every other term
`q(x) exp(δ x)` with `δ ≠ 0` becomes `((d/dx + δ) ^ (deg p + 1) q)(x) exp(δ x)`, whose polynomial
has the same degree as `q`. By Rolle's theorem each differentiation loses at most one zero.

This zero estimate is used in Schneider's proof of the Gelfond–Schneider theorem for real
numbers: an auxiliary function `∑ᵢⱼ aᵢⱼ zⁱ exp(j z log α)` cannot vanish at more real points
than the number of its coefficients.

## Main results

* `TauCeti.card_lt_of_sum_eval_mul_exp_eq_zero`: for a nonempty finite index set, pairwise
  distinct exponents `γₖ` and nonzero `pₖ`, a finite set of zeros of `∑ₖ pₖ(x) exp(γₖ x)` has
  fewer than `∑ₖ (deg pₖ + 1)` points.
* `TauCeti.finite_setOf_sum_eval_mul_exp_eq_zero`: under the same hypotheses, the zero set of
  such a function is finite.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.4, Lemma 4.23.
-/

public section

open Finset Polynomial

namespace TauCeti

/-- The derivative of `∑ₖ pₖ(x) exp(γₖ x)` is `∑ₖ (pₖ' + γₖ pₖ)(x) exp(γₖ x)`. -/
private theorem hasDerivAt_sum_eval_mul_exp {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (p : ι → ℝ[X]) (x : ℝ) :
    HasDerivAt (fun x ↦ ∑ i ∈ s, (p i).eval x * Real.exp (γ i * x))
      (∑ i ∈ s, (derivative (p i) + C (γ i) * p i).eval x * Real.exp (γ i * x)) x := by
  refine HasDerivAt.fun_sum fun i _ ↦ ?_
  refine (((p i).hasDerivAt x).fun_mul ((hasDerivAt_id' x).const_mul (γ i)).exp).congr_deriv ?_
  simp only [eval_add, eval_mul, eval_C, mul_one]
  ring

/-- **Zero estimate for real exponential polynomials** (Evertse, Lemma 4.23). Let `s` be a
nonempty finite index set, `γ` exponents that are pairwise distinct on `s`, and `p` nonzero real
polynomials. Then every finite set `Z` of zeros of `x ↦ ∑ₖ pₖ(x) exp(γₖ x)` has fewer than
`∑ₖ (deg pₖ + 1)` points. -/
theorem card_lt_of_sum_eval_mul_exp_eq_zero {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {γ : ι → ℝ} (hγ : Set.InjOn γ s) {p : ι → ℝ[X]} (hp : ∀ i ∈ s, p i ≠ 0) {Z : Finset ℝ}
    (hZ : ∀ x ∈ Z, ∑ i ∈ s, (p i).eval x * Real.exp (γ i * x) = 0) :
    #Z < ∑ i ∈ s, ((p i).natDegree + 1) := by
  classical
  induction hs using Finset.Nonempty.cons_induction generalizing γ p Z with
  | singleton a =>
    -- A single term `p(x) exp(γ x)` vanishes exactly at the roots of `p`.
    have hpa := hp a (mem_singleton_self a)
    have hsub : Z ⊆ (p a).roots.toFinset := fun x hx ↦ by
      have := hZ x hx
      rw [sum_singleton, mul_eq_zero, or_iff_left (Real.exp_ne_zero _)] at this
      exact Multiset.mem_toFinset.2 ((mem_roots hpa).2 this)
    rw [sum_singleton]
    exact Nat.lt_succ_of_le ((card_le_card hsub).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' _)))
  | cons a t hat ht ih =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at hp
    have hγ' : Set.InjOn γ t := hγ.mono (by simp)
    -- Shift the exponents by `-γ a` and differentiate `N = deg p_a + 1` times.
    set δ : ι → ℝ := fun i ↦ γ i - γ a
    set D : ℝ → ℝ[X] → ℝ[X] := fun d r ↦ derivative r + C d * r
    set N := (p a).natDegree + 1
    set F : ℕ → ℝ → ℝ := fun n x ↦
      ∑ i ∈ cons a t hat, ((D (δ i))^[n] (p i)).eval x * Real.exp (δ i * x)
    have hF : ∀ n < N, ∀ x, HasDerivAt (F n) (F (n + 1) x) x := fun n _ x ↦ by
      simpa only [F, Function.iterate_succ_apply'] using
        hasDerivAt_sum_eval_mul_exp (cons a t hat) δ (fun i ↦ (D (δ i))^[n] (p i)) x
    have hF₀ : ∀ x ∈ Z, F 0 x = 0 := fun x hx ↦ by
      have h : F 0 x = Real.exp (-(γ a * x)) *
          ∑ i ∈ cons a t hat, (p i).eval x * Real.exp (γ i * x) := by
        simp only [F, δ, Function.iterate_zero_apply, mul_sum]
        refine sum_congr rfl fun i _ ↦ ?_
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      rw [h, hZ x hx, mul_zero]
    obtain ⟨Z', hZ', hcard⟩ := exists_card_le_card_add_of_hasDerivAt hF hF₀
    -- The term of index `a` has exponent `0`, so it disappears after `N` differentiations.
    have hδ : ∀ i ∈ t, δ i ≠ 0 := fun i hi h ↦
      hat (hγ (by simp [hi]) (by simp) (sub_eq_zero.1 h) ▸ hi)
    have hDa : (D (δ a))^[N] (p a) = 0 := by
      simp only [D, δ, sub_self, map_zero, zero_mul, add_zero]
      exact iterate_derivative_eq_zero (Nat.lt_succ_self _)
    have hFN : ∀ x, F N x = ∑ i ∈ t, ((D (δ i))^[N] (p i)).eval x * Real.exp (δ i * x) :=
      fun x ↦ by simp only [F, sum_cons, hDa, eval_zero, zero_mul, zero_add]
    have hlt := ih (γ := δ) (fun i hi j hj h ↦ hγ' hi hj (sub_left_inj.1 h))
      (p := fun i ↦ (D (δ i))^[N] (p i))
      (fun i hi ↦ (iterate_derivative_add_C_mul_eq_zero_iff (hδ i hi) N).not.2 (hp.2 i hi))
      (fun x hx ↦ (hFN x).symm.trans (hZ' x hx))
    rw [sum_congr rfl fun i hi ↦ by
      rw [natDegree_iterate_derivative_add_C_mul (hδ i hi) N]] at hlt
    rw [sum_cons]
    omega

/-- The zero set of a real exponential polynomial `x ↦ ∑ₖ pₖ(x) exp(γₖ x)`, with nonzero
polynomials `pₖ` and exponents `γₖ` pairwise distinct on a nonempty finite index set, is
finite. -/
theorem finite_setOf_sum_eval_mul_exp_eq_zero {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {γ : ι → ℝ} (hγ : Set.InjOn γ s) {p : ι → ℝ[X]} (hp : ∀ i ∈ s, p i ≠ 0) :
    {x : ℝ | ∑ i ∈ s, (p i).eval x * Real.exp (γ i * x) = 0}.Finite := by
  by_contra h
  obtain ⟨Z, hZ, hcard⟩ := Set.Infinite.exists_subset_card_eq h (∑ i ∈ s, ((p i).natDegree + 1))
  exact (card_lt_of_sum_eval_mul_exp_eq_zero hs hγ hp fun x hx ↦ hZ hx).ne hcard

end TauCeti
