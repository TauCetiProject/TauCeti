/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Coeff
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Powers of linear forms span the homogeneous polynomials

Over a field `K` of characteristic zero, the `n`-th powers of linear forms span the space of
homogeneous polynomials of degree `n` in finitely many variables. This file proves the sharper
statement in which the linear forms are restricted to a polynomially dense set of coefficient
vectors: if `S ⊆ K^σ` is such that only the zero polynomial vanishes at every point of `S`, then
the powers `(∑ i, x i • X i) ^ n` for `x ∈ S` already span the degree-`n` homogeneous polynomials.

The argument is by duality. A linear functional `φ` on the polynomial ring that vanishes on all
these powers defines a polynomial `Q` in the coordinates `x`, with
`Q (x) = φ ((∑ i, x i • X i) ^ n)` for every point `x`; by the multinomial theorem the
coefficient of `Q` at an exponent `d` of total degree `n` is the multinomial coefficient of `d`
times `φ (X ^ d)`. Since `Q` vanishes on `S`, it is zero, and since multinomial coefficients do not
vanish in characteristic zero, `φ` kills every monomial of degree `n`, hence the whole homogeneous
component.

This is the classical polarization argument, used for instance to show that the restrictions of
the trace polynomials of the representations of a semisimple Lie algebra span the invariant
polynomials on a Cartan subalgebra, where `S` is the set of dominant integral weights.

## Main results

* `TauCeti.MvPolynomial.span_sum_smul_X_pow_eq_homogeneousSubmodule`: the `n`-th powers of the
  linear forms with coefficient vectors in a polynomially dense set span the homogeneous
  polynomials of degree `n`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

variable {K : Type*} [Field K] [CharZero K]

/-- **Polarization.** Over a field of characteristic zero, let `S` be a polynomially dense set of
points of `K^σ`, in the sense that only the zero polynomial vanishes at every point of `S`. Then the
`n`-th powers of the linear forms `∑ i, x i • X i` with `x ∈ S` span the homogeneous polynomials of
degree `n`. -/
theorem span_sum_smul_X_pow_eq_homogeneousSubmodule (S : Set (σ → K))
    (hS : ∀ q : MvPolynomial σ K, (∀ x ∈ S, eval x q = 0) → q = 0) (n : ℕ) :
    Submodule.span K ((fun x ↦ (∑ i, x i • X i : MvPolynomial σ K) ^ n) '' S) =
      homogeneousSubmodule σ K n := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) fun u hu ↦ ?_
  · rintro _ ⟨x, -, rfl⟩
    exact sum_smul_X_pow_mem_homogeneousSubmodule x n
  by_contra hu'
  obtain ⟨φ, hφu, hφS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu' inferInstance
  set D := (Finset.univ : Finset σ).finsuppAntidiag n
  -- on homogeneous polynomials of degree `n`, `φ` is determined by its values on monomials
  have hφ {p : MvPolynomial σ K} (hp : p ∈ homogeneousSubmodule σ K n) :
      φ p = ∑ d ∈ D, p.coeff d * φ (monomial d 1) := by
    conv_lhs => rw [← aeval_X_left_apply p,
      ((mem_homogeneousSubmodule n p).mp hp).aeval_eq_sum_finsuppAntidiag, map_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    simp [monomial_eq, Finsupp.prod_fintype, C_mul']
  -- the polynomial in the coordinates whose value at `x` is `φ ((∑ i, x i • X i) ^ n)`
  set Q : MvPolynomial σ K := ∑ d ∈ D, monomial d ((d.multinomial : K) * φ (monomial d 1))
  have hQ (x : σ → K) : eval x Q = φ ((∑ i, x i • X i : MvPolynomial σ K) ^ n) := by
    rw [hφ (sum_smul_X_pow_mem_homogeneousSubmodule x n), map_sum]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hdeg : d.sum (fun _ m ↦ m) = n := by
      simpa [Finsupp.sum_fintype] using (Finset.mem_finsuppAntidiag.mp hd).1
    simp only [eval_monomial, coeff_linearCombination_X_pow_of_fintype, hdeg, ↓reduceIte]
    ring
  have hQ0 : Q = 0 := hS Q fun x hx ↦ by
    rw [hQ]
    exact (Submodule.mem_bot K).mp
      (hφS ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, hx, rfl⟩))
  have hmono (d) (hd : d ∈ D) : φ (monomial d 1) = 0 := by
    have hcoeff := congr_arg (fun q : MvPolynomial σ K ↦ q.coeff d) hQ0
    simp only [Q, coeff_sum, coeff_monomial, Finset.sum_ite_eq', hd, ↓reduceIte,
      AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_left (Nat.cast_ne_zero.mpr
      (Finsupp.multinomial_eq d ▸ Nat.multinomial_pos _ _).ne')
  exact hφu <| (hφ hu).trans <|
    Finset.sum_eq_zero fun d hd ↦ by rw [hmono d hd, mul_zero]

end TauCeti.MvPolynomial
