/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Derivation.Ideal
import TauCeti.RingTheory.Ideal.Operations

/-!
# Derivatives of products of polynomials in ideal powers

If every derivative of order at most `K` of each of `n` univariate polynomials evaluates into an
ideal `J` at a point, then every derivative of order at most `K` of their product, times an
arbitrary cofactor, evaluates into `J ^ n`. No factorial is cancelled and the order bound `K` is
unrestricted.

The ordinary statement is the instance of `Derivation.iterate_mul_prod_mem_ideal_pow` for the
derivative and evaluation. The Hasse statement is proved separately from Mathlib's
`Polynomial.hasseDeriv_mul`; its hypotheses are not implied by those on ordinary derivatives:
over `ℤ`, the `p`-th derivative of `X ^ p` is `p !` while its `p`-th Hasse derivative is `1`.
The multivariate form is `MvPolynomial.pderiv_prod_mem_ideal_pow`.

## Main results

* `Polynomial.derivative_prod_mem_ideal_pow`: ordinary derivatives of univariate polynomials.
* `Polynomial.hasseDeriv_prod_mem_ideal_pow`: Hasse derivatives of univariate polynomials.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Lemma 11.14 and (11.22), p. 283, for
  the Hasse statement `Polynomial.hasseDeriv_prod_mem_ideal_pow`; the ordinary statement adapts
  their argument to iterated derivatives.
-/

public section

open Polynomial

namespace Polynomial

variable {R ι : Type*} [CommSemiring R]

/-- **Ordinary derivatives of a product in an ideal power**: if every derivative of order at most
`K` of each of the `card ι` factors `f i` evaluates into `J` at `a`, then every derivative of
order at most `K` of the product with an arbitrary cofactor `g` evaluates into `J ^ card ι`.
No factorial is cancelled and `K` is unrestricted. -/
theorem derivative_prod_mem_ideal_pow [Fintype ι] (f : ι → R[X]) (g : R[X]) (a : R)
    (J : Ideal R) (K : ℕ) (hf : ∀ i, ∀ k ≤ K, (derivative^[k] (f i)).eval a ∈ J) :
    ∀ k ≤ K, (derivative^[k] (g * ∏ i, f i)).eval a ∈ J ^ Fintype.card ι := by
  have hD : ⇑(derivative' : Derivation R R[X] R[X]) = ⇑derivative := funext derivative'_apply
  have h := derivative'.iterate_mul_prod_mem_ideal_pow (evalRingHom a) f g J K
  rw [hD, coe_evalRingHom] at h
  exact h hf

/-- If the Hasse derivatives of order at most `K` of `p` and `q` evaluate at `a` into the ideals
`I` and `I'`, then those of `p * q` evaluate into `I * I'`. -/
theorem hasseDeriv_mul_mem_ideal_mul {I I' : Ideal R} {K : ℕ} {p q : R[X]} {a : R}
    (hp : ∀ k ≤ K, (hasseDeriv k p).eval a ∈ I) (hq : ∀ k ≤ K, (hasseDeriv k q).eval a ∈ I') :
    ∀ k ≤ K, (hasseDeriv k (p * q)).eval a ∈ I * I' := by
  intro k hk
  rw [hasseDeriv_mul, eval_finsetSum]
  refine sum_mem fun ij hij => ?_
  have hij := Finset.mem_antidiagonal.1 hij
  rw [eval_mul]
  exact Ideal.mul_mem_mul (hp _ (by omega)) (hq _ (by omega))

/-- **Hasse derivatives of a product in an ideal power** (IK, Lemma 11.14 and (11.22)): if every
Hasse derivative of order at most `K` of each of the `card ι` factors `f i` evaluates into `J` at
`a`, then every Hasse derivative of order at most `K` of the product with an arbitrary cofactor
`g` evaluates into `J ^ card ι`. -/
theorem hasseDeriv_prod_mem_ideal_pow [Fintype ι] (f : ι → R[X]) (g : R[X]) (a : R)
    (J : Ideal R) (K : ℕ) (hf : ∀ i, ∀ k ≤ K, (hasseDeriv k (f i)).eval a ∈ J) :
    ∀ k ≤ K, (hasseDeriv k (g * ∏ i, f i)).eval a ∈ J ^ Fintype.card ι :=
  Ideal.pow_card_mul_prod_induction (fun I p => ∀ k ≤ K, (hasseDeriv k p).eval a ∈ I)
    (fun _ _ _ => Submodule.mem_top) hasseDeriv_mul_mem_ideal_mul hf g

end Polynomial
