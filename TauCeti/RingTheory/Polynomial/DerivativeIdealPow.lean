/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Derivation.Basic

/-!
# Derivatives of products in ideal powers

If every derivative of order at most `K` of each of `n` factors evaluates into an ideal `J` at a
point, then every derivative of order at most `K` of their product, times an arbitrary cofactor,
evaluates into `J ^ n`. The Leibniz rule writes the `k`-th derivative of a product as a sum of
products with one derivative of each factor, of orders at most `k`, so each term contributes one
factor from `J` per factor of the product. No factorial is cancelled and the order bound `K` is
unrestricted.

The statements hold for iterates of an arbitrary derivation followed by a ring homomorphism, and
separately for Hasse derivatives, whose hypotheses are not implied by those on ordinary
derivatives: over `ℤ`, the `p`-th derivative of `X ^ p` is `p !` while its `p`-th Hasse derivative
is `1`.

## Main results

* `Ideal.mul_prod_mem_pow_of_mul_mem`: a property of pairs of an ideal and an element, stable
  under multiplication in the stated sense, passes from the factors of a finite product to the
  product with any cofactor, at the power `J ^ card ι`.
* `Derivation.iterate_mul_mem_ideal_mul`, `Derivation.iterate_mul_prod_mem_ideal_pow`: the
  statements for iterates of a derivation `D : Derivation R A A` followed by `φ : A →+* S`.
* `Polynomial.derivative_prod_mem_ideal_pow`: ordinary derivatives of univariate polynomials.
* `Polynomial.hasseDeriv_prod_mem_ideal_pow`: Hasse derivatives of univariate polynomials.
* `MvPolynomial.pderiv_prod_mem_ideal_pow`: iterated partial derivatives of multivariate
  polynomials, in an arbitrary variable.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Lemma 11.14 and (11.22), p. 283.
-/

public section

open Polynomial

namespace Ideal

variable {A S ι : Type*} [CommMonoid A] [CommSemiring S]

/-- Let `P I x` be a property of an ideal `I` of `S` and an element `x` of `A`, which holds for
`⊤` and every element, and passes to products in the form `P I x → P J y → P (I * J) (x * y)`.
If `P J (f i)` for every factor of a finite product, then `P (J ^ card ι) (g * ∏ i, f i)` for
every cofactor `g`. -/
theorem mul_prod_mem_pow_of_mul_mem [Fintype ι] {J : Ideal S} (P : Ideal S → A → Prop)
    (htop : ∀ x, P ⊤ x) (hmul : ∀ {I : Ideal S} {x y : A}, P I x → P J y → P (I * J) (x * y))
    {f : ι → A} (hf : ∀ i, P J (f i)) (g : A) :
    P (J ^ Fintype.card ι) (g * ∏ i, f i) := by
  classical
  suffices ∀ s : Finset ι, P (J ^ s.card) (g * ∏ i ∈ s, f i) from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using htop g
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ, mul_left_comm,
      mul_comm (f i)]
    exact hmul ih (hf i)

end Ideal

namespace Derivation

variable {R A S ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [CommSemiring S]

/-- If the iterates of order at most `K` of a derivation `D` at `x` and at `y` map under `φ` into
the ideals `I` and `I'`, then those at `x * y` map into `I * I'`. -/
theorem iterate_mul_mem_ideal_mul (D : Derivation R A A) (φ : A →+* S) {I I' : Ideal S}
    {K : ℕ} {x y : A} (hx : ∀ k ≤ K, φ (D^[k] x) ∈ I) (hy : ∀ k ≤ K, φ (D^[k] y) ∈ I') :
    ∀ k ≤ K, φ (D^[k] (x * y)) ∈ I * I' := by
  intro k hk
  rw [D.iterate_apply_mul, map_sum]
  refine sum_mem fun ij hij => ?_
  have hij := Finset.mem_antidiagonal.1 hij
  rw [map_nsmul, map_mul]
  exact Submodule.smul_of_tower_mem _ _
    (Ideal.mul_mem_mul (hx _ (by omega)) (hy _ (by omega)))

/-- **Derivatives of a product in an ideal power.** If the iterates of order at most `K` of a
derivation `D` at each of the `card ι` factors `f i` map under `φ` into an ideal `J`, then the
iterates of order at most `K` at their product with an arbitrary cofactor `g` map into
`J ^ card ι`. -/
theorem iterate_mul_prod_mem_ideal_pow [Fintype ι] (D : Derivation R A A) (φ : A →+* S)
    (f : ι → A) (g : A) (J : Ideal S) (K : ℕ) (hf : ∀ i, ∀ k ≤ K, φ (D^[k] (f i)) ∈ J) :
    ∀ k ≤ K, φ (D^[k] (g * ∏ i, f i)) ∈ J ^ Fintype.card ι :=
  Ideal.mul_prod_mem_pow_of_mul_mem (fun I x => ∀ k ≤ K, φ (D^[k] x) ∈ I)
    (fun _ _ _ => Submodule.mem_top) (D.iterate_mul_mem_ideal_mul φ) hf g

end Derivation

namespace Polynomial

variable {R ι : Type*} [CommSemiring R]

/-- **Ordinary derivatives of a product in an ideal power**: if every derivative of order at most
`K` of each of the `card ι` factors `f i` evaluates into `J` at `a`, then every derivative of
order at most `K` of the product with an arbitrary cofactor `g` evaluates into `J ^ card ι`.
No factorial is cancelled and `K` is unrestricted. -/
theorem derivative_prod_mem_ideal_pow [Fintype ι] (f : ι → R[X]) (g : R[X]) (a : R)
    (J : Ideal R) (K : ℕ) (hf : ∀ i, ∀ k ≤ K, (derivative^[k] (f i)).eval a ∈ J) :
    ∀ k ≤ K, (derivative^[k] (g * ∏ i, f i)).eval a ∈ J ^ Fintype.card ι :=
  derivative'.iterate_mul_prod_mem_ideal_pow (evalRingHom a) f g J K hf

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
  Ideal.mul_prod_mem_pow_of_mul_mem (fun I p => ∀ k ≤ K, (hasseDeriv k p).eval a ∈ I)
    (fun _ _ _ => Submodule.mem_top) hasseDeriv_mul_mem_ideal_mul hf g

end Polynomial

namespace MvPolynomial

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
