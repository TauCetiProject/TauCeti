/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The polynomial operators `X_a ∂_b`

For indices `a b : σ`, the operator `X_a ∂_b` on `R[X_σ]` multiplies the partial derivative along
`X_b` by `X_a`. It is a derivation, sending `X_b` to `X_a` and every other variable to zero, and
these derivations satisfy the commutation relations of the elementary matrices of `gl_σ`:

```
⁅X_a ∂_b, X_c ∂_d⁆ = δ_bc X_a ∂_d - δ_da X_c ∂_b.
```

Each `X_a ∂_b` preserves homogeneous degree. In coordinate-free form, the derivation of a
symmetric algebra induced by a linear endomorphism is `SymmetricAlgebra.derivationOfEnd`; the
operators here are written in the variables of `R[X_σ]`, as the polynomial model of the
`sl₂`-modules uses them.

For two distinct variables `x = X a`, `y = X b` the operators `E = x ∂_y` and `F = y ∂_x`, with
`H = ⁅E, F⁆ = x ∂_x - y ∂_y`, form an `sl₂`-triple. On `x ^ i y ^ j` the operator `E` lowers the
`y`-exponent and raises the `x`-exponent with coefficient `j`, `F` does the reverse with
coefficient `i`, and `H` acts by `i - j`. Thus on the degree-`d` homogeneous polynomials the
monomials `x ^ (d - i) y ^ i` form a weight string with weights `d - 2 i`, as in the polynomial
model of the `sl₂`-module `V(d)`.

On a tensor product of two polynomial rings, `X_a ∂_b` acts by the Leibniz rule on both
factors; over a ring this is Mathlib's tensor product of Lie modules. Multiplication of
polynomials intertwines this action with the action on the product.

## Main definitions

* `TauCeti.polynomialOperator R a b`: the derivation `X_a ∂_b` of `R[X_σ]`.
* `TauCeti.tensorPolynomialOperator R a b`: the action of `X_a ∂_b` on `R[X_σ] ⊗ R[X_σ]`.

## Main results

* `TauCeti.lie_polynomialOperator`: the commutation relations of `gl_σ`.
* `MvPolynomial.IsHomogeneous.polynomialOperator`: `X_a ∂_b` preserves homogeneous degree.
* `TauCeti.isSl2Triple_polynomialOperator`: `x ∂_x - y ∂_y`, `x ∂_y`, `y ∂_x` is an
  `sl₂`-triple.
* `TauCeti.polynomialOperator_X_pow_mul_X_pow_succ` and
  `TauCeti.polynomialOperator_self_sub_polynomialOperator_self_X_pow_mul_X_pow`: the action of
  `E` (and, swapping the variables, `F`) and of `H` on monomials.
* `TauCeti.tensorPolynomialOperator_tmul` and `TauCeti.lie_tensorPolynomialOperator`: the
  Leibniz rule on pure tensors and the `gl_σ` relations on the tensor product.

## Implementation notes

The commutator of two endomorphisms in the statement of
`TauCeti.lie_tensorPolynomialOperator` is the bracket of `LieRing.ofAssociativeRing`, which is
a local instance here, as in Mathlib.

## References

* P. Etingof, *Lie groups and Lie algebras*, §11.4, for the polynomial model of the
  `sl₂`-modules.
-/

public section

open MvPolynomial TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

section CommSemiring

variable (R : Type*) [CommSemiring R] {σ : Type*}

/-- The polynomial operator `X_a ∂_b`: the partial derivative along `X b`, multiplied by `X a`.
It is a derivation of `R[X_σ]` sending `X b` to `X a` and every other variable to zero. -/
noncomputable def polynomialOperator (a b : σ) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  (X a : MvPolynomial σ R) • pderiv b

/-- `X_a ∂_b` multiplies the partial derivative along `X b` by `X a`. -/
theorem polynomialOperator_apply (a b : σ) (p : MvPolynomial σ R) :
    polynomialOperator R a b p = X a * pderiv b p := by
  simp [polynomialOperator]

/-- `X_a ∂_b` sends `X b` to `X a` and every other variable to zero. -/
theorem polynomialOperator_X [DecidableEq σ] (a b c : σ) :
    polynomialOperator R a b (X c) = if c = b then X a else 0 := by
  split_ifs with h <;> simp [polynomialOperator_apply, h]

@[simp]
theorem polynomialOperator_X_self (a b : σ) : polynomialOperator R a b (X b) = X a := by
  simp [polynomialOperator_apply]

@[simp]
theorem polynomialOperator_X_of_ne {a b c : σ} (h : c ≠ b) :
    polynomialOperator R a b (X c) = 0 := by
  simp [polynomialOperator_apply, h]

/-- `X_a ∂_b` sends the monomial with exponent `s` to `s b` times the monomial in which one
factor `X b` is replaced by `X a`. -/
@[simp]
theorem polynomialOperator_monomial (a b : σ) (s : σ →₀ ℕ) (r : R) :
    polynomialOperator R a b (monomial s r) =
      monomial (s - Finsupp.single b 1 + Finsupp.single a 1) (r * s b) := by
  rw [polynomialOperator_apply, pderiv_monomial, X, monomial_mul_monomial, one_mul, add_comm]

variable {R} in
/-- `X_a ∂_b` preserves homogeneous degree. -/
theorem _root_.MvPolynomial.IsHomogeneous.polynomialOperator {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (a b : σ) : (TauCeti.polynomialOperator R a b p).IsHomogeneous n := by
  rcases n with _ | n
  · obtain ⟨c, rfl⟩ : ∃ c, p = C c :=
      ⟨_, totalDegree_eq_zero_iff_eq_C.mp (le_antisymm hp.totalDegree_le (Nat.zero_le _))⟩
    simpa [polynomialOperator_apply, pderiv_C] using isHomogeneous_zero σ R 0
  · simpa [polynomialOperator_apply, add_comm] using (isHomogeneous_X R a).mul hp.pderiv

/-! ### The raising and lowering operators on monomials in two variables -/

/-- For distinct variables `x = X a` and `y = X b`,
`x ∂_y (x ^ i y ^ (j + 1)) = (j + 1) x ^ (i + 1) y ^ j`. -/
theorem polynomialOperator_X_pow_mul_X_pow_succ {a b : σ} (hab : a ≠ b) (i j : ℕ) :
    polynomialOperator R a b (X a ^ i * X b ^ (j + 1)) =
      ((j : R) + 1) • (X a ^ (i + 1) * X b ^ j) := by
  simp [Derivation.leibniz_pow, Algebra.smul_def, hab]
  ring

/-! ### The action on a tensor product -/

/-- The action of `X_a ∂_b` on `R[X_σ] ⊗ R[X_σ]`: `X_a ∂_b ⊗ 1 + 1 ⊗ X_a ∂_b`. Over a ring, this
is the action of the tensor product of Lie modules over the derivations, see
`TauCeti.tensorPolynomialOperator_eq_toEnd`. -/
noncomputable def tensorPolynomialOperator (a b : σ) :
    Module.End R (MvPolynomial σ R ⊗[R] MvPolynomial σ R) :=
  (polynomialOperator R a b).toLinearMap.rTensor _ +
    (polynomialOperator R a b).toLinearMap.lTensor _

/-- The action on the tensor product is `X_a ∂_b ⊗ 1 + 1 ⊗ X_a ∂_b`. -/
theorem tensorPolynomialOperator_def (a b : σ) :
    tensorPolynomialOperator R a b =
      (polynomialOperator R a b).toLinearMap.rTensor _ +
        (polynomialOperator R a b).toLinearMap.lTensor _ :=
  (rfl)

/-- **The Leibniz rule on pure tensors**: `X_a ∂_b` acts on `p ⊗ q` through each factor in
turn. -/
@[simp]
theorem tensorPolynomialOperator_tmul (a b : σ) (p q : MvPolynomial σ R) :
    tensorPolynomialOperator R a b (p ⊗ₜ q) =
      polynomialOperator R a b p ⊗ₜ q + p ⊗ₜ polynomialOperator R a b q := by
  simp [tensorPolynomialOperator_def]

/-- Multiplication of polynomials intertwines the action of `X_a ∂_b` on the tensor product with
its action on `R[X_σ]`: this is the Leibniz rule `D (p q) = D p q + p D q`. -/
theorem mul'_tensorPolynomialOperator (a b : σ) (x : MvPolynomial σ R ⊗[R] MvPolynomial σ R) :
    LinearMap.mul' R _ (tensorPolynomialOperator R a b x) =
      polynomialOperator R a b (LinearMap.mul' R _ x) := by
  have : LinearMap.mul' R _ ∘ₗ tensorPolynomialOperator R a b =
      (polynomialOperator R a b).toLinearMap ∘ₗ LinearMap.mul' R (MvPolynomial σ R) :=
    TensorProduct.ext' fun p q ↦ by simp [Derivation.leibniz]; ring
  exact congr($this x)

end CommSemiring

section CommRing

variable (R : Type*) [CommRing R] {σ : Type*}

/-! ### The commutation relations of `gl_σ` -/

/-- **The `gl_σ` relations.** The operators `X_a ∂_b` commute like the elementary matrices:
`⁅X_a ∂_b, X_c ∂_d⁆ = δ_bc X_a ∂_d - δ_da X_c ∂_b`. -/
theorem lie_polynomialOperator [DecidableEq σ] (a b c d : σ) :
    ⁅polynomialOperator R a b, polynomialOperator R c d⁆ =
      (if b = c then polynomialOperator R a d else 0) -
        if d = a then polynomialOperator R c b else 0 := by
  refine derivation_ext fun e ↦ ?_
  rw [Derivation.commutator_apply, sub_apply]
  by_cases hed : e = d <;> by_cases heb : e = b <;> by_cases hbc : b = c <;>
    by_cases hda : d = a <;> simp_all [polynomialOperator_X, eq_comm]

/-! ### The `sl₂`-triple in two variables -/

/-- **The polynomial `sl₂`-triple.** For distinct variables `x = X a` and `y = X b`, the
operators `H = x ∂_x - y ∂_y`, `E = x ∂_y` and `F = y ∂_x` form an `sl₂`-triple. -/
theorem isSl2Triple_polynomialOperator [Nontrivial R] {a b : σ} (hab : a ≠ b) :
    IsSl2Triple (polynomialOperator R a a - polynomialOperator R b b)
      (polynomialOperator R a b) (polynomialOperator R b a) := by
  classical
  exact {
    h_ne_zero h := by simpa [hab] using congr($h (X a : MvPolynomial σ R))
    lie_e_f := by simp [lie_polynomialOperator]
    lie_h_e_nsmul := by simp [lie_polynomialOperator, hab.symm, two_smul]
    lie_h_f_nsmul := by simp [lie_polynomialOperator, hab, two_smul, sub_eq_add_neg] }

/-- For distinct variables `x = X a` and `y = X b`, `x ∂_x - y ∂_y` acts on `x ^ i y ^ j` by the
weight `i - j`. -/
theorem polynomialOperator_self_sub_polynomialOperator_self_X_pow_mul_X_pow {a b : σ}
    (hab : a ≠ b) (i j : ℕ) :
    (polynomialOperator R a a - polynomialOperator R b b) (X a ^ i * X b ^ j) =
      ((i : R) - j) • (X a ^ i * X b ^ j) := by
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [Derivation.leibniz_pow, Algebra.smul_def, hab, hab.symm] <;> ring

/-! ### The action on a tensor product -/

/-- The action of `X_a ∂_b` on `R[X_σ] ⊗ R[X_σ]` is that of the tensor product of Lie modules
over the derivations. -/
theorem tensorPolynomialOperator_eq_toEnd (a b : σ) :
    tensorPolynomialOperator R a b =
      LieModule.toEnd R (Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) _
        (polynomialOperator R a b) :=
  TensorProduct.ext' fun p q ↦ by simp [LieModule.toEnd_apply_apply]

/-- **The `gl_σ` relations on the tensor product**: the total operators commute like the
elementary matrices. -/
theorem lie_tensorPolynomialOperator [DecidableEq σ] (a b c d : σ) :
    ⁅tensorPolynomialOperator R a b, tensorPolynomialOperator R c d⁆ =
      (if b = c then tensorPolynomialOperator R a d else 0) -
        if d = a then tensorPolynomialOperator R c b else 0 := by
  simp only [tensorPolynomialOperator_eq_toEnd]
  rw [← LieHom.map_lie, lie_polynomialOperator, map_sub]
  split_ifs <;> simp only [map_zero]

end CommRing

end TauCeti
