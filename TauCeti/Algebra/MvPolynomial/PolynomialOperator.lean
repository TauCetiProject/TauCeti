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

In two variables `x = X 0`, `y = X 1` the operators `E = x ∂_y` and `F = y ∂_x`, with
`H = ⁅E, F⁆ = x ∂_x - y ∂_y`, form an `sl₂`-triple. On `x ^ i y ^ j` the operator `E` lowers the
`y`-exponent and raises the `x`-exponent with coefficient `j`, `F` does the reverse with
coefficient `i`, and `H` acts by `i - j`. Thus on the degree-`d` homogeneous polynomials the
monomials `x ^ (d - i) y ^ i` form a weight string with weights `d - 2 i`, as in the polynomial
model of the `sl₂`-module `V(d)`.

On a tensor product of two polynomial rings, `X_a ∂_b` acts through Mathlib's tensor product of
Lie modules, by the Leibniz rule on both factors; multiplication of polynomials intertwines this
action with the action on the product.

## Main definitions

* `TauCeti.polynomialOperator R a b`: the derivation `X_a ∂_b` of `R[X_σ]`.
* `TauCeti.tensorPolynomialOperator R a b`: the action of `X_a ∂_b` on `R[X_σ] ⊗ R[X_σ]`.

## Main results

* `TauCeti.lie_polynomialOperator`: the commutation relations of `gl_σ`.
* `MvPolynomial.IsHomogeneous.polynomialOperator`: `X_a ∂_b` preserves homogeneous degree.
* `TauCeti.isSl2Triple_polynomialOperator`: `x ∂_x - y ∂_y`, `x ∂_y`, `y ∂_x` is an
  `sl₂`-triple.
* `TauCeti.polynomialOperator_zero_one_X_pow_mul_X_pow`,
  `TauCeti.polynomialOperator_one_zero_X_pow_mul_X_pow` and
  `TauCeti.polynomialOperator_sub_X_pow_mul_X_pow`: the action of `E`, `F` and `H` on monomials.
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
theorem polynomialOperator_monomial (a b : σ) (s : σ →₀ ℕ) (r : R) :
    polynomialOperator R a b (monomial s r) =
      monomial (s - Finsupp.single b 1 + Finsupp.single a 1) (r * s b) := by
  rw [polynomialOperator_apply, pderiv_monomial, X, monomial_mul_monomial, one_mul, add_comm]

/-- `X_a ∂_b` preserves homogeneous degree. -/
theorem _root_.MvPolynomial.IsHomogeneous.polynomialOperator {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (a b : σ) : (TauCeti.polynomialOperator R a b p).IsHomogeneous n := by
  rcases n with _ | n
  · obtain ⟨c, rfl⟩ : ∃ c, p = C c :=
      ⟨_, totalDegree_eq_zero_iff_eq_C.mp (le_antisymm hp.totalDegree_le (Nat.zero_le _))⟩
    simpa [polynomialOperator_apply, pderiv_C] using isHomogeneous_zero σ R 0
  · simpa [polynomialOperator_apply, add_comm] using (isHomogeneous_X R a).mul hp.pderiv

/-- `X_a ∂_b` preserves each space of homogeneous polynomials of a fixed degree. -/
theorem polynomialOperator_mem_homogeneousSubmodule {p : MvPolynomial σ R} {n : ℕ}
    (hp : p ∈ homogeneousSubmodule σ R n) (a b : σ) :
    polynomialOperator R a b p ∈ homogeneousSubmodule σ R n :=
  (mem_homogeneousSubmodule n _).mpr (((mem_homogeneousSubmodule n p).mp hp).polynomialOperator R
    a b)

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

/-- `⁅x ∂_y, y ∂_x⁆ = x ∂_x - y ∂_y`. -/
theorem lie_polynomialOperator_zero_one_one_zero :
    ⁅polynomialOperator R (0 : Fin 2) 1, polynomialOperator R (1 : Fin 2) 0⁆ =
      polynomialOperator R 0 0 - polynomialOperator R 1 1 := by
  simp [lie_polynomialOperator]

/-- **The polynomial `sl₂`-triple.** In two variables `x = X 0` and `y = X 1`, the operators
`H = x ∂_x - y ∂_y`, `E = x ∂_y` and `F = y ∂_x` form an `sl₂`-triple. -/
theorem isSl2Triple_polynomialOperator [Nontrivial R] :
    IsSl2Triple (polynomialOperator R (0 : Fin 2) 0 - polynomialOperator R (1 : Fin 2) 1)
      (polynomialOperator R (0 : Fin 2) 1) (polynomialOperator R (1 : Fin 2) 0) where
  h_ne_zero h := by
    simpa using congr($h (X 0 : MvPolynomial (Fin 2) R))
  lie_e_f := lie_polynomialOperator_zero_one_one_zero R
  lie_h_e_nsmul := by simp [lie_polynomialOperator, two_smul]
  lie_h_f_nsmul := by simp [lie_polynomialOperator, two_smul, sub_eq_add_neg]

/-- `x ∂_y (x ^ i y ^ (j + 1)) = (j + 1) x ^ (i + 1) y ^ j`. -/
theorem polynomialOperator_zero_one_X_pow_mul_X_pow (i j : ℕ) :
    polynomialOperator R (0 : Fin 2) 1 (X 0 ^ i * X 1 ^ (j + 1)) =
      ((j : R) + 1) • (X 0 ^ (i + 1) * X 1 ^ j) := by
  simp [Derivation.leibniz_pow, Algebra.smul_def]
  ring

/-- `y ∂_x (x ^ (i + 1) y ^ j) = (i + 1) x ^ i y ^ (j + 1)`. -/
theorem polynomialOperator_one_zero_X_pow_mul_X_pow (i j : ℕ) :
    polynomialOperator R (1 : Fin 2) 0 (X 0 ^ (i + 1) * X 1 ^ j) =
      ((i : R) + 1) • (X 0 ^ i * X 1 ^ (j + 1)) := by
  simp [Derivation.leibniz_pow, Algebra.smul_def]
  ring

/-- `x ∂_x - y ∂_y` acts on `x ^ i y ^ j` by the weight `i - j`. -/
theorem polynomialOperator_sub_X_pow_mul_X_pow (i j : ℕ) :
    (polynomialOperator R (0 : Fin 2) 0 - polynomialOperator R (1 : Fin 2) 1) (X 0 ^ i * X 1 ^ j) =
      ((i : R) - j) • (X 0 ^ i * X 1 ^ j) := by
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [Derivation.leibniz_pow, Algebra.smul_def] <;> ring

/-! ### The action on a tensor product -/

/-- The action of `X_a ∂_b` on `R[X_σ] ⊗ R[X_σ]`, by the tensor product of Lie modules over the
derivations: `X_a ∂_b ⊗ 1 + 1 ⊗ X_a ∂_b`. -/
noncomputable def tensorPolynomialOperator (a b : σ) :
    Module.End R (MvPolynomial σ R ⊗[R] MvPolynomial σ R) :=
  LieModule.toEnd R (Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) _
    (polynomialOperator R a b)

/-- **The Leibniz rule on pure tensors**: `X_a ∂_b` acts on `p ⊗ q` through each factor in
turn. -/
@[simp]
theorem tensorPolynomialOperator_tmul (a b : σ) (p q : MvPolynomial σ R) :
    tensorPolynomialOperator R a b (p ⊗ₜ q) =
      polynomialOperator R a b p ⊗ₜ q + p ⊗ₜ polynomialOperator R a b q := by
  simp [tensorPolynomialOperator, LieModule.toEnd_apply_apply]

/-- The action on the tensor product is `X_a ∂_b ⊗ 1 + 1 ⊗ X_a ∂_b`. -/
theorem tensorPolynomialOperator_eq (a b : σ) :
    tensorPolynomialOperator R a b =
      (polynomialOperator R a b).toLinearMap.rTensor _ +
        (polynomialOperator R a b).toLinearMap.lTensor _ :=
  TensorProduct.ext' fun p q ↦ by simp

/-- **The `gl_σ` relations on the tensor product**: the total operators commute like the
elementary matrices. -/
theorem lie_tensorPolynomialOperator [DecidableEq σ] (a b c d : σ) :
    ⁅tensorPolynomialOperator R a b, tensorPolynomialOperator R c d⁆ =
      (if b = c then tensorPolynomialOperator R a d else 0) -
        if d = a then tensorPolynomialOperator R c b else 0 := by
  rw [tensorPolynomialOperator, tensorPolynomialOperator, ← LieHom.map_lie, lie_polynomialOperator,
    map_sub]
  split_ifs <;> simp only [tensorPolynomialOperator, map_zero]

/-- Multiplication of polynomials intertwines the action of `X_a ∂_b` on the tensor product with
its action on `R[X_σ]`: this is the Leibniz rule `D (p q) = D p q + p D q`. -/
theorem mul'_tensorPolynomialOperator (a b : σ) (x : MvPolynomial σ R ⊗[R] MvPolynomial σ R) :
    LinearMap.mul' R _ (tensorPolynomialOperator R a b x) =
      polynomialOperator R a b (LinearMap.mul' R _ x) := by
  have : LinearMap.mul' R _ ∘ₗ tensorPolynomialOperator R a b =
      (polynomialOperator R a b).toLinearMap ∘ₗ LinearMap.mul' R (MvPolynomial σ R) :=
    TensorProduct.ext' fun p q ↦ by simp [Derivation.leibniz]; ring
  exact congr($this x)

end CommRing

end TauCeti
