/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# Evaluations of elements of a symmetric algebra

Let `M` be a free module over an infinite integral domain `R`. Every linear form `f : M → R`
extends to the evaluation `SymmetricAlgebra.lift f : S(M) →ₐ[R] R`, and an element of `S(M)` is a
polynomial function on the dual of `M` through these evaluations. This file shows that the function
determines the element: two elements of `S(M)` with the same value at every linear form are equal.
In a basis of `M`, `S(M)` is a polynomial algebra (`SymmetricAlgebra.equivMvPolynomial`) and the
evaluations are the evaluations of polynomials at all points, which separate polynomials over an
infinite domain (`MvPolynomial.funext`).

The function is polynomial in the usual sense along every affine line of linear forms, over any
commutative ring and without freeness: for `p : S(M)` and linear forms `f`, `g`, the values
`SymmetricAlgebra.lift (f + t • g) p` are the values at `t` of one polynomial in `R[X]`, namely the
image of `p` under the evaluation at the `R[X]`-valued linear form `f + X • g`. Over a domain, this
is how an identity between two such functions known at infinitely many points of a line is
extended to the whole line.

For a Cartan subalgebra `H` of a semisimple Lie algebra, `S(H)` is the algebra of polynomial
functions on the weights `H*`, and this is how an identity in `S(H)` is checked one weight at a
time.

## Main results

* `SymmetricAlgebra.exists_polynomial_eval_eq_lift_add_smul`: along an affine line of
  linear forms, the evaluations of an element of `S(M)` are the values of a polynomial.
* `TauCeti.SymmetricAlgebra.eq_of_forall_lift_apply_eq`: two elements of `S(M)` on which every
  evaluation `SymmetricAlgebra.lift f` agrees are equal.
-/

public section

namespace SymmetricAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **An element of the symmetric algebra is a polynomial function along every affine line** of
linear forms: for `p : S(M)` and linear forms `f`, `g` there is a polynomial `q` with
`q.eval t = SymmetricAlgebra.lift (f + t • g) p` for every `t : R`. -/
theorem exists_polynomial_eval_eq_lift_add_smul (p : SymmetricAlgebra R M) (f g : M →ₗ[R] R) :
    ∃ q : Polynomial R, ∀ t : R, q.eval t = SymmetricAlgebra.lift (f + t • g) p := by
  -- the evaluation at the `R[X]`-valued linear form `f + X • g`, followed by `X ↦ t`
  let φ : M →ₗ[R] Polynomial R := Polynomial.monomial 0 ∘ₗ f + Polynomial.monomial 1 ∘ₗ g
  refine ⟨SymmetricAlgebra.lift φ p, fun t ↦ ?_⟩
  have hcomp : (Polynomial.aeval t).comp (SymmetricAlgebra.lift φ) =
      SymmetricAlgebra.lift (f + t • g) := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_ofClass, AlgHom.coe_comp,
      SymmetricAlgebra.lift_ι_apply]
    simp only [φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_add,
      Polynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]
    ring
  rw [← Polynomial.coe_aeval_eq_eval, ← hcomp, AlgHom.comp_apply]

end SymmetricAlgebra

namespace TauCeti.SymmetricAlgebra

variable {R M : Type*} [CommRing R] [IsDomain R] [Infinite R] [AddCommGroup M] [Module R M]
  [Module.Free R M]

/-- **An element of the symmetric algebra of a free module over an infinite domain is determined by
its values at all linear forms**: if `SymmetricAlgebra.lift f p = SymmetricAlgebra.lift f q` for
every `f : Module.Dual R M`, then `p = q`. -/
theorem eq_of_forall_lift_apply_eq {p q : SymmetricAlgebra R M}
    (h : ∀ f : Module.Dual R M, SymmetricAlgebra.lift f p = SymmetricAlgebra.lift f q) :
    p = q := by
  let b := Module.Free.chooseBasis R M
  let e := SymmetricAlgebra.equivMvPolynomial b
  -- through `e`, the evaluation at the linear form `b.constr R x` is evaluation at the point `x`
  have heval (x : Module.Free.ChooseBasisIndex R M → R) (s : SymmetricAlgebra R M) :
      SymmetricAlgebra.lift (b.constr R x) s = MvPolynomial.eval x (e s) := by
    rw [← e.symm_apply_apply s]
    generalize e s = P
    have hcomp : (SymmetricAlgebra.lift (b.constr R x)).comp
        (e.symm : MvPolynomial (Module.Free.ChooseBasisIndex R M) R →ₐ[R] SymmetricAlgebra R M) =
          MvPolynomial.aeval x :=
      MvPolynomial.algHom_ext fun i ↦ by simp [e, b.constr_basis]
    rw [e.apply_symm_apply, ← MvPolynomial.coe_aeval_eq_eval, ← hcomp]
    simp
  apply e.injective
  exact MvPolynomial.funext fun x ↦ by rw [← heval, ← heval, h]

end TauCeti.SymmetricAlgebra
