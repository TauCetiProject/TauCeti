/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# Elements of a symmetric algebra are determined by their evaluations

Let `M` be a free module over an infinite integral domain `R`. Every linear form `f : M → R`
extends to the evaluation `SymmetricAlgebra.lift f : S(M) →ₐ[R] R`, and an element of `S(M)` is a
polynomial function on the dual of `M` through these evaluations. This file shows that the function
determines the element: two elements of `S(M)` with the same value at every linear form are equal.
In a basis of `M`, `S(M)` is a polynomial algebra (`SymmetricAlgebra.equivMvPolynomial`) and the
evaluations are the evaluations of polynomials at all points, which separate polynomials over an
infinite domain (`MvPolynomial.funext`).

For a Cartan subalgebra `H` of a semisimple Lie algebra, `S(H)` is the algebra of polynomial
functions on the weights `H*`, and this is how an identity in `S(H)` is checked one weight at a
time.

## Main results

* `TauCeti.SymmetricAlgebra.eq_of_forall_lift_apply_eq`: two elements of `S(M)` on which every
  evaluation `SymmetricAlgebra.lift f` agrees are equal.
-/

public section

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
