/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import TauCeti.Algebra.BrauerGroup.Group

/-!
# Brauer classes of Clifford algebras

A central simple algebra isomorphic to a Clifford algebra has a self-inverse Brauer class:
Mathlib's `CliffordAlgebra.reverseOpEquiv` identifies the Clifford algebra with its opposite.
This gives the even-rank case of two-torsion for the Clifford invariant.

## Main results

* `TauCeti.BrauerGroup.inv_mk_eq_mk_of_algEquiv_cliffordAlgebra`: a central simple algebra
  isomorphic to a Clifford algebra has a self-inverse Brauer class.
-/

public section

namespace TauCeti

universe u

/-- **A central simple algebra isomorphic to a Clifford algebra has a self-inverse Brauer class**:
the reversion identifies a Clifford algebra with its opposite algebra. No hypothesis on the form
is needed beyond the central simplicity carried by `A`. -/
theorem BrauerGroup.inv_mk_eq_mk_of_algEquiv_cliffordAlgebra {K : Type u} [Field K]
    {W : Type*} [AddCommGroup W] [Module K W] {P : QuadraticForm K W} (A : CSA.{u, u} K)
    (e : CliffordAlgebra P ≃ₐ[K] A) : (BrauerGroup.mk A)⁻¹ = BrauerGroup.mk A :=
  BrauerGroup.inv_mk_eq_mk_of_algEquiv_op
    (e.symm.trans (CliffordAlgebra.reverseOpEquiv.trans (AlgEquiv.op e)))

end TauCeti
