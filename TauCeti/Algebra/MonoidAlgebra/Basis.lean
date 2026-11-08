/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The coordinates of the standard basis of a monoid algebra

Mathlib defines the standard basis `MonoidAlgebra.basis X k` of `k[X]` by
`repr := MonoidAlgebra.coeffLinearEquiv _` but records no lemma for the resulting `repr`. This
file is that missing bridge: the coordinates in the standard basis are the coefficients.

It is all that is needed for the generic basis API -- `Module.Basis.coe_sumCoords`,
`Module.Basis.sumCoords_self_apply`, `LinearMap.toMatrix_apply` -- to compute in terms of
`MonoidAlgebra.coeff`.

## Main statements

* `MonoidAlgebra.basis_repr`: the coordinates of `k[X]` in the standard basis are the
  coefficients.
* `Module.Dual.coeff_basis_toDualEquiv_symm_apply`: the coefficients under the
  standard-basis dual equivalence are evaluations on basis vectors.
* `MonoidAlgebra.span_single_one_eq_span_single_one_iff`: distinct basis vectors `single i 1`
  over a nontrivial semiring span distinct lines.
-/

public section

/-- The coordinates of `k[X]` in the standard basis are the coefficients. -/
@[simp]
theorem MonoidAlgebra.basis_repr {k : Type*} [Semiring k] {X : Type*} (v : MonoidAlgebra k X) :
    (MonoidAlgebra.basis X k).repr v = v.coeff :=
  rfl

/-- The coefficients of the vector corresponding to a functional under the standard-basis
identification `k[X] ≃ Hom_k(k[X], k)` are the values of the functional on the basis. -/
@[simp]
theorem Module.Dual.coeff_basis_toDualEquiv_symm_apply {k : Type*} [CommSemiring k]
    {X : Type*} [Finite X] [DecidableEq X] (f : Module.Dual k (MonoidAlgebra k X)) (x : X) :
    ((MonoidAlgebra.basis X k).toDualEquiv.symm f).coeff x =
      f (MonoidAlgebra.single x 1) := by
  simpa using (MonoidAlgebra.basis X k).coord_toDualEquiv_symm_apply x f

/-- Over a nontrivial semiring, the basis vectors `single i 1` and `single j 1` of a monoid
algebra span the same line exactly when `i = j`. -/
@[simp]
theorem MonoidAlgebra.span_single_one_eq_span_single_one_iff {R : Type*} [Semiring R]
    [Nontrivial R] {ι : Type*} {i j : ι} :
    R ∙ MonoidAlgebra.single i (1 : R) = R ∙ MonoidAlgebra.single j (1 : R) ↔ i = j := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hi := h.le (Submodule.mem_span_singleton_self (MonoidAlgebra.single i (1 : R)))
  simpa using (MonoidAlgebra.single_mem_span_single (s := {j})).mp (by simpa using hi)
