/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space

/-!
# Matrix coefficients of weight vectors

If `m` is a vector of weight `c` in a comodule over a coalgebra, with coaction `m ↦ m ⊗ c` for a
group-like element `c`, then each matrix coefficient of `m` is the scalar multiple `φ(m) • c`.
Conversely, when the underlying module is projective over the base commutative semiring, linear
functionals detect the coaction, so `m` has group-like weight `c` if and only if every matrix
coefficient of `m` has that scalar-multiple form.

## Main declarations

* `GroupLike.matrixCoefficient_of_mem_weightSpace`: matrix coefficients of a weight vector.
* `GroupLike.mem_weightSpace_iff_forall_matrixCoefficient`: projective converse characterizing
  weight vectors by their matrix coefficients.
-/

public section

open TauCeti.Comodule

namespace GroupLike

variable {R C M : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [TauCeti.Comodule R C M]

/-- A matrix coefficient of a weight vector `m` of weight `c` is the multiple `φ(m) c` of `c`. -/
theorem matrixCoefficient_of_mem_weightSpace {c : GroupLike R C} {m : M}
    (hc : m ∈ GroupLike.weightSpace (M := M) c) (φ : Module.Dual R M) :
    matrixCoefficient (C := C) φ m = φ m • c.val :=
  matrixCoefficient_of_coact_eq_tmul (GroupLike.mem_weightSpace.mp hc) φ

/-- In a projective comodule over a commutative semiring, a vector has group-like weight `c` if and
only if each of its matrix coefficients is the corresponding scalar multiple of `c`. -/
theorem mem_weightSpace_iff_forall_matrixCoefficient [Module.Projective R M] {c : GroupLike R C}
    {m : M} :
    m ∈ GroupLike.weightSpace (M := M) c ↔
      ∀ φ : Module.Dual R M, matrixCoefficient (C := C) φ m = φ m • c.val :=
  GroupLike.mem_weightSpace.trans coact_eq_tmul_iff_forall_matrixCoefficient

end GroupLike
