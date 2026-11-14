/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Matrix coefficients of weight vectors

If `m` is a vector in a comodule over a coalgebra with coaction `m ↦ m ⊗ x`, then each matrix
coefficient of `m` is the scalar multiple `φ(m) • x`. Conversely, when the underlying module is
projective over the base commutative semiring, linear functionals detect the coaction, so
`coact m = m ⊗ x` (and in particular `m` has group-like weight `c` when `x = c`) if and only if
every matrix coefficient of `m` has that scalar-multiple form.

## Main declarations

* `TauCeti.Comodule.coact_eq_tmul_iff_forall_matrixCoefficient`: projective characterization of
  pure-tensor coactions `coact m = m ⊗ x` via matrix coefficients.
* `GroupLike.matrixCoefficient_of_mem_weightSpace`: matrix coefficients of a weight vector.
* `GroupLike.mem_weightSpace_iff_forall_matrixCoefficient`: projective converse characterizing
  weight vectors by their matrix coefficients.
-/

public section

open scoped TensorProduct
open TauCeti.Comodule

namespace TauCeti.Comodule

/-- In a projective comodule over a commutative semiring, the coaction of `m` equals `m ⊗ x` if and
only if each matrix coefficient of `m` is the corresponding scalar multiple of `x`. -/
theorem coact_eq_tmul_iff_forall_matrixCoefficient {R C M : Type*} [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M]
    [TauCeti.Comodule R C M] [Module.Projective R M] {m : M} {x : C} :
    coact (R := R) (C := C) m = m ⊗ₜ[R] x ↔
      ∀ φ : Module.Dual R M, matrixCoefficient (C := C) φ m = φ m • x := by
  constructor
  · intro hm φ
    rw [matrixCoefficient_def, hm]
    simp
  · intro h
    have hcontract (φ : Module.Dual R M) (z : M ⊗[R] C) :
        LinearMap.tensorComponent φ (TensorProduct.comm R M C z) =
          TensorProduct.lid R C (TensorProduct.map φ LinearMap.id z) := by
      induction z using TensorProduct.inductionOn with
      | tmul v a => simp
      | add y w hy hw => simp [hy, hw]
    apply (TensorProduct.comm R M C).injective
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro φ
    rw [hcontract, ← matrixCoefficient_def, h φ, TensorProduct.comm_tmul,
      LinearMap.tensorComponent_tmul]

end TauCeti.Comodule

namespace GroupLike

variable {R C M : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [TauCeti.Comodule R C M]

/-- A matrix coefficient of a weight vector `m` of weight `c` is the multiple `φ(m) c` of `c`. -/
theorem matrixCoefficient_of_mem_weightSpace {c : GroupLike R C} {m : M}
    (hc : m ∈ GroupLike.weightSpace (M := M) c) (φ : Module.Dual R M) :
    matrixCoefficient (C := C) φ m = φ m • c.val := by
  rw [matrixCoefficient_def, GroupLike.mem_weightSpace.mp hc]
  simp

/-- In a projective comodule over a commutative semiring, a vector has group-like weight `c` if and
only if each of its matrix coefficients is the corresponding scalar multiple of `c`. -/
theorem mem_weightSpace_iff_forall_matrixCoefficient [Module.Projective R M] {c : GroupLike R C}
    {m : M} :
    m ∈ GroupLike.weightSpace (M := M) c ↔
      ∀ φ : Module.Dual R M, matrixCoefficient (C := C) φ m = φ m • c.val :=
  GroupLike.mem_weightSpace.trans coact_eq_tmul_iff_forall_matrixCoefficient

end GroupLike
