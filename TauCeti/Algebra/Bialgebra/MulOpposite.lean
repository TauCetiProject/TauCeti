/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.TensorProduct.Opposite
public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.MulOpposite

/-!
# Opposite bialgebras

For an `R`-bialgebra `A`, the multiplicative opposite `Aᵐᵒᵖ` (equipped with Mathlib's coalgebra
structure from `Mathlib.RingTheory.Coalgebra.MulOpposite`) is again an `R`-bialgebra
(`MulOpposite.instBialgebra`).
-/

@[expose] public section

open scoped TensorProduct

namespace MulOpposite

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

noncomputable instance instBialgebra : Bialgebra R Aᵐᵒᵖ :=
  Bialgebra.mk' R Aᵐᵒᵖ
    (by simp [counit_def])
    (fun {a b} ↦ by
      induction a using MulOpposite.rec' with | h a =>
      induction b using MulOpposite.rec' with | h b =>
      simp [counit_def, mul_comm])
    (by simp [comul_def, Algebra.TensorProduct.one_def])
    (fun {a b} ↦ by
      induction a using MulOpposite.rec' with | h a =>
      induction b using MulOpposite.rec' with | h b =>
      let f := (Algebra.TensorProduct.opAlgEquiv R R A A).symm
      have hf (z : A ⊗[R] A) :
          TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap z =
            f (op z) := by
        induction z using TensorProduct.inductionOn with
        | add u v hu hv => simp only [map_add, op_add, hu, hv]
        | tmul x y => simp [f]
      simp only [← op_mul, comul_op, Bialgebra.comul_mul, hf]
      rw [op_mul, map_mul])

end MulOpposite
