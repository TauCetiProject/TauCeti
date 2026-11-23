/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.MulOpposite

/-!
# Opposite bialgebras

For an `R`-bialgebra `A`, the multiplicative opposite `Aᵐᵒᵖ` (equipped with Mathlib's coalgebra
structure from `Mathlib.RingTheory.Coalgebra.MulOpposite`) is again an `R`-bialgebra
(`MulOpposite.instBialgebra`).

We also record `@[simp]` evaluation lemmas for `Coalgebra.comul` and `Coalgebra.counit` on
`MulOpposite.op` and `Coalgebra.Repr.op` for opposite coproduct representations.
-/

@[expose] public section

open scoped TensorProduct

namespace MulOpposite

variable {R A : Type*} [CommSemiring R]

section Coalgebra

variable [AddCommMonoid A] [Module R A]

@[simp]
theorem comul_op [CoalgebraStruct R A] (a : A) :
    Coalgebra.comul (R := R) (op a) =
      TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap
        (Coalgebra.comul (R := R) a) :=
  rfl

@[simp]
theorem counit_op [CoalgebraStruct R A] (a : A) :
    Coalgebra.counit (R := R) (op a) = Coalgebra.counit (R := R) a :=
  rfl

theorem counit_apply [CoalgebraStruct R A] (x : Aᵐᵒᵖ) :
    Coalgebra.counit (R := R) x = Coalgebra.counit (R := R) x.unop :=
  rfl

instance instIsCocomm [Coalgebra R A] [Coalgebra.IsCocomm R A] :
    Coalgebra.IsCocomm R Aᵐᵒᵖ where
  comm_comp_comul := by
    ext x
    induction x using MulOpposite.rec' with | h x =>
    simp [comul_op, ← TensorProduct.map_comm, Coalgebra.comm_comul]

end Coalgebra

section Bialgebra

variable [Semiring A] [Bialgebra R A]

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
      have hmul (u v : A ⊗[R] A) :
          TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap (u * v) =
            TensorProduct.map (opLinearEquiv R).toLinearMap
                (opLinearEquiv R).toLinearMap v *
              TensorProduct.map (opLinearEquiv R).toLinearMap
                (opLinearEquiv R).toLinearMap u := by
        induction u using TensorProduct.inductionOn with
        | add u₁ u₂ h₁ h₂ => simp [add_mul, mul_add, h₁, h₂]
        | tmul u₁ u₂ =>
          induction v using TensorProduct.inductionOn with
          | add v₁ v₂ h₁ h₂ => simp [mul_add, add_mul, h₁, h₂]
          | tmul v₁ v₂ => simp
      simp only [← op_mul, comul_op, Bialgebra.comul_mul]
      exact hmul _ _)

end Bialgebra

end MulOpposite

namespace Coalgebra.Repr

variable {R A ι : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]

/-- Maps both legs of a finite coproduct representation to the multiplicative opposite `Aᵐᵒᵖ`. -/
def op {a : A} (r : Coalgebra.Repr R a ι) : Coalgebra.Repr R (MulOpposite.op a) ι where
  index := r.index
  left i := MulOpposite.op (r.left i)
  right i := MulOpposite.op (r.right i)
  eq := by
    have h := congrArg (TensorProduct.map (MulOpposite.opLinearEquiv R).toLinearMap
      (MulOpposite.opLinearEquiv R).toLinearMap) r.eq
    simpa [map_sum] using h

@[simp]
theorem op_index {a : A} (r : Coalgebra.Repr R a ι) : r.op.index = r.index :=
  rfl

@[simp]
theorem op_left {a : A} (r : Coalgebra.Repr R a ι) (i : ι) :
    r.op.left i = MulOpposite.op (r.left i) :=
  rfl

@[simp]
theorem op_right {a : A} (r : Coalgebra.Repr R a ι) (i : ι) :
    r.op.right i = MulOpposite.op (r.right i) :=
  rfl

end Coalgebra.Repr
