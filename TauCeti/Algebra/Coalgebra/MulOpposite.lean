/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.MulOpposite

/-!
# Coalgebra lemmas for multiplicative opposites

For an `R`-coalgebra `A` equipped with Mathlib's coalgebra structure on `Aᵐᵒᵖ`
(`Mathlib.RingTheory.Coalgebra.MulOpposite`), this file records `@[simp]` evaluation lemmas for
`Coalgebra.comul` and `Coalgebra.counit` on `MulOpposite.op`, the comultiplication transport
`MulOpposite.comul_opLinearEquiv_symm`, the cocommutativity instance `MulOpposite.instIsCocomm`, and
`Coalgebra.Repr.op` for mapping finite coproduct representations into `Aᵐᵒᵖ`.
-/

public section

open scoped TensorProduct

namespace MulOpposite

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

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

/-- Comultiplication commutes with `(MulOpposite.opLinearEquiv R).symm`. -/
theorem comul_opLinearEquiv_symm [CoalgebraStruct R A] (x : Aᵐᵒᵖ) :
    Coalgebra.comul (R := R) ((opLinearEquiv R).symm x) =
      TensorProduct.map (opLinearEquiv R).symm.toLinearMap
        (opLinearEquiv R).symm.toLinearMap (Coalgebra.comul (R := R) x) := by
  induction x using MulOpposite.rec' with | h a =>
  simp only [coe_opLinearEquiv_symm, unop_op, comul_op]
  generalize Coalgebra.comul (R := R) a = w
  induction w using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [map_add]
    rw [← hu, ← hv]
  | tmul b c =>
    simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

instance instIsCocomm [Coalgebra R A] [Coalgebra.IsCocomm R A] :
    Coalgebra.IsCocomm R Aᵐᵒᵖ where
  comm_comp_comul := by
    ext x
    induction x using MulOpposite.rec' with | h x =>
    simp [comul_op, ← TensorProduct.map_comm, Coalgebra.comm_comul]

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
theorem op_index {a : A} (r : Coalgebra.Repr R a ι) : r.op.index = r.index := by
  rfl

@[simp]
theorem op_left {a : A} (r : Coalgebra.Repr R a ι) (i : ι) :
    r.op.left i = MulOpposite.op (r.left i) := by
  rfl

@[simp]
theorem op_right {a : A} (r : Coalgebra.Repr R a ι) (i : ι) :
    r.op.right i = MulOpposite.op (r.right i) := by
  rfl

end Coalgebra.Repr
