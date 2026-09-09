/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.TensorProduct

/-!
# The semiring of regular-form classes

Orthogonal sum and tensor product make the isometry classes of regular finite-dimensional
quadratic forms over a field of characteristic different from two into a commutative semiring.
The essential compatibility is the isometry distributing tensor product over orthogonal product.

The rank is compatible with both operations, so it is packaged as a semiring homomorphism to the
natural numbers. This is the dimension map from which parity invariants can be obtained by
composition.

## Main results

* `TauCeti.instCommSemiringRegularFormClass`: the commutative semiring structure.
* `TauCeti.RegularFormClass.rankHom`: rank as a semiring homomorphism to `ℕ`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §1.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-! ### Distributivity -/

/-- Tensor product distributes over concatenation of presentations, up to isometry of the
presented forms. -/
theorem equivalent_presentedForm_tmul_append (p q r : RegularFormPresentation K) :
    (presentedForm (p.tmul (q.append r))).Equivalent
      (presentedForm ((p.tmul q).append (p.tmul r))) :=
  QuadraticMap.Equivalent.trans (equivalent_presentedForm_tmul p (q.append r)) <|
    QuadraticMap.Equivalent.trans
      (QuadraticMap.Equivalent.tmul
        (⟨QuadraticMap.IsometryEquiv.refl (presentedForm p)⟩ :
          (presentedForm p).Equivalent (presentedForm p))
        (equivalent_presentedForm_append_prod q r)) <|
      QuadraticMap.Equivalent.trans
        (⟨QuadraticForm.IsometryEquiv.tmulProd (presentedForm p) (presentedForm q)
            (presentedForm r)⟩ :
          ((presentedForm p).tmul ((presentedForm q).prod (presentedForm r))).Equivalent
            (((presentedForm p).tmul (presentedForm q)).prod
              ((presentedForm p).tmul (presentedForm r)))) <|
        QuadraticMap.Equivalent.trans
          (QuadraticMap.Equivalent.prod
            (QuadraticMap.Equivalent.symm (equivalent_presentedForm_tmul p q))
            (QuadraticMap.Equivalent.symm (equivalent_presentedForm_tmul p r)))
          (QuadraticMap.Equivalent.symm
            (equivalent_presentedForm_append_prod (p.tmul q) (p.tmul r)))

omit [Invertible (2 : K)] in
/-- Tensoring a presentation with the empty presentation gives the empty class. -/
private lemma mk_tmul_zero (p : RegularFormPresentation K) :
    Quotient.mk (regularFormSetoid K) (p.tmul ⟨0, Fin.elim0⟩) =
      (0 : RegularFormClass K) := by
  rw [RegularFormClass.zero_def]
  let indexEquiv : Fin (p.tmul ⟨0, Fin.elim0⟩).1 ≃ Fin 0 := finCongr (by simp)
  let _ : IsEmpty (Fin (p.tmul ⟨0, Fin.elim0⟩).1) := Function.isEmpty indexEquiv
  apply RegularFormClass.mk_eq_mk_iff.mpr
  exact ⟨{
    toLinearEquiv := LinearEquiv.funCongrLeft K K indexEquiv.symm
    map_app' := fun x ↦ by
      calc
        presentedForm ⟨0, Fin.elim0⟩
            (LinearEquiv.funCongrLeft K K indexEquiv.symm x) = 0 := by
          rw [presentedForm_apply]
          simp
        _ = presentedForm (p.tmul ⟨0, Fin.elim0⟩) x := by
          rw [presentedForm_apply]
          simp
  }⟩

/-! ### The commutative semiring -/

/-- Tensor product distributes over orthogonal sum on regular-form classes. -/
theorem RegularFormClass.mul_add (x y z : RegularFormClass K) :
    x * (y + z) = x * y + x * z := by
  refine Quotient.inductionOn₃ x y z fun p q r ↦ ?_
  rw [RegularFormClass.mk_add_mk, RegularFormClass.mk_mul_mk,
    RegularFormClass.mk_mul_mk, RegularFormClass.mk_mul_mk,
    RegularFormClass.mk_add_mk]
  exact RegularFormClass.mk_eq_mk_iff.mpr (equivalent_presentedForm_tmul_append p q r)

/-- Tensoring a regular-form class with the zero class gives the zero class. -/
theorem RegularFormClass.mul_zero (x : RegularFormClass K) : x * 0 = 0 := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.zero_def, RegularFormClass.mk_mul_mk]
  exact mk_tmul_zero p

/-- Orthogonal sum and tensor product make regular-form classes a commutative semiring. -/
instance instCommSemiringRegularFormClass : CommSemiring (RegularFormClass K) where
  left_distrib := RegularFormClass.mul_add
  right_distrib x y z := by
    rw [mul_comm (x + y), RegularFormClass.mul_add, mul_comm z x, mul_comm z y]
  zero_mul x := by rw [mul_comm, RegularFormClass.mul_zero]
  mul_zero := RegularFormClass.mul_zero

/-! ### Rank -/

/-- The rank of a regular-form class, as a semiring homomorphism. Orthogonal sum adds ranks and
tensor product multiplies them. -/
def RegularFormClass.rankHom : RegularFormClass K →+* ℕ where
  toFun := RegularFormClass.rank
  map_zero' := RegularFormClass.rank_zero
  map_one' := RegularFormClass.rank_one
  map_add' := RegularFormClass.rank_add
  map_mul' := RegularFormClass.rank_mul

/-- Applying the rank homomorphism computes the rank. -/
@[simp]
theorem RegularFormClass.rankHom_apply (x : RegularFormClass K) :
    RegularFormClass.rankHom x = x.rank := (rfl)

end TauCeti
