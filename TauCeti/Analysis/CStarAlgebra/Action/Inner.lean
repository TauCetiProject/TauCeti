/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import TauCeti.Analysis.CStarAlgebra.Action.Analytic
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Inner dynamics of a self-adjoint element

Let `h` be a self-adjoint element of a unital C⋆-algebra `A`. The unitaries `exp (ith)` define a
point-norm continuous real action `τ_t a = exp (ith) a exp (-ith)` on `A`,
`TauCeti.CStarAction.ofSelfAdjoint`, with `TauCeti.CStarAction.ofSelfAdjoint_apply`. These are
the inner dynamics of quantum mechanics with bounded Hamiltonian `h`.

Every element is entire analytic for this action,
`TauCeti.CStarAction.isEntireAnalytic_ofSelfAdjoint`, with complex-time extension
`τ_z a = exp (izh) a exp (-izh)`, `TauCeti.CStarAction.entireExtension_ofSelfAdjoint`.
-/

public section

noncomputable section

open Complex NormedSpace selfAdjoint

namespace TauCeti.CStarAction

variable {A : Type*} [CStarAlgebra A]

/-- The adjoint of `exp (ib)` is `exp (-ib)`. -/
private theorem star_expUnitary (b : selfAdjoint A) : star (expUnitary b) = expUnitary (-b) := by
  rw [Unitary.star_eq_inv, inv_eq_of_mul_eq_one_right]
  rw [← Commute.expUnitary_add (Commute.refl (b : A)).neg_right, add_neg_cancel, expUnitary_zero]

/-- The inner dynamics `τ_t a = exp (ith) a exp (-ith)` of a self-adjoint element `h`. -/
def ofSelfAdjoint (h : selfAdjoint A) : CStarAction (Multiplicative ℝ) A where
  toMonoidHom :=
    { toFun t := Unitary.conjStarAlgAut ℂ A (expUnitary (t.toAdd • h))
      map_one' := by simp
      map_mul' s t := by
        rw [toAdd_mul, add_smul,
          Commute.expUnitary_add (((Commute.refl (h : A)).smul_left _).smul_right _), map_mul] }
  continuous_orbit a := by
    have hu : Continuous fun t : Multiplicative ℝ => (expUnitary (t.toAdd • h) : A) :=
      continuous_subtype_val.comp (continuous_expUnitary.comp (by fun_prop))
    exact (hu.mul continuous_const).mul hu.star

private theorem ofSelfAdjoint_eq (h : selfAdjoint A) (t : Multiplicative ℝ) :
    ofSelfAdjoint h t = Unitary.conjStarAlgAut ℂ A (expUnitary (t.toAdd • h)) :=
  (rfl)

/-- The inner dynamics of a self-adjoint element `h` is `τ_t a = exp (ith) a exp (-ith)`. -/
@[simp]
theorem ofSelfAdjoint_apply (h : selfAdjoint A) (t : Multiplicative ℝ) (a : A) :
    ofSelfAdjoint h t a = exp ((I * t.toAdd) • (h : A)) * a * exp (-(I * t.toAdd) • (h : A)) := by
  rw [ofSelfAdjoint_eq, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, star_expUnitary,
    expUnitary_coe, expUnitary_coe, NegMemClass.coe_neg, val_smul, smul_neg, ← Complex.coe_smul,
    smul_smul, neg_smul]

/-- `z ↦ exp (izh) a exp (-izh)` is entire. -/
private theorem differentiable_exp_mul_mul_exp (h a : A) :
    Differentiable ℂ fun z : ℂ => exp ((I * z) • h) * a * exp (-(I * z) • h) := by
  have hd : Differentiable ℂ fun z : ℂ => exp (z • h) :=
    fun z => (hasDerivAt_exp_smul_const h z).differentiableAt
  exact ((hd.comp (differentiable_id.const_mul I)).mul (differentiable_const a)).mul
    (hd.comp (differentiable_id.const_mul I).neg)

/-- The complex-time extension of the inner dynamics of a self-adjoint element `h` is
`τ_z a = exp (izh) a exp (-izh)`. -/
@[simp]
theorem entireExtension_ofSelfAdjoint (h : selfAdjoint A) (a : A) :
    (ofSelfAdjoint h).entireExtension a =
      fun z => exp ((I * z) • (h : A)) * a * exp (-(I * z) • (h : A)) :=
  entireExtension_eq_of_differentiable (differentiable_exp_mul_mul_exp _ a) fun t => by simp

/-- Every element is entire analytic for the inner dynamics of a self-adjoint element. -/
theorem isEntireAnalytic_ofSelfAdjoint (h : selfAdjoint A) (a : A) :
    (ofSelfAdjoint h).IsEntireAnalytic a := by
  rw [isEntireAnalytic_iff, entireExtension_ofSelfAdjoint]
  exact ⟨differentiable_exp_mul_mul_exp _ a, fun t => by simp⟩

end TauCeti.CStarAction
