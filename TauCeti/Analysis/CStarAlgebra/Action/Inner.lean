/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import TauCeti.Analysis.CStarAlgebra.Action.Analytic
public import TauCeti.Analysis.CStarAlgebra.Exponential
import TauCeti.Analysis.SpecialFunctions.Exponential

/-!
# Inner dynamics of a self-adjoint element

Let `h` be a self-adjoint element of a unital C⋆-algebra `A`. The unitaries `exp (ith)` define a
point-norm continuous real action `τ_t a = exp (ith) a exp (-ith)` on `A`,
`selfAdjoint.cstarAction`, with `selfAdjoint.cstarAction_apply`. These are the inner dynamics of
quantum mechanics with bounded Hamiltonian `h`.

Every element is entire analytic for this action, `selfAdjoint.isEntireAnalytic_cstarAction`, with
complex-time extension `τ_z a = exp (izh) a exp (-izh)`,
`selfAdjoint.entireExtension_cstarAction`. At imaginary time `t * I` the dynamics is
`a ↦ exp (-t h) a exp (t h)`, `selfAdjoint.entireExtension_cstarAction_mul_I`, the evolution that
appears in the KMS condition at inverse temperature `t`.
-/

public section

noncomputable section

open Complex NormedSpace
open TauCeti CStarAction

namespace selfAdjoint

variable {A : Type*} [CStarAlgebra A]

/-- The inner dynamics `τ_t a = exp (ith) a exp (-ith)` of a self-adjoint element `h`. -/
def cstarAction (h : selfAdjoint A) : CStarAction (Multiplicative ℝ) A where
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

/-- The inner dynamics of a self-adjoint element is conjugation by `expUnitary`. -/
theorem cstarAction_eq_conjStarAlgAut (h : selfAdjoint A) (t : Multiplicative ℝ) :
    cstarAction h t = Unitary.conjStarAlgAut ℂ A (expUnitary (t.toAdd • h)) :=
  (rfl)

/-- The inner dynamics of a self-adjoint element `h` is `τ_t a = exp (ith) a exp (-ith)`. -/
@[simp]
theorem cstarAction_apply (h : selfAdjoint A) (t : Multiplicative ℝ) (a : A) :
    cstarAction h t a = exp ((I * t.toAdd) • (h : A)) * a * exp (-(I * t.toAdd) • (h : A)) := by
  rw [cstarAction_eq_conjStarAlgAut, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    star_expUnitary, ← neg_smul]
  simp only [expUnitary_coe, val_smul, ← Complex.coe_smul, ← mul_smul, ofReal_neg, mul_neg]

/-- The complex-time extension of the inner dynamics is `τ_z a = exp (izh) a exp (-izh)`. -/
@[simp]
theorem entireExtension_cstarAction (h : selfAdjoint A) (a : A) :
    (cstarAction h).entireExtension a =
      fun z => exp ((I * z) • (h : A)) * a * exp (-(I * z) • (h : A)) :=
  entireExtension_eq_of_differentiable
    (differentiable_exp_smul_mul_mul_exp_neg_smul _ a) fun t => by simp

/-- At imaginary time `t * I` the inner dynamics is `a ↦ exp (-t h) a exp (t h)`. -/
@[simp]
theorem entireExtension_cstarAction_mul_I (h : selfAdjoint A) (a : A) (t : ℝ) :
    (cstarAction h).entireExtension a (t * I) = exp (-t • (h : A)) * a * exp (t • (h : A)) := by
  rw [entireExtension_cstarAction]
  have hI : I * (t * I) = -t := by rw [mul_left_comm, I_mul_I, mul_neg_one]
  simp only [hI, neg_neg, ← Complex.coe_smul, ofReal_neg]

/-- Every element is entire analytic for the inner dynamics of a self-adjoint element. -/
theorem isEntireAnalytic_cstarAction (h : selfAdjoint A) (a : A) :
    (cstarAction h).IsEntireAnalytic a := by
  rw [isEntireAnalytic_iff, entireExtension_cstarAction]
  exact ⟨differentiable_exp_smul_mul_mul_exp_neg_smul _ a, fun t => by simp⟩

end selfAdjoint
