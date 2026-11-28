/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.MeasureTheory.Function.BoundedBorel.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential of a bounded Borel symbol

Pointwise evaluation `BoundedBorelFunction.evalStarAlgHom x : BoundedBorelFunction X →⋆ₐ[ℂ] ℂ` is a
continuous unital star algebra homomorphism for the supremum norm. By `NormedSpace.map_exp`, the
Banach-algebra exponential `NormedSpace.exp f` of a bounded Borel symbol `f` evaluates pointwise as
the scalar complex exponential (`BoundedBorelFunction.exp_apply`, `BoundedBorelFunction.coe_exp`).
-/

public section

noncomputable section

namespace TauCeti.BoundedBorelFunction

variable {X : Type*} [MeasurableSpace X]

/-- The Banach-algebra exponential of a bounded Borel symbol evaluates pointwise as `Complex.exp`.
-/
@[simp]
theorem exp_apply (f : BoundedBorelFunction X) (x : X) :
    NormedSpace.exp f x = Complex.exp (f x) := by
  let +nondep : NormedAlgebra ℚ (BoundedBorelFunction X) := .restrictScalars ℚ ℂ _
  have hcont : Continuous (evalStarAlgHom x) :=
    (continuous_eval x).congr fun g ↦ (evalStarAlgHom_apply x g).symm
  rw [← evalStarAlgHom_apply, NormedSpace.map_exp (evalStarAlgHom x) hcont f,
    evalStarAlgHom_apply, Complex.exp_eq_exp_ℂ]

/-- Function coercion turns `NormedSpace.exp` on bounded Borel symbols into composition with
`Complex.exp`. -/
theorem coe_exp (f : BoundedBorelFunction X) :
    ⇑(NormedSpace.exp f) = Complex.exp ∘ ⇑f :=
  funext (exp_apply f)

end TauCeti.BoundedBorelFunction
