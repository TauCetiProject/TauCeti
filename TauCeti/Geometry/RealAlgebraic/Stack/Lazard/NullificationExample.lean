/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic

/-!
# A nullified ordinary fiber with nonzero Lazard evaluation

The polynomial `x*T + x*z` vanishes as a polynomial in `T` at `x = 0`. Its Lazard evaluation
there is `T` at `(x, z) = (0, 0)`: dividing by the maximal power of `x` before specializing
retains the root at zero and its multiplicity. This example records the distinction used when
lifting over a nullified fiber.
-/

public section

open MvPolynomial Polynomial

namespace TauCeti

/-- The polynomial `x*T + x*z`, with `T` distinguished and `x,z` the base variables. -/
noncomputable def nullifiedFiberPolynomial : MvPolynomial (Fin 3) ℝ :=
  X (Fin.last 2) * X 0 + X 0 * X 1

private noncomputable def nullifiedFiberBasePolynomial :=
  optionEquivRight ℝ (Fin 2) (rename finSuccEquivLast nullifiedFiberPolynomial)

private noncomputable def nullifiedFiberBasePoint : Fin 2 → Polynomial ℝ := fun _ ↦ 0

private theorem nullifiedFiberBasePolynomial_eq :
    nullifiedFiberBasePolynomial =
      X 0 * (MvPolynomial.C Polynomial.X + X 1) := by
  simp only [nullifiedFiberBasePolynomial, nullifiedFiberPolynomial, map_add, map_mul,
    rename_X]
  rw [finSuccEquivLast_last, show (0 : Fin 3) = Fin.castSucc (0 : Fin 2) by rfl,
    finSuccEquivLast_castSucc, optionEquivRight_X_none,
    show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) by rfl,
    finSuccEquivLast_castSucc]
  simp only [optionEquivRight_X_some]
  ring

/-- At the base point `(x, z) = (0, 0)`, the ordinary fiber in `T` is zero, while its Lazard
evaluation is `T`. Thus the Lazard fiber retains one root at zero with multiplicity one. -/
theorem nullifiedFiber_lazardEval_data :
    MvPolynomial.eval (fun _ : Fin 2 ↦ (0 : Polynomial ℝ))
        (optionEquivRight ℝ (Fin 2)
          (rename finSuccEquivLast nullifiedFiberPolynomial)) = 0 ∧
      (optionEquivRight ℝ (Fin 2)
        (rename finSuccEquivLast nullifiedFiberPolynomial)).lazardEval
          (fun _ ↦ (0 : Polynomial ℝ)) = Polynomial.X ∧
      Polynomial.X.IsRoot (0 : ℝ) ∧ Polynomial.X.rootMultiplicity (0 : ℝ) = 1 := by
  change MvPolynomial.eval nullifiedFiberBasePoint nullifiedFiberBasePolynomial = 0 ∧
    nullifiedFiberBasePolynomial.lazardEval nullifiedFiberBasePoint = Polynomial.X ∧
    Polynomial.X.IsRoot (0 : ℝ) ∧ Polynomial.X.rootMultiplicity (0 : ℝ) = 1
  have hfactor := nullifiedFiberBasePolynomial_eq
  constructor
  · rw [hfactor]
    simp [nullifiedFiberBasePoint]
  constructor
  · rw [hfactor, lazardEval_mul]
    have hx : (X 0 : MvPolynomial (Fin 2) (Polynomial ℝ)).lazardEval
        nullifiedFiberBasePoint = 1 := by
      simpa [nullifiedFiberBasePoint] using
        (MvPolynomial.lazardEval_X_sub_C nullifiedFiberBasePoint (0 : Fin 2))
    have hsum' : (MvPolynomial.C Polynomial.X + X 1 :
        MvPolynomial (Fin 2) (Polynomial ℝ)).lazardEval nullifiedFiberBasePoint =
          Polynomial.X := by
      rw [MvPolynomial.lazardEval_eq_eval]
      · simp [nullifiedFiberBasePoint]
      · simp [nullifiedFiberBasePoint]
    rw [hx]
    rw [hsum']
    simp
  constructor
  · simp
  · simpa using (Polynomial.rootMultiplicity_X_sub_C_self (R := ℝ) (x := (0 : ℝ)))

end TauCeti
