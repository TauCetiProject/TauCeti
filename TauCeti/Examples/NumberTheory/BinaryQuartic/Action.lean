/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuartic.Action
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Examples of binary quartic changes of variables

Swapping coordinates reverses the coefficients. The two elementary shears distinguish
row-vector substitution from its transpose. Scalar substitution exhibits the determinant
weights, whereas the twisted action of a scalar is trivial. A shear in characteristic three
preserves a nonzero discriminant even when both `I` and `J` vanish.
-/

public section

open Matrix TauCeti TauCeti.BinaryQuartic

namespace TauCeti.Examples.NumberTheory.BinaryQuartic

/-- Swapping `x` and `y` reverses the five coefficients. -/
example {R : Type*} [CommSemiring R] (f : TauCeti.BinaryQuartic R) :
    subst !![0, 1; 1, 0] f = ![f 4, f 3, f 2, f 1, f 0] := by
  funext i
  fin_cases i <;> simp [subst_def, eval_def]

/-- The lower shear replaces `x` by `x + y` in `x³y`. -/
example : subst !![1, 0; 1, 1] (![0, 1, 0, 0, 0] : TauCeti.BinaryQuartic ℤ) =
    ![0, 1, 3, 3, 1] := by
  funext i
  fin_cases i <;> norm_num [subst_def, eval_def]

/-- The upper shear fixes `x⁴`; transposing the substitution would fail this equality. -/
example : subst !![1, 1; 0, 1] (![1, 0, 0, 0, 0] : TauCeti.BinaryQuartic ℤ) =
    ![1, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> norm_num [subst_def, eval_def]

/-- A scalar matrix with determinant four multiplies `I = 3` by `4⁴`. -/
example : invI (subst (Matrix.scalar (Fin 2) (2 : ℚ)) ![0, 1, 0, -1, 0]) = 768 := by
  rw [Matrix.scalar_apply, subst_scalar, invI_smul]
  norm_num [invI_def]

/-- The same scalar acts trivially under the determinant twist. -/
example (f : TauCeti.BinaryQuartic ℚ) :
    twistedSMul (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 2 (by norm_num))) f = f :=
  twistedSMul_scalar _ _

/-- Swapping coefficients preserves the sign of a nonzero `J`. -/
example : invJ (subst !![0, 1; 1, 0] (![1, 0, 0, 1, 0] : TauCeti.BinaryQuartic ℤ)) = -27 := by
  rw [invJ_subst]
  norm_num [Matrix.det_fin_two, invJ_def]

/-- In characteristic three, discriminant covariance carries information absent from `I,J`. -/
example : disc (subst !![1, 0; 1, 1] (![0, 1, 0, -1, 0] : TauCeti.BinaryQuartic (ZMod 3))) =
    1 := by
  rw [disc_subst]
  norm_num [Matrix.det_fin_two, disc_def]
  decide

end TauCeti.Examples.NumberTheory.BinaryQuartic
