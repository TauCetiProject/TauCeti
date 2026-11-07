/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Composition of bounded nonlinear right inverses

Right inverses of two continuous linear maps compose in the reverse order of the original
maps. Their norm-bound constants multiply. No linearity, continuity, or completeness assumption
on the right inverses is needed beyond the native `NonlinearRightInverse` data.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap.NonlinearRightInverse

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {T : E →L[𝕜] F} {S : F →L[𝕜] G}

/-- Compose bounded nonlinear right inverses. The inverse functions compose in the reverse
order of the original continuous linear maps. -/
def comp (R : T.NonlinearRightInverse) (Q : S.NonlinearRightInverse) :
    (S.comp T).NonlinearRightInverse where
  toFun z := R (Q z)
  nnnorm := R.nnnorm * Q.nnnorm
  bound' z := by
    calc
      ‖R (Q z)‖ ≤ R.nnnorm * ‖Q z‖ := R.bound _
      _ ≤ R.nnnorm * (Q.nnnorm * ‖z‖) :=
        mul_le_mul_of_nonneg_left (Q.bound z) R.nnnorm.coe_nonneg
      _ = (R.nnnorm * Q.nnnorm : ℝ≥0) * ‖z‖ := by
        rw [NNReal.coe_mul, mul_assoc]
  right_inv' z := by
    rw [ContinuousLinearMap.comp_apply, R.right_inv, Q.right_inv]

/-- The actual composed inverse is composition of the two inverse functions. -/
@[simp]
theorem comp_apply (R : T.NonlinearRightInverse) (Q : S.NonlinearRightInverse) (z : G) :
    R.comp Q z = R (Q z) := by
  simp only [comp]

/-- The public norm-bound constant of the composition is the product of the constants. -/
@[simp]
theorem comp_nnnorm (R : T.NonlinearRightInverse) (Q : S.NonlinearRightInverse) :
    (R.comp Q).nnnorm = R.nnnorm * Q.nnnorm := by
  simp only [comp]

end ContinuousLinearMap.NonlinearRightInverse
