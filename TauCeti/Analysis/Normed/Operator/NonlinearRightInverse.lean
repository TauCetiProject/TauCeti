/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Packaging and composition of bounded nonlinear right inverses

A continuous semilinear right inverse `r` of a split surjection `q` packages as a
`ContinuousLinearMap.NonlinearRightInverse` whose underlying function is `r` itself and whose norm
bound is `‖r‖₊` (`ContinuousLinearMap.toNonlinearRightInverse`).

Right inverses of two continuous linear maps compose in the reverse order of the original
maps, and their norm-bound constants multiply (`ContinuousLinearMap.NonlinearRightInverse.comp`).
No linearity, continuity, or completeness assumption on the right inverses is needed beyond the
native `NonlinearRightInverse` data.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} {σ' : 𝕜₂ →+* 𝕜₁} [RingHomIsometric σ']
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜₁ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- A continuous semilinear right inverse `r` of `q` (for a split surjection) defines a
`NonlinearRightInverse` whose underlying map is `r` itself, hence continuous and semilinear. -/
noncomputable def toNonlinearRightInverse (q : E →SL[σ] F) (r : F →SL[σ'] E)
    (hqr : Function.RightInverse r q) : q.NonlinearRightInverse :=
  { toFun := r, nnNorm := ‖r‖₊, bound' := r.le_opNorm, right_inv' := hqr }

@[simp]
theorem coe_toNonlinearRightInverse (q : E →SL[σ] F) (r : F →SL[σ'] E)
    (hqr : Function.RightInverse r q) : ⇑(q.toNonlinearRightInverse r hqr) = r := (rfl)

@[simp]
theorem toNonlinearRightInverse_nnNorm (q : E →SL[σ] F) (r : F →SL[σ'] E)
    (hqr : Function.RightInverse r q) : (q.toNonlinearRightInverse r hqr).nnNorm = ‖r‖₊ := (rfl)

end ContinuousLinearMap

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
  nnNorm := R.nnNorm * Q.nnNorm
  bound' z := by
    calc
      ‖R (Q z)‖ ≤ R.nnNorm * ‖Q z‖ := R.bound _
      _ ≤ R.nnNorm * (Q.nnNorm * ‖z‖) :=
        mul_le_mul_of_nonneg_left (Q.bound z) R.nnNorm.coe_nonneg
      _ = (R.nnNorm * Q.nnNorm : ℝ≥0) * ‖z‖ := by
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
    (R.comp Q).nnNorm = R.nnNorm * Q.nnNorm := by
  simp only [comp]

end ContinuousLinearMap.NonlinearRightInverse
