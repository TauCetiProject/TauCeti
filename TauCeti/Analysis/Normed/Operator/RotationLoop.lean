/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.UnitInterval

/-!
# The full rotation of a complex normed space

The **full rotation** `t ↦ e^{2πit}` of a complex normed space `E`, read as a loop of real-linear
operators (`TauCeti.rotationLoop`), is a continuous closed loop
(`TauCeti.continuous_rotationLoop`, `TauCeti.rotationLoop_zero_eq_one`). On a complex inner
product space it preserves the inner product (`TauCeti.inner_rotationLoop_apply`), so it is a loop
of linear symplectic maps for `Im ⟪·, ·⟫`; it normalizes the Maslov index of such loops.
-/

public section

noncomputable section

open Real
open scoped InnerProductSpace unitInterval

namespace TauCeti

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (E) in
/-- The **full rotation** `t ↦ e^{2πit}` of a complex normed space, as a loop of real-linear
maps. -/
def rotationLoop (t : I) : E →L[ℝ] E :=
  (Complex.exp ((2 * π * t : ℝ) * Complex.I) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

/-- The full rotation at time `t` is multiplication by `e^{2πit}`. -/
@[simp]
theorem rotationLoop_apply (t : I) (z : E) :
    rotationLoop E t z = Complex.exp ((2 * π * t : ℝ) * Complex.I) • z :=
  (rfl)

variable (E) in
/-- The full rotation is a continuous family of operators. -/
theorem continuous_rotationLoop : Continuous (rotationLoop E) :=
  (ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ).continuous.comp (by fun_prop)

variable (E) in
/-- The full rotation is a closed loop. -/
theorem rotationLoop_zero_eq_one : rotationLoop E 0 = rotationLoop E 1 := by
  ext z
  simp only [rotationLoop_apply, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I]

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The full rotation preserves the inner product, so in particular the symplectic form
`Im ⟪·, ·⟫`. -/
theorem inner_rotationLoop_apply (t : I) (x y : E) :
    ⟪rotationLoop E t x, rotationLoop E t y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [rotationLoop_apply, rotationLoop_apply, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul', Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, one_pow, one_mul]

end TauCeti
