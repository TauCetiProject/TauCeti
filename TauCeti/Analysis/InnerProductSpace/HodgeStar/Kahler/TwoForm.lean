/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import TauCeti.Analysis.InnerProductSpace.Complex

/-!
# The Kähler two-form on a complex inner product space

On a complex inner product space `E` carrying a compatible real scalar action
(`[IsScalarTower ℝ ℂ E]`), the **Kähler two-form** is the real continuous alternating two-form
`TauCeti.kahlerTwoForm E v = Im ⟪v₀, v₁⟫_ℂ`.

For `E = ℂ` with the standard Hermitian inner product conjugate-linear in the first slot,
`ω(1, i) = 1`. When `E` also carries a compatible real inner product,
`ω(v, w) = ⟪i • v, w⟫_ℝ` (`TauCeti.kahlerTwoForm_apply_eq_inner`). Complex linear isometries pull
`kahlerTwoForm` back to itself (`TauCeti.kahlerTwoForm_comp_linearIsometry`).

## Main definitions

* `TauCeti.kahlerTwoForm`: the Kähler two-form `ω(v, w) = Im ⟪v, w⟫_ℂ` on a complex inner product
  space.

## Main results

* `TauCeti.kahlerTwoForm_apply`: evaluation formula `kahlerTwoForm E v = Im ⟪v 0, v 1⟫_ℂ`.
* `TauCeti.kahlerTwoForm_comp_linearIsometry`: naturality under complex linear isometries.
* `TauCeti.kahlerTwoForm_apply_eq_inner`: identification `kahlerTwoForm E ![v, w] = ⟪i • v, w⟫_ℝ`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), §II.6.
-/

public section

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti

section

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The **Kähler two-form** `ω(v, w) = Im ⟪v, w⟫_ℂ` on a complex inner product space, as a real
continuous alternating two-form. For `E = ℂ` with the standard Hermitian product conjugate-linear
in the first slot, `ω(1, i) = 1`. -/
def kahlerTwoForm : E [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := (inner ℂ (v 0) (v 1)).im
  map_update_add' m i x y := by fin_cases i <;> simp [inner_add_left, inner_add_right]
  map_update_smul' m i c x := by
    have hsmul : c • x = (c : ℂ) • x := by rw [← Complex.coe_algebraMap, algebraMap_smul]
    fin_cases i
    · have h : (inner ℂ (c • x) (m 1)).im = c * (inner ℂ x (m 1)).im := by
        rw [hsmul, inner_smul_left]; simp
      simpa using h
    · have h : (inner ℂ (m 0) (c • x)).im = c * (inner ℂ (m 0) x).im := by
        rw [hsmul, inner_smul_right]; simp
      simpa using h
  cont := Complex.continuous_im.comp ((continuous_apply 0).inner (continuous_apply 1))
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all [← Complex.ofReal_pow]

variable {E}

/-- Evaluation formula for `TauCeti.kahlerTwoForm`. -/
@[simp]
theorem kahlerTwoForm_apply (v : Fin 2 → E) :
    kahlerTwoForm E v = (inner ℂ (v 0) (v 1)).im :=
  (rfl)

/-- Naturality of `TauCeti.kahlerTwoForm` under any complex linear isometry `f : E →ₗᵢ[ℂ] F`. -/
theorem kahlerTwoForm_comp_linearIsometry {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [InnerProductSpace ℂ F] [IsScalarTower ℝ ℂ F] (f : E →ₗᵢ[ℂ] F) :
    (kahlerTwoForm F).compContinuousLinearMap (f.toContinuousLinearMap.restrictScalars ℝ) =
      kahlerTwoForm E := by
  ext v
  simp [kahlerTwoForm_apply, f.inner_map_map]

end

/-- In terms of a compatible real inner product, `ω(v, w) = ⟪i • v, w⟫_ℝ`. -/
theorem kahlerTwoForm_apply_eq_inner {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] (v w : E) :
    kahlerTwoForm E ![v, w] = ⟪Complex.I • v, w⟫_ℝ := by
  rw [kahlerTwoForm_apply, TauCeti.inner_real_eq_re_inner ℂ, inner_smul_left]
  simp

end TauCeti
