/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import TauCeti.Analysis.InnerProductSpace.Complex

/-!
# The Kähler two-form on a complex inner product space

On a complex inner product space `E` carrying a compatible real scalar action
(`IsScalarTower ℝ ℂ E`), the **Kähler two-form** is the real continuous alternating two-form
`TauCeti.kahlerTwoForm E v = Im ⟪v₀, v₁⟫_ℂ`.

For `E = ℂ` with the standard Hermitian inner product conjugate-linear in the first slot,
`ω(1, i) = 1`. On any (possibly seminormed) complex inner product space, `kahlerTwoForm E` has
comass at most `1` (`TauCeti.norm_kahlerTwoForm_le`), and on any nontrivial normed complex inner
product space (without finite-dimensionality), its comass equals `1` (`TauCeti.norm_kahlerTwoForm`).
When `E` also carries a compatible real inner product, `ω(v, w) = ⟪i • v, w⟫_ℝ`
(`TauCeti.kahlerTwoForm_apply_eq_inner`), and on pairs `kahlerTwoForm E` agrees with the symplectic
form `TauCeti.imInnerSymplecticForm E` (`TauCeti.kahlerTwoForm_apply_eq_imInnerSymplecticForm`).
Complex linear isometries pull `kahlerTwoForm` back to itself
(`TauCeti.kahlerTwoForm_comp_linearIsometry`).

## Main definitions

* `TauCeti.kahlerTwoForm`: the Kähler two-form `ω(v, w) = Im ⟪v, w⟫_ℂ` on a complex inner product
  space.

## Main results

* `TauCeti.kahlerTwoForm_apply`: evaluation formula `kahlerTwoForm E v = Im ⟪v 0, v 1⟫_ℂ`.
* `TauCeti.norm_kahlerTwoForm_le`: degree-two Wirtinger comass upper bound on any (possibly
  seminormed) complex inner product space.
* `TauCeti.norm_kahlerTwoForm`: degree-two Wirtinger comass equality on any nontrivial normed
  complex inner product space.
* `TauCeti.kahlerTwoForm_comp_linearIsometry`: naturality under complex linear isometries.
* `TauCeti.kahlerTwoForm_apply_eq_inner`: identification `kahlerTwoForm E ![v, w] = ⟪i • v, w⟫_ℝ`.
* `TauCeti.kahlerTwoForm_apply_eq_imInnerSymplecticForm`: identification
  `kahlerTwoForm E ![v, w] = imInnerSymplecticForm E v w`.

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

/-- The Kähler two-form has comass at most one on every (possibly seminormed) complex inner product
space. -/
theorem norm_kahlerTwoForm_le : ‖kahlerTwoForm E‖ ≤ 1 := by
  refine (kahlerTwoForm E).opNorm_le_bound zero_le_one fun v ↦ ?_
  rw [kahlerTwoForm_apply, Real.norm_eq_abs, one_mul, Fin.prod_univ_two]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm (v 0) (v 1))

/-- Naturality of `TauCeti.kahlerTwoForm` under any complex linear isometry `f : E →ₗᵢ[ℂ] F`. -/
theorem kahlerTwoForm_comp_linearIsometry {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [InnerProductSpace ℂ F] [IsScalarTower ℝ ℂ F] (f : E →ₗᵢ[ℂ] F) :
    (kahlerTwoForm F).compContinuousLinearMap (f.toContinuousLinearMap.restrictScalars ℝ) =
      kahlerTwoForm E := by
  ext v
  simp [kahlerTwoForm_apply, f.inner_map_map]

end

/-- **Wirtinger inequality in degree two**: on every nontrivial normed complex inner product space
(no finite-dimensionality required), the Kähler two-form has comass one. -/
theorem norm_kahlerTwoForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] [Nontrivial E] :
    ‖kahlerTwoForm E‖ = 1 := by
  refine le_antisymm norm_kahlerTwoForm_le ?_
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  set u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hx]
  have hval : kahlerTwoForm E ![u, Complex.I • u] = 1 := by
    simp [kahlerTwoForm_apply, inner_smul_right, hu]
  simpa [hval, Fin.prod_univ_two, norm_smul, hu] using
    (kahlerTwoForm E).le_opNorm ![u, Complex.I • u]

/-- In terms of a compatible real inner product, `ω(v, w) = ⟪i • v, w⟫_ℝ`. -/
theorem kahlerTwoForm_apply_eq_inner {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] (v w : E) :
    kahlerTwoForm E ![v, w] = ⟪Complex.I • v, w⟫_ℝ := by
  rw [kahlerTwoForm_apply, TauCeti.inner_real_eq_re_inner ℂ, inner_smul_left]
  simp

/-- On pairs, `TauCeti.kahlerTwoForm E` evaluates to `TauCeti.imInnerSymplecticForm E`. -/
theorem kahlerTwoForm_apply_eq_imInnerSymplecticForm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] (v w : E) :
    kahlerTwoForm E ![v, w] = imInnerSymplecticForm E v w := by
  rw [kahlerTwoForm_apply, imInnerSymplecticForm_apply]
  rfl

end TauCeti
