/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Analysis.Fourier.Hardy.CircleIndexOperator.Chart
import TauCeti.Topology.Algebra.GroupWithZero.Inversion
import TauCeti.Topology.ContinuousMap.CodRestrict
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# An affine representative of the circle index symbol

The affine interpolation between the two circle symbol branches vanishes only at the
zero covector over `-1`. In oriented local coordinates, real displacement runs in the
direction of increasing angle and imaginary displacement is the covector coordinate.
The angular displacement from `-1` is twice the arctangent of half the real coordinate.
On the punctured coordinate plane, `circleIndexAffineLocalHomotopy` is a homotopy from
`circleIndexAffineLocalScalar` to the inversion homeomorphism `Homeomorph.inv₀ ℂ`.

The rectangle comparison is due to Atiyah and Singer, *The Index of Elliptic Operators: I*,
§8, Fig. 3, p. 526. The affine representative and explicit local deformation are adapted from
`CircleAffineSymbol.lean` in the Lean-Atiyah-Singer formalization by Alpha Squared Labs and Codex.
[Atiyah–Singer I](https://doi.org/10.2307/1970715)
[Lean-Atiyah-Singer](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer)
-/

public section

noncomputable section

open scoped ContDiff
open Topology
open Real (coe_boundaryCayley)

namespace TauCeti

/-- The affine scalar joining the constant lower branch to the circle character on the upper
edge. The real argument is the normalized covector. -/
def circleIndexAffineScalar : C(Circle × ℝ, ℂ) where
  toFun p := AffineMap.lineMap (1 : ℂ) (p.1 : ℂ) ((1 + p.2) / 2)
  continuous_toFun := by simp only [AffineMap.lineMap_apply_module]; fun_prop

/-- The affine representative is the real line map at normalized time `(1 + s) / 2`. -/
theorem circleIndexAffineScalar_eq_lineMap (z : Circle) (s : ℝ) :
    circleIndexAffineScalar (z, s) = AffineMap.lineMap (1 : ℂ) (z : ℂ) ((1 + s) / 2) :=
  (rfl)

/-- The scalar is affine in the covector, with values `1` at `-1` and `z` at `1`. -/
theorem circleIndexAffineScalar_apply (z : Circle) (s : ℝ) :
    circleIndexAffineScalar (z, s) = (1 - (s : ℂ)) / 2 + (1 + (s : ℂ)) / 2 * z := by
  rw [circleIndexAffineScalar_eq_lineMap, AffineMap.lineMap_apply_module]
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- At the lower edge the affine scalar is constant. -/
@[simp] theorem circleIndexAffineScalar_neg_one (z : Circle) :
    circleIndexAffineScalar (z, -1) = 1 := by
  norm_num [circleIndexAffineScalar_eq_lineMap]

/-- At the upper edge the affine scalar is the circle coordinate. -/
@[simp] theorem circleIndexAffineScalar_one (z : Circle) :
    circleIndexAffineScalar (z, 1) = z := by
  norm_num [circleIndexAffineScalar_eq_lineMap]

/-- The affine scalar is constant above the identity of the circle. -/
@[simp] theorem circleIndexAffineScalar_one_left (s : ℝ) :
    circleIndexAffineScalar (1, s) = 1 := by
  simp [circleIndexAffineScalar_eq_lineMap]

/-- The affine representative is smooth in the period-one position and the real covector. -/
theorem contDiff_circleIndexAffineScalar_comp_circleExp :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦
      circleIndexAffineScalar (Circle.exp (2 * Real.pi * p.1), p.2)) := by
  simp only [circleIndexAffineScalar_apply, Circle.coe_exp, ← Complex.ofRealCLM_apply]
  fun_prop

/-- The sole noninvertible value of the affine scalar occurs at the zero covector over `-1`. -/
@[simp] theorem circleIndexAffineScalar_eq_zero_iff (p : Circle × ℝ) :
    circleIndexAffineScalar p = 0 ↔ p = (-1, 0) := by
  obtain ⟨z, s⟩ := p
  rw [circleIndexAffineScalar_apply]
  constructor
  · intro h
    have he : (1 + (s : ℂ)) * z = -(1 - (s : ℂ)) := by linear_combination 2 * h
    have hn := congrArg norm he
    simp only [norm_mul, Circle.norm_coe, mul_one, norm_neg, ← Complex.ofReal_one,
      ← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hn
    have hs := congrArg (fun x : ℝ ↦ x ^ 2) hn
    rw [sq_abs, sq_abs] at hs
    obtain rfl : s = 0 := by nlinarith
    exact Prod.ext (Subtype.ext (by simpa using he)) rfl
  · rintro ⟨⟩
    norm_num

/-- In the oriented chart twice the affine scalar has the Cayley denominator. -/
theorem two_mul_circleIndexAffineScalar_circleIndexAffineParametrization (w : ℂ) :
    2 * circleIndexAffineScalar (circleIndexAffineParametrization w) =
      (-Complex.I * w.re - 2 * w.im) / (1 - (w.re / 2 : ℂ) * Complex.I) := by
  rw [circleIndexAffineParametrization_apply, circleIndexAffineScalar_apply, coe_boundaryCayley]
  push_cast
  have hd : (w.re : ℂ) / 2 + Complex.I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hc : 1 - (w.re : ℂ) / 2 * Complex.I ≠ 0 := Complex.ne_zero_of_re_pos (by simp)
  apply (eq_div_iff hc).mpr
  set q := ((w.re : ℂ) / 2 - Complex.I) / ((w.re : ℂ) / 2 + Complex.I)
  have h : q * ((w.re : ℂ) / 2 + Complex.I) = (w.re : ℂ) / 2 - Complex.I :=
    div_mul_cancel₀ _ hd
  linear_combination -(1 + (w.im : ℂ)) * Complex.I * h +
    (1 + (w.im : ℂ)) * (1 + q) * Complex.I_sq

local notation "U" => {w : ℂ // w ≠ 0}

/-- The affine scalar in chart coordinates, restricted to the punctured complex plane. -/
def circleIndexAffineLocalScalar : C(U, U) :=
  let s := {w : ℂ | w ≠ 0}
  let f := circleIndexAffineScalar.comp
    ⟨circleIndexAffineParametrization,
      isOpenEmbedding_circleIndexAffineParametrization.continuous⟩
  have h : Set.MapsTo f s s := fun _ hw h₀ ↦ hw <|
    isOpenEmbedding_circleIndexAffineParametrization.injective <|
      ((circleIndexAffineScalar_eq_zero_iff _).mp h₀).trans
        circleIndexAffineParametrization_zero.symm
  (f.restrict s).codRestrict s fun w ↦ h w.property

/-- In the ambient complex plane the restricted scalar has its original value. -/
@[simp] theorem coe_circleIndexAffineLocalScalar (w : U) :
    (circleIndexAffineLocalScalar w : ℂ) =
      circleIndexAffineScalar (circleIndexAffineParametrization w) := by
  dsimp only [circleIndexAffineLocalScalar]
  refine (ContinuousMap.coe_codRestrict_apply _ _ _ _).trans ?_
  rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rfl

private def localPhase (t : unitInterval) : ℂ :=
  Complex.exp ((-(1 - (t : ℝ)) * Real.pi / 2 : ℝ) * Complex.I)

private def localDenominator (t : unitInterval) (w : ℂ) : ℂ :=
  (1 - (((1 - (t : ℝ)) * w.re / 2 : ℝ) : ℂ) * Complex.I) *
    (((1 - (t : ℝ)) + t * ‖w‖ ^ 2 : ℝ) : ℂ)

private theorem localDenominator_ne_zero (t : unitInterval) (w : U) :
    localDenominator t w ≠ 0 := by
  unfold localDenominator
  apply mul_ne_zero (Complex.ne_zero_of_re_pos (by simp))
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  simpa [AffineMap.lineMap_apply_module] using
    (convex_Ioi (𝕜 := ℝ) 0).lineMap_mem zero_lt_one (pow_pos (norm_pos_iff.mpr w.property) 2)
      t.property

private def localNumerator (t : unitInterval) (w : ℂ) : ℂ :=
  ⟨w.re, -((2 - (t : ℝ)) * w.im)⟩

private theorem localNumerator_ne_zero (t : unitInterval) (w : U) :
    localNumerator t w ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [localNumerator, Complex.zero_re] at hr
  simp only [localNumerator, Complex.zero_im, neg_eq_zero, mul_eq_zero] at hi
  have ht : 2 - (t : ℝ) ≠ 0 := by linarith [t.property.2]
  exact w.property (Complex.ext hr (hi.resolve_left ht))

private def localValue (p : unitInterval × U) : ℂ :=
  ((1 + (p.1 : ℝ)) / 2 : ℝ) * localPhase p.1 * localNumerator p.1 p.2 / localDenominator p.1 p.2

private theorem continuous_localValue : Continuous localValue := by
  have hD : Continuous (fun p : unitInterval × U ↦ localDenominator p.1 p.2) := by
    unfold localDenominator
    fun_prop
  have hN : Continuous (fun p : unitInterval × U ↦
      ((1 + (p.1 : ℝ)) / 2 : ℝ) * localPhase p.1 * localNumerator p.1 p.2) := by
    simp only [localPhase, localNumerator, Complex.mk_eq_add_mul_I]
    fun_prop
  unfold localValue
  simpa only [Pi.div_def] using hN.div hD fun p ↦ localDenominator_ne_zero p.1 p.2

private theorem localValue_ne_zero (p : unitInterval × U) : localValue p ≠ 0 := by
  have ht : 0 < (1 + (p.1 : ℝ)) / 2 := by linarith [p.1.property.1]
  simpa only [localValue, localPhase] using div_ne_zero
    (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') (Complex.exp_ne_zero _))
      (localNumerator_ne_zero p.1 p.2)) (localDenominator_ne_zero p.1 p.2)

private theorem localValue_zero (w : U) :
    localValue (0, w) = circleIndexAffineScalar (circleIndexAffineParametrization w) := by
  have h := two_mul_circleIndexAffineScalar_circleIndexAffineParametrization w
  rw [localValue]
  have hphase : localPhase 0 = -Complex.I := by simp [localPhase]
  rw [hphase]
  simp only [localDenominator, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero,
    Complex.ofReal_one, mul_one, Complex.ofReal_div, Complex.ofReal_ofNat, one_div]
  have hn : -Complex.I * localNumerator 0 w = -Complex.I * w.val.re - 2 * w.val.im := by
    have hv : localNumerator 0 w = (w.val.re : ℂ) - 2 * w.val.im * Complex.I := by
      apply Complex.ext <;> simp [localNumerator]
    rw [hv]
    linear_combination 2 * (w.val.im : ℂ) * Complex.I_sq
  rw [mul_assoc, hn, mul_div_assoc, ← h]
  push_cast
  ring

private theorem localValue_one (w : U) : localValue (1, w) = w.val⁻¹ := by
  rw [localValue]
  have hn : localNumerator 1 w = (starRingEnd ℂ) w.val := by
    apply Complex.ext <;> norm_num [localNumerator]
  rw [hn, Complex.inv_def, Complex.normSq_eq_norm_sq]
  norm_num [localPhase, localDenominator, div_eq_mul_inv]

/-- The homotopy from the charted affine scalar to complex inversion on the punctured plane.
Its positive real scale absorbs the factor of two in the Cayley formula. -/
def circleIndexAffineLocalHomotopy :
    ContinuousMap.Homotopy circleIndexAffineLocalScalar (Homeomorph.inv₀ ℂ : C(U, U)) where
  toFun p := ⟨localValue p, localValue_ne_zero p⟩
  continuous_toFun := continuous_localValue.subtype_mk localValue_ne_zero
  map_zero_left w := by
    apply Subtype.ext
    simpa only [Subtype.coe_mk, coe_circleIndexAffineLocalScalar] using localValue_zero w
  map_one_left w := by
    apply Subtype.ext
    simpa only [Subtype.coe_mk, ContinuousMap.coe_ofClass, Homeomorph.coe_inv₀_apply] using
      localValue_one w

/-- The numerator reflects across the real axis, stretches the imaginary component and rotates
by a phase. The denominator multiplies a complex Cayley factor by the positive real radial
weight `(1 - t) + t * ‖w‖ ^ 2`. At time one the reflected point divided by `‖w‖ ^ 2` is `w⁻¹`. -/
theorem circleIndexAffineLocalHomotopy_apply (t : unitInterval) (w : U) :
    (circleIndexAffineLocalHomotopy (t, w) : ℂ) =
      ((1 + (t : ℝ)) / 2 : ℝ) * Complex.exp ((-(1 - (t : ℝ)) * Real.pi / 2 : ℝ) * Complex.I) *
        (⟨w.val.re, -((2 - (t : ℝ)) * w.val.im)⟩ : ℂ) /
        ((1 - (((1 - (t : ℝ)) * w.val.re / 2 : ℝ) : ℂ) * Complex.I) *
          (((1 - (t : ℝ)) + t * ‖w.val‖ ^ 2 : ℝ) : ℂ)) := (rfl)

end TauCeti
