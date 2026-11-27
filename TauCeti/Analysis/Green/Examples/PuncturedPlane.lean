/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.FlatDifferentialForm
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A family of one-forms on the punctured plane

Weight the planar form `(x - y) dx + (x + y) dy` by `(x² + y²)^(-α)`. Its exterior derivative
has coefficient `2 (1 - α) (x² + y²)^(-α)` in the positive area form. Thus precisely the
member with exponent `α = 1` is closed. Every member restricts to the same form on the unit
circle, with period `2π`, so none admits a single-valued real primitive on the punctured plane.
-/

public noncomputable section

open Set Complex
open scoped ContDiff

namespace TauCeti.Green.Examples

/-- The coefficient of `dx` in the radially weighted form on the punctured plane. -/
def puncturedPlaneP (α : ℝ) (z : ℂ) : ℝ :=
  (z.re - z.im) * normSq z ^ (-α)

/-- The coefficient of `dy` in the radially weighted form on the punctured plane. -/
def puncturedPlaneQ (α : ℝ) (z : ℂ) : ℝ :=
  (z.re + z.im) * normSq z ^ (-α)

/-- Evaluation of the horizontal coefficient in Cartesian coordinates. -/
@[simp]
theorem puncturedPlaneP_apply (α : ℝ) (z : ℂ) :
    puncturedPlaneP α z = (z.re - z.im) * normSq z ^ (-α) := (rfl)

/-- Evaluation of the vertical coefficient in Cartesian coordinates. -/
@[simp]
theorem puncturedPlaneQ_apply (α : ℝ) (z : ℂ) :
    puncturedPlaneQ α z = (z.re + z.im) * normSq z ^ (-α) := (rfl)

/-- The weighted covector field is smooth away from the origin for every real exponent. -/
theorem contDiffOn_oneForm_puncturedPlane (α : ℝ) :
    ContDiffOn ℝ ∞ (oneForm (puncturedPlaneP α) (puncturedPlaneQ α)) {0}ᶜ := by
  intro z hz
  have hρ : ContDiffAt ℝ ∞ (fun w : ℂ ↦ normSq w ^ (-α)) z := by
    simp only [normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  have hP : ContDiffAt ℝ ∞ (puncturedPlaneP α) z :=
    (reCLM.contDiff.contDiffAt.sub imCLM.contDiff.contDiffAt).mul hρ
  have hQ : ContDiffAt ℝ ∞ (puncturedPlaneQ α) z :=
    (reCLM.contDiff.contDiffAt.add imCLM.contDiff.contDiffAt).mul hρ
  rw [oneForm_eq_clm]
  exact ((hP.smul contDiffAt_const).add (hQ.smul contDiffAt_const)).contDiffWithinAt

private theorem hasFDerivAt_puncturedPlaneWeight (α : ℝ) {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ normSq w ^ (-α))
      ((-α * normSq z ^ (-α - 1)) • ((2 * z.re) • reCLM + (2 * z.im) • imCLM)) z := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hd := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.rpow_const (p := -α) (Or.inl hn)
  have hcoords : 2 • innerSL ℝ z = (2 * z.re) • reCLM + (2 * z.im) • imCLM := by
    ext v
    simp [two_smul, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    ring
  simpa only [normSq_eq_norm_sq, hcoords] using hd

/-- The curl in the positively oriented basis `(1, I)` at a nonzero point. -/
theorem curl_puncturedPlane (α : ℝ) {z : ℂ} (hz : z ≠ 0) :
    curl (puncturedPlaneP α) (puncturedPlaneQ α) z =
      2 * (1 - α) * normSq z ^ (-α) := by
  have hρ := hasFDerivAt_puncturedPlaneWeight α hz
  have hP := (reCLM.hasFDerivAt.fun_sub imCLM.hasFDerivAt).fun_mul hρ
  have hQ := (reCLM.hasFDerivAt.fun_add imCLM.hasFDerivAt).fun_mul hρ
  simp only [reCLM_apply, imCLM_apply] at hP hQ
  unfold curl puncturedPlaneP puncturedPlaneQ
  rw [hP.fderiv, hQ.fderiv]
  have hρz : normSq z ≠ 0 := normSq_eq_zero.not.mpr hz
  calc
    _ = 2 * normSq z ^ (-α) - 2 * α * (normSq z ^ (-α - 1) * normSq z) := by
      simp [normSq_apply]
      ring
    _ = _ := by
      rw [← Real.rpow_add_one hρz, sub_add_cancel]
      ring

attribute [local instance] Complex.finrank_real_complex_fact

/-- The flat exterior derivative within the punctured plane is the computed multiple of
`dx ∧ dy`, as an equality of alternating forms. -/
theorem extDerivWithin_oneForm_puncturedPlane (α : ℝ) {z : ℂ} (hz : z ≠ 0) :
    extDerivWithin (fun w ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      (oneForm (puncturedPlaneP α) (puncturedPlaneQ α) w)) {0}ᶜ z =
      (2 * (1 - α) * normSq z ^ (-α)) • Complex.orientation.volumeFormL := by
  have hω := ((contDiffOn_oneForm_puncturedPlane α z hz).contDiffAt
    (isOpen_compl_singleton.mem_nhds hz)).differentiableAt (by simp)
  have hd := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ)
    (0 : Fin 1)).differentiableAt.comp z hω
  rw [extDerivWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hz)]
  simp only [ContinuousAlternatingMap.ofSubsingletonLIE_apply]
  rw [hd.extDeriv_oneForm_eq_smul_volumeFormL, curl_puncturedPlane α hz]

/-- The member with exponent one is the unique closed form in the family. -/
theorem eqOn_extDerivWithin_oneForm_puncturedPlane_zero_iff (α : ℝ) :
    EqOn (extDerivWithin (fun w ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      (oneForm (puncturedPlaneP α) (puncturedPlaneQ α) w)) {0}ᶜ) 0 {0}ᶜ ↔ α = 1 := by
  constructor
  · intro h
    have he := h (x := 1) one_ne_zero
    rw [extDerivWithin_oneForm_puncturedPlane α one_ne_zero] at he
    have hc := congrArg (fun (A : ContinuousAlternatingMap ℝ ℂ ℝ (Fin 2)) ↦ A ![1, I]) he
    simp only [ContinuousAlternatingMap.smul_apply, Complex.orientation_volumeFormL_one_I] at hc
    symm
    simpa [sub_eq_zero] using hc
  · rintro rfl z hz
    rw [extDerivWithin_oneForm_puncturedPlane 1 hz]
    simp

/-- Every member of the family evaluates to one on the positively parametrized unit
circle's velocity. -/
theorem circulationFun_puncturedPlane_circleMap (α t : ℝ) :
    circulationFun (puncturedPlaneP α) (puncturedPlaneQ α) (circleMap 0 1) t = 1 := by
  have hρ : normSq (circleMap 0 1 t) = 1 := by simp [normSq_eq_norm_sq, norm_circleMap_zero]
  rw [circulationFun, puncturedPlaneP, puncturedPlaneQ, deriv_circleMap, hρ, Real.one_rpow]
  simp only [mul_one, mul_I_re, mul_I_im]
  nlinarith [normSq_apply (circleMap 0 1 t)]

/-- The positively oriented unit-circle period is `2π` for every exponent. -/
theorem integral_circulationFun_puncturedPlane_circleMap (α : ℝ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      circulationFun (puncturedPlaneP α) (puncturedPlaneQ α) (circleMap 0 1) t) = 2 * Real.pi := by
  simp [circulationFun_puncturedPlane_circleMap]

/-- No real function on the punctured plane has the weighted one-form as its derivative,
even for the closed member of the family. -/
theorem not_exists_eqOn_fderiv_oneForm_puncturedPlane (α : ℝ) :
    ¬ ∃ g : ℂ → ℝ, EqOn (fderiv ℝ g) (oneForm (puncturedPlaneP α) (puncturedPlaneQ α)) {0}ᶜ := by
  rintro ⟨g, hg⟩
  have hd (t : ℝ) : HasDerivAt (g ∘ circleMap 0 1) 1 t := by
    have ht := hg (circleMap_ne_center (c := 0) (θ := t) one_ne_zero)
    have hv := circulationFun_puncturedPlane_circleMap α t
    rw [circulationFun_eq_oneForm, ← ht] at hv
    have hdiff : DifferentiableAt ℝ g (circleMap 0 1 t) := by
      by_contra h
      simp [fderiv_zero_of_not_differentiableAt h] at hv
    have hc := hdiff.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_circleMap 0 1 t).differentiableAt.hasDerivAt
    rwa [hv] at hc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 2 * Real.pi) (fun t _ ↦ hd t) (intervalIntegrable_const)
  have hp := periodic_circleMap 0 1 0
  simp only [zero_add] at hp
  simp [Function.comp_apply, hp] at h

end TauCeti.Green.Examples
