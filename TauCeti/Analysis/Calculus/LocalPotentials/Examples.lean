/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.SimplyConnected
public import TauCeti.Analysis.Complex.HasPrimitives
public import TauCeti.Analysis.Complex.LocalPotentials
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Examples separating local potentials, `C¹` closedness, and global exactness

This file exercises `TauCeti.HasLocalPotentials`, `TauCeti.localPotentialIntegral`, and
`TauCeti.exists_hasFDerivAt_of_simplyConnected` on four test families that separate the hypotheses
and conclusions of the theory:

1. **The exact coordinate form `dx = Complex.reCLM` on `ℂ`:** has local potentials on every open
   `Ω ⊆ ℂ`, integrates along *every* continuous path `γ : Path a b` to `b.re - a.re` — in
   particular along arbitrary continuous graphs `t ↦ t + i W(t)` where no derivative of `W` is
   assumed — and its global potentials on `ℂ` are precisely `z ↦ z.re + c`.
2. **The non-closed form `x dy` on `ℂ`:** admits no local potentials on any nonempty domain `Ω`,
   as integrating a putative local potential around a small axis-aligned square inside a ball in
   `Ω` forces the square's positive area to vanish.
3. **The non-`C¹` exact form `d(|x|^(3/2))` on `ℝ`:** has a global `C¹` potential
   `x ↦ |x| ^ ((3 : ℝ) / 2)` (hence local potentials on `univ`), yet its covector field is not
   differentiable at `0` (hence not `C¹`).
4. **The punctured-plane angular form `(x dy - y dx) / (x² + y²)` on `{0}ᶜ`:** has local `C¹`
   potentials on `{0}ᶜ` via branches of `Complex.arg` on `Complex.slitPlane` and
   `-Complex.slitPlane`, admits the global potential `Complex.arg` on the simply connected slit
   plane, integrates to `2π` around the unit circle (and `4π` twice, `-2π` reversed), and
   therefore admits *no* global potential on `{0}ᶜ`. Correspondingly, `z ↦ z⁻¹` is exact on
   `Complex.slitPlane` with primitive `Complex.log`, and not exact on `{0}ᶜ`.

## Main declarations

* `TauCeti.localPotentialIntegral_reCLM`,
  `TauCeti.localPotentialIntegral_reCLM_continuousGraphPath`, and
  `TauCeti.forall_hasFDerivAt_reCLM_iff`: path integral along arbitrary continuous paths and
  classification of global potentials of `dx`.
* `TauCeti.xDyForm` and `TauCeti.not_hasLocalPotentials_xDyForm`: `x dy` has no local potentials on
  any nonempty set.
* `TauCeti.absPowThreeHalvesForm`, `TauCeti.hasLocalPotentials_absPowThreeHalvesForm`, and
  `TauCeti.not_differentiableAt_absPowThreeHalvesForm_zero`: `d(|x|^(3/2))` has local potentials
  without being `C¹`.
* `TauCeti.planarAngularForm`, `TauCeti.hasLocalPotentials_planarAngularForm`,
  `TauCeti.localPotentialIntegral_planarAngularForm_unitCircleLoop`, and
  `TauCeti.not_exists_hasFDerivAt_planarAngularForm_compl_zero`: the angular `1`-form separates
  local potentials from global potentials on `{0}ᶜ`.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §§1.3, 2.2, 4.2.
* Raoul Bott and Loring W. Tu, *Differential Forms in Algebraic Topology*, Springer, 1982, §I.3
  (the angular `1`-form on the punctured plane).
-/

public section

noncomputable section

open Set Metric Filter Complex ContinuousLinearMap
open scoped Topology ContDiff Real Interval

namespace TauCeti

/-! ### 1. The coordinate form `dx = Complex.reCLM` -/

/-- `dx = Complex.reCLM` has local `C¹` potentials on every open subset of `ℂ`. -/
theorem hasLocalPotentials_reCLM {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    HasLocalPotentials Ω (fun _ ↦ Complex.reCLM) :=
  hasLocalPotentials_const hΩ Complex.reCLM

/-- Along any continuous path `γ : Path a b` in `ℂ`, `dx = Complex.reCLM` integrates to
`b.re - a.re`, with no differentiability assumption on `γ`. -/
theorem localPotentialIntegral_reCLM {a b : ℂ} (γ : Path a b) :
    localPotentialIntegral (fun _ ↦ Complex.reCLM) γ = b.re - a.re :=
  localPotentialIntegral_const Complex.reCLM γ

/-- Continuous graph path `t ↦ t + i W(t)` from `0` to `1` associated to any continuous `W : ℝ → ℝ`
vanishing at `0` and `1` (including nowhere-differentiable Weierstrass-type functions). -/
def continuousGraphPath (W : ℝ → ℝ) (hW : Continuous W) (hW0 : W 0 = 0) (hW1 : W 1 = 0) :
    Path (0 : ℂ) 1 where
  toFun t := (t : ℝ) + Complex.I * W t
  continuous_toFun := by fun_prop
  source' := by simp [hW0]
  target' := by simp [hW1]

/-- `dx` over any continuous graph path `t ↦ t + i W(t)` with `W(0) = W(1) = 0` evaluates to `1`,
even when `W` is nowhere differentiable. -/
theorem localPotentialIntegral_reCLM_continuousGraphPath (W : ℝ → ℝ) (hW : Continuous W)
    (hW0 : W 0 = 0) (hW1 : W 1 = 0) :
    localPotentialIntegral (fun _ ↦ Complex.reCLM) (continuousGraphPath W hW hW0 hW1) = 1 := by
  simp [localPotentialIntegral_reCLM]

/-- The global potentials of `dx = Complex.reCLM` on `ℂ` are precisely `z ↦ z.re + c`. -/
theorem forall_hasFDerivAt_reCLM_iff {g : ℂ → ℝ} :
    (∀ z : ℂ, HasFDerivAt g Complex.reCLM z) ↔ ∃ c : ℝ, ∀ z : ℂ, g z = z.re + c := by
  refine ⟨fun hg ↦ ?_, fun ⟨c, hc⟩ z ↦ ?_⟩
  · have hdiff : DifferentiableOn ℝ g univ :=
      fun z _ ↦ (hg z).differentiableAt.differentiableWithinAt
    have hfderiv : (univ : Set ℂ).EqOn (fderiv ℝ g) (fderiv ℝ Complex.reCLM) :=
      fun z _ ↦ (hg z).fderiv.trans Complex.reCLM.hasFDerivAt.fderiv.symm
    obtain ⟨c, hc⟩ := isOpen_univ.exists_eq_add_of_fderiv_eq isPreconnected_univ
      hdiff Complex.reCLM.differentiable.differentiableOn hfderiv
    exact ⟨c, fun z ↦ hc (mem_univ z)⟩
  · have heq : g = fun w ↦ Complex.reCLM w + c := funext hc
    rw [heq]
    exact Complex.reCLM.hasFDerivAt.add_const c

/-- `dx` (`Complex.ofRealCLM.comp Complex.reCLM : ℂ →L[ℝ] ℂ`) is `ℝ`-linear rather than
`ℂ`-linear, so it is not of the holomorphic form `(toSpanSingleton ℂ w).restrictScalars ℝ`. -/
theorem not_exists_ofRealCLM_comp_reCLM_eq_toSpanSingleton :
    ¬ ∃ w : ℂ, Complex.ofRealCLM.comp Complex.reCLM =
      (toSpanSingleton ℂ w).restrictScalars ℝ := by
  rintro ⟨w, hw⟩
  have h1 := DFunLike.congr_fun hw 1
  have hI := DFunLike.congr_fun hw Complex.I
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.one_re,
    Complex.ofRealCLM_apply, Complex.ofReal_one, ContinuousLinearMap.coe_restrictScalars',
    toSpanSingleton_apply, Complex.I_re, Complex.ofReal_zero, smul_eq_mul, one_mul] at h1 hI
  rw [← h1, mul_one] at hI
  exact Complex.I_ne_zero hI.symm

/-! ### 2. The non-closed covector field `x dy` -/

/-- The planar `1`-form `x dy` on `ℂ`, sending a tangent vector `w` at `z` to `z.re * w.im`. -/
def xDyForm (z : ℂ) : ℂ →L[ℝ] ℝ :=
  z.re • Complex.imCLM

/-- Explicit evaluation of `xDyForm` on a tangent vector. -/
@[simp]
theorem xDyForm_apply (z w : ℂ) : xDyForm z w = z.re * w.im := by rfl

/-- `x dy` has no local potentials on any nonempty subset `Ω ⊆ ℂ`: a potential on a ball around
`z₀ ∈ Ω` would integrate around a small square inside the ball to both `0` and the positive area of
the square. -/
theorem not_hasLocalPotentials_xDyForm {Ω : Set ℂ} (hΩ : Ω.Nonempty) :
    ¬ HasLocalPotentials Ω xDyForm := by
  intro hφ
  obtain ⟨z₀, hz₀⟩ := hΩ
  obtain ⟨r, hr, -, g, -, hd⟩ := hasLocalPotentials_iff.mp hφ z₀ hz₀
  set ε : ℝ := r / 2
  have hε : 0 < ε := half_pos hr
  have hmem_sq {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ ε) (hb0 : 0 ≤ b) (hb1 : b ≤ ε) :
      z₀ + (a : ℂ) + (b : ℂ) * I ∈ ball z₀ r := by
    rw [mem_ball, add_assoc, dist_self_add_left]
    have hnorm : ‖(a : ℂ) + (b : ℂ) * I‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
      simp only [Complex.norm_def, Complex.normSq_apply, add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]
      ring_nf
    rw [hnorm]
    have hsq : a ^ 2 + b ^ 2 < r ^ 2 := by
      have ha_sq : a ^ 2 ≤ ε ^ 2 := sq_le_sq' (by linarith) ha1
      have hb_sq : b ^ 2 ≤ ε ^ 2 := sq_le_sq' (by linarith) hb1
      have hε_sq : 2 * ε ^ 2 < r ^ 2 := by simp [ε]; nlinarith
      linarith
    exact (Real.sqrt_lt' hr).mpr hsq
  have hhoriz {p : ℂ} (hp : ∀ t ∈ Icc (0 : ℝ) 1, p + ((t * ε : ℝ) : ℂ) ∈ ball z₀ r) :
      g (p + (ε : ℂ)) - g p = 0 := by
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun τ : ℝ ↦ g (p + ((τ * ε : ℝ) : ℂ))) 0 t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hlin : HasDerivAt (fun τ : ℝ ↦ p + ((τ * ε : ℝ) : ℂ)) (ε : ℂ) t := by
        have h1 : HasDerivAt (fun τ : ℝ ↦ τ * ε) ε t := by
          simpa using (hasDerivAt_id t).mul_const ε
        exact ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h1).const_add p).congr_deriv
          (by simp)
      exact ((hd _ (hp t ht)).comp_hasDerivAt t hlin).congr_deriv (by simp [xDyForm_apply])
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder IntervalIntegrable.zero
    simpa using hftc.symm
  have hvert {p : ℂ} (hp : ∀ t ∈ Icc (0 : ℝ) 1, p + ((t * ε : ℝ) : ℂ) * I ∈ ball z₀ r) :
      g (p + (ε : ℂ) * I) - g p = p.re * ε := by
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun τ : ℝ ↦ g (p + ((τ * ε : ℝ) : ℂ) * I)) (p.re * ε) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hlin : HasDerivAt (fun τ : ℝ ↦ p + ((τ * ε : ℝ) : ℂ) * I) ((ε : ℂ) * I) t := by
        have h1 : HasDerivAt (fun τ : ℝ ↦ τ * ε) ε t := by
          simpa using (hasDerivAt_id t).mul_const ε
        have h2 : HasDerivAt (fun τ : ℝ ↦ ((τ * ε : ℝ) : ℂ) * I) ((ε : ℂ) * I) t :=
          ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h1).mul_const I).congr_deriv (by simp)
        exact (h2.const_add p)
      exact ((hd _ (hp t ht)).comp_hasDerivAt t hlin).congr_deriv (by simp [xDyForm_apply])
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder intervalIntegrable_const
    simpa using hftc.symm
  have hbot : g (z₀ + (ε : ℂ)) - g z₀ = 0 :=
    hhoriz fun t ht ↦ by
      simpa using hmem_sq (mul_nonneg ht.1 hε.le) (mul_le_of_le_one_left hε.le ht.2) le_rfl hε.le
  have htop : g (z₀ + (ε : ℂ) * I + (ε : ℂ)) - g (z₀ + (ε : ℂ) * I) = 0 :=
    hhoriz fun t ht ↦ by
      have hmem := hmem_sq (mul_nonneg ht.1 hε.le) (mul_le_of_le_one_left hε.le ht.2) hε.le le_rfl
      convert hmem using 1; ring
  have hleft : g (z₀ + (ε : ℂ) * I) - g z₀ = z₀.re * ε :=
    hvert fun t ht ↦ by
      simpa using hmem_sq le_rfl hε.le (mul_nonneg ht.1 hε.le) (mul_le_of_le_one_left hε.le ht.2)
  have hright : g (z₀ + (ε : ℂ) + (ε : ℂ) * I) - g (z₀ + (ε : ℂ)) = (z₀.re + ε) * ε := by
    have hv := hvert (p := z₀ + (ε : ℂ)) fun t ht ↦
      hmem_sq hε.le le_rfl (mul_nonneg ht.1 hε.le) (mul_le_of_le_one_left hε.le ht.2)
    simpa using hv
  have hcomm : z₀ + (ε : ℂ) * I + (ε : ℂ) = z₀ + (ε : ℂ) + (ε : ℂ) * I := by ring
  rw [hcomm] at htop
  nlinarith

/-! ### 3. The non-`C¹` covector field `d(|x|^(3/2))` on `ℝ` -/

/-- The `C¹` potential `x ↦ |x| ^ (3 / 2) = |x| * √|x|` on `ℝ`. -/
def absPowThreeHalvesPotential (x : ℝ) : ℝ :=
  |x| * Real.sqrt |x|

/-- `absPowThreeHalvesPotential x` equals `|x| ^ ((3 : ℝ) / 2)`. -/
theorem absPowThreeHalvesPotential_eq_rpow (x : ℝ) :
    absPowThreeHalvesPotential x = |x| ^ ((3 : ℝ) / 2) := by
  have hsplit : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
  rw [absPowThreeHalvesPotential, Real.sqrt_eq_rpow, hsplit,
    Real.rpow_add' (abs_nonneg x) (by norm_num), Real.rpow_one]

/-- Scalar derivative `(3 / 2) * sgn(x) * √|x|` of `x ↦ |x| ^ (3 / 2)`. -/
def absPowThreeHalvesDeriv (x : ℝ) : ℝ :=
  if 0 ≤ x then (3 / 2) * Real.sqrt x else -(3 / 2) * Real.sqrt (-x)

/-- The covector field `d(|x|^(3/2))` on `ℝ`. -/
def absPowThreeHalvesForm (x : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (absPowThreeHalvesDeriv x)

/-- `absPowThreeHalvesPotential` has scalar derivative `absPowThreeHalvesDeriv x` at every `x`. -/
theorem hasDerivAt_absPowThreeHalvesPotential (x : ℝ) :
    HasDerivAt absPowThreeHalvesPotential (absPowThreeHalvesDeriv x) x := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · have hpos : absPowThreeHalvesDeriv x = (3 / 2) * Real.sqrt x := by
      simp [absPowThreeHalvesDeriv, hx.le]
    rw [hpos]
    have heq : absPowThreeHalvesPotential =ᶠ[𝓝 x] fun y ↦ y * Real.sqrt y := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [absPowThreeHalvesPotential, abs_of_pos hy]
    have hd : HasDerivAt (fun y : ℝ ↦ y * Real.sqrt y)
        (1 * Real.sqrt x + x * (1 / (2 * Real.sqrt x))) x :=
      (hasDerivAt_id x).mul (Real.hasDerivAt_sqrt hx.ne')
    have hval : 1 * Real.sqrt x + x * (1 / (2 * Real.sqrt x)) = (3 / 2) * Real.sqrt x := by
      have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
      have hne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
      field_simp [hne]
      nlinarith
    rw [hval] at hd
    exact hd.congr_of_eventuallyEq heq
  · have h0 : absPowThreeHalvesDeriv 0 = 0 := by simp [absPowThreeHalvesDeriv]
    rw [h0, hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.isLittleO_iff.mpr fun c hc ↦ ?_
    have hcont : Continuous fun h : ℝ ↦ Real.sqrt |h| := Real.continuous_sqrt.comp continuous_abs
    have htend : Tendsto (fun h : ℝ ↦ Real.sqrt |h|) (𝓝 0) (𝓝 0) := by
      simpa using (hcont.continuousAt (x := 0)).tendsto
    filter_upwards [htend (Iio_mem_nhds hc)] with h hh
    simp only [zero_add, absPowThreeHalvesPotential, abs_zero, zero_mul, sub_zero, smul_zero,
      Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (le_of_lt hh) (abs_nonneg h)
  · have hneg : ¬ (0 ≤ x) := not_le.mpr hx
    have hval : absPowThreeHalvesDeriv x = -(3 / 2) * Real.sqrt (-x) := by
      simp [absPowThreeHalvesDeriv, hneg]
    rw [hval]
    have hx_pos : 0 < -x := neg_pos.mpr hx
    have heq : absPowThreeHalvesPotential =ᶠ[𝓝 x] fun y ↦ (-y) * Real.sqrt (-y) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [absPowThreeHalvesPotential, abs_of_neg hy]
    have hd_inner : HasDerivAt (fun u : ℝ ↦ u * Real.sqrt u)
        (1 * Real.sqrt (-x) + (-x) * (1 / (2 * Real.sqrt (-x)))) (-x) :=
      (hasDerivAt_id (-x)).mul (Real.hasDerivAt_sqrt hx_pos.ne')
    have hd_comp : HasDerivAt (fun y : ℝ ↦ (-y) * Real.sqrt (-y))
        ((1 * Real.sqrt (-x) + (-x) * (1 / (2 * Real.sqrt (-x)))) * (-1)) x :=
      hd_inner.comp x (hasDerivAt_neg x)
    have hsimp : (1 * Real.sqrt (-x) + (-x) * (1 / (2 * Real.sqrt (-x)))) * (-1) =
        -(3 / 2) * Real.sqrt (-x) := by
      have hsq : Real.sqrt (-x) * Real.sqrt (-x) = -x := Real.mul_self_sqrt hx_pos.le
      have hne : Real.sqrt (-x) ≠ 0 := (Real.sqrt_pos.mpr hx_pos).ne'
      field_simp [hne]
      nlinarith
    rw [hsimp] at hd_comp
    exact hd_comp.congr_of_eventuallyEq heq

/-- The scalar derivative `absPowThreeHalvesDeriv` is continuous on `ℝ`. -/
theorem continuous_absPowThreeHalvesDeriv : Continuous absPowThreeHalvesDeriv := by
  refine continuous_if_le continuous_const continuous_id
    (Continuous.continuousOn (by fun_prop)) (Continuous.continuousOn (by fun_prop)) ?_
  intro x hx
  subst hx
  simp

/-- The potential `x ↦ |x| ^ (3 / 2)` is `C¹` on `ℝ`. -/
theorem contDiff_absPowThreeHalvesPotential : ContDiff ℝ 1 absPowThreeHalvesPotential := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (hasDerivAt_absPowThreeHalvesPotential x).differentiableAt, ?_⟩
  have hfderiv : fderiv ℝ absPowThreeHalvesPotential = absPowThreeHalvesForm :=
    funext fun x ↦ (hasDerivAt_absPowThreeHalvesPotential x).hasFDerivAt.fderiv
  rw [hfderiv]
  have hlin : Continuous fun c : ℝ ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous
  exact hlin.comp continuous_absPowThreeHalvesDeriv

/-- `d(|x|^(3/2))` has local `C¹` potentials on all of `ℝ`. -/
theorem hasLocalPotentials_absPowThreeHalvesForm :
    HasLocalPotentials (univ : Set ℝ) absPowThreeHalvesForm :=
  hasLocalPotentials_of_hasFDerivAt isOpen_univ contDiff_absPowThreeHalvesPotential.contDiffOn
    fun x _ ↦ (hasDerivAt_absPowThreeHalvesPotential x).hasFDerivAt

/-- Nevertheless, `d(|x|^(3/2))` is not differentiable at `0` (hence not `C¹` on `ℝ`). -/
theorem not_differentiableAt_absPowThreeHalvesForm_zero :
    ¬ DifferentiableAt ℝ absPowThreeHalvesForm 0 := by
  intro hdiff
  have hscalar : DifferentiableAt ℝ absPowThreeHalvesDeriv 0 := by
    have happ := ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiableAt.comp 0 hdiff)
    simpa [Function.comp_def, absPowThreeHalvesForm] using happ
  let L : ℝ := deriv absPowThreeHalvesDeriv 0
  have hL := hscalar.hasDerivAt.tendsto_slope_zero
  obtain ⟨δ, hδ, hdist⟩ := Metric.tendsto_nhdsWithin_nhds.mp hL 1 zero_lt_one
  have hden : 0 < |L| + 2 := by positivity
  set s : ℝ := min (Real.sqrt (δ / 2)) (1 / (|L| + 2))
  have hs_pos : 0 < s := lt_min (Real.sqrt_pos.mpr (half_pos hδ)) (by positivity)
  set t : ℝ := s ^ 2
  have ht_pos : 0 < t := sq_pos_of_pos hs_pos
  have ht_lt_δ : t < δ := by
    have hs_le : s ≤ Real.sqrt (δ / 2) := min_le_left _ _
    have ht_le : t ≤ δ / 2 := by
      calc s ^ 2 ≤ Real.sqrt (δ / 2) ^ 2 := sq_le_sq' (by linarith) hs_le
        _ = δ / 2 := Real.sq_sqrt (half_pos hδ).le
    linarith
  have hclose := hdist ht_pos.ne' (by simpa [Real.dist_eq, abs_of_pos ht_pos] using ht_lt_δ)
  have hsqrt_t : Real.sqrt t = s := Real.sqrt_sq hs_pos.le
  have hval : t⁻¹ • (absPowThreeHalvesDeriv (0 + t) - absPowThreeHalvesDeriv 0) = (3 / 2) / s := by
    simp only [zero_add, absPowThreeHalvesDeriv, ht_pos.le, ↓reduceIte, le_rfl, Real.sqrt_zero,
      mul_zero, sub_zero, smul_eq_mul, hsqrt_t, t]
    field_simp [hs_pos.ne']
  rw [hval, Real.dist_eq] at hclose
  have hs_ub : s ≤ 1 / (|L| + 2) := min_le_right _ _
  have hbig : (3 / 2) * (|L| + 2) ≤ (3 / 2) / s := by
    rw [le_div_iff₀ hs_pos]
    have hmul := mul_le_mul_of_nonneg_left hs_ub (by positivity : (0 : ℝ) ≤ (3 / 2) * (|L| + 2))
    have hrhs : (3 / 2) * (|L| + 2) * (1 / (|L| + 2)) = 3 / 2 := by field_simp [hden.ne']
    linarith
  have habs := (abs_lt.mp hclose).2
  have hL_le : L ≤ |L| := le_abs_self L
  linarith

/-! ### 4. The punctured-plane angular form `(x dy - y dx) / (x² + y²)` -/

/-- The planar angular `1`-form `(x dy - y dx) / (x² + y²)` on `ℂ`, defined as the imaginary part
of `w ↦ w • z⁻¹`. -/
def planarAngularForm (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp ((toSpanSingleton ℂ z⁻¹).restrictScalars ℝ)

/-- Explicit coordinate formula `(z.re * w.im - z.im * w.re) / Complex.normSq z`. -/
theorem planarAngularForm_apply (z w : ℂ) :
    planarAngularForm z w = (z.re * w.im - z.im * w.re) / Complex.normSq z := by
  simp only [planarAngularForm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', toSpanSingleton_apply, smul_eq_mul,
    Complex.imCLM_apply, Complex.mul_im, Complex.inv_re, Complex.inv_im]
  ring

/-- `Complex.arg` has Fréchet derivative `planarAngularForm z` at every `z ∈ Complex.slitPlane`. -/
theorem hasFDerivAt_arg_planarAngularForm {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasFDerivAt Complex.arg (planarAngularForm z) z := by
  have heq : Complex.arg = Complex.imCLM ∘ Complex.log := funext fun w ↦ (Complex.log_im w).symm
  rw [heq]
  exact Complex.imCLM.hasFDerivAt.comp z ((Complex.hasDerivAt_log hz).hasFDerivAt.restrictScalars ℝ)

/-- `Complex.arg` is smooth (`C^∞`, hence `C¹`) on `Complex.slitPlane`. -/
theorem contDiffOn_arg_slitPlane {n : WithTop ℕ∞} :
    ContDiffOn ℝ n Complex.arg Complex.slitPlane := by
  have heq : Complex.arg = Complex.imCLM ∘ Complex.log := funext fun w ↦ (Complex.log_im w).symm
  rw [heq]
  refine Complex.imCLM.contDiff.comp_contDiffOn ?_
  exact fun z hz ↦ ((Complex.contDiffAt_log hz).restrict_scalars ℝ).contDiffWithinAt

/-- On `Complex.slitPlane`, `planarAngularForm` has local `C¹` potentials with global potential
`Complex.arg`. -/
theorem hasLocalPotentials_planarAngularForm_slitPlane :
    HasLocalPotentials Complex.slitPlane planarAngularForm :=
  hasLocalPotentials_of_hasFDerivAt Complex.isOpen_slitPlane contDiffOn_arg_slitPlane
    fun _ hz ↦ hasFDerivAt_arg_planarAngularForm hz

/-- On the opposite slit plane `{z | -z ∈ Complex.slitPlane}`, the shifted branch
`z ↦ Complex.arg (-z)` is `C¹` and differentiates to `planarAngularForm z`. -/
theorem hasFDerivAt_arg_neg_planarAngularForm {z : ℂ} (hz : -z ∈ Complex.slitPlane) :
    HasFDerivAt (fun w ↦ Complex.arg (-w)) (planarAngularForm z) z := by
  have hcomp := (hasFDerivAt_arg_planarAngularForm hz).comp z (hasFDerivAt_id z).neg
  refine hcomp.congr_fderiv ?_
  ext w
  simp [planarAngularForm_apply]
  ring

/-- The angular `1`-form has local `C¹` potentials on the entire punctured plane `{0}ᶜ`. -/
theorem hasLocalPotentials_planarAngularForm :
    HasLocalPotentials ({0}ᶜ : Set ℂ) planarAngularForm :=
  (hasLocalPotentials_toSpanSingleton_iff.mpr
    ⟨isOpen_compl_singleton, differentiableOn_inv⟩).continuousLinearMap_comp Complex.imCLM

/-- Counterclockwise parametrization `t ↦ exp(2π i t)` of the unit circle as a loop at `1`. -/
def unitCircleLoop : Path (1 : ℂ) 1 where
  toFun t := Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    change Complex.exp (2 * Real.pi * (1 : ℝ) * Complex.I) = 1
    simp

private theorem exp_mul_I_mem_slitPlane_of_mem_Icc {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    Complex.exp ((θ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases eq_or_lt_of_le hθ.1 with rfl | hgt
  · right
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg, Real.sin_pi_div_two]
    norm_num
  · rcases eq_or_lt_of_le hθ.2 with rfl | hlt
    · right
      rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two]
      norm_num
    · left
      rw [Complex.exp_ofReal_mul_I_re]
      exact Real.cos_pos_of_mem_Ioo ⟨hgt, hlt⟩

/-- The `ℂ`-linear `1`-form `dz / z` integrates around the unit circle once counterclockwise to
`2π i`, evaluated via branches of `Complex.log` on `Complex.slitPlane` and `-Complex.slitPlane`. -/
theorem localPotentialIntegral_toSpanSingleton_inv_unitCircleLoop :
    localPotentialIntegral (fun z : ℂ ↦ (toSpanSingleton ℂ z⁻¹).restrictScalars ℝ)
      unitCircleLoop = 2 * Real.pi * Complex.I := by
  let t : ℕ → unitInterval := fun k ↦
    match k with
    | 0 => 0
    | 1 => ⟨1 / 4, by norm_num⟩
    | 2 => ⟨3 / 4, by norm_num⟩
    | _ => 1
  have hmono : Monotone t := by
    intro i j hij
    match i, j with
    | 0, _ => exact (t _).2.1
    | 1, 0 => omega
    | 1, 1 => exact le_rfl
    | 1, 2 => exact Subtype.mk_le_mk.mpr (by norm_num)
    | 1, _ + 3 => exact Subtype.mk_le_mk.mpr (by norm_num)
    | 2, 0 => omega
    | 2, 1 => omega
    | 2, 2 => exact le_rfl
    | 2, _ + 3 => exact Subtype.mk_le_mk.mpr (by norm_num)
    | _ + 3, 0 => omega
    | _ + 3, 1 => omega
    | _ + 3, 2 => omega
    | _ + 3, _ + 3 => exact le_rfl
  let U : ℕ → Set ℂ := fun k ↦
    if k = 1 then {z : ℂ | -z ∈ Complex.slitPlane} else Complex.slitPlane
  let g : ℕ → ℂ → ℂ := fun k ↦
    if k = 1 then fun z ↦ Complex.log (-z) else Complex.log
  have hU : ∀ i < 3, IsOpen (U i) := by
    intro i _
    simp only [U]
    split_ifs
    · exact Complex.isOpen_slitPlane.preimage continuous_neg
    · exact Complex.isOpen_slitPlane
  have hd : ∀ i < 3, ∀ z ∈ U i,
      HasFDerivAt (g i) ((toSpanSingleton ℂ z⁻¹).restrictScalars ℝ) z := by
    intro i _ z hz
    simp only [U, g] at hz ⊢
    split_ifs at hz ⊢
    · have hlog : HasDerivAt (fun w : ℂ ↦ Complex.log (-w)) z⁻¹ z :=
        ((Complex.hasDerivAt_log hz).comp z (hasDerivAt_neg z)).congr_deriv
          (by rw [← neg_inv]; ring)
      exact hlog.hasFDerivAt.restrictScalars ℝ
    · exact (Complex.hasDerivAt_log hz).hasFDerivAt.restrictScalars ℝ
  have hmaps : ∀ i < 3, MapsTo unitCircleLoop (Icc (t i) (t (i + 1))) (U i) := by
    intro i hi τ hτ
    match i with
    | 0 =>
      change unitCircleLoop τ ∈ Complex.slitPlane
      have h0 : (0 : ℝ) ≤ τ := hτ.1
      have h1 : (τ : ℝ) ≤ 1 / 4 := hτ.2
      have hθ : 2 * Real.pi * (τ : ℝ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      simpa [unitCircleLoop] using exp_mul_I_mem_slitPlane_of_mem_Icc hθ
    | 1 =>
      change -unitCircleLoop τ ∈ Complex.slitPlane
      have h0 : (1 : ℝ) / 4 ≤ τ := hτ.1
      have h1 : (τ : ℝ) ≤ 3 / 4 := hτ.2
      have hneg_exp : -unitCircleLoop τ =
          Complex.exp (((2 * Real.pi * (τ : ℝ) - Real.pi : ℝ) : ℂ) * Complex.I) := by
        change -Complex.exp (2 * Real.pi * (τ : ℝ) * Complex.I) = _
        rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I, div_neg, div_one]
        push_cast; rfl
      rw [hneg_exp]
      exact exp_mul_I_mem_slitPlane_of_mem_Icc
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    | 2 =>
      change unitCircleLoop τ ∈ Complex.slitPlane
      have h0 : (3 : ℝ) / 4 ≤ τ := hτ.1
      have h1 : (τ : ℝ) ≤ 1 := hτ.2
      have hper : unitCircleLoop τ =
          Complex.exp (((2 * Real.pi * (τ : ℝ) - 2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
        change Complex.exp (2 * Real.pi * (τ : ℝ) * Complex.I) = _
        rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub,
          show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I by push_cast; ring,
          Complex.exp_two_pi_mul_I, div_one]
        push_cast; rfl
      rw [hper]
      exact exp_mul_I_mem_slitPlane_of_mem_Icc
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    | _ + 3 => omega
  have hquarter : unitCircleLoop (t 1) = Complex.I := by
    change Complex.exp (2 * Real.pi * (1 / 4 : ℝ) * Complex.I) = Complex.I
    have hq : (2 : ℂ) * Real.pi * ((1 / 4 : ℝ) : ℂ) * Complex.I = (Real.pi / 2) * Complex.I := by
      push_cast; ring
    rw [hq, Complex.exp_pi_div_two_mul_I]
  have hthree : unitCircleLoop (t 2) = -Complex.I := by
    change Complex.exp (2 * Real.pi * (3 / 4 : ℝ) * Complex.I) = -Complex.I
    have hq : (2 : ℂ) * Real.pi * ((3 / 4 : ℝ) : ℂ) * Complex.I =
        Real.pi * Complex.I + (Real.pi / 2) * Complex.I := by
      push_cast; ring
    rw [hq, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
    ring
  rw [localPotentialIntegral_eq_sum_sub_of_hasFDerivAt (n := 3) (t := t) rfl hmono rfl hU hd hmaps]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have ht0 : unitCircleLoop (t 0) = 1 := unitCircleLoop.source
  have ht3 : unitCircleLoop (t 3) = 1 := unitCircleLoop.target
  rw [ht0, hquarter, hthree, ht3]
  simp only [g, ↓reduceIte, Nat.reduceEqDiff, neg_neg, Complex.log_one,
    Complex.log_I, Complex.log_neg_I]
  ring

/-- The potential integral of the planar angular form around the unit circle once counterclockwise
is `2π`, obtained as the imaginary part of
`localPotentialIntegral_toSpanSingleton_inv_unitCircleLoop`. -/
theorem localPotentialIntegral_planarAngularForm_unitCircleLoop :
    localPotentialIntegral planarAngularForm unitCircleLoop = 2 * Real.pi := by
  have hpot : HasLocalPotentials ({0}ᶜ : Set ℂ)
      (fun z : ℂ ↦ (toSpanSingleton ℂ z⁻¹).restrictScalars ℝ) :=
    hasLocalPotentials_toSpanSingleton_iff.mpr ⟨isOpen_compl_singleton, differentiableOn_inv⟩
  have h := hpot.localPotentialIntegral_continuousLinearMap_comp Complex.imCLM
    (γ := unitCircleLoop) (fun τ ↦ Complex.exp_ne_zero _)
  unfold planarAngularForm
  simpa [localPotentialIntegral_toSpanSingleton_inv_unitCircleLoop] using h

/-- Traversing the unit circle twice counterclockwise yields `4π`. -/
theorem localPotentialIntegral_planarAngularForm_unitCircleLoop_twice :
    localPotentialIntegral planarAngularForm (unitCircleLoop.trans unitCircleLoop) =
      4 * Real.pi := by
  have hmem : ∀ τ, unitCircleLoop τ ∈ ({0}ᶜ : Set ℂ) :=
    fun τ ↦ Complex.exp_ne_zero _
  rw [hasLocalPotentials_planarAngularForm.localPotentialIntegral_trans hmem hmem,
    localPotentialIntegral_planarAngularForm_unitCircleLoop]
  ring

/-- Reversing the unit circle loop yields `-2π`. -/
theorem localPotentialIntegral_planarAngularForm_unitCircleLoop_symm :
    localPotentialIntegral planarAngularForm unitCircleLoop.symm = -(2 * Real.pi) := by
  rw [localPotentialIntegral_symm, localPotentialIntegral_planarAngularForm_unitCircleLoop]

/-- Despite having local `C¹` potentials everywhere on `{0}ᶜ`, the planar angular form admits *no*
global primitive on `{0}ᶜ`. -/
theorem not_exists_hasFDerivAt_planarAngularForm_compl_zero :
    ¬ ∃ g : ℂ → ℝ, ∀ z ∈ ({0}ᶜ : Set ℂ), HasFDerivAt g (planarAngularForm z) z := by
  rintro ⟨g, hg⟩
  have hmem : ∀ τ, unitCircleLoop τ ∈ ({0}ᶜ : Set ℂ) := fun τ ↦ Complex.exp_ne_zero _
  have h0 : localPotentialIntegral planarAngularForm unitCircleLoop = 0 := by
    rw [localPotentialIntegral_eq_sub_of_hasFDerivAt isOpen_compl_singleton hg hmem, sub_self]
  rw [localPotentialIntegral_planarAngularForm_unitCircleLoop] at h0
  exact Real.two_pi_pos.ne' h0

/-- On the simply connected slit plane `Complex.slitPlane`, `z ↦ z⁻¹` is exact
(`Complex.IsExactOn`), recovering the existence of a holomorphic logarithm from
`DifferentiableOn.isExactOn_of_simplyConnected`. -/
theorem isExactOn_inv_slitPlane : Complex.IsExactOn (fun z : ℂ ↦ z⁻¹) Complex.slitPlane := by
  have : ContractibleSpace Complex.slitPlane :=
    Complex.starConvex_one_slitPlane.contractibleSpace ⟨1, Complex.one_mem_slitPlane⟩
  exact (differentiableOn_inv.mono fun _ hz ↦
    Complex.slitPlane_ne_zero hz).isExactOn_of_simplyConnected Complex.isOpen_slitPlane

/-- On `{0}ᶜ`, which is not simply connected, `z ↦ z⁻¹` has no global complex primitive. -/
theorem not_isExactOn_inv_compl_zero : ¬ Complex.IsExactOn (fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ) := by
  rintro ⟨G, hG⟩
  refine not_exists_hasFDerivAt_planarAngularForm_compl_zero
    ⟨fun z ↦ (G z).im, fun z hz ↦ ?_⟩
  exact Complex.imCLM.hasFDerivAt.comp z ((hG z hz).hasFDerivAt.restrictScalars ℝ)

end TauCeti
