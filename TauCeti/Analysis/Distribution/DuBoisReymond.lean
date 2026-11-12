/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The du Bois-Reymond lemma on an interval

A function on an open interval whose distributional derivative vanishes is constant. Concretely,
if `f : ℝ → F` is locally integrable on `Ioo a b` and

`∫ x, deriv ψ x • f x = 0`

for every smooth `ψ : ℝ → ℝ` with `tsupport ψ ⊆ Ioo a b`, then `f` is almost everywhere equal to a
constant on `Ioo a b`, and constant there if it is continuous on `Ioo a b`. This is the
one-variable **du Bois-Reymond lemma**, the derivative form of the fundamental lemma of the
calculus of variations, whose zeroth-order form is Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

The reduction to the zeroth-order lemma is the classical one. Fix a test function `ρ` on the
interval with total integral `1`. For a test function `g`, the function `g - (∫ g) ρ` has total
integral zero, so its primitive `ψ` is again a test function on the interval, with `deriv ψ = g -
(∫ g) ρ`; the hypothesis applied to `ψ` gives `∫ g • f = (∫ g) • ∫ ρ • f`, that is
`∫ g • (f - c) = 0` for the constant `c = ∫ ρ • f`. Hence `f = c` almost everywhere on the
interval, and everywhere if `f` is continuous.

The one-sided version says that a continuous real function whose distributional derivative is
nonnegative is monotone: if `∫ x, deriv ψ x * f x ≤ 0` for every nonnegative test function `ψ` on
the interval, then `f` is monotone there. For `x ≤ y` in the interval, take `ψ` to be the
difference of the primitives of two copies of a narrow bump of integral one, centred at `x` and at
`y`; then `ψ ≥ 0`, and `∫ ψ' f` is the difference of the averages of `f` against the two bumps,
which are close to `f x` and `f y` by continuity. Without continuity the same argument applies at
almost every pair of points: by the Lebesgue differentiation theorem, in the form
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`, the averages of `f` against
bumps shrinking to `x` converge to `f x` for almost every `x`. So a locally integrable function
with nonnegative distributional derivative is monotone on a subset of the interval of full measure.
More generally, if `F' + g ≤ 0` in the sense of distributions, with `g` integrable on the
interval, then `F + ∫ g` is antitone on a subset of full measure: the primitive `∫ g` has
distributional derivative `g`.

## Main declarations

* `ContDiff.exists_contDiff_deriv_eq_of_integral_eq_zero`: the primitive of a test function on
  an interval with total integral zero is a test function on the interval.
* `MeasureTheory.LocallyIntegrableOn.exists_ae_eq_const_Ioo_of_integral_deriv_smul_eq_zero`:
  **the du Bois-Reymond lemma**.
* `ContinuousOn.exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero`: its form for continuous
  functions.
* `ContinuousOn.monotoneOn_of_integral_deriv_mul_nonpos`: a continuous function with nonnegative
  distributional derivative is monotone.
* `MeasureTheory.LocallyIntegrableOn.exists_monotoneOn_of_integral_deriv_mul_nonpos`: a locally
  integrable function with nonnegative distributional derivative is monotone on a subset of full
  measure.
* `MeasureTheory.LocallyIntegrableOn.exists_antitoneOn_add_intervalIntegral_of_integral_mul_le`:
  if `F' + g ≤ 0` in the sense of distributions, then `F + ∫ g` is antitone on a subset of full
  measure.
-/

public section

namespace TauCeti

open MeasureTheory Set Filter Topology _root_.intervalIntegral
open scoped ContDiff

/-- **The primitive of a mean-zero test function is a test function.** If `φ : ℝ → ℝ` is smooth
with `tsupport φ ⊆ Ioo a b` and `∫ φ = 0`, then `φ` is the derivative of a smooth function `ψ` with
`tsupport ψ ⊆ Ioo a b`. Such a `ψ` has compact support, since `Ioo a b` is bounded. -/
theorem _root_.ContDiff.exists_contDiff_deriv_eq_of_integral_eq_zero {a b : ℝ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo a b) (hint : ∫ x, φ x = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ Ioo a b ∧ deriv ψ = φ := by
  have hφc : Continuous φ := hφ.continuous
  have hφ0 : ∀ x, x ∉ Ioo a b → φ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφs h)
  rcases le_or_gt b a with hba | hab
  · -- The interval is empty, so `φ = 0` and `ψ = 0` works.
    have hφ0' : φ = 0 := funext fun x ↦ hφ0 x (by simp [Ioo_eq_empty (not_lt.mpr hba)])
    exact ⟨0, contDiff_const, by simp, by simp [hφ0']⟩
  -- The primitive of `φ` based at `a`.
  set ψ : ℝ → ℝ := fun t ↦ ∫ s in a..t, φ s
  have hderiv : ∀ t, HasDerivAt ψ (φ t) t := fun t ↦
    integral_hasDerivAt_right (hφc.intervalIntegrable _ _) (hφc.stronglyMeasurableAtFilter _ _)
      hφc.continuousAt
  have hψd : deriv ψ = φ := funext fun t ↦ (hderiv t).deriv
  have hψ : ContDiff ℝ ∞ ψ :=
    contDiff_infty_iff_deriv.mpr ⟨fun t ↦ (hderiv t).differentiableAt, hψd ▸ hφ⟩
  -- `φ` vanishes near both endpoints, so the primitive vanishes near them as well.
  obtain ⟨εa, hεa, hφa⟩ := Metric.eventually_nhds_iff.mp
    (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ (hφs h).1.ne rfl)
  obtain ⟨εb, hεb, hφb⟩ := Metric.eventually_nhds_iff.mp
    (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ (hφs h).2.ne rfl)
  have hleft : ∀ t, t < a + εa → ψ t = 0 := fun t ht ↦
    integral_eq_zero_of_lt_add (fun x hx ↦ hφ0 x fun h ↦ h.1.not_ge hx) hφa ht
  have hright : ∀ t, b - εb < t → ψ t = 0 := fun t ht ↦ by
    -- The integral over the whole interval is `∫ φ = 0`, and the integral from `t` to `b` vanishes
    -- by the left-endpoint argument applied to `φ` reflected about `0`.
    have hab0 : ∫ s in a..b, φ s = 0 := by
      rw [integral_of_le hab.le, setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦
        hφ0 s fun h ↦ hs (mem_Ioc.mpr ⟨h.1, h.2.le⟩), hint]
    have htb : ∫ s in t..b, φ s = 0 := by
      rw [← neg_neg t, ← neg_neg b, ← integral_comp_neg]
      exact integral_eq_zero_of_lt_add (fun x hx ↦ hφ0 _ fun h ↦ h.2.not_ge (le_neg.mp hx))
        (fun y hy ↦ hφb (by rwa [← dist_neg_neg, neg_neg])) (by linarith)
    have := integral_add_adjacent_intervals (hφc.intervalIntegrable (μ := volume) a t)
      (hφc.intervalIntegrable t b)
    rwa [htb, add_zero, hab0] at this
  have hsupp : tsupport ψ ⊆ Icc (a + εa) (b - εb) := closure_minimal
    (fun t ht ↦ ⟨not_lt.mp fun h ↦ ht (hleft t h), not_lt.mp fun h ↦ ht (hright t h)⟩) isClosed_Icc
  exact ⟨ψ, hψ, hsupp.trans (Icc_subset_Ioo (lt_add_of_pos_right a hεa) (sub_lt_self b hεb)), hψd⟩

end TauCeti

namespace MeasureTheory.LocallyIntegrableOn

open Set Filter
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The du Bois-Reymond lemma.** A function locally integrable on an open interval whose
pairing with the derivative of every test function on the interval vanishes,
`∫ x, deriv ψ x • f x = 0`, is almost everywhere equal to a constant on the interval. -/
theorem exists_ae_eq_const_Ioo_of_integral_deriv_smul_eq_zero
    {a b : ℝ} {f : ℝ → F} (hf : LocallyIntegrableOn f (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → ∫ x, deriv ψ x • f x = 0) :
    ∃ c : F, f =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ c := by
  rcases le_or_gt b a with hba | hab
  · exact ⟨0, by simp [Ioo_eq_empty (not_lt.mpr hba), EventuallyEq]⟩
  -- A test function `g` on the interval pairs integrably with `f`.
  have hint : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo a b →
      Integrable fun x ↦ g x • f x := fun g hg hgc hgs ↦
    TestFunction.integrable_smul (Ω := ⟨Ioo a b, isOpen_Ioo⟩) ⟨g, hg, hgc, hgs⟩ hf
  -- A normalized bump function supported in the interval.
  let β : ContDiffBump ((a + b) / 2) := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  have hrOut : β.rOut = (b - a) / 4 := rfl
  set ρ : ℝ → ℝ := β.normed volume with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := β.contDiff_normed
  have hρc : HasCompactSupport ρ := β.hasCompactSupport_normed
  have hρs : tsupport ρ ⊆ Ioo a b := by
    rw [hρ_def, β.tsupport_normed_eq, hrOut, Real.closedBall_eq_Icc]
    exact Icc_subset_Ioo (by linarith) (by linarith)
  have hρint : ∫ x, ρ x = 1 := β.integral_normed
  refine ⟨∫ x, ρ x • f x, ?_⟩
  -- Every test function on the interval is orthogonal to `f - c`.
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo a b →
      ∫ x, g x • (f x - ∫ y, ρ y • f y) = 0 := by
    intro g hg hgc hgs
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
    set φ : ℝ → ℝ := fun x ↦ g x - (∫ y, g y) * ρ x with hφ_def
    have hφ : ContDiff ℝ ∞ φ := hg.sub (contDiff_const.mul hρ)
    have hφs : tsupport φ ⊆ Ioo a b :=
      (tsupport_sub _ _).trans (union_subset hgs (tsupport_mul_subset_right.trans hρs))
    have hφint : ∫ x, φ x = 0 := by
      simp only [hφ_def]
      rw [integral_sub hgi (hρi.const_mul _), MeasureTheory.integral_const_mul, hρint, mul_one,
        sub_self]
    obtain ⟨ψ, hψ, hψs, hψd⟩ := hφ.exists_contDiff_deriv_eq_of_integral_eq_zero hφs hφint
    have h0 := h ψ hψ hψs
    rw [hψd] at h0
    simp only [hφ_def, sub_smul, mul_smul] at h0
    have hρf : Integrable fun x ↦ (∫ y, g y) • ρ x • f x := (hint ρ hρ hρc hρs).smul _
    rw [integral_sub (hint g hg hgc hgs) hρf, MeasureTheory.integral_smul, sub_eq_zero] at h0
    simp only [smul_sub]
    rw [integral_sub (hint g hg hgc hgs) (hgi.smul_const _), _root_.integral_smul_const, h0,
      sub_self]
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.sub (locallyIntegrableOn_const _)) key
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mpr hae] with x hx
  exact sub_eq_zero.mp hx

end MeasureTheory.LocallyIntegrableOn

namespace TauCeti

open MeasureTheory Set Filter Topology _root_.intervalIntegral
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The du Bois-Reymond lemma** for continuous functions. A function continuous on an open
interval whose pairing with the derivative of every test function on the interval vanishes,
`∫ x, deriv ψ x • f x = 0`, is constant on the interval. -/
theorem _root_.ContinuousOn.exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero {a b : ℝ}
    {f : ℝ → F} (hf : ContinuousOn f (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → ∫ x, deriv ψ x • f x = 0) :
    ∃ c : F, EqOn f (fun _ ↦ c) (Ioo a b) := by
  have hf' := hf.locallyIntegrableOn (μ := volume) measurableSet_Ioo
  obtain ⟨c, hc⟩ := hf'.exists_ae_eq_const_Ioo_of_integral_deriv_smul_eq_zero h
  exact ⟨c, Measure.eqOn_open_of_ae_eq hc isOpen_Ioo hf continuousOn_const⟩

/-- For a nonnegative bump `β` of integral one vanishing outside `(-r, r)` and `x ≤ y`, the
difference `ψ t = B (t - x) - B (t - y)` of translates of the primitive `B` of `β` is a
nonnegative smooth function supported in `[x - r, y + r]` with `ψ' t = β (t - x) - β (t - y)`. -/
private lemma exists_nonneg_deriv_eq_sub_bump {β : ℝ → ℝ} {r : ℝ}
    (hβ : ContDiff ℝ ∞ β)
    (hβnn : ∀ t, 0 ≤ β t) (hβ0 : ∀ t, r ≤ |t| → β t = 0) (hβ1 : ∫ t, β t = 1) {x y : ℝ}
    (hxy : x ≤ y) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t, 0 ≤ ψ t) ∧ tsupport ψ ⊆ Icc (x - r) (y + r) ∧
      ∀ t, deriv ψ t = β (t - x) - β (t - y) := by
  -- `0 < r`, since otherwise `β` vanishes identically, contradicting `∫ β = 1`.
  have hr : 0 < r := by
    by_contra! hr
    simp [fun t ↦ hβ0 t (hr.trans (abs_nonneg t))] at hβ1
  -- The primitive `B` of `β`: monotone, `0` on `(-∞, -r]` and `1` on `[r, ∞)`.
  set B : ℝ → ℝ := fun t ↦ ∫ s in (-r)..t, β s with hB_def
  have hBderiv : ∀ t, HasDerivAt B (β t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hβ.continuous.intervalIntegrable _ _)
      (hβ.continuous.stronglyMeasurableAtFilter _ _) hβ.continuous.continuousAt
  have hderivB : deriv B = β := funext fun t ↦ (hBderiv t).deriv
  have hB : ContDiff ℝ ∞ B := contDiff_infty_iff_deriv.mpr
    ⟨fun t ↦ (hBderiv t).differentiableAt, hderivB ▸ hβ⟩
  have hBmono : Monotone B := monotone_of_deriv_nonneg (fun t ↦ (hBderiv t).differentiableAt)
    fun t ↦ (hBderiv t).deriv ▸ hβnn t
  have hBleft : ∀ t, t ≤ -r → B t = 0 := by
    intro t ht
    simp only [hB_def]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_ge ht] at hs
    exact hβ0 s (le_abs.mpr (Or.inr (by linarith [hs.2])))
  have hBright : ∀ t, r ≤ t → B t = 1 := by
    intro t ht
    simp only [hB_def]
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_, hβ1]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
    exact hβ0 s (le_abs.mpr (by grind))
  refine ⟨fun t ↦ B (t - x) - B (t - y),
    (hB.comp (contDiff_id.sub contDiff_const)).sub (hB.comp (contDiff_id.sub contDiff_const)),
    fun t ↦ sub_nonneg.mpr (hBmono (by linarith)), ?_, fun t ↦ ?_⟩
  · refine closure_minimal (fun t ht ↦ ⟨?_, ?_⟩) isClosed_Icc
    · by_contra h'
      exact ht (by simp [hBleft (t - x) (by linarith), hBleft (t - y) (by linarith)])
    · by_contra h'
      exact ht (by simp [hBright (t - x) (by linarith), hBright (t - y) (by linarith)])
  · exact (((hBderiv _).comp t ((hasDerivAt_id t).sub_const x)).sub
      ((hBderiv _).comp t ((hasDerivAt_id t).sub_const y))).deriv.trans (by simp)

/-- For a nonnegative bump `β` of integral one vanishing outside `(-r, r)`, and `f` continuous on
an open set containing `[z - r, z + r]` and within `η` of `f z` on `(z - r, z + r)`, the average
`∫ t, β (t - z) * f t` is within `η` of `f z`. -/
private lemma integral_bump_mul_mem_Icc {β f : ℝ → ℝ} {r z η : ℝ} {U : Set ℝ}
    (hβ : Continuous β) (hβnn : ∀ t, 0 ≤ β t) (hβ0 : ∀ t, r ≤ |t| → β t = 0)
    (hβ1 : ∫ t, β t = 1) (hf : ContinuousOn f U) (hU : IsOpen U) (hzU : Icc (z - r) (z + r) ⊆ U)
    (hfz : ∀ t, |t - z| < r → |f t - f z| < η) :
    Integrable (fun t ↦ β (t - z) * f t) ∧ ∫ t, β (t - z) * f t ∈ Icc (f z - η) (f z + η) := by
  have hts : tsupport (fun t ↦ β (t - z)) ⊆ Icc (z - r) (z + r) := by
    refine closure_minimal (fun t ht ↦ ?_) isClosed_Icc
    rw [← Real.closedBall_eq_Icc, Metric.mem_closedBall, Real.dist_eq]
    exact (not_le.mp (mt (hβ0 _) ht)).le
  have hcs : HasCompactSupport fun t ↦ β (t - z) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts
  have hcont : Continuous fun t ↦ β (t - z) * f t :=
    ((hβ.comp (continuous_sub_right z)).continuousOn.mul hf).continuous_of_tsupport_subset hU
      ((tsupport_mul_subset_left).trans (hts.trans hzU))
  have hI : Integrable fun t ↦ β (t - z) * f t :=
    hcont.integrable_of_hasCompactSupport hcs.mul_right
  have hβz : Integrable fun t ↦ β (t - z) :=
    (hβ.comp (continuous_sub_right z)).integrable_of_hasCompactSupport hcs
  have hconst : ∀ c, ∫ t, β (t - z) * c = c := fun c ↦ by
    rw [MeasureTheory.integral_mul_const, integral_sub_right_eq_self, hβ1, one_mul]
  -- Pointwise, `β (t - z) * f t` lies between `β (t - z) * (f z ∓ η)`.
  have hpt : ∀ t, |β (t - z) * f t - β (t - z) * f z| ≤ β (t - z) * η := fun t ↦ by
    by_cases ht : |t - z| < r
    · rw [← mul_sub, abs_mul, abs_of_nonneg (hβnn _)]
      exact mul_le_mul_of_nonneg_left (hfz t ht).le (hβnn _)
    · simp [hβ0 _ (not_lt.mp ht)]
  refine ⟨hI, ?_, ?_⟩
  · conv_lhs => rw [← hconst (f z - η)]
    refine integral_mono (hβz.mul_const _) hI fun t ↦ ?_
    have := (abs_le.mp (hpt t)).1
    simp only [mul_sub]
    linarith
  · conv_rhs => rw [← hconst (f z + η)]
    refine integral_mono hI (hβz.mul_const _) fun t ↦ ?_
    have := (abs_le.mp (hpt t)).2
    simp only [mul_add]
    linarith

/-- **The monotone du Bois-Reymond lemma.** A real function continuous on an open interval whose
distributional derivative is nonnegative, in the sense that `∫ x, deriv ψ x * f x ≤ 0` for every
nonnegative test function `ψ` on the interval, is monotone on the interval. -/
theorem _root_.ContinuousOn.monotoneOn_of_integral_deriv_mul_nonpos {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → (∀ x, 0 ≤ ψ x) →
      ∫ x, deriv ψ x * f x ≤ 0) :
    MonotoneOn f (Ioo a b) := by
  intro x hx y hy hxy
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  -- A radius `r` such that, near `x` and near `y`, `f` stays within `η / 2` of its value at the
  -- centre, and the closed `r`-neighbourhoods of `x` and `y` lie in the interval.
  have hnear : ∀ z ∈ Ioo a b, ∃ r > 0, Icc (z - r) (z + r) ⊆ Ioo a b ∧
      ∀ t, |t - z| < r → |f t - f z| < η / 2 := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((isOpen_Ioo.eventually_mem hz).and
      ((hf.continuousAt (isOpen_Ioo.mem_nhds hz)).eventually
        (Metric.ball_mem_nhds _ (half_pos hη))))
    refine ⟨ε / 2, half_pos hε, fun t ht ↦ (hball ?_).1, fun t ht ↦ ?_⟩
    · rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [ht.1, ht.2]
    · simpa [Real.dist_eq] using (hball (by rw [Real.dist_eq]; linarith)).2
  obtain ⟨rx, hrx, hxsub, hfx⟩ := hnear x hx
  obtain ⟨ry, hry, hysub, hfy⟩ := hnear y hy
  set r := min rx ry
  have hr : 0 < r := lt_min hrx hry
  have hrx' : r ≤ rx := min_le_left _ _
  have hry' : r ≤ ry := min_le_right _ _
  -- A nonnegative bump `β` of integral one vanishing outside `(-r, r)`.
  let β₀ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set β : ℝ → ℝ := β₀.normed volume with hβ_def
  have hβ0 : ∀ t, r ≤ |t| → β t = 0 := fun t ht ↦ Function.notMem_support.mp <| by
    simpa [hβ_def, β₀.support_normed_eq] using ht
  obtain ⟨ψ, hψ, hψnn, hψs, hψd⟩ := exists_nonneg_deriv_eq_sub_bump β₀.contDiff_normed
    β₀.nonneg_normed hβ0 β₀.integral_normed hxy
  obtain ⟨hIx, hx1, -⟩ := integral_bump_mul_mem_Icc β₀.continuous_normed β₀.nonneg_normed hβ0
    β₀.integral_normed hf isOpen_Ioo
    ((Icc_subset_Icc (by linarith) (by linarith)).trans hxsub) fun t ht ↦ hfx t (by linarith)
  obtain ⟨hIy, -, hy2⟩ := integral_bump_mul_mem_Icc β₀.continuous_normed β₀.nonneg_normed hβ0
    β₀.integral_normed hf isOpen_Ioo
    ((Icc_subset_Icc (by linarith) (by linarith)).trans hysub) fun t ht ↦ hfy t (by linarith)
  have h0 := h ψ hψ (hψs.trans (Icc_subset_Ioo
    (hxsub ⟨by linarith, by linarith⟩).1 (hysub ⟨by linarith, by linarith⟩).2)) hψnn
  simp_rw [hψd, sub_mul] at h0
  rw [integral_sub hIx hIy] at h0
  linarith

end TauCeti

namespace MeasureTheory.LocallyIntegrableOn

open Set Filter Topology
open scoped ContDiff Convolution
open ContinuousLinearMap (lsmul lsmul_apply)

/-- **The monotone du Bois-Reymond lemma for locally integrable functions.** A real function
locally integrable on an open interval whose distributional derivative is nonnegative, in the
sense that `∫ x, deriv ψ x * f x ≤ 0` for every nonnegative test function `ψ` on the interval, is
monotone on a subset of the interval of full measure. -/
theorem exists_monotoneOn_of_integral_deriv_mul_nonpos
    {a b : ℝ} {f : ℝ → ℝ} (hf : LocallyIntegrableOn f (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → (∀ x, 0 ≤ ψ x) →
      ∫ x, deriv ψ x * f x ≤ 0) :
    ∃ s ⊆ Ioo a b, volume (Ioo a b \ s) = 0 ∧ MonotoneOn f s := by
  -- The compact intervals `K n = [a + 1 / (n + 1), b - 1 / (n + 1)]` exhaust `(a, b)`, and `f` is
  -- integrable on each of them.
  set K : ℕ → Set ℝ := fun n ↦ Icc (a + 1 / (n + 1)) (b - 1 / (n + 1))
  have hKsub (n : ℕ) : K n ⊆ Ioo a b := fun x hx ↦ by
    have : (0 : ℝ) < 1 / (n + 1) := by positivity
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hint (n : ℕ) : Integrable ((K n).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (hf.integrableOn_compact_subset (hKsub n) isCompact_Icc)
  -- Normalized bumps `β k` of radius `1 / (k + 1)`; by the Lebesgue differentiation theorem their
  -- averages of `1_{K n} f` converge to `1_{K n} f` almost everywhere, for every `n`.
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun k ↦
    ⟨1 / (2 * (k + 1)), 1 / (k + 1), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩
  have hφr (k : ℕ) : (φ k).rOut = 1 / (k + 1) := rfl
  have hφratio (k : ℕ) : (φ k).rOut ≤ 2 * (φ k).rIn := le_of_eq <| by
    dsimp only [φ]
    field_simp
  have hlim : ∀ᵐ x, ∀ n, Tendsto (fun k ↦ ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume]
      (K n).indicator f) x) atTop (𝓝 ((K n).indicator f x)) :=
    ae_all_iff.2 fun n ↦ ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall hφratio)
      (hint n).locallyIntegrable
  refine ⟨{x | x ∈ Ioo a b ∧ ∀ n, Tendsto (fun k ↦ ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume]
      (K n).indicator f) x) atTop (𝓝 ((K n).indicator f x))}, fun x hx ↦ hx.1,
    measure_mono_null ?_ (ae_iff.1 hlim), ?_⟩
  · exact fun x hx hx' ↦ hx.2 ⟨hx.1, hx'⟩
  rintro x ⟨hx, hxlim⟩ y ⟨hy, hylim⟩ hxy
  -- Choose `n` with `2 / (n + 1) < x - a` and `2 / (n + 1) < b - y`.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos (lt_min (sub_pos.2 hx.1) (sub_pos.2 hy.2)))
  have hn1 : 1 / ((n : ℝ) + 1) < (x - a) / 2 :=
    hn.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two)
  have hn2 : 1 / ((n : ℝ) + 1) < (b - y) / 2 :=
    hn.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two)
  have hn0 : (0 : ℝ) < 1 / (n + 1) := by positivity
  -- For `k ≥ n`, the bump `β k` centred at a point of `[x, y]` is supported in `K n`.
  have hrk (k : ℕ) (hk : n ≤ k) : 1 / ((k : ℝ) + 1) ≤ 1 / (n + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
  have hβ0 (k : ℕ) (t : ℝ) (ht : (φ k).rOut ≤ |t|) : (φ k).normed volume t = 0 :=
    Function.notMem_support.mp <| by simpa [(φ k).support_normed_eq] using ht
  have hpt (k : ℕ) (hk : n ≤ k) (z : ℝ) (hz : z ∈ Icc x y) (t : ℝ) :
      (φ k).normed volume (t - z) * (K n).indicator f t = (φ k).normed volume (t - z) * f t := by
    by_cases ht : t ∈ K n
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht, hβ0 k _ (not_lt.mp fun hlt ↦ ht ?_), zero_mul, zero_mul]
      rw [hφr, abs_lt] at hlt
      have := hrk k hk
      exact ⟨by linarith [hlt.1, hz.1], by linarith [hlt.2, hz.2]⟩
  -- These averages are the convolutions of `1_{K n} f` with `β k`, and are integrals of `f`.
  have hconv (k : ℕ) (hk : n ≤ k) (z : ℝ) (hz : z ∈ Icc x y) :
      ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] (K n).indicator f) z =
        ∫ t, (φ k).normed volume (t - z) * f t := by
    rw [convolution_eq_swap]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    simp only [lsmul_apply, smul_eq_mul]
    rw [← neg_sub t z, (φ k).normed_neg, hpt k hk z hz]
  have hI (k : ℕ) (hk : n ≤ k) (z : ℝ) (hz : z ∈ Icc x y) :
      Integrable fun t ↦ (φ k).normed volume (t - z) * f t := by
    obtain ⟨C, hC⟩ := ((φ k).continuous_normed (μ := volume)).bounded_above_of_compact_support
      (φ k).hasCompactSupport_normed
    have hβc : Continuous fun t ↦ (φ k).normed volume (t - z) :=
      ((φ k).continuous_normed (μ := volume)).comp (continuous_sub_right z)
    exact ((hint n).bdd_mul hβc.aestronglyMeasurable (c := C)
      (Eventually.of_forall fun t ↦ hC _)).congr (Eventually.of_forall fun t ↦ hpt k hk z hz t)
  -- The hypothesis, against the difference of primitives of the two bumps, compares the averages.
  have hle (k : ℕ) (hk : n ≤ k) : ∫ t, (φ k).normed volume (t - x) * f t ≤
      ∫ t, (φ k).normed volume (t - y) * f t := by
    obtain ⟨ψ, hψ, hψnn, hψs, hψd⟩ := TauCeti.exists_nonneg_deriv_eq_sub_bump (φ k).contDiff_normed
      (φ k).nonneg_normed (hβ0 k) (φ k).integral_normed hxy
    have hsub : Icc (x - (φ k).rOut) (y + (φ k).rOut) ⊆ Ioo a b := by
      rw [hφr]
      have := hrk k hk
      exact Icc_subset_Ioo (by linarith) (by linarith)
    have h0 := h ψ hψ (hψs.trans hsub) hψnn
    simp_rw [hψd, sub_mul] at h0
    rw [integral_sub (hI k hk x ⟨le_rfl, hxy⟩) (hI k hk y ⟨hxy, le_rfl⟩)] at h0
    linarith
  have hxK : x ∈ K n := ⟨by linarith, by linarith⟩
  have hyK : y ∈ K n := ⟨by linarith, by linarith⟩
  have hX := (hxlim n).congr' (eventually_atTop.2 ⟨n, fun k hk ↦ hconv k hk x ⟨le_rfl, hxy⟩⟩)
  have hY := (hylim n).congr' (eventually_atTop.2 ⟨n, fun k hk ↦ hconv k hk y ⟨hxy, le_rfl⟩⟩)
  rw [indicator_of_mem hxK] at hX
  rw [indicator_of_mem hyK] at hY
  exact le_of_tendsto_of_tendsto hX hY (eventually_atTop.2 ⟨n, hle⟩)

/-- **Functions whose distributional derivative is bounded above by an integrable function.** Let
`F` be locally integrable and `g` integrable on `(a, b)`, and suppose that `F' + g ≤ 0` in the
sense of distributions: `∫ x, ψ x * g x ≤ ∫ x, deriv ψ x * F x` for every nonnegative test
function `ψ` on the interval. Then `x ↦ F x + ∫ t in a..x, g t` is antitone on a subset of the
interval of full measure. -/
theorem exists_antitoneOn_add_intervalIntegral_of_integral_mul_le
    {a b : ℝ} {F g : ℝ → ℝ} (hF : LocallyIntegrableOn F (Ioo a b)) (hg : IntegrableOn g (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → (∀ x, 0 ≤ ψ x) →
      ∫ x, ψ x * g x ≤ ∫ x, deriv ψ x * F x) :
    ∃ s ⊆ Ioo a b, volume (Ioo a b \ s) = 0 ∧
      AntitoneOn (fun x ↦ F x + ∫ t in a..x, g t) s := by
  rcases le_or_gt b a with hba | hab
  · exact ⟨∅, empty_subset _, by simp [Ioo_eq_empty (not_lt.mpr hba)], fun _ h ↦ h.elim⟩
  set G : ℝ → ℝ := fun x ↦ ∫ t in a..x, g t
  have hgi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hg
  have hGc : ContinuousOn G (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' hgi left_mem_uIcc
  have hGloc : LocallyIntegrableOn G (Ioo a b) :=
    (hGc.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  -- `-(F + G)` has nonnegative distributional derivative.
  have hderiv : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → (∀ x, 0 ≤ ψ x) →
      ∫ x, deriv ψ x * (-(F + G)) x ≤ 0 := by
    intro ψ hψ hψs hψnn
    -- `ψ` and `ψ'` are test functions on the interval, so they pair integrably with `F`, `G`, `g`.
    have hψ' : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2
    have hψ's : tsupport (deriv ψ) ⊆ Ioo a b := fun x hx ↦ hψs (tsupport_deriv_subset hx)
    have hint (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (hks : tsupport k ⊆ Ioo a b) (f : ℝ → ℝ)
        (hf : LocallyIntegrableOn f (Ioo a b)) : Integrable fun x ↦ k x * f x := by
      have hkc : HasCompactSupport k :=
        isCompact_Icc.of_isClosed_subset (isClosed_tsupport k) (hks.trans Ioo_subset_Icc_self)
      exact TestFunction.integrable_smul (Ω := ⟨Ioo a b, isOpen_Ioo⟩) ⟨k, hk, hkc, hks⟩ hf
    -- Integration by parts: `∫ ψ' G = -∫ ψ g`, since `ψ (b) = 0`.
    have hzero (k : ℝ → ℝ) (hk : ∀ x ∉ Ioo a b, k x = 0) : ∫ x, k x = ∫ x in a..b, k x := by
      rw [intervalIntegral.integral_of_le hab.le, setIntegral_eq_integral_of_forall_compl_eq_zero
        fun x hx ↦ hk x fun hx' ↦ hx (Ioo_subset_Ioc_self hx')]
    have hvan (k : ℝ → ℝ) (hks : tsupport k ⊆ Ioo a b) (x : ℝ) (hx : x ∉ Ioo a b) : k x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hks h')
    have hIBP : ∫ x, deriv ψ x * G x = -∫ x, ψ x * g x := by
      have h1 := TauCeti.intervalIntegral.integral_deriv_smul_primitive_eq_sub_of_le hab.le
        (hψ.of_le (mod_cast le_top)) hgi
      rw [hvan ψ hψs b fun hb ↦ hb.2.false, zero_smul, zero_sub] at h1
      simp only [smul_eq_mul] at h1
      rw [hzero _ fun x hx ↦ by simp [hvan _ hψ's x hx],
        hzero _ fun x hx ↦ by simp [hvan _ hψs x hx], h1]
    have hFG : ∫ x, deriv ψ x * (-(F + G)) x =
        -(∫ x, deriv ψ x * F x) - ∫ x, deriv ψ x * G x := by
      simp only [Pi.neg_apply, Pi.add_apply, mul_neg, mul_add]
      rw [MeasureTheory.integral_neg, integral_add (hint _ hψ' hψ's F hF) (hint _ hψ' hψ's G hGloc)]
      ring
    rw [hFG, hIBP]
    linarith [h ψ hψ hψs hψnn]
  obtain ⟨s, hs, hnull, hmono⟩ :=
    (hF.add hGloc).neg.exists_monotoneOn_of_integral_deriv_mul_nonpos hderiv
  refine ⟨s, hs, hnull, fun x hx y hy hxy ↦ ?_⟩
  have := hmono hx hy hxy
  simp only [Pi.neg_apply, Pi.add_apply, neg_le_neg_iff] at this
  exact this

end MeasureTheory.LocallyIntegrableOn
