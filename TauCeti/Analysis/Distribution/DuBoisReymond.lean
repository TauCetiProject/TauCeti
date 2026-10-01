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
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The du Bois-Reymond lemma on an interval

A function on an open interval whose distributional derivative vanishes is constant. Concretely,
if `f : ℝ → F` is continuous on `Ioo a b` and

`∫ x, deriv ψ x • f x = 0`

for every smooth `ψ : ℝ → ℝ` with `tsupport ψ ⊆ Ioo a b`, then `f` is constant on
`Ioo a b`. This is the one-variable **du Bois-Reymond lemma**, the derivative form of the
fundamental lemma of the calculus of variations, whose zeroth-order form is Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

The reduction to the zeroth-order lemma is the classical one. Fix a test function `ρ` on the
interval with total integral `1`. For a test function `g`, the function `g - (∫ g) ρ` has total
integral zero, so its primitive `ψ` is again a test function on the interval, with `deriv ψ = g -
(∫ g) ρ`; the hypothesis applied to `ψ` gives `∫ g • f = (∫ g) • ∫ ρ • f`, that is
`∫ g • (f - c) = 0` for the constant `c = ∫ ρ • f`. Hence `f = c` almost everywhere on the
interval, and everywhere by continuity.

The one-sided version says that a continuous real function whose distributional derivative is
nonnegative is monotone: if `∫ x, deriv ψ x * f x ≤ 0` for every nonnegative test function `ψ` on
the interval, then `f` is monotone there. For `x ≤ y` in the interval, take `ψ` to be the
difference of the primitives of two copies of a narrow bump of integral one, centred at `x` and at
`y`; then `ψ ≥ 0`, and `∫ ψ' f` is the difference of the averages of `f` against the two bumps,
which are close to `f x` and `f y` by continuity.

## Main declarations

* `ContDiff.exists_contDiff_deriv_eq_of_integral_eq_zero`: the primitive of a test function on
  an interval with total integral zero is a test function on the interval.
* `ContinuousOn.exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero`: **the du Bois-Reymond
  lemma**.
* `ContinuousOn.monotoneOn_of_integral_deriv_mul_nonpos`: a continuous function with nonnegative
  distributional derivative is monotone.
-/

public section

namespace TauCeti

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The primitive of a mean-zero test function is a test function.** If `φ : ℝ → ℝ` is smooth
with `tsupport φ ⊆ Ioo a b` and `∫ φ = 0`, then `φ` is the derivative of a smooth compactly
supported function `ψ` with `tsupport ψ ⊆ Ioo a b`. -/
theorem _root_.ContDiff.exists_contDiff_deriv_eq_of_integral_eq_zero {a b : ℝ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ Ioo a b) (hint : ∫ x, φ x = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioo a b ∧ deriv ψ = φ := by
  have hφc : Continuous φ := hφ.continuous
  have hφ0 : ∀ x, x ∉ Ioo a b → φ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφs h)
  rcases le_or_gt b a with hba | hab
  · -- The interval is empty, so `φ = 0` and `ψ = 0` works.
    have hφ0' : φ = 0 := funext fun x ↦ hφ0 x (by simp [Ioo_eq_empty (not_lt.mpr hba)])
    exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp, by simp [hφ0']⟩
  -- The primitive of `φ` based at `a`.
  set ψ : ℝ → ℝ := fun t ↦ ∫ s in a..t, φ s with hψ_def
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
  have hleft : ∀ t, t < a + εa → ψ t = 0 := by
    intro t ht
    simp only [hψ_def]
    refine (integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans integral_zero
    rcases le_or_gt s a with hsa | hsa
    · exact hφ0 s fun h ↦ h.1.not_ge hsa
    · have h1 : s < a + εa := lt_of_le_of_lt hs.2 (max_lt (by linarith) ht)
      refine hφa ?_
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hsa)]
      linarith
  have hright : ∀ t, b - εb < t → ψ t = 0 := by
    intro t ht
    simp only [hψ_def]
    rw [← integral_add_adjacent_intervals (hφc.intervalIntegrable a b)
      (hφc.intervalIntegrable b t)]
    have h₁ : ∫ s in a..b, φ s = 0 := by
      rw [integral_of_le hab.le, setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦
        hφ0 s fun h ↦ hs (mem_Ioc.mpr ⟨h.1, h.2.le⟩), hint]
    have h₂ : ∫ s in b..t, φ s = 0 := by
      refine (integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans integral_zero
      rcases le_or_gt b s with hbs | hbs
      · exact hφ0 s fun h ↦ h.2.not_ge hbs
      · have h1 : b - εb < s := lt_of_lt_of_le (lt_min (by linarith) ht) hs.1
        refine hφb ?_
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hbs)]
        linarith
    rw [h₁, h₂, add_zero]
  have hsupp : tsupport ψ ⊆ Icc (a + εa) (b - εb) := by
    refine closure_minimal (fun t ht ↦ ⟨?_, ?_⟩) isClosed_Icc
    · by_contra h
      exact ht (hleft t (not_le.mp h))
    · by_contra h
      exact ht (hright t (not_le.mp h))
  exact ⟨ψ, hψ, isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) hsupp,
    hsupp.trans fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩, hψd⟩

variable [CompleteSpace F]

/-- **The du Bois-Reymond lemma.** A function continuous on an open interval whose pairing with
the derivative of every test function on the interval vanishes,
`∫ x, deriv ψ x • f x = 0`, is constant on the interval. -/
theorem _root_.ContinuousOn.exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero {a b : ℝ}
    {f : ℝ → F} (hf : ContinuousOn f (Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → ∫ x, deriv ψ x • f x = 0) :
    ∃ c : F, EqOn f (fun _ ↦ c) (Ioo a b) := by
  rcases le_or_gt b a with hba | hab
  · exact ⟨0, fun x hx ↦ absurd hx (by simp [Ioo_eq_empty (not_lt.mpr hba)])⟩
  -- A test function `g` on the interval pairs with `f` like a compactly supported continuous
  -- function.
  have hint : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ Ioo a b →
      Integrable fun x ↦ g x • f x := fun g hg hgc hgs ↦
    ((hg.continuousOn.smul hf).continuous_of_tsupport_subset isOpen_Ioo
      ((tsupport_smul_subset_left g f).trans hgs)).integrable_of_hasCompactSupport hgc.smul_right
  -- A normalized bump function supported in the interval.
  let β : ContDiffBump ((a + b) / 2) := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  have hrOut : β.rOut = (b - a) / 4 := rfl
  set ρ : ℝ → ℝ := β.normed volume with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := β.contDiff_normed
  have hρc : HasCompactSupport ρ := β.hasCompactSupport_normed
  have hρs : tsupport ρ ⊆ Ioo a b := by
    rw [hρ_def, β.tsupport_normed_eq, hrOut]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
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
    have hφs : tsupport φ ⊆ Ioo a b := by
      refine (closure_minimal (fun x hx ↦ ?_)
        ((isClosed_tsupport g).union (isClosed_tsupport ρ))).trans (union_subset hgs hρs)
      by_contra hx'
      simp only [mem_union, not_or] at hx'
      exact hx (by simp [hφ_def, image_eq_zero_of_notMem_tsupport hx'.1,
        image_eq_zero_of_notMem_tsupport hx'.2])
    have hφint : ∫ x, φ x = 0 := by
      simp only [hφ_def]
      rw [integral_sub hgi (hρi.const_mul _), MeasureTheory.integral_const_mul, hρint, mul_one,
        sub_self]
    obtain ⟨ψ, hψ, -, hψs, hψd⟩ := hφ.exists_contDiff_deriv_eq_of_integral_eq_zero hφs hφint
    have h0 := h ψ hψ hψs
    rw [hψd] at h0
    simp only [hφ_def, sub_smul, mul_smul] at h0
    have hρf : Integrable fun x ↦ (∫ y, g y) • ρ x • f x :=
      (hint ρ hρ.continuous hρc hρs).smul _
    rw [integral_sub (hint g hg.continuous hgc hgs) hρf, MeasureTheory.integral_smul,
      sub_eq_zero] at h0
    simp only [smul_sub]
    rw [integral_sub (hint g hg.continuous hgc hgs) (hgi.smul_const _),
      _root_.integral_smul_const, h0, sub_self]
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hf.sub continuousOn_const).locallyIntegrableOn measurableSet_Ioo) key
  have heq : EqOn (fun x ↦ f x - ∫ y, ρ y • f y) (fun _ ↦ (0 : F)) (Ioo a b) :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' measurableSet_Ioo).mpr hae) isOpen_Ioo
      (hf.sub continuousOn_const) continuousOn_const
  intro x hx
  exact sub_eq_zero.mp (heq hx)

/-- For a nonnegative bump `β` of integral one vanishing outside `(-r, r)` and `x ≤ y`, the
difference `ψ t = B (t - x) - B (t - y)` of translates of the primitive `B` of `β` is a
nonnegative smooth function supported in `[x - r, y + r]` with `ψ' t = β (t - x) - β (t - y)`. -/
private lemma exists_nonneg_deriv_eq_sub_bump {β : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hβ : ContDiff ℝ ∞ β)
    (hβnn : ∀ t, 0 ≤ β t) (hβ0 : ∀ t, r ≤ |t| → β t = 0) (hβ1 : ∫ t, β t = 1) {x y : ℝ}
    (hxy : x ≤ y) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t, 0 ≤ ψ t) ∧ tsupport ψ ⊆ Icc (x - r) (y + r) ∧
      ∀ t, deriv ψ t = β (t - x) - β (t - y) := by
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
    exact hβ0 s (by rw [abs_of_nonpos (by linarith [hs.2])]; linarith [hs.2])
  have hBright : ∀ t, r ≤ t → B t = 1 := by
    intro t ht
    simp only [hB_def]
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_, hβ1]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
    rcases hs with hs | hs
    · exact hβ0 s (by rw [abs_of_nonpos (by linarith)]; linarith)
    · exact hβ0 s (by rw [abs_of_pos (by linarith)]; linarith)
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
private lemma integral_bump_mul_mem_Icc {β f : ℝ → ℝ} {r z η : ℝ} {U : Set ℝ} (hr : 0 < r)
    (hβ : Continuous β) (hβnn : ∀ t, 0 ≤ β t) (hβ0 : ∀ t, r ≤ |t| → β t = 0)
    (hβ1 : ∫ t, β t = 1) (hf : ContinuousOn f U) (hU : IsOpen U) (hzU : Icc (z - r) (z + r) ⊆ U)
    (hfz : ∀ t, |t - z| < r → |f t - f z| < η) :
    Integrable (fun t ↦ β (t - z) * f t) ∧ ∫ t, β (t - z) * f t ∈ Icc (f z - η) (f z + η) := by
  have hts : tsupport (fun t ↦ β (t - z)) ⊆ Icc (z - r) (z + r) := by
    refine closure_minimal (fun t ht ↦ ?_) isClosed_Icc
    by_contra h'
    refine ht (hβ0 _ ?_)
    rw [mem_Icc, not_and_or, not_le, not_le] at h'
    rcases h' with h' | h'
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
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
    obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp
      (hf.continuousAt (isOpen_Ioo.mem_nhds hz)) (η / 2) (half_pos hη)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_Ioo z hz
    refine ⟨min δ ε / 2, by positivity, fun t ht ↦ hball ?_, fun t ht ↦ ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [ht.1, ht.2, min_le_right δ ε]
    · simpa [Real.dist_eq] using hfδ (by
        rw [Real.dist_eq]; linarith [min_le_left δ ε, lt_min hδ hε])
  obtain ⟨rx, hrx, hxsub, hfx⟩ := hnear x hx
  obtain ⟨ry, hry, hysub, hfy⟩ := hnear y hy
  set r := min rx ry with hr_def
  have hr : 0 < r := lt_min hrx hry
  have hrx' : r ≤ rx := min_le_left _ _
  have hry' : r ≤ ry := min_le_right _ _
  -- A nonnegative bump `β` of integral one vanishing outside `(-r, r)`.
  let β₀ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set β : ℝ → ℝ := β₀.normed volume with hβ_def
  have hβ0 : ∀ t, r ≤ |t| → β t = 0 := fun t ht ↦ by
    by_contra hne
    have : t ∈ Function.support β := hne
    rw [hβ_def, β₀.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at this
    exact (this.trans_le ht).false
  obtain ⟨ψ, hψ, hψnn, hψs, hψd⟩ := exists_nonneg_deriv_eq_sub_bump hr β₀.contDiff_normed
    (β₀.nonneg_normed) hβ0 β₀.integral_normed hxy
  obtain ⟨hIx, hx1, -⟩ := integral_bump_mul_mem_Icc hr β₀.continuous_normed β₀.nonneg_normed hβ0
    β₀.integral_normed hf isOpen_Ioo
    ((Icc_subset_Icc (by linarith) (by linarith)).trans hxsub) fun t ht ↦ hfx t (by linarith)
  obtain ⟨hIy, -, hy2⟩ := integral_bump_mul_mem_Icc hr β₀.continuous_normed β₀.nonneg_normed hβ0
    β₀.integral_normed hf isOpen_Ioo
    ((Icc_subset_Icc (by linarith) (by linarith)).trans hysub) fun t ht ↦ hfy t (by linarith)
  have h0 := h ψ hψ (hψs.trans (Icc_subset_Ioo
    (hxsub ⟨by linarith, by linarith⟩).1 (hysub ⟨by linarith, by linarith⟩).2)) hψnn
  simp_rw [hψd, sub_mul] at h0
  rw [integral_sub hIx hIy] at h0
  linarith

end TauCeti
