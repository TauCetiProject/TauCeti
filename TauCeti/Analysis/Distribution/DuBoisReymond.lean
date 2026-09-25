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

## Main declarations

* `ContDiff.exists_contDiff_deriv_eq_of_integral_eq_zero`: the primitive of a test function on
  an interval with total integral zero is a test function on the interval.
* `ContinuousOn.exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero`: **the du Bois-Reymond
  lemma**.
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

end TauCeti
