/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.ContinuousLog.Basic
import TauCeti.Analysis.Complex.SlitPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible

/-!
# The normalized holomorphic logarithm of Gamma

`TauCeti.logGamma` is the holomorphic logarithm of `Complex.Gamma` on the slit plane
`ℂ ∖ (-∞, 0]`, normalized to vanish at `2` (and at `1`). It agrees with the real logarithm of
Gamma on the positive real axis, commutes with complex conjugation on the slit plane, and satisfies
the functional equation `logGamma (z + 1) = logGamma z + log z` for `z ∈ slitPlane`. In
particular, its value at `3` is `Real.log 2`, and its real part is `Real.log ‖Complex.Gamma z‖`.

The branch is constructed once on the whole slit plane, using
`TauCeti.exists_differentiableOn_eqOn_exp_comp`; its restrictions to sectors therefore agree
without further choices. Conversely, any continuous logarithm of `Gamma` on an exterior sector
`{z : ℂ | |arg z| < π - δ ∧ 1 < ‖z‖}` differs from `logGamma` by an integer multiple of `2πi`, and
coincides with `logGamma` when normalized to vanish at `2`. This file makes no asymptotic
assertion.
-/

public section

namespace TauCeti

open Complex Set

private theorem exists_normalized_logGamma :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L slitPlane ∧
      EqOn (Complex.exp ∘ L) Complex.Gamma slitPlane ∧ L 2 = 0 := by
  have hpole {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) : z ≠ -(n : ℂ) := by
    rintro rfl
    have hneg := (Complex.neg_ofReal_mem_slitPlane (x := (n : ℝ))).mp hz
    exact (Nat.cast_nonneg n).not_gt hneg
  have hsc : IsSimplyConnected slitPlane := by
    let : ContractibleSpace slitPlane :=
      starConvex_one_slitPlane.contractibleSpace ⟨1, one_mem_slitPlane⟩
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hL, he⟩ := exists_differentiableOn_eqOn_exp_comp hsc isOpen_slitPlane
    (fun z hz => (Complex.differentiableAt_Gamma z
      (hpole hz)).differentiableWithinAt)
    (by rintro ⟨z, hz, hzero⟩
        exact Complex.Gamma_ne_zero (hpole hz) hzero)
  have htwo : Complex.exp (L 2) = 1 := by
    simpa using (he (ofNat_mem_slitPlane 2))
  refine ⟨fun z => L z - L 2, hL.sub_const _, fun z hz => ?_, sub_self _⟩
  simpa [Complex.exp_sub, htwo] using he hz

/-- The holomorphic logarithm of Gamma on the slit plane, normalized by `logGamma 2 = 0`.
Outside the slit plane its values are unspecified. -/
noncomputable def logGamma : ℂ → ℂ := Classical.choose exists_normalized_logGamma

/-- The normalized logarithm of Gamma is holomorphic on the whole slit plane. -/
theorem differentiableOn_logGamma : DifferentiableOn ℂ logGamma slitPlane :=
  (Classical.choose_spec exists_normalized_logGamma).1

/-- Exponentiating the normalized logarithm recovers Gamma. -/
@[simp]
theorem exp_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.exp (logGamma z) = Complex.Gamma z :=
  (Classical.choose_spec exists_normalized_logGamma).2.1 hz

/-- The normalization of the logarithm of Gamma. -/
@[simp]
theorem logGamma_two : logGamma 2 = 0 :=
  (Classical.choose_spec exists_normalized_logGamma).2.2

/-- The normalized logarithm of Gamma is analytic at every point of the slit plane. -/
theorem analyticOnNhd_logGamma : AnalyticOnNhd ℂ logGamma slitPlane :=
  differentiableOn_logGamma.analyticOnNhd isOpen_slitPlane

/-- A holomorphic logarithm of Gamma on the slit plane vanishing at `2` is the chosen branch. -/
theorem eqOn_logGamma {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L slitPlane)
    (he : ∀ z ∈ slitPlane, Complex.exp (L z) = Complex.Gamma z) (h2 : L 2 = 0) :
    EqOn L logGamma slitPlane := by
  exact eqOn_of_eqOn_exp_comp isOpen_slitPlane
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    hL differentiableOn_logGamma (fun z hz => he z hz) (fun _ hz => exp_logGamma hz)
    (ofNat_mem_slitPlane 2) (h2.trans logGamma_two.symm)

/-- The real part of any value of the branch is the logarithm of the Gamma norm. -/
theorem logGamma_re {z : ℂ} (hz : z ∈ slitPlane) :
    (logGamma z).re = Real.log ‖Complex.Gamma z‖ := by
  rw [← exp_logGamma hz, Complex.norm_exp, Real.log_exp]

/-- On the positive real axis the holomorphic branch agrees with the real logarithm of Gamma. -/
@[simp]
theorem logGamma_ofReal {x : ℝ} (hx : 0 < x) :
    logGamma x = (Real.log (Real.Gamma x) : ℂ) := by
  let d : ℝ → ℂ := fun t => logGamma t - (Real.log (Real.Gamma t) : ℂ)
  have hc : ContinuousOn d (Ioi 0) := by
    exact (differentiableOn_logGamma.continuousOn.comp continuous_ofReal.continuousOn
      (fun t ht => ofReal_mem_slitPlane.mpr ht)).sub
      (continuous_ofReal.comp_continuousOn
        (Real.differentiableOn_Gamma_Ioi.continuousOn.log
          (fun t ht => (Real.Gamma_pos_of_pos ht).ne')))
  have he : ∀ t ∈ Ioi (0 : ℝ), Complex.exp (d t) = 1 := by
    intro t ht
    simp only [d, Complex.exp_sub, exp_logGamma (ofReal_mem_slitPlane.mpr ht),
      Complex.Gamma_ofReal, ← Complex.ofReal_exp,
      Real.exp_log (Real.Gamma_pos_of_pos ht), div_self (ofReal_ne_zero.mpr
        (Real.Gamma_pos_of_pos ht).ne')]
  have hd : d x = d 2 :=
    eq_of_isPreconnected_of_forall_exp_eq_one (isPreconnected_Ioi.image d hc)
      (by rintro _ ⟨t, ht, rfl⟩; exact he t ht) ⟨x, hx, rfl⟩ ⟨2, by norm_num, rfl⟩
  have hd2 : d 2 = 0 := by simp [d]
  exact sub_eq_zero.mp (hd.trans hd2)

/-- At `1` the normalized branch vanishes, since `Γ(1) = 1`. -/
@[simp]
theorem logGamma_one : logGamma 1 = 0 := by
  simpa using logGamma_ofReal one_pos

/-- At `3` the normalized branch takes the value `log 2`. -/
@[simp]
theorem logGamma_three : logGamma 3 = (Real.log 2 : ℂ) := by
  simpa using logGamma_ofReal (x := 3) (by norm_num)

/-- Any continuous logarithm of `Gamma` on the slit plane vanishing at `1` equals `logGamma`. -/
theorem eqOn_logGamma_of_one {L : ℂ → ℂ} (hL : ContinuousOn L slitPlane)
    (he : ∀ z ∈ slitPlane, Complex.exp (L z) = Complex.Gamma z) (h1 : L 1 = 0) :
    EqOn L logGamma slitPlane := by
  intro z hz
  let d : ℂ → ℂ := fun w ↦ L w - logGamma w
  have hd : ContinuousOn d slitPlane := hL.sub differentiableOn_logGamma.continuousOn
  have hexp : ∀ w ∈ slitPlane, Complex.exp (d w) = 1 := fun w hw ↦ by
    rw [Complex.exp_sub, he w hw, exp_logGamma hw, div_self]
    rw [← exp_logGamma hw]
    exact Complex.exp_ne_zero _
  have hconn :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  have hdz : d z = d 1 :=
    eq_of_isPreconnected_of_forall_exp_eq_one (hconn.image d hd)
      (by rintro _ ⟨w, hw, rfl⟩; exact hexp w hw) ⟨z, hz, rfl⟩ ⟨1, one_mem_slitPlane, rfl⟩
  have hd1 : d 1 = 0 := by simp [d, h1]
  exact sub_eq_zero.mp (hdz.trans hd1)

/-- `logGamma` commutes with complex conjugation on the slit plane. -/
theorem logGamma_conj {z : ℂ} (hz : z ∈ slitPlane) :
    logGamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logGamma z) := by
  let L : ℂ → ℂ := fun w ↦ (starRingEnd ℂ) (logGamma ((starRingEnd ℂ) w))
  have hL : ContinuousOn L slitPlane :=
    continuous_conj.comp_continuousOn (differentiableOn_logGamma.continuousOn.comp
      continuous_conj.continuousOn fun _ hw ↦ conj_mem_slitPlane.mpr hw)
  have he : ∀ w ∈ slitPlane, Complex.exp (L w) = Complex.Gamma w := fun w hw ↦ by
    dsimp [L]
    rw [Complex.exp_conj, exp_logGamma (conj_mem_slitPlane.mpr hw), ← Complex.Gamma_conj,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
  have h1 : L 1 = 0 := by simp [L]
  simpa [L] using (eqOn_logGamma_of_one hL he h1 (conj_mem_slitPlane.mpr hz)).symm

/-- Functional equation `logGamma (z + 1) = logGamma z + log z` on the slit plane. -/
theorem logGamma_add_one {z : ℂ} (hz : z ∈ slitPlane) :
    logGamma (z + 1) = logGamma z + Complex.log z := by
  have hadd {w : ℂ} (hw : w ∈ slitPlane) : w + 1 ∈ slitPlane :=
    (mem_slitPlane_iff.mp hw).imp (fun h ↦ by simp; linarith) (fun h ↦ by simpa using h)
  let L : ℂ → ℂ := fun w ↦ logGamma (w + 1) - Complex.log w
  have hL : ContinuousOn L slitPlane :=
    (differentiableOn_logGamma.continuousOn.comp (continuousOn_id.add continuousOn_const)
      fun _ hw ↦ hadd hw).sub (continuousOn_id.clog fun _ hw ↦ hw)
  have he : ∀ w ∈ slitPlane, Complex.exp (L w) = Complex.Gamma w := fun w hw ↦ by
    have hw0 := slitPlane_ne_zero hw
    dsimp [L]
    rw [Complex.exp_sub, exp_logGamma (hadd hw), Complex.exp_log hw0, Complex.Gamma_add_one w hw0,
      mul_div_cancel_left₀ _ hw0]
  have h1 : L 1 = 0 := by norm_num [L]
  exact sub_eq_iff_eq_add.mp (eqOn_logGamma_of_one hL he h1 hz)

/-- The derivative of the normalized branch is the digamma function. -/
theorem deriv_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    deriv logGamma z = Complex.digamma z := by
  exact deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_slitPlane differentiableOn_logGamma
    (fun _ hw => exp_logGamma hw) hz

/-- `logGamma` has derivative `digamma z` at every point of the slit plane. -/
theorem hasDerivAt_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt logGamma (Complex.digamma z) z :=
  deriv_logGamma hz ▸
    (differentiableOn_logGamma.differentiableAt (isOpen_slitPlane.mem_nhds hz)).hasDerivAt

/-- Holomorphy on every sector avoiding the negative real axis. All these sectors use the same
branch, so their restrictions agree on every overlap. -/
theorem differentiableOn_logGamma_sector {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ logGamma {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
  refine differentiableOn_logGamma.mono fun z hz => mem_slitPlane_iff_arg.mpr ⟨?_, ?_⟩
  · have harg : z.arg < Real.pi := lt_of_le_of_lt (le_abs_self _) (by linarith [hz.1])
    exact ne_of_lt harg
  · rintro rfl
    norm_num at hz

private theorem isPreconnected_sector {δ : ℝ} (hδ0 : 0 ≤ δ) :
    IsPreconnected {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
  let φ : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hφ : Continuous φ := by fun_prop
  have himg : φ '' (Ioi 1 ×ˢ Ioo (-(Real.pi - δ)) (Real.pi - δ)) =
      {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
      have hr0 : 0 < r := lt_trans zero_lt_one hr
      have harg : (φ (r, θ)).arg = θ := by
        dsimp [φ]
        rw [arg_real_mul _ hr0, arg_exp_mul_I, toIocMod_eq_self]
        exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      have hnorm : ‖φ (r, θ)‖ = r := by
        dsimp [φ]
        rw [norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hr0.le, mul_one]
      exact ⟨by rw [harg]; exact abs_lt.mpr hθ, by rwa [hnorm]⟩
    · rintro ⟨harg, hnorm⟩
      exact ⟨(‖z‖, z.arg), ⟨hnorm, abs_lt.mp harg⟩, norm_mul_exp_arg_mul_I z⟩
  rw [← himg]
  exact (isPreconnected_Ioi.prod isPreconnected_Ioo).image φ hφ.continuousOn

/-- Any continuous logarithm of `Gamma` on `{z : ℂ | |arg z| < π - δ ∧ 1 < ‖z‖}` differs from
`logGamma` by an integer multiple of `2πi`. No hypothesis on `δ` is required: for `π ≤ δ` the
sector is empty, and for `δ < 0` it contains the pole `-2` where `Gamma (-2) = 0`. -/
theorem exists_int_eq_logGamma_add_sector {δ : ℝ} {L : ℂ → ℂ}
    (hL : ContinuousOn L {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖})
    (he : ∀ z ∈ {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖},
      Complex.exp (L z) = Complex.Gamma z) :
    ∃ k : ℤ, ∀ z ∈ {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖},
      L z = logGamma z + k * (2 * Real.pi * Complex.I) := by
  set S : Set ℂ := {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖}
  rcases le_or_gt Real.pi δ with hπδ | hδπ
  · exact ⟨0, fun z hz ↦ False.elim (by linarith [abs_nonneg z.arg, hz.1])⟩
  rcases lt_or_ge δ 0 with hδ0 | hδ0
  · refine ⟨0, fun _ _ ↦ False.elim ?_⟩
    have hm2 : (-2 : ℂ) ∈ S := by
      have harg : (-2 : ℂ).arg = Real.pi := by
        simpa using arg_ofReal_of_neg (x := -2) (by norm_num)
      refine ⟨?_, by norm_num⟩
      rw [harg, abs_of_pos Real.pi_pos]
      linarith
    have h0 := he (-2) hm2
    have hg0 : Complex.Gamma (-2) = 0 := by simpa using Complex.Gamma_neg_nat_eq_zero 2
    exact Complex.exp_ne_zero (L (-2)) (h0.trans hg0)
  have hsub : S ⊆ slitPlane := fun z hz ↦ mem_slitPlane_iff_arg.mpr
    ⟨ne_of_lt ((le_abs_self _).trans_lt (by linarith [hz.1])),
      by rintro rfl; norm_num [S] at hz⟩
  have h2S : (2 : ℂ) ∈ S := by
    have harg : (2 : ℂ).arg = 0 := by simp
    exact ⟨by rw [harg, abs_zero]; linarith, by norm_num⟩
  let d : ℂ → ℂ := fun z ↦ L z - logGamma z
  have hd : ContinuousOn d S := hL.sub (differentiableOn_logGamma.continuousOn.mono hsub)
  have hexp : ∀ z ∈ S, Complex.exp (d z) = 1 := fun z hz ↦ by
    rw [Complex.exp_sub, he z hz, exp_logGamma (hsub hz), div_self]
    rw [← exp_logGamma (hsub hz)]
    exact Complex.exp_ne_zero _
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (hexp 2 h2S)
  refine ⟨k, fun z hz ↦ ?_⟩
  have hdz : d z = d 2 :=
    eq_of_isPreconnected_of_forall_exp_eq_one ((isPreconnected_sector hδ0).image d hd)
      (by rintro _ ⟨w, hw, rfl⟩; exact hexp w hw) ⟨z, hz, rfl⟩ ⟨2, h2S, rfl⟩
  dsimp [d] at hdz hk
  linear_combination hdz + hk

/-- Any continuous logarithm of `Gamma` on `{z : ℂ | |arg z| < π - δ ∧ 1 < ‖z‖}` normalized by
`L 2 = 0` coincides with `logGamma` on that sector. -/
theorem eqOn_logGamma_sector {δ : ℝ} {L : ℂ → ℂ}
    (hL : ContinuousOn L {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖})
    (he : ∀ z ∈ {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖},
      Complex.exp (L z) = Complex.Gamma z)
    (h2 : L 2 = 0) :
    EqOn L logGamma {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
  obtain ⟨k, hk⟩ := exists_int_eq_logGamma_add_sector hL he
  intro z hz
  rcases lt_or_ge δ Real.pi with hδπ | hπδ
  · have h2S : (2 : ℂ) ∈ {w : ℂ | |w.arg| < Real.pi - δ ∧ 1 < ‖w‖} := by
      have harg : (2 : ℂ).arg = 0 := by simp
      exact ⟨by rw [harg, abs_zero]; linarith, by norm_num⟩
    have hk0 := hk 2 h2S
    rw [h2, logGamma_two, zero_add] at hk0
    rw [hk z hz, ← hk0, add_zero]
  · exact False.elim (by linarith [abs_nonneg z.arg, hz.1])

end TauCeti
