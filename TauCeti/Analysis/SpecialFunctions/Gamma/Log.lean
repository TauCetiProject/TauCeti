/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.ContinuousLog.Basic
import TauCeti.Analysis.Complex.SectorBounds
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
without further choices. Conversely, any continuous logarithm of `Gamma` on a preconnected subset
of `slitPlane` — and in particular on any exterior sector `{z : ℂ | |arg z| < π - δ ∧ 1 < ‖z‖}` —
differs from `logGamma` by an integer multiple of `2πi`, and coincides with `logGamma` once it
agrees at a single point (such as `2` or `1`). This file makes no asymptotic assertion.
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

/-- Any continuous logarithm of `Complex.Gamma` on a preconnected subset `U ⊆ slitPlane` differs
from `logGamma` on `U` by an integer multiple of `2πi`. -/
theorem exists_int_eq_logGamma_add_of_isPreconnected {U : Set ℂ} (hU : IsPreconnected U)
    (hsub : U ⊆ slitPlane) {L : ℂ → ℂ} (hL : ContinuousOn L U)
    (he : ∀ z ∈ U, Complex.exp (L z) = Complex.Gamma z) :
    ∃ k : ℤ, ∀ z ∈ U, L z = logGamma z + k * (2 * Real.pi * Complex.I) := by
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  obtain ⟨k, hk⟩ := exists_int_forall_eq_add_of_exp_eq
    (continuousOn_iff_continuous_domRestrict.mp (differentiableOn_logGamma.continuousOn.mono hsub))
    (continuousOn_iff_continuous_domRestrict.mp hL)
    fun z ↦ (exp_logGamma (hsub z.2)).trans (he z z.2).symm
  exact ⟨k, fun z hz ↦ hk ⟨z, hz⟩⟩

/-- Any continuous logarithm of `Complex.Gamma` on a preconnected subset `U ⊆ slitPlane` that
agrees with `logGamma` at one point of `U` coincides with `logGamma` throughout `U`. -/
theorem eqOn_logGamma_of_isPreconnected {U : Set ℂ} (hU : IsPreconnected U)
    (hsub : U ⊆ slitPlane) {L : ℂ → ℂ} (hL : ContinuousOn L U)
    (he : ∀ z ∈ U, Complex.exp (L z) = Complex.Gamma z) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (h0 : L z₀ = logGamma z₀) :
    EqOn L logGamma U := by
  obtain ⟨k, hk⟩ := exists_int_eq_logGamma_add_of_isPreconnected hU hsub hL he
  have hk0 : (k : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination h0 - hk z₀ hz₀
  intro z hz
  rw [hk z hz, hk0, add_zero]

/-- A continuous logarithm of Gamma on the slit plane vanishing at `2` is the chosen branch. -/
theorem eqOn_logGamma {L : ℂ → ℂ} (hL : ContinuousOn L slitPlane)
    (he : ∀ z ∈ slitPlane, Complex.exp (L z) = Complex.Gamma z) (h2 : L 2 = 0) :
    EqOn L logGamma slitPlane :=
  eqOn_logGamma_of_isPreconnected
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    subset_rfl hL he (ofNat_mem_slitPlane 2) (h2.trans logGamma_two.symm)

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
    EqOn L logGamma slitPlane :=
  eqOn_logGamma_of_isPreconnected
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    subset_rfl hL he one_mem_slitPlane (h1.trans logGamma_one.symm)

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
  have hadd {w : ℂ} (hw : w ∈ slitPlane) : w + 1 ∈ slitPlane := by
    simpa [add_comm] using ofReal_add_mem_slitPlane hw zero_le_one
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

/-- Any continuous logarithm of `Gamma` on `{z : ℂ | |arg z| < π - δ ∧ 1 < ‖z‖}` differs from
`logGamma` by an integer multiple of `2πi`. No hypothesis on `δ` is required: for `π ≤ δ` the
sector is empty, and for `δ < 0` it contains the pole `-2` where `Gamma (-2) = 0`. -/
theorem exists_int_eq_logGamma_add_sector {δ : ℝ} {L : ℂ → ℂ}
    (hL : ContinuousOn L {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖})
    (he : ∀ z ∈ {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖},
      Complex.exp (L z) = Complex.Gamma z) :
    ∃ k : ℤ, ∀ z ∈ {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖},
      L z = logGamma z + k * (2 * Real.pi * Complex.I) := by
  rcases lt_or_ge δ 0 with hδ0 | hδ0
  · refine ⟨0, fun _ _ ↦ False.elim ?_⟩
    have hm2 : (-2 : ℂ) ∈ {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
      have harg : (-2 : ℂ).arg = Real.pi := by
        simpa using arg_ofReal_of_neg (x := -2) (by norm_num)
      exact ⟨by rw [harg, abs_of_pos Real.pi_pos]; linarith, by norm_num⟩
    exact Complex.exp_ne_zero (L (-2))
      ((he (-2) hm2).trans (by simpa using Complex.Gamma_neg_nat_eq_zero 2))
  · refine exists_int_eq_logGamma_add_of_isPreconnected
      isPreconnected_setOf_abs_arg_lt_and_lt_norm (fun z hz ↦ ?_) hL he
    exact mem_slitPlane_of_abs_arg_lt (by linarith [hz.1])
      (norm_pos_iff.mp (zero_lt_one.trans hz.2))

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
  have h2S : (2 : ℂ) ∈ {w : ℂ | |w.arg| < Real.pi - δ ∧ 1 < ‖w‖} :=
    ⟨by simp; linarith [abs_nonneg z.arg, hz.1], by norm_num⟩
  have hk0 : (k : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination h2 - logGamma_two - hk 2 h2S
  rw [hk z hz, hk0, add_zero]

end TauCeti
