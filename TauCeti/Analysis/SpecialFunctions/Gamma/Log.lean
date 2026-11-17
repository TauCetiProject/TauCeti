/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.ContinuousLog.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible

/-!
# The normalized holomorphic logarithm of Gamma

`TauCeti.logGamma` is the holomorphic logarithm of `Complex.Gamma` on the slit plane
`ℂ ∖ (-∞, 0]`, normalized to vanish at `2` (and hence also at `1`). It agrees with the real
logarithm of Gamma on the positive real axis, satisfies the functional equation
`logGamma (z + 1) = logGamma z + Complex.log z` throughout the slit plane, takes value `Real.log 2`
at `3`, and has real part `Real.log ‖Complex.Gamma z‖`.

The branch is constructed once on the whole slit plane, using
`TauCeti.exists_differentiableOn_eqOn_exp_comp`; its restrictions to open connected subsets and
sectors avoiding the negative real axis are uniquely determined by their value at a single point
(`TauCeti.eqOn_logGamma_of_isOpen`, `TauCeti.eqOn_logGamma_sector`). This file makes no asymptotic
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

/-- A holomorphic logarithm of Gamma on an open preconnected subset of the slit plane agreeing with
`logGamma` at one point agrees with `logGamma` on the whole subset. -/
theorem eqOn_logGamma_of_isOpen {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hU : U ⊆ slitPlane) {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L U)
    (he : ∀ z ∈ U, Complex.exp (L z) = Complex.Gamma z) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (heq : L z₀ = logGamma z₀) : EqOn L logGamma U :=
  eqOn_of_eqOn_exp_comp hUo hUc hL (differentiableOn_logGamma.mono hU) he
    (fun _ hz => exp_logGamma (hU hz)) hz₀ heq

/-- A holomorphic logarithm of Gamma on the slit plane vanishing at `2` is the chosen branch. -/
theorem eqOn_logGamma {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L slitPlane)
    (he : ∀ z ∈ slitPlane, Complex.exp (L z) = Complex.Gamma z) (h2 : L 2 = 0) :
    EqOn L logGamma slitPlane :=
  eqOn_logGamma_of_isOpen isOpen_slitPlane
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    Subset.rfl hL he (ofNat_mem_slitPlane 2) (h2.trans logGamma_two.symm)

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

/-- The normalized branch vanishes at `1` (as well as at `2`). -/
@[simp]
theorem logGamma_one : logGamma 1 = 0 := by
  simpa using logGamma_ofReal (x := 1) one_pos

/-- At `3` the normalized branch takes the value `log 2`. -/
@[simp]
theorem logGamma_three : logGamma 3 = (Real.log 2 : ℂ) := by
  simpa using logGamma_ofReal (x := 3) (by norm_num)

/-- Functional equation of the holomorphic logarithm of Gamma on the slit plane:
`logGamma (z + 1) = logGamma z + Complex.log z`. -/
theorem logGamma_add_one {z : ℂ} (hz : z ∈ slitPlane) :
    logGamma (z + 1) = logGamma z + Complex.log z := by
  have hshift : ∀ w ∈ slitPlane, w + 1 ∈ slitPlane := fun w hw =>
    (mem_slitPlane_iff.mp hw).imp (fun h => by rw [add_re, one_re]; linarith)
      (fun h => by simpa using h)
  have hL₁ : DifferentiableOn ℂ (fun w => logGamma (w + 1)) slitPlane :=
    differentiableOn_logGamma.comp (differentiableOn_id.add (differentiableOn_const 1)) hshift
  have hL₂ : DifferentiableOn ℂ (fun w => logGamma w + Complex.log w) slitPlane :=
    differentiableOn_logGamma.add fun w hw =>
      (Complex.hasDerivAt_log hw).differentiableAt.differentiableWithinAt
  have he₁ : ∀ w ∈ slitPlane, Complex.exp (logGamma (w + 1)) = Complex.Gamma (w + 1) :=
    fun w hw => exp_logGamma (hshift w hw)
  have he₂ : ∀ w ∈ slitPlane,
      Complex.exp (logGamma w + Complex.log w) = Complex.Gamma (w + 1) := fun w hw => by
    rw [Complex.exp_add, exp_logGamma hw, Complex.exp_log (slitPlane_ne_zero hw),
      Complex.Gamma_add_one w (slitPlane_ne_zero hw), mul_comm]
  exact eqOn_of_eqOn_exp_comp isOpen_slitPlane
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    hL₁ hL₂ he₁ he₂ one_mem_slitPlane (by norm_num [logGamma_one]) hz

/-- Iterated functional equation on the slit plane:
`logGamma (z + n) = logGamma z + ∑ k ∈ Finset.range n, Complex.log (z + k)`. -/
theorem logGamma_add_natCast {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    logGamma (z + n) = logGamma z + ∑ k ∈ Finset.range n, Complex.log (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmem : z + (n : ℂ) ∈ slitPlane :=
      (mem_slitPlane_iff.mp hz).imp (fun h => by rw [add_re, natCast_re]; positivity)
        (fun h => by simpa using h)
    rw [Nat.cast_succ, ← add_assoc, logGamma_add_one hmem, ih, Finset.sum_range_succ, add_assoc]

/-- The derivative of the normalized branch is the digamma function. -/
theorem deriv_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    deriv logGamma z = Complex.digamma z := by
  exact deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_slitPlane differentiableOn_logGamma
    (fun _ hw => exp_logGamma hw) hz

/-- Holomorphy on every sector avoiding the negative real axis. All these sectors use the same
branch, so their restrictions agree on every overlap. -/
theorem differentiableOn_logGamma_sector {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ logGamma {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
  refine differentiableOn_logGamma.mono fun z hz => mem_slitPlane_iff_arg.mpr ⟨?_, ?_⟩
  · have harg : z.arg < Real.pi := lt_of_le_of_lt (le_abs_self _) (by linarith [hz.1])
    exact ne_of_lt harg
  · rintro rfl
    norm_num at hz

/-- Uniqueness on sectors: for `0 < δ`, any holomorphic logarithm of Gamma on
`{z | |arg z| < π - δ ∧ 1 < ‖z‖}` vanishing at `2` agrees with `logGamma` there. -/
theorem eqOn_logGamma_sector {δ : ℝ} (hδ : 0 < δ) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖})
    (he : ∀ z ∈ {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖}, Complex.exp (L z) = Complex.Gamma z)
    (h2 : L 2 = 0) :
    EqOn L logGamma {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
  set S : Set ℂ := {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖}
  by_cases hδπ : δ < Real.pi
  · have hSsub : S ⊆ slitPlane := fun z hz => mem_slitPlane_iff_arg.mpr
      ⟨ne_of_lt (lt_of_le_of_lt (le_abs_self _) (by linarith [hz.1])),
        by rintro rfl; exact absurd hz.2 (by norm_num)⟩
    have hSopen : IsOpen S := isOpen_iff_mem_nhds.mpr fun z hz =>
      ((Complex.continuousAt_arg (hSsub hz)).abs.eventually (Iio_mem_nhds hz.1)).and
        (continuous_norm.continuousAt.eventually (Ioi_mem_nhds hz.2))
    have hSimg : S = (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I)) ''
        (Ioi 1 ×ˢ Ioo (-(Real.pi - δ)) (Real.pi - δ)) := by
      ext z
      constructor
      · intro hz
        refine ⟨(‖z‖, z.arg), ⟨hz.2, abs_lt.mp hz.1⟩, Complex.norm_mul_exp_arg_mul_I z⟩
      · rintro ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
        have hr0 : 0 < r := zero_lt_one.trans hr
        have harg : ((r : ℂ) * Complex.exp (θ * I)).arg = θ := by
          rw [arg_real_mul _ hr0, arg_exp_mul_I, toIocMod_eq_self]
          constructor <;> linarith [hθ.1, hθ.2]
        have hnorm : ‖(r : ℂ) * Complex.exp (θ * I)‖ = r := by
          rw [norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real,
            Real.norm_of_nonneg hr0.le, mul_one]
        exact ⟨by rw [harg]; exact abs_lt.mpr hθ, by rw [hnorm]; exact hr⟩
    have hSconn : IsPreconnected S := by
      rw [hSimg]
      exact (isPreconnected_Ioi.prod isPreconnected_Ioo).image _ (by fun_prop)
    have h2S : (2 : ℂ) ∈ S := by
      refine ⟨?_, by norm_num⟩
      have harg2 : (2 : ℂ).arg = 0 := by simp
      rw [harg2, abs_zero]
      linarith
    exact eqOn_logGamma_of_isOpen hSopen hSconn hSsub hL he h2S (h2.trans logGamma_two.symm)
  · intro z hz
    exact absurd hz.1 (by linarith [abs_nonneg z.arg])

end TauCeti
