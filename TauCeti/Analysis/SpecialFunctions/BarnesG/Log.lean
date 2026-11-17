/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.BarnesG.Basic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.ContinuousLog.Basic
import TauCeti.Analysis.Complex.SlitPlane

/-!
# The normalized holomorphic logarithm of the Barnes `G`-function

`TauCeti.logBarnesG` is the holomorphic logarithm of `TauCeti.barnesG` on the slit plane
`ℂ \ (-∞, 0]`, normalized to vanish at `1` (matching `barnesG 1 = 1`). On the positive real axis
it agrees with the real logarithm of `(barnesG x).re`, satisfies Schwarz reflection
`logBarnesG (conj z) = conj (logBarnesG z)`, and obeys the additive Gamma recurrence
`logBarnesG (z + 1) = logBarnesG z + logGamma z` across the entire slit plane.

For every `z` with `z + 1 ∈ Complex.slitPlane` (in particular throughout `Complex.slitPlane` and on
`(-1, ∞)`), `logBarnesG (z + 1)` satisfies the Alexeiewsky–Barnes integral representation
(DLMF 5.17.4)
`logBarnesG (z + 1) = z * log(2π) / 2 - z * (z + 1) / 2 + z * logGamma (z + 1)`
`  - ∫ t in (0 : ℝ)..1, z * logGamma (t * z + 1)`.
This representation expresses `logBarnesG` directly in terms of `logGamma` and its straight-line
integral, providing the analytic foundation for full-sector asymptotic expansions of `logBarnesG`.

## Main definitions

* `TauCeti.logBarnesG`: the holomorphic logarithm of `barnesG` on `Complex.slitPlane`, normalized
  by `logBarnesG 1 = 0`.

## Main results

* `TauCeti.differentiableOn_logBarnesG`, `TauCeti.analyticOnNhd_logBarnesG`,
  `TauCeti.exp_logBarnesG`, `TauCeti.eqOn_logBarnesG`: holomorphy, exponentiation, and branch
  uniqueness on `Complex.slitPlane`.
* `TauCeti.logBarnesG_ofReal`, `TauCeti.logBarnesG_conj`: real-axis agreement and conjugation
  symmetry on `Complex.slitPlane`.
* `TauCeti.logBarnesG_add_one`, `TauCeti.logBarnesG_natCast_add_one`,
  `TauCeti.logBarnesG_natCast_add_two`: additive recurrence with `TauCeti.logGamma` and logarithmic
  superfactorial values at positive integers.
* `TauCeti.deriv_logBarnesG`, `TauCeti.deriv_logBarnesG_add_one`: derivative formulas on the slit
  plane.
* `TauCeti.logBarnesG_add_one_eq_integral`, `TauCeti.logBarnesG_ofReal_add_one_eq_integral`: the
  Alexeiewsky–Barnes integral representation of `logBarnesG (z + 1)` in terms of `logGamma`.
-/

public section

open Complex Set
open scoped BigOperators Nat

namespace TauCeti

/-! ### Construction, uniqueness, and basic symmetries on the slit plane -/

private theorem exists_normalized_logBarnesG :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L slitPlane ∧
      EqOn (Complex.exp ∘ L) barnesG slitPlane ∧ L 1 = 0 := by
  have hsc : IsSimplyConnected slitPlane := by
    let : ContractibleSpace slitPlane :=
      starConvex_one_slitPlane.contractibleSpace ⟨1, one_mem_slitPlane⟩
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hL, he⟩ := exists_differentiableOn_eqOn_exp_comp hsc isOpen_slitPlane
    differentiable_barnesG.differentiableOn
    (by rintro ⟨z, hz, hzero⟩
        exact barnesG_ne_zero_of_mem_slitPlane hz hzero)
  have hone : Complex.exp (L 1) = 1 := by
    simpa using he one_mem_slitPlane
  refine ⟨fun z ↦ L z - L 1, hL.sub_const _, fun z hz ↦ ?_, sub_self _⟩
  simpa [Complex.exp_sub, hone] using he hz

/-- The holomorphic logarithm of `barnesG` on `Complex.slitPlane`, normalized by
`logBarnesG 1 = 0`. Outside the slit plane its values are unspecified. -/
noncomputable def logBarnesG : ℂ → ℂ := Classical.choose exists_normalized_logBarnesG

/-- The normalized logarithm of `barnesG` is holomorphic on the whole slit plane. -/
theorem differentiableOn_logBarnesG : DifferentiableOn ℂ logBarnesG slitPlane :=
  (Classical.choose_spec exists_normalized_logBarnesG).1

/-- Exponentiating `logBarnesG` on the slit plane recovers `barnesG`. -/
@[simp]
theorem exp_logBarnesG {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.exp (logBarnesG z) = barnesG z :=
  (Classical.choose_spec exists_normalized_logBarnesG).2.1 hz

/-- The normalized logarithm of `barnesG` vanishes at `1`. -/
@[simp]
theorem logBarnesG_one : logBarnesG 1 = 0 :=
  (Classical.choose_spec exists_normalized_logBarnesG).2.2

/-- `logBarnesG` is analytic on open neighborhoods throughout `Complex.slitPlane`. -/
theorem analyticOnNhd_logBarnesG : AnalyticOnNhd ℂ logBarnesG slitPlane :=
  differentiableOn_logBarnesG.analyticOnNhd isOpen_slitPlane

/-- Any holomorphic logarithm of `barnesG` on `Complex.slitPlane` vanishing at `1` agrees with
`logBarnesG` on the whole slit plane. -/
theorem eqOn_logBarnesG {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L slitPlane)
    (he : ∀ z ∈ slitPlane, Complex.exp (L z) = barnesG z) (h1 : L 1 = 0) :
    EqOn L logBarnesG slitPlane :=
  eqOn_of_eqOn_exp_comp isOpen_slitPlane
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    hL differentiableOn_logBarnesG (fun z hz ↦ he z hz) (fun _ hz ↦ exp_logBarnesG hz)
    one_mem_slitPlane (h1.trans logBarnesG_one.symm)

/-- On `Complex.slitPlane`, the real part of `logBarnesG z` is `Real.log ‖barnesG z‖`. -/
theorem logBarnesG_re {z : ℂ} (hz : z ∈ slitPlane) :
    (logBarnesG z).re = Real.log ‖barnesG z‖ := by
  rw [← exp_logBarnesG hz, Complex.norm_exp, Real.log_exp]

/-- On the positive real axis, `logBarnesG` agrees with the real logarithm of `(barnesG x).re`. -/
@[simp]
theorem logBarnesG_ofReal {x : ℝ} (hx : 0 < x) :
    logBarnesG x = (Real.log (barnesG x).re : ℂ) := by
  let d : ℝ → ℂ := fun t ↦ logBarnesG t - (Real.log (barnesG t).re : ℂ)
  have hc_re : Continuous (fun t : ℝ ↦ (barnesG (t : ℂ)).re) :=
    Complex.continuous_re.comp (continuous_barnesG.comp continuous_ofReal)
  have hc : ContinuousOn d (Ioi 0) :=
    (differentiableOn_logBarnesG.continuousOn.comp continuous_ofReal.continuousOn
      (fun t ht ↦ ofReal_mem_slitPlane.mpr ht)).sub
      (continuous_ofReal.comp_continuousOn
        (hc_re.continuousOn.log fun t ht ↦ (barnesG_ofReal_re_pos ht).ne'))
  have he : ∀ t ∈ Ioi (0 : ℝ), Complex.exp (d t) = 1 := by
    intro t ht
    rw [Set.mem_Ioi] at ht
    simp only [d, Complex.exp_sub, exp_logBarnesG (ofReal_mem_slitPlane.mpr ht),
      ← Complex.ofReal_exp, Real.exp_log (barnesG_ofReal_re_pos ht),
      ← barnesG_ofReal_eq_re t,
      div_self (barnesG_ne_zero_of_mem_slitPlane (ofReal_mem_slitPlane.mpr ht))]
  have hd : d x = d 1 :=
    eq_of_isPreconnected_of_forall_exp_eq_one (isPreconnected_Ioi.image d hc)
      (by rintro _ ⟨t, ht, rfl⟩; exact he t ht) ⟨x, hx, rfl⟩ ⟨1, zero_lt_one, rfl⟩
  have hd1 : d 1 = 0 := by simp [d]
  exact sub_eq_zero.mp (hd.trans hd1)

/-- At `z = 2`, the normalized logarithm vanishes. -/
@[simp]
theorem logBarnesG_two : logBarnesG 2 = 0 := by
  simpa using logBarnesG_ofReal (x := 2) (by norm_num)

/-- At `z = 3`, the normalized logarithm vanishes. -/
@[simp]
theorem logBarnesG_three : logBarnesG 3 = 0 := by
  simpa using logBarnesG_ofReal (x := 3) (by norm_num)

/-- At `z = 4`, the normalized logarithm equals `log 2`. -/
@[simp]
theorem logBarnesG_four : logBarnesG 4 = (Real.log 2 : ℂ) := by
  simpa [barnesG_four] using logBarnesG_ofReal (x := 4) (by norm_num)

/-- Schwarz reflection for `logBarnesG` on `Complex.slitPlane`. -/
theorem logBarnesG_conj {z : ℂ} (hz : z ∈ slitPlane) :
    logBarnesG (starRingEnd ℂ z) = starRingEnd ℂ (logBarnesG z) := by
  have hconj {w : ℂ} (hw : w ∈ slitPlane) : starRingEnd ℂ w ∈ slitPlane := by
    simpa [mem_slitPlane_iff] using hw
  let d : ℂ → ℂ := fun w ↦ logBarnesG (starRingEnd ℂ w) - starRingEnd ℂ (logBarnesG w)
  have hc : ContinuousOn d slitPlane :=
    (differentiableOn_logBarnesG.continuousOn.comp continuous_conj.continuousOn
      fun _ hw ↦ hconj hw).sub
      (continuous_conj.comp_continuousOn differentiableOn_logBarnesG.continuousOn)
  have he : ∀ w ∈ slitPlane, Complex.exp (d w) = 1 := by
    intro w hw
    have hne : starRingEnd ℂ (barnesG w) ≠ 0 := by
      simp [barnesG_ne_zero_of_mem_slitPlane hw]
    simp only [d, Complex.exp_sub, exp_logBarnesG (hconj hw), Complex.exp_conj,
      exp_logBarnesG hw, barnesG_conj, div_self hne]
  have hconn : IsPreconnected slitPlane :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  have hd : d z = d 1 :=
    eq_of_isPreconnected_of_forall_exp_eq_one (hconn.image d hc)
      (by rintro _ ⟨w, hw, rfl⟩; exact he w hw) ⟨z, hz, rfl⟩ ⟨1, one_mem_slitPlane, rfl⟩
  have hd1 : d 1 = 0 := by simp [d]
  exact sub_eq_zero.mp (hd.trans hd1)

/-! ### Additive Gamma recurrence, derivatives, and sectors -/

/-- Additive functional equation on the slit plane:
`logBarnesG (z + 1) = logBarnesG z + logGamma z`. -/
theorem logBarnesG_add_one {z : ℂ} (hz : z ∈ slitPlane) :
    logBarnesG (z + 1) = logBarnesG z + logGamma z := by
  have hshift {w : ℂ} (hw : w ∈ slitPlane) : w + 1 ∈ slitPlane := by
    simpa [add_comm] using ofReal_add_mem_slitPlane hw zero_le_one
  let L : ℂ → ℂ := fun w ↦ logBarnesG (w + 1) - logGamma w
  have hL : DifferentiableOn ℂ L slitPlane :=
    (differentiableOn_logBarnesG.comp (differentiable_id.add_const 1).differentiableOn
      fun _ hw ↦ hshift hw).sub differentiableOn_logGamma
  have he : ∀ w ∈ slitPlane, Complex.exp (L w) = barnesG w := by
    intro w hw
    rw [Complex.exp_sub, exp_logBarnesG (hshift hw), exp_logGamma hw,
      barnesG_add_one (slitPlane_ne_zero hw),
      mul_div_cancel_left₀ _ (Complex.Gamma_ne_zero (ne_neg_natCast_of_mem_slitPlane hw))]
  have hlg1 : logGamma 1 = 0 := by
    simpa using logGamma_ofReal (x := 1) zero_lt_one
  have h11 : (1 : ℂ) + 1 = 2 := by ring
  have h1 : L 1 = 0 := by simp [L, h11, hlg1]
  exact sub_eq_iff_eq_add.mp (eqOn_logBarnesG hL he h1 hz)

/-- At positive integers `n + 1`, `logBarnesG (n + 1)` is the sum of `log (k!)` for `k < n`. -/
theorem logBarnesG_natCast_add_one (n : ℕ) :
    logBarnesG (n + 1) = ∑ k ∈ Finset.range n, (Real.log (k ! : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn_slit : ((n : ℂ) + 1) ∈ slitPlane := by
      exact_mod_cast ofReal_mem_slitPlane.mpr (Nat.cast_add_one_pos (α := ℝ) n)
    have hlg : logGamma ((n : ℂ) + 1) = (Real.log (n ! : ℝ) : ℂ) := by
      have h := logGamma_ofReal (x := (n : ℝ) + 1) (Nat.cast_add_one_pos n)
      rw [Real.Gamma_nat_eq_factorial] at h
      simpa using h
    rw [Nat.cast_succ, logBarnesG_add_one hn_slit, ih, hlg, Finset.sum_range_succ]

/-- At positive integers `n + 2`, `logBarnesG (n + 2)` equals `Real.log (Nat.superFactorial n)`. -/
theorem logBarnesG_natCast_add_two (n : ℕ) :
    logBarnesG (n + 2) = (Real.log (Nat.superFactorial n) : ℂ) := by
  have hx : 0 < (n : ℝ) + 2 := by positivity
  have h := logBarnesG_ofReal hx
  have hcast : (((n : ℝ) + 2 : ℝ) : ℂ) = (n : ℂ) + 2 := by push_cast; ring
  rw [hcast, barnesG_natCast_add_two, natCast_re] at h
  exact h

/-- The complex derivative of `logBarnesG` on `Complex.slitPlane` is `logDeriv barnesG`. -/
theorem deriv_logBarnesG {z : ℂ} (hz : z ∈ slitPlane) :
    deriv logBarnesG z = logDeriv barnesG z :=
  deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_slitPlane differentiableOn_logBarnesG
    (fun _ hw ↦ exp_logBarnesG hw) hz

/-- For every `z` with `z + 1 ∈ Complex.slitPlane` (including `z = 0`),
`deriv logBarnesG (z + 1) = log(2π) / 2 - 1 / 2 - z + z * digamma (z + 1)`. -/
theorem deriv_logBarnesG_add_one {z : ℂ} (hz : z + 1 ∈ slitPlane) :
    deriv logBarnesG (z + 1) =
      (Real.log (2 * Real.pi) : ℂ) / 2 - 1 / 2 - z + z * Complex.digamma (z + 1) := by
  have hz_succ : ∀ n : ℕ, z ≠ -((n : ℂ) + 1) := fun n h ↦
    ne_neg_natCast_of_mem_slitPlane hz n (by linear_combination h)
  rw [deriv_logBarnesG hz, logDeriv_barnesG_add_one_of_ne_neg_succ hz_succ]

/-- On `Complex.slitPlane`, `deriv logBarnesG (z + 1)` also takes the unshifted digamma form
`log(2π) / 2 + 1 / 2 - z + z * digamma z`. -/
theorem deriv_logBarnesG_add_one_of_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) :
    deriv logBarnesG (z + 1) =
      (Real.log (2 * Real.pi) : ℂ) / 2 + 1 / 2 - z + z * Complex.digamma z := by
  have hshift : z + 1 ∈ slitPlane := by
    simpa [add_comm] using ofReal_add_mem_slitPlane hz zero_le_one
  rw [deriv_logBarnesG hshift, logDeriv_barnesG_add_one (ne_neg_natCast_of_mem_slitPlane hz)]

/-- Holomorphy of `logBarnesG` on every sector avoiding the negative real axis; all sector
restrictions share the single normalized branch on `Complex.slitPlane`. -/
theorem differentiableOn_logBarnesG_sector {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ logBarnesG {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
  refine differentiableOn_logBarnesG.mono fun z hz ↦ mem_slitPlane_iff_arg.mpr ⟨?_, ?_⟩
  · have harg : z.arg < Real.pi := lt_of_le_of_lt (le_abs_self _) (by linarith [hz.1])
    exact ne_of_lt harg
  · rintro rfl
    norm_num at hz

/-! ### Alexeiewsky–Barnes integral representation -/

private noncomputable def logBarnesGAntideriv (w : ℂ) : ℂ :=
  logBarnesG (w + 1) -
    (w * (Real.log (2 * Real.pi) : ℂ) / 2 - w * (w + 1) / 2 + w * logGamma (w + 1))

private theorem hasDerivAt_logBarnesGAntideriv {w : ℂ} (hw : w + 1 ∈ slitPlane) :
    HasDerivAt logBarnesGAntideriv (-logGamma (w + 1)) w := by
  have hd_lb : HasDerivAt (fun u : ℂ ↦ logBarnesG (u + 1))
      ((Real.log (2 * Real.pi) : ℂ) / 2 - 1 / 2 - w + w * Complex.digamma (w + 1)) w := by
    have hdiff : DifferentiableAt ℂ logBarnesG (w + 1) :=
      differentiableOn_logBarnesG.differentiableAt (isOpen_slitPlane.mem_nhds hw)
    have hc := hdiff.hasDerivAt.comp w ((hasDerivAt_id w).add_const (1 : ℂ))
    rw [Function.comp_def] at hc
    exact hc.congr_deriv (by rw [deriv_logBarnesG_add_one hw]; ring)
  have hd_lin : HasDerivAt (fun u : ℂ ↦ u * (Real.log (2 * Real.pi) : ℂ) / 2)
      ((Real.log (2 * Real.pi) : ℂ) / 2) w := by
    have hm := ((hasDerivAt_id w).mul_const (Real.log (2 * Real.pi) : ℂ)).div_const 2
    exact hm.congr_deriv (by ring)
  have hd_quad : HasDerivAt (fun u : ℂ ↦ u * (u + 1) / 2) (w + 1 / 2) w := by
    have hm := (((hasDerivAt_id w).mul ((hasDerivAt_id w).add_const 1)).div_const 2)
    refine hm.congr_deriv ?_
    simp only [id_eq]
    ring
  have hd_lg : HasDerivAt (fun u : ℂ ↦ u * logGamma (u + 1))
      (logGamma (w + 1) + w * Complex.digamma (w + 1)) w := by
    have hdiff : DifferentiableAt ℂ logGamma (w + 1) :=
      differentiableOn_logGamma.differentiableAt (isOpen_slitPlane.mem_nhds hw)
    have hc : HasDerivAt (fun u : ℂ ↦ logGamma (u + 1)) (Complex.digamma (w + 1)) w := by
      have hm := hdiff.hasDerivAt.comp w ((hasDerivAt_id w).add_const (1 : ℂ))
      rw [Function.comp_def] at hm
      exact hm.congr_deriv (by rw [deriv_logGamma hw]; ring)
    exact ((hasDerivAt_id w).fun_mul hc).congr_deriv (by simp only [id_eq]; ring)
  refine (hd_lb.sub ((hd_lin.sub hd_quad).add hd_lg)).congr_deriv ?_
  ring

/-- **Alexeiewsky–Barnes integral representation** (DLMF 5.17.4): for every `z : ℂ` with
`z + 1 ∈ Complex.slitPlane` (in particular for every `z ∈ Complex.slitPlane`),
`logBarnesG (z + 1)` is expressed in terms of `logGamma` and its straight-line integral from `1`
to `z + 1`. -/
theorem logBarnesG_add_one_eq_integral {z : ℂ} (hz : z + 1 ∈ slitPlane) :
    logBarnesG (z + 1) =
      z * (Real.log (2 * Real.pi) : ℂ) / 2 - z * (z + 1) / 2 + z * logGamma (z + 1) -
        ∫ t in (0 : ℝ)..1, z * logGamma ((t : ℂ) * z + 1) := by
  have hseg : ∀ t ∈ uIcc (0 : ℝ) 1, (t : ℂ) * z + 1 ∈ slitPlane := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hz' : 1 + z ∈ slitPlane := by rwa [add_comm] at hz
    have hsmul := StarConvex.add_smul_mem starConvex_one_slitPlane hz' ht.1 ht.2
    have h_eq : (1 : ℂ) + t • z = (t : ℂ) * z + 1 := by
      rw [Complex.real_smul]
      ring
    rwa [h_eq] at hsmul
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ logBarnesGAntideriv ((s : ℂ) * z))
        (-(z * logGamma ((t : ℂ) * z + 1))) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℂ ↦ logBarnesGAntideriv (u * z))
        (-(z * logGamma ((t : ℂ) * z + 1))) (t : ℂ) := by
      have hm := (hasDerivAt_logBarnesGAntideriv (hseg t ht)).comp (t : ℂ)
        ((hasDerivAt_id (t : ℂ)).mul_const z)
      rw [Function.comp_def] at hm
      exact hm.congr_deriv (by ring)
    exact hc.comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ ↦ -(z * logGamma ((t : ℂ) * z + 1))) (uIcc (0 : ℝ) 1) := by
    have hlg : ContinuousOn (fun t : ℝ ↦ logGamma ((t : ℂ) * z + 1)) (uIcc (0 : ℝ) 1) :=
      differentiableOn_logGamma.continuousOn.comp
        ((continuous_ofReal.mul continuous_const).add continuous_const).continuousOn hseg
    exact (hlg.const_mul z).neg
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have h0 : logBarnesGAntideriv (((0 : ℝ) : ℂ) * z) = 0 := by simp [logBarnesGAntideriv]
  have h1 : logBarnesGAntideriv (((1 : ℝ) : ℂ) * z) = logBarnesGAntideriv z := by simp
  rw [intervalIntegral.integral_neg, h0, h1, sub_zero] at hint
  dsimp only [logBarnesGAntideriv] at hint
  linear_combination -hint

/-- Real-interval form of the Alexeiewsky–Barnes integral representation: for every real `x > -1`,
`logBarnesG (x + 1) = x * log(2π) / 2 - x * (x + 1) / 2 + x * logGamma (x + 1)`
`  - ∫ t in 0..x, logGamma (t + 1)`. -/
theorem logBarnesG_ofReal_add_one_eq_integral {x : ℝ} (hx : -1 < x) :
    logBarnesG ((x : ℂ) + 1) =
      (x : ℂ) * (Real.log (2 * Real.pi) : ℂ) / 2 - (x : ℂ) * ((x : ℂ) + 1) / 2 +
        (x : ℂ) * logGamma ((x : ℂ) + 1) - ∫ t in (0 : ℝ)..x, logGamma ((t : ℂ) + 1) := by
  have hpos : 0 < x + 1 := by linarith
  have hslit : (x : ℂ) + 1 ∈ slitPlane := by
    exact_mod_cast ofReal_mem_slitPlane.mpr hpos
  rw [logBarnesG_add_one_eq_integral hslit]
  have hsub : (∫ t in (0 : ℝ)..1, (x : ℂ) * logGamma ((t : ℂ) * (x : ℂ) + 1)) =
      ∫ u in (0 : ℝ)..x, logGamma ((u : ℂ) + 1) := by
    have hsmul : (fun t : ℝ ↦ (x : ℂ) * logGamma ((t : ℂ) * (x : ℂ) + 1)) =
        fun t : ℝ ↦ x • logGamma (((t * x : ℝ) : ℂ) + 1) := by
      ext t
      rw [Complex.real_smul, Complex.ofReal_mul]
    rw [hsmul, intervalIntegral.integral_smul,
      intervalIntegral.smul_integral_comp_mul_right (f := fun u : ℝ ↦ logGamma ((u : ℂ) + 1)) x,
      zero_mul, one_mul]
  rw [hsub]

end TauCeti
