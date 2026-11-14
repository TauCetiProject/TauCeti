/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Order.Interval.Set.Infinite
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.Conformal.BlaschkeProduct
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.Poisson.Integral
import TauCeti.Analysis.Complex.Poisson.Logarithm
import TauCeti.Analysis.Complex.ValueDistribution.Proximity.Basic
import TauCeti.Analysis.SpecialFunctions.Integrability.PosLog
import TauCeti.Analysis.SpecialFunctions.Log.PosLog

/-!
# Nevanlinna's quotient representation and its optimality

Given a function `g : ℂ → ℂ` analytic on a neighbourhood of a closed disc `closedBall 0 R`,
Nevanlinna's quotient representation expresses `g` as a quotient `f₁ / h` of bounded analytic
functions near `closedBall 0 R` normalized by `h 0 = 1`, controlling both `Real.log ‖h z‖` and
`Real.log ‖h z * g z‖` on the disc in terms of the Nevanlinna proximity function
`m(R, g) = ValueDistribution.proximity g ⊤ R = circleAverage (Real.posLog ‖g ·‖) 0 R`.

The construction proceeds in three steps:

1. **Blaschke factorization on a zero-free circle**
   (`AnalyticOnNhd.exists_blaschkeProduct_div_mul_eq` in
   `TauCeti.Analysis.Complex.Conformal.BlaschkeProduct`).
   When `g` is analytic on `closedBall 0 r` (`0 < r`) and has no zeros on `sphere 0 r`, `g` factors
   throughout `closedBall 0 r` as `g z = blaschkeProduct a n (z / r) * G z` with interior parameters
   `‖a i‖ < 1` and `G` analytic and zero-free on `closedBall 0 r`.
2. **The radius-`r` quotient multiplier (`TauCeti.quotientMultiplier`).**
   Setting
   `quotientMultiplier g r z = exp (m(r, g) - circleAverage (w ↦ H(z, w) • log⁺ ‖g w‖) 0 r)`,
   where `H(z, w) = herglotzRieszKernel 0 z w`, gives a zero-free function analytic off
   `sphere 0 |r|` with `quotientMultiplier g r 0 = 1` (`r ≠ 0`). Combining the exponentiated
   Herglotz formula for `G` with `log ‖g‖ = log⁺ ‖g‖ - log⁺ ‖g‖⁻¹` yields the complex product
   identity `AnalyticOnNhd.quotientMultiplier_mul_of_norm_eq` (exhibiting the unimodular centre
   phase `G 0 / ‖G 0‖`) and the interior bounds
   `Real.log ‖quotientMultiplier g r z‖ ≤ m(r, g)` and
   `Real.log ‖quotientMultiplier g r z * g z‖ ≤ m(r, g)` for `z ∈ ball 0 r`.
3. **Radial smoothing across boundary zeros (`AnalyticOnNhd.exists_log_norm_le_proximity_add`).**
   When `g` has zeros on `sphere 0 R` (for instance `g z = z - 1` at `R = 1`), the zero-free
   Herglotz formula does not apply on `closedBall 0 R` directly. Extending `g` to a slightly larger
   open disc, choosing `r > R` avoiding the finitely many zeros of `g` there, and using local radial
   continuity of `r ↦ m(r, g)` (`ContinuousOn.continuousAt_proximity_top`) yields `h` analytic near
   `closedBall 0 R` with `h 0 = 1` and both `Real.log ‖h z‖` and `Real.log ‖h z * g z‖` bounded by
   `m(R, g) + ε` on `closedBall 0 R`.

Conversely, Jensen's inequality at `h 0 = 1` (`AnalyticOnNhd.log_norm_le_circleAverage_log_norm`)
together with the pointwise bound `log ‖h z‖ + log⁺ ‖g z‖ ≤ max (log ‖h z‖) (log ‖h z * g z‖)` off
the isolated zeros of `h` on `sphere 0 R` shows that no multiplier `h` with `1 ≤ ‖h 0‖` can improve
upon `m(R, g)` (`AnalyticOnNhd.proximity_top_le_of_forall_mem_sphere_log_norm_le` and
`AnalyticOnNhd.proximity_top_le_max_sSup_log_norm`), identifying `m(R, g)` as the infimum over all
normalized multipliers (`AnalyticOnNhd.sInf_max_sSup_log_norm_eq_proximity_top`).

## Main definitions

* `TauCeti.quotientMultiplier g r`: Nevanlinna's radius-`r` quotient multiplier
  `z ↦ exp (m(r, g) - circleAverage (w ↦ herglotzRieszKernel 0 z w • log⁺ ‖g w‖) 0 r)`.

## Main results

* `TauCeti.log_norm_quotientMultiplier_le_proximity`,
  `AnalyticOnNhd.quotientMultiplier_mul_of_norm_eq`, and
  `AnalyticOnNhd.log_norm_quotientMultiplier_mul_le_proximity`: the complex product identity (with
  centre phase `G 0 / ‖G 0‖`) and interior logarithmic bounds for `quotientMultiplier g r` and
  `quotientMultiplier g r * g`.
* `AnalyticOnNhd.exists_gt_log_norm_quotientMultiplier_le_proximity_add`,
  `AnalyticOnNhd.exists_log_norm_le_proximity_add`, and
  `AnalyticOnNhd.exists_max_sSup_log_norm_le_proximity_add`: radial smoothing of
  `quotientMultiplier` across boundary zeros and Nevanlinna's quotient representation.
* `MeromorphicOn.eventuallyEq_codiscreteWithin_log_norm_add_posLog`,
  `AnalyticOnNhd.proximity_top_le_of_forall_mem_sphere_log_norm_le`,
  `AnalyticOnNhd.proximity_top_le_max_sSup_log_norm`, and
  `AnalyticOnNhd.sInf_max_sSup_log_norm_eq_proximity_top`: codiscrete log-norm splitting, optimality
  of the quotient bound, and variational characterization of `m(R, g)`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), Lemma 2.3.1 and Remark 2.3.3 (pp. 639–641).
* R. Nevanlinna, *Analytic Functions*, Grundlehren der mathematischen Wissenschaften **162**,
  Springer (1970), Chapter VI.
-/

public section

open Complex Filter MeasureTheory Metric Real Set Topology

namespace TauCeti

/-! ### Nevanlinna's quotient multiplier -/

/-- **Nevanlinna's quotient multiplier** on the disc of radius `r`:
`quotientMultiplier g r z =`
`exp (m(r, g) - circleAverage (w ↦ herglotzRieszKernel 0 z w • log⁺ ‖g w‖) 0 r)`,
where `m(r, g) = ValueDistribution.proximity g ⊤ r`. -/
noncomputable def quotientMultiplier (g : ℂ → ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((ValueDistribution.proximity g ⊤ r : ℂ) -
    circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖ : ℂ)) 0 r)

/-- Defining formula for `TauCeti.quotientMultiplier`. -/
lemma quotientMultiplier_apply (g : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    quotientMultiplier g r z =
      Complex.exp ((ValueDistribution.proximity g ⊤ r : ℂ) -
        circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖ : ℂ)) 0 r) :=
  (rfl)

/-- The quotient multiplier is nowhere zero. -/
@[simp]
lemma quotientMultiplier_ne_zero (g : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    quotientMultiplier g r z ≠ 0 :=
  Complex.exp_ne_zero _

/-- For a constant `c` of norm at most `1`, `log⁺ ‖c‖ = 0` and the quotient multiplier is `1`. -/
lemma quotientMultiplier_const_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) (r : ℝ) (z : ℂ) :
    quotientMultiplier (fun _ ↦ c) r z = 1 := by
  have hlog : Real.posLog ‖c‖ = 0 := (Real.posLog_eq_zero_iff ‖c‖).mpr (by simpa using hc)
  simp [quotientMultiplier_apply, hlog, circleAverage_const]

@[simp]
lemma quotientMultiplier_zero_left (r : ℝ) (z : ℂ) :
    quotientMultiplier 0 r z = 1 := by
  rw [Pi.zero_def]
  exact quotientMultiplier_const_of_norm_le_one (by norm_num) r z

@[simp]
lemma quotientMultiplier_one_left (r : ℝ) (z : ℂ) :
    quotientMultiplier 1 r z = 1 := by
  rw [Pi.one_def]
  exact quotientMultiplier_const_of_norm_le_one (by norm_num) r z

/-- For any nonzero radius `r`, the quotient multiplier is normalized by `h_r(0) = 1`. -/
@[simp]
lemma quotientMultiplier_apply_zero (g : ℂ → ℂ) {r : ℝ} (hr : r ≠ 0) :
    quotientMultiplier g r 0 = 1 := by
  have hsphere : EqOn (fun w ↦ herglotzRieszKernel 0 0 w • (Real.posLog ‖g w‖ : ℂ))
      (fun w ↦ (Real.posLog ‖g w‖ : ℂ)) (sphere 0 |r|) := by
    intro w hw
    have hw0 : w ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hw
      exact norm_ne_zero_iff.mp (hw.trans_ne (abs_ne_zero.mpr hr))
    simp [herglotzRieszKernel_def, div_self hw0]
  have havg : circleAverage (fun w ↦ (Real.posLog ‖g w‖ : ℂ)) 0 r =
      (ValueDistribution.proximity g ⊤ r : ℂ) := by
    simp [ValueDistribution.proximity_top, circleAverage_def, real_smul,
      intervalIntegral.integral_ofReal]
  rw [quotientMultiplier_apply, circleAverage_congr_sphere hsphere, havg, sub_self,
    Complex.exp_zero]

/-- When `log⁺ ‖g‖` is circle-integrable on `sphere 0 |r|`, `quotientMultiplier g r` is analytic on
the complement of `sphere 0 |r|` (in particular on `ball 0 |r|`). -/
lemma analyticOnNhd_quotientMultiplier {g : ℂ → ℂ} {r : ℝ}
    (hg : CircleIntegrable (fun w ↦ Real.posLog ‖g w‖) 0 r) :
    AnalyticOnNhd ℂ (quotientMultiplier g r) (sphere 0 |r|)ᶜ := by
  have hg' : CircleIntegrable (fun w ↦ (Real.posLog ‖g w‖ : ℂ)) 0 r := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  intro z hz
  exact (analyticAt_const.sub
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hg' z hz)).cexp'

/-- Nonnegative circle-integrable boundary data have nonnegative Herglotz–Riesz real part on the
open disc `ball 0 r`. -/
private lemma re_circleAverage_herglotzRieszKernel_smul_nonneg {φ : ℂ → ℝ} {r : ℝ} {z : ℂ}
    (hφ : CircleIntegrable φ 0 r) (hnonneg : ∀ w ∈ sphere (0 : ℂ) |r|, 0 ≤ φ w)
    (hz : z ∈ ball 0 r) :
    0 ≤ (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (φ w : ℂ)) 0 r).re := by
  have hr : 0 < r := pos_of_mem_ball hz
  have hz_abs : z ∈ ball (0 : ℂ) |r| := by rwa [abs_of_pos hr]
  have hz_not : z ∉ sphere (0 : ℂ) |r| := Set.disjoint_right.mp sphere_disjoint_ball hz_abs
  rw [re_circleAverage_herglotzRieszKernel_smul hφ hz_not,
    ← poissonKernel_eq_re_herglotzRieszKernel, ← planarPoissonIntegral_def]
  exact planarPoissonIntegral_nonneg hz_abs hnonneg

/-- When `log⁺ ‖g‖` is circle-integrable on `sphere 0 |r|`, nonnegativity of the Poisson average of
`log⁺ ‖g‖` bounds `Real.log ‖quotientMultiplier g r z‖` by `ValueDistribution.proximity g ⊤ r` for
every `z ∈ ball 0 r`. -/
lemma log_norm_quotientMultiplier_le_proximity {g : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hg : CircleIntegrable (fun w ↦ Real.posLog ‖g w‖) 0 r) (hz : z ∈ ball 0 r) :
    Real.log ‖quotientMultiplier g r z‖ ≤ ValueDistribution.proximity g ⊤ r := by
  rw [quotientMultiplier_apply, Complex.norm_exp, Real.log_exp, Complex.sub_re, Complex.ofReal_re]
  linarith [re_circleAverage_herglotzRieszKernel_smul_nonneg hg (fun _ _ ↦ Real.posLog_nonneg) hz]

end TauCeti

/-- For meromorphic functions `f, g : 𝕜 → 𝕜` of finite meromorphic order on `U`, off a discrete
subset of `U` (where neither vanishes nor has a pole), `log ‖f z‖ + log⁺ ‖g z‖` agrees with
`max (log ‖f z‖) (log ‖f z * g z‖)`. -/
theorem MeromorphicOn.eventuallyEq_codiscreteWithin_log_norm_add_posLog
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {f g : 𝕜 → 𝕜}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hord_f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤)
    (hord_g : ∀ u ∈ U, meromorphicOrderAt g u ≠ ⊤) :
    ((fun z ↦ Real.log ‖f z‖) + fun z ↦ Real.posLog ‖g z‖) =ᶠ[codiscreteWithin U]
      fun z ↦ max (Real.log ‖f z‖) (Real.log ‖f z * g z‖) := by
  filter_upwards [hf.codiscreteWithin_setOfPred_ne_zero hord_f,
    hg.codiscreteWithin_setOfPred_ne_zero hord_g] with z hzf hzg
  simp [Pi.add_apply, Real.posLog_apply, add_max, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hzf) (norm_ne_zero_iff.mpr hzg)]

namespace AnalyticOnNhd

/-! ### Complex product identity and Nevanlinna's quotient representation -/

/-- **Complex product identity for the quotient multiplier.** If `G` is analytic and zero-free near
`closedBall 0 r` and `‖g‖ = ‖G‖` on `sphere 0 r`, then for every `z ∈ ball 0 r`
`quotientMultiplier g r z * G z` equals `(G 0 / ‖G 0‖)` times
`exp (m(r, g) - circleAverage (w ↦ herglotzRieszKernel 0 z w • log⁺ ‖g w‖⁻¹) 0 r)`. -/
theorem quotientMultiplier_mul_of_norm_eq {g G : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hG : AnalyticOnNhd ℂ G (closedBall 0 r)) (hG0 : ∀ w ∈ closedBall 0 r, G w ≠ 0)
    (hgnorm : EqOn (fun w ↦ ‖g w‖) (fun w ↦ ‖G w‖) (sphere 0 r)) (hz : z ∈ ball 0 r) :
    TauCeti.quotientMultiplier g r z * G z =
      (G 0 / ‖G 0‖) * Complex.exp ((ValueDistribution.proximity g ⊤ r : ℂ) -
        circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖⁻¹ : ℂ)) 0 r) := by
  have hr : 0 < r := pos_of_mem_ball hz
  have hz_not : z ∉ sphere (0 : ℂ) |r| := by
    rw [abs_of_pos hr, mem_sphere_zero_iff_norm]
    exact (mem_ball_zero_iff.mp hz).ne
  have hGc : G 0 ≠ 0 := hG0 0 (mem_closedBall_self hr.le)
  have hG_norm_ne : (‖G 0‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hGc)
  have hexpG := hG.exp_circleAverage_herglotzRieszKernel_smul_log_norm hG0 hz
  have hGz : G z = (G 0 / ‖G 0‖) *
      Complex.exp (circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r) :=
    by rw [hexpG]; field_simp
  -- Transfer continuity of the norm from `G` to `g` on `sphere 0 |r|` and split
  -- `log ‖G‖ = log⁺ ‖g‖ - log⁺ ‖g‖⁻¹`.
  have hcont_G : ContinuousOn (fun w ↦ ‖G w‖) (sphere 0 |r|) := by
    rw [abs_of_pos hr]
    exact (hG.continuousOn.mono sphere_subset_closedBall).norm
  have hcont_g : ContinuousOn (fun w ↦ ‖g w‖) (sphere 0 |r|) :=
    hcont_G.congr fun w hw ↦ hgnorm (by rwa [abs_of_pos hr] at hw)
  have hcont_ker : ContinuousOn (herglotzRieszKernel 0 z) (sphere 0 |r|) :=
    continuousOn_herglotzRieszKernel_sphere hz_not
  have hint_pos : CircleIntegrable
      (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖ : ℂ)) 0 r :=
    (continuous_ofReal.comp_continuousOn
      (continuous_posLog.comp_continuousOn hcont_g)).circleIntegrable'.continuousOn_smul hcont_ker
  have hint_inv : CircleIntegrable
      (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖⁻¹ : ℂ)) 0 r := by
    have hcont_inv : ContinuousOn (fun w ↦ ‖g w‖⁻¹) (sphere 0 |r|) :=
      hcont_g.inv₀ fun w hw ↦ by
        rw [abs_of_pos hr] at hw
        exact (hgnorm hw).trans_ne (norm_ne_zero_iff.mpr (hG0 w (sphere_subset_closedBall hw)))
    exact (continuous_ofReal.comp_continuousOn
      (continuous_posLog.comp_continuousOn hcont_inv)).circleIntegrable'.continuousOn_smul hcont_ker
  have hsplit : circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.log ‖G w‖ : ℂ)) 0 r =
      circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖ : ℂ)) 0 r -
        circleAverage (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖⁻¹ : ℂ)) 0 r := by
    rw [← circleAverage_sub hint_pos hint_inv]
    refine circleAverage_congr_sphere fun w hw ↦ ?_
    rw [abs_of_pos hr] at hw
    have hgw : ‖G w‖ = ‖g w‖ := (hgnorm hw).symm
    simp only [Pi.sub_apply, hgw, ← Real.posLog_sub_posLog_inv, Complex.ofReal_sub, smul_sub]
  rw [hGz, TauCeti.quotientMultiplier_apply, hsplit, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- **Interior product bound for the quotient multiplier.** If `g` is analytic on a neighbourhood of
`closedBall 0 r` and has no zeros on `sphere 0 r`, then for every `z ∈ ball 0 r`
`Real.log ‖quotientMultiplier g r z * g z‖ ≤ ValueDistribution.proximity g ⊤ r`. -/
theorem log_norm_quotientMultiplier_mul_le_proximity {g : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r)) (hs : ∀ w ∈ sphere 0 r, g w ≠ 0)
    (hz : z ∈ ball 0 r) :
    Real.log ‖TauCeti.quotientMultiplier g r z * g z‖ ≤ ValueDistribution.proximity g ⊤ r := by
  have hr : 0 < r := pos_of_mem_ball hz
  obtain ⟨ι, _, a, n, G, ha, hG, hG0, hg_eq⟩ := hg.exists_blaschkeProduct_div_mul_eq hr hs
  have hgnorm : EqOn (fun w ↦ ‖g w‖) (fun w ↦ ‖G w‖) (sphere 0 r) := by
    intro w hw
    have hwr : ‖w / r‖ = 1 := by
      rw [norm_div, mem_sphere_zero_iff_norm.mp hw, Complex.norm_real, Real.norm_of_nonneg hr.le,
        div_self hr.ne']
    simp only
    rw [hg_eq w (sphere_subset_closedBall hw), norm_mul,
      TauCeti.norm_blaschkeProduct_eq_one (fun i ↦ (ha i).le) hwr, one_mul]
  have hprod : TauCeti.quotientMultiplier g r z * g z =
      TauCeti.blaschkeProduct a n (z / r) * (TauCeti.quotientMultiplier g r z * G z) := by
    rw [hg_eq z (ball_subset_closedBall hz)]
    ring
  have hB_le : ‖TauCeti.blaschkeProduct a n (z / r)‖ ≤ 1 := by
    refine TauCeti.norm_blaschkeProduct_le_one (fun i ↦ (ha i).le) ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_le_one hr]
    exact (mem_ball_zero_iff.mp hz).le
  have hphase_norm : ‖G 0 / ‖G 0‖‖ = 1 := by
    have hGc : ‖G 0‖ ≠ 0 := norm_ne_zero_iff.mpr (hG0 0 (mem_closedBall_self hr.le))
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hGc]
  have hg_abs : AnalyticOnNhd ℂ g (closedBall 0 |r|) := by rwa [abs_of_pos hr]
  have hint_inv : CircleIntegrable (fun w ↦ Real.posLog ‖g w‖⁻¹) 0 r :=
    (hg_abs.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_posLog_inv_norm
  have hnonneg : 0 ≤ (circleAverage
      (fun w ↦ herglotzRieszKernel 0 z w • (Real.posLog ‖g w‖⁻¹ : ℂ)) 0 r).re :=
    TauCeti.re_circleAverage_herglotzRieszKernel_smul_nonneg hint_inv
      (fun _ _ ↦ Real.posLog_nonneg) hz
  have hexp_le : ‖TauCeti.quotientMultiplier g r z * g z‖ ≤
      Real.exp (ValueDistribution.proximity g ⊤ r) := by
    rw [hprod, hG.quotientMultiplier_mul_of_norm_eq hG0 hgnorm hz, norm_mul, norm_mul,
      hphase_norm, one_mul, Complex.norm_exp, Complex.sub_re, Complex.ofReal_re]
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) hB_le).trans
      (Real.exp_le_exp.mpr (by linarith))
  rcases (norm_nonneg (TauCeti.quotientMultiplier g r z * g z)).eq_or_lt with h0 | hpos
  · simp only [← h0, Real.log_zero]
    exact ValueDistribution.proximity_nonneg r
  · exact (Real.log_le_log hpos hexp_le).trans_eq (Real.log_exp _)

/-! ### Radial smoothing across boundary zeros -/

/-- **Radial smoothing of the quotient multiplier across boundary zeros.** If `g` is analytic on a
neighbourhood of `closedBall 0 R` (`0 < R`), does not vanish identically on `closedBall 0 R`, and
`0 < ε`, there exists `r > R` such that `g` is analytic near `closedBall 0 r`, has no zeros on
`sphere 0 r`, `quotientMultiplier g r` is analytic near `closedBall 0 R`, and both
`Real.log ‖quotientMultiplier g r z‖` and `Real.log ‖quotientMultiplier g r z * g z‖` are at most
`ValueDistribution.proximity g ⊤ R + ε` on `closedBall 0 R`. -/
theorem exists_gt_log_norm_quotientMultiplier_le_proximity_add {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hR : 0 < R)
    (hne : ∃ z₀ ∈ closedBall (0 : ℂ) R, g z₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > R, AnalyticOnNhd ℂ g (closedBall 0 r) ∧ (∀ w ∈ sphere (0 : ℂ) r, g w ≠ 0) ∧
      AnalyticOnNhd ℂ (TauCeti.quotientMultiplier g r) (closedBall 0 R) ∧
      ∀ z ∈ closedBall (0 : ℂ) R,
        Real.log ‖TauCeti.quotientMultiplier g r z‖ ≤ ValueDistribution.proximity g ⊤ R + ε ∧
        Real.log ‖TauCeti.quotientMultiplier g r z * g z‖ ≤
          ValueDistribution.proximity g ⊤ R + ε := by
  obtain ⟨z₀, hz₀, hgz₀⟩ := hne
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (0 : ℂ) R).exists_thickening_subset_open
    (isOpen_analyticAt ℂ g) hg
  have hg_ball : AnalyticOnNhd ℂ g (ball 0 (R + δ)) := by
    rwa [thickening_closedBall hδ hR.le, add_comm] at hsub
  have hs_nhds : ball (0 : ℂ) (R + δ) ∈ 𝓝ˢ (sphere (0 : ℂ) |R|) :=
    isOpen_ball.mem_nhdsSet.mpr (by
      rw [abs_of_pos hR]
      exact sphere_subset_closedBall.trans (closedBall_subset_ball (by linarith)))
  obtain ⟨δ₁, hδ₁, hprox⟩ :=
    Metric.continuousAt_iff.mp (hg_ball.continuousOn.continuousAt_proximity_top hs_nhds) ε hε
  set r_max := R + min (δ / 2) δ₁
  have hR_lt : R < r_max := lt_add_of_pos_right R (lt_min (half_pos hδ) hδ₁)
  -- Finitely many zeros of `g` lie in `closedBall 0 (R + δ / 2)`; pick `r ∈ (R, r_max)` avoiding
  -- their moduli.
  have hZ_fin : {z ∈ closedBall (0 : ℂ) (R + δ / 2) | g z = 0}.Finite :=
    hg_ball.finite_setOf_mem_and_eq_zero_of_isCompact (convex_ball 0 (R + δ)).isPreconnected
      (closedBall_subset_ball (by linarith) hz₀) hgz₀
      (isCompact_closedBall 0 (R + δ / 2)) (closedBall_subset_ball (by linarith))
  obtain ⟨r, hr_mem, hr_not⟩ := ((Set.Ioo_infinite hR_lt).sdiff (hZ_fin.image norm)).nonempty
  have hr_pos : 0 < r := hR.trans hr_mem.1
  have hg_r : AnalyticOnNhd ℂ g (closedBall 0 r) :=
    hg_ball.mono (closedBall_subset_ball (by linarith [hr_mem.2, min_le_left (δ / 2) δ₁]))
  have hs_r : ∀ w ∈ sphere (0 : ℂ) r, g w ≠ 0 := fun w hw hgw ↦
    hr_not ⟨w, ⟨by rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm.mp hw]; linarith
      [hr_mem.2, min_le_left (δ / 2) δ₁], hgw⟩, mem_sphere_zero_iff_norm.mp hw⟩
  have hg_r_abs : AnalyticOnNhd ℂ g (closedBall 0 |r|) := by rwa [abs_of_pos hr_pos]
  have hint_r : CircleIntegrable (fun w ↦ Real.posLog ‖g w‖) 0 r :=
    (hg_r_abs.continuousOn.mono sphere_subset_closedBall).circleIntegrable_posLog_norm
  have hprox_le : ValueDistribution.proximity g ⊤ r ≤ ValueDistribution.proximity g ⊤ R + ε := by
    have hdist : dist r R < δ₁ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hr_mem.1)]
      linarith [hr_mem.2, min_le_right (δ / 2) δ₁]
    linarith [(abs_lt.mp (Real.dist_eq _ _ ▸ hprox hdist)).2]
  refine ⟨r, hr_mem.1, hg_r, hs_r, (TauCeti.analyticOnNhd_quotientMultiplier hint_r).mono ?_,
    fun z hz ↦ ?_⟩
  · intro z hz
    rw [mem_compl_iff, mem_sphere_zero_iff_norm, abs_of_pos hr_pos]
    exact ((mem_closedBall_zero_iff.mp hz).trans_lt hr_mem.1).ne
  · have hzr : z ∈ ball (0 : ℂ) r := closedBall_subset_ball hr_mem.1 hz
    exact ⟨(TauCeti.log_norm_quotientMultiplier_le_proximity hint_r hzr).trans hprox_le,
      (hg_r.log_norm_quotientMultiplier_mul_le_proximity hs_r hzr).trans hprox_le⟩

/-- **Nevanlinna's quotient representation** (Calegari–Dimitrov–Tang, Lemma 2.3.1).
If `g` is analytic on a neighbourhood of `closedBall 0 R` and `0 < ε`, there exists `h` analytic on
a neighbourhood of `closedBall 0 R` with `h 0 = 1` such that both `Real.log ‖h z‖` and
`Real.log ‖h z * g z‖` are at most `ValueDistribution.proximity g ⊤ R + ε` for every
`z ∈ closedBall 0 R` (and in particular for every `z ∈ sphere 0 R`). -/
theorem exists_log_norm_le_proximity_add {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1 ∧
      ∀ z ∈ closedBall (0 : ℂ) R,
        Real.log ‖h z‖ ≤ ValueDistribution.proximity g ⊤ R + ε ∧
        Real.log ‖h z * g z‖ ≤ ValueDistribution.proximity g ⊤ R + ε := by
  rcases lt_trichotomy R 0 with hRneg | rfl | hRpos
  · exact ⟨1, analyticOnNhd_const, rfl, fun _ hz ↦
      False.elim ((closedBall_eq_empty.mpr hRneg).subset hz)⟩
  · refine ⟨1, analyticOnNhd_const, rfl, fun z hz ↦ ?_⟩
    rw [closedBall_zero, mem_singleton_iff] at hz
    subst hz
    rw [ValueDistribution.proximity_top, circleAverage_zero]
    exact ⟨by simp; linarith [Real.posLog_nonneg (x := ‖g 0‖)],
      by simp [Real.posLog_apply]; linarith [le_max_right 0 (Real.log ‖g 0‖)]⟩
  · by_cases hall : ∀ z ∈ closedBall (0 : ℂ) R, g z = 0
    · refine ⟨1, analyticOnNhd_const, rfl, fun z hz ↦ ?_⟩
      simp [hall z hz, add_nonneg (ValueDistribution.proximity_nonneg R) hε.le]
    · push Not at hall
      obtain ⟨r, hr, -, -, hh, hbound⟩ :=
        hg.exists_gt_log_norm_quotientMultiplier_le_proximity_add hRpos hall hε
      exact ⟨TauCeti.quotientMultiplier g r, hh,
        TauCeti.quotientMultiplier_apply_zero g (hRpos.trans hr).ne', hbound⟩

/-- Supremum form of **Nevanlinna's quotient representation** on `sphere 0 R`: if `g` is analytic on
a neighbourhood of `closedBall 0 R` (`0 ≤ R`) and `0 < ε`, some normalized analytic multiplier `h`
near `closedBall 0 R` bounds both boundary logarithmic suprema by
`ValueDistribution.proximity g ⊤ R + ε`. -/
theorem exists_max_sSup_log_norm_le_proximity_add {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1 ∧
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R))
          (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R)) ≤
        ValueDistribution.proximity g ⊤ R + ε := by
  obtain ⟨h, hh, hh0, hbound⟩ := hg.exists_log_norm_le_proximity_add hε
  have hne : (sphere (0 : ℂ) R).Nonempty := ⟨R, by simp [abs_of_nonneg hR]⟩
  refine ⟨h, hh, hh0, max_le ?_ ?_⟩
  · exact csSup_le (hne.image _) fun _ ⟨z, hz, hzv⟩ ↦
      hzv ▸ (hbound z (sphere_subset_closedBall hz)).1
  · exact csSup_le (hne.image _) fun _ ⟨z, hz, hzv⟩ ↦
      hzv ▸ (hbound z (sphere_subset_closedBall hz)).2

/-! ### Optimality of the quotient bound -/

/-- **Optimality of Nevanlinna's quotient bound, bound form** (Calegari–Dimitrov–Tang,
Remark 2.3.3). For any `g : ℂ → ℂ` and any `h` analytic on a neighbourhood of `closedBall 0 R`
(`0 ≤ R`) with `1 ≤ ‖h 0‖` (in particular when `h 0 = 1`), if both `Real.log ‖h z‖ ≤ M` and
`Real.log ‖h z * g z‖ ≤ M` hold on `sphere 0 R`, then `ValueDistribution.proximity g ⊤ R ≤ M`. -/
theorem proximity_top_le_of_forall_mem_sphere_log_norm_le {g h : ℂ → ℂ} {R M : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 R)) (hR : 0 ≤ R) (hh0 : 1 ≤ ‖h 0‖)
    (hM : ∀ z ∈ sphere (0 : ℂ) R, Real.log ‖h z‖ ≤ M ∧ Real.log ‖h z * g z‖ ≤ M) :
    ValueDistribution.proximity g ⊤ R ≤ M := by
  have hh0_pos : 0 < ‖h 0‖ := zero_lt_one.trans_le hh0
  have hlog_h0 : 0 ≤ Real.log ‖h 0‖ := Real.log_nonneg hh0
  rcases hR.eq_or_lt with rfl | hRpos
  · have h0 := hM 0 (by simp)
    rw [ValueDistribution.proximity_top, circleAverage_zero, Real.posLog_apply]
    rcases eq_or_ne ‖g 0‖ 0 with hg0 | hg0
    · simp [hg0]; linarith [h0.1]
    · have hmul : Real.log ‖h 0 * g 0‖ = Real.log ‖h 0‖ + Real.log ‖g 0‖ := by
        rw [norm_mul, Real.log_mul hh0_pos.ne' hg0]
      exact max_le (by linarith [h0.1]) (by linarith [h0.2, hmul])
  · have hh_abs : AnalyticOnNhd ℂ h (closedBall 0 |R|) := by rwa [abs_of_pos hRpos]
    have hjensen : 0 ≤ circleAverage (fun z ↦ Real.log ‖h z‖) 0 R :=
      hlog_h0.trans (hh_abs.log_norm_le_circleAverage_log_norm (norm_pos_iff.mp hh0_pos))
    have hint_h : CircleIntegrable (fun z ↦ Real.log ‖h z‖) 0 R :=
      (hh_abs.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    by_cases hint_g : CircleIntegrable (fun z ↦ Real.posLog ‖g z‖) 0 R
    · have h0_mem : (0 : ℂ) ∈ closedBall 0 |R| := mem_closedBall_self (abs_nonneg R)
      have hord_0 : meromorphicOrderAt h 0 ≠ ⊤ := by
        rw [(hh_abs 0 h0_mem).meromorphicOrderAt_eq,
          (hh_abs 0 h0_mem).analyticOrderAt_eq_zero.mpr (norm_pos_iff.mp hh0_pos)]
        simp
      have hord_h : ∀ u ∈ closedBall (0 : ℂ) |R|, meromorphicOrderAt h u ≠ ⊤ := fun _ hu ↦
        hh_abs.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
          (convex_closedBall 0 |R|).isPreconnected h0_mem hu hord_0
      have hne_cod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|), h z ≠ 0 :=
        (hh_abs.meromorphicOn.codiscreteWithin_setOfPred_ne_zero hord_h).filter_mono
          (codiscreteWithin_mono sphere_subset_closedBall)
      let φ : ℂ → ℝ := fun z ↦ if h z = 0 then M else Real.log ‖h z‖ + Real.posLog ‖g z‖
      have hcod : ((fun z ↦ Real.log ‖h z‖) + fun z ↦ Real.posLog ‖g z‖) =ᶠ[
          codiscreteWithin (sphere (0 : ℂ) |R|)] φ := by
        filter_upwards [hne_cod] with z hz
        simp [φ, hz]
      have hφ_le : ∀ z ∈ sphere (0 : ℂ) |R|, φ z ≤ M := by
        intro z hz
        by_cases hzh : h z = 0
        · simp [φ, hzh]
        · have hMz := hM z (abs_of_pos hRpos ▸ hz)
          simp only [φ, hzh, ↓reduceIte, Real.posLog_apply, add_max, add_zero]
          rcases eq_or_ne (g z) 0 with hzg | hzg
          · simpa [hzg] using hMz.1
          · rw [← Real.log_mul (norm_ne_zero_iff.mpr hzh) (norm_ne_zero_iff.mpr hzg), ← norm_mul]
            exact max_le hMz.1 hMz.2
      have hsum_le :
          circleAverage (fun z ↦ Real.log ‖h z‖) 0 R + ValueDistribution.proximity g ⊤ R ≤ M := by
        rw [ValueDistribution.proximity_top, ← circleAverage_add hint_h hint_g,
          circleAverage_congr_codiscreteWithin hcod hRpos.ne']
        exact circleAverage_mono_on_of_le_circle
          (CircleIntegrable.congr_codiscreteWithin hcod (hint_h.add hint_g)) hφ_le
      linarith
    · have hM0 : 0 ≤ M :=
        hjensen.trans (circleAverage_mono_on_of_le_circle hint_h fun z hz ↦
          (hM z (abs_of_pos hRpos ▸ hz)).1)
      rw [ValueDistribution.proximity_top, circleAverage.integral_undef hint_g]
      exact hM0

/-- **Optimality of Nevanlinna's quotient bound** (Calegari–Dimitrov–Tang, Remark 2.3.3).
For `h` analytic near `closedBall 0 R` (`0 ≤ R`) with `1 ≤ ‖h 0‖` (in particular when `h 0 = 1`)
and `g` continuous on `sphere 0 R`,
`m(R, g) ≤ max (sup_{|z|=R} log ‖h z‖) (sup_{|z|=R} log ‖h z * g z‖)`.

Because `1 ≤ ‖h 0‖` forces `sup_{|z|=R} log ‖h z‖ ≥ 0` by the maximum modulus principle, Lean's
totalized value `Real.log 0 = 0` at any boundary zero of `h` or `h * g` never alters the maximum
of the two suprema. -/
theorem proximity_top_le_max_sSup_log_norm {g h : ℂ → ℂ} {R : ℝ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 R)) (hg : ContinuousOn g (sphere 0 R))
    (hR : 0 ≤ R) (hh0 : 1 ≤ ‖h 0‖) :
    ValueDistribution.proximity g ⊤ R ≤
      max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R)) := by
  have hh_cont : ContinuousOn h (sphere 0 R) := hh.continuousOn.mono sphere_subset_closedBall
  have hbdd_h : BddAbove ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R) :=
    (isCompact_sphere 0 R).bddAbove_image_log_norm hh_cont
  have hbdd_hg : BddAbove ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R) :=
    (isCompact_sphere 0 R).bddAbove_image_log_norm (hh_cont.mul hg)
  refine hh.proximity_top_le_of_forall_mem_sphere_log_norm_le hR hh0 fun z hz ↦ ⟨?_, ?_⟩
  · exact (le_csSup hbdd_h ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  · exact (le_csSup hbdd_hg ⟨z, hz, rfl⟩).trans (le_max_right _ _)

/-- **Variational characterization of the Nevanlinna proximity function.** For `g` analytic near
`closedBall 0 R` (`0 ≤ R`), `ValueDistribution.proximity g ⊤ R` is the infimum of
`max (sup_{|z|=R} log ‖h z‖) (sup_{|z|=R} log ‖h z * g z‖)` over all `h` analytic near
`closedBall 0 R` with `h 0 = 1`. -/
theorem sInf_max_sSup_log_norm_eq_proximity_top {g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hR : 0 ≤ R) :
    sInf ((fun h : ℂ → ℂ ↦ max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R))
        (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R))) ''
      {h : ℂ → ℂ | AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1}) =
      ValueDistribution.proximity g ⊤ R := by
  set F : (ℂ → ℂ) → ℝ := fun h ↦
    max (sSup ((fun z ↦ Real.log ‖h z‖) '' sphere (0 : ℂ) R))
      (sSup ((fun z ↦ Real.log ‖h z * g z‖) '' sphere (0 : ℂ) R))
  set S : Set (ℂ → ℂ) := {h : ℂ → ℂ | AnalyticOnNhd ℂ h (closedBall 0 R) ∧ h 0 = 1}
  have hg_cont : ContinuousOn g (sphere 0 R) := hg.continuousOn.mono sphere_subset_closedBall
  have hne : (F '' S).Nonempty := ⟨F 1, ⟨1, ⟨analyticOnNhd_const, rfl⟩, rfl⟩⟩
  have hbdd : BddBelow (F '' S) := by
    refine ⟨ValueDistribution.proximity g ⊤ R, ?_⟩
    rintro _ ⟨h, ⟨hh, hh0⟩, rfl⟩
    exact hh.proximity_top_le_max_sSup_log_norm hg_cont hR (by simp [hh0])
  refine le_antisymm ?_ (le_csInf hne fun _ ⟨h, ⟨hh, hh0⟩, hv⟩ ↦
    hv ▸ hh.proximity_top_le_max_sSup_log_norm hg_cont hR (by simp [hh0]))
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨h, hh, hh0, hle⟩ := hg.exists_max_sSup_log_norm_le_proximity_add hR hε
  exact (csInf_le hbdd ⟨h, ⟨hh, hh0⟩, rfl⟩).trans hle

end AnalyticOnNhd

/-! ### Non-vacuity checks

1. Specialization of `AnalyticOnNhd.exists_log_norm_le_proximity_add` to the closed unit disc and
   unit circle.
2. For `g = 1` and `h = 1` on the unit circle, both logarithmic suprema and `m(1, 1)` equal `0`.
3. For `g z = z - 1` (which vanishes on the boundary at `z = 1`), radial smoothing still produces a
   normalized analytic multiplier near `closedBall 0 1` for every `ε > 0`. -/

example {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 1) ∧ h 0 = 1 ∧
      ∀ z ∈ sphere (0 : ℂ) 1,
        Real.log ‖h z‖ ≤ ValueDistribution.proximity g ⊤ 1 + ε ∧
        Real.log ‖h z * g z‖ ≤ ValueDistribution.proximity g ⊤ 1 + ε := by
  obtain ⟨h, hh, hh0, hbound⟩ := hg.exists_log_norm_le_proximity_add hε
  exact ⟨h, hh, hh0, fun z hz ↦ hbound z (sphere_subset_closedBall hz)⟩

example :
    sSup ((fun z : ℂ ↦ Real.log ‖(1 : ℂ → ℂ) z‖) '' sphere (0 : ℂ) 1) = 0 ∧
      ValueDistribution.proximity (1 : ℂ → ℂ) ⊤ 1 = 0 := by
  have hne : (sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  have himg : (fun z : ℂ ↦ Real.log ‖(1 : ℂ → ℂ) z‖) '' sphere (0 : ℂ) 1 = {0} := by
    simp [hne.image_const]
  refine ⟨by rw [himg, csSup_singleton], ?_⟩
  rw [Pi.one_def]
  simp

example {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 1) ∧ h 0 = 1 ∧
      ∀ z ∈ sphere (0 : ℂ) 1,
        Real.log ‖h z‖ ≤ ValueDistribution.proximity (fun w ↦ w - 1) ⊤ 1 + ε ∧
        Real.log ‖h z * (z - 1)‖ ≤ ValueDistribution.proximity (fun w ↦ w - 1) ⊤ 1 + ε := by
  have hg : AnalyticOnNhd ℂ (fun w : ℂ ↦ w - 1) (closedBall 0 1) :=
    analyticOnNhd_id.sub analyticOnNhd_const
  obtain ⟨h, hh, hh0, hbound⟩ := hg.exists_log_norm_le_proximity_add hε
  exact ⟨h, hh, hh0, fun z hz ↦ hbound z (sphere_subset_closedBall hz)⟩
