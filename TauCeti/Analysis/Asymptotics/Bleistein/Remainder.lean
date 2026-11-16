/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Bleistein.ChangeOfVariables
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Bleistein's canonical functions and uniform remainder expansion

After Bleistein's change of variables (`TauCeti.Analysis.Asymptotics.Bleistein.ChangeOfVariables`),
an integral with a critical point coalescing with an algebraic endpoint `t = 0` and infinite
transformed upper limit (`κ = +∞`) takes the canonical form
`∫ w in (0, ∞), (exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w`.
Expanding `f` around `w = a` expresses the asymptotic series and explicit remainder bound in terms
of the parabolic-cylinder-type integrals (DLMF §2.3(v), 2.3.31–2.3.33):

* `TauCeti.bleisteinF lam s y`, defined by
  `∫ τ in (0, ∞), exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)` (DLMF 2.3.33);
* `TauCeti.bleisteinG lam N y`, defined by
  `∫ τ in (0, ∞), exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)`.

For `lam > 0`, both `bleisteinF lam s` and `bleisteinG lam N` are integrable for every `y : ℝ`,
continuous on `ℝ`, satisfy `0 < bleisteinG lam N y` and `|bleisteinF lam s y| ≤ bleisteinG lam s y`,
and pass the special-value identities (`N = 0`, even `N`, `y = 0`, and `lam = 1, s = 1`). Rescaling
`τ = √x * w` yields the general remainder bound `TauCeti.norm_bleistein_remainder_le` and, combined
with `TauCeti.integral_bleisteinCoord_Ioo_eq_Ioi` and `TauCeti.integral_bleisteinCoord_Ioi_eq_Ioi`,
the uniform asymptotic expansion DLMF 2.3.32 with absolute convergence of the original integral.

## Main definitions

* `TauCeti.bleisteinF`: the coefficient functions `F_s(y)` of DLMF 2.3.33.
* `TauCeti.bleisteinG`: the comparison functions `G_N(y)` for the Bleistein remainder bound.

## Main results

* `TauCeti.integrableOn_bleisteinF`, `TauCeti.integrableOn_bleisteinG`,
  `TauCeti.continuous_bleisteinF`, `TauCeti.continuous_bleisteinG`: integrability and continuity.
* `TauCeti.bleisteinG_pos`, `TauCeti.abs_bleisteinF_le_bleisteinG`,
  `TauCeti.bleisteinG_zero_eq_bleisteinF`, `TauCeti.bleisteinG_two_mul_eq_bleisteinF`,
  `TauCeti.bleisteinF_zero_zero`, `TauCeti.bleisteinG_zero_zero`, `TauCeti.bleisteinF_one_one`:
  positivity, comparison, and closed-form evaluations.
* `TauCeti.norm_bleistein_remainder_le`: the uniform remainder bound on `(0, ∞)`.
* `TauCeti.integrableOn_bleistein_Ioo`, `TauCeti.norm_exp_smul_integral_bleistein_Ioo_sub_le`,
  `TauCeti.integrableOn_bleistein_Ioi`, `TauCeti.norm_exp_smul_integral_bleistein_Ioi_sub_le`:
  absolute convergence and uniform asymptotic remainder bound (DLMF 2.3.32) for finite and
  infinite `k`.

## References

* N. Bleistein, *Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity*, Comm. Pure Appl. Math. **19** (1966), 353–370.
* NIST Digital Library of Mathematical Functions, §2.3(v), <https://dlmf.nist.gov/2.3.v>.
-/

public section

open Filter Set MeasureTheory Function
open scoped ContDiff Topology

namespace TauCeti

/-! ### Canonical functions `bleisteinF` and `bleisteinG` (DLMF 2.3.33) -/

/-- The canonical coefficient function
`F_s(y) = ∫ τ in (0, ∞), exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)`
of Bleistein's uniform expansion (DLMF 2.3.33). -/
noncomputable def bleisteinF (lam : ℝ) (s : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)

/-- Unfolding identity for `bleisteinF`. -/
theorem bleisteinF_def (lam : ℝ) (s : ℕ) (y : ℝ) :
    bleisteinF lam s y =
      ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1) :=
  (rfl)

/-- The majorant function
`G_N(y) = ∫ τ in (0, ∞), exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)`
controlling the remainder in Bleistein's uniform expansion. -/
noncomputable def bleisteinG (lam : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)

/-- Unfolding identity for `bleisteinG`. -/
theorem bleisteinG_def (lam : ℝ) (N : ℕ) (y : ℝ) :
    bleisteinG lam N y =
      ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) :=
  (rfl)

/-! ### Integrability, positivity, and continuity -/

/-- Locally uniform Gaussian dominating bound for `bleisteinF` and `bleisteinG` when `|y| ≤ R`. -/
private lemma bleistein_integrand_bound {lam y R τ : ℝ} (n : ℕ) (hR : |y| ≤ R) (hτ : 0 < τ) :
    Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ n * τ ^ (lam - 1) ≤
      Real.exp (R ^ 2) * ((τ + R) ^ n * (τ ^ (lam - 1) * Real.exp (-(1 / 4) * τ ^ 2))) := by
  have hy2 : y ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg y) hR 2
  have hexp_arg : -τ ^ 2 / 2 + y * τ ≤ R ^ 2 + -(1 / 4) * τ ^ 2 := by
    nlinarith [sq_nonneg (τ / 2 - y)]
  have hexp : Real.exp (-τ ^ 2 / 2 + y * τ) ≤ Real.exp (R ^ 2) * Real.exp (-(1 / 4) * τ ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp_arg
  have habs : |τ - y| ≤ τ + R := by
    calc
      |τ - y| ≤ |τ| + |y| := abs_sub τ y
      _ = τ + |y| := by rw [abs_of_pos hτ]
      _ ≤ τ + R := add_le_add_right hR τ
  have hpow : |τ - y| ^ n ≤ (τ + R) ^ n := pow_le_pow_left₀ (abs_nonneg _) habs n
  calc
    Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ n * τ ^ (lam - 1)
      ≤ (Real.exp (R ^ 2) * Real.exp (-(1 / 4) * τ ^ 2)) * (τ + R) ^ n * τ ^ (lam - 1) := by
        gcongr
    _ = Real.exp (R ^ 2) * ((τ + R) ^ n * (τ ^ (lam - 1) * Real.exp (-(1 / 4) * τ ^ 2))) := by
        ring

/-- Integrability on `(0, ∞)` of the locally uniform Gaussian dominating bound for `lam > 0`. -/
private lemma integrableOn_bleistein_domBound {lam R : ℝ} (hlam : 0 < lam) (n : ℕ) :
    IntegrableOn
      (fun τ : ℝ ↦
        Real.exp (R ^ 2) * ((τ + R) ^ n * (τ ^ (lam - 1) * Real.exp (-(1 / 4) * τ ^ 2))))
      (Ioi 0) := by
  have hsum : IntegrableOn
      (fun τ : ℝ ↦ ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) * R ^ (n - k)) *
          (τ ^ ((k : ℝ) + lam - 1) * Real.exp (-(1 / 4) * τ ^ 2)))
      (Ioi 0) := by
    refine integrable_finsetSum _ fun k _ ↦ ?_
    have hk : -1 < (k : ℝ) + lam - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4) hk).const_mul _
  refine IntegrableOn.congr_fun (hsum.const_mul (Real.exp (R ^ 2))) (fun τ hτ ↦ ?_)
    measurableSet_Ioi
  have hτ0 : 0 < τ := hτ
  congr 1
  rw [add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hrpow : τ ^ k * τ ^ (lam - 1) = τ ^ ((k : ℝ) + lam - 1) := by
    rw [← Real.rpow_natCast τ k, ← Real.rpow_add hτ0, add_sub_assoc]
  calc
    (n.choose k : ℝ) * R ^ (n - k) * (τ ^ ((k : ℝ) + lam - 1) * Real.exp (-(1 / 4) * τ ^ 2))
      = (n.choose k : ℝ) * R ^ (n - k) * ((τ ^ k * τ ^ (lam - 1)) *
          Real.exp (-(1 / 4) * τ ^ 2)) := by rw [hrpow]
    _ = τ ^ k * R ^ (n - k) * (n.choose k : ℝ) *
          (τ ^ (lam - 1) * Real.exp (-(1 / 4) * τ ^ 2)) := by ring

/-- For `lam > 0`, the integrand of `bleisteinG lam N y` is integrable on `(0, ∞)`. -/
theorem integrableOn_bleisteinG {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (y : ℝ) :
    IntegrableOn
      (fun τ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)) (Ioi 0) := by
  have hcont : ContinuousOn
      (fun τ : ℝ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)) (Ioi 0) := by
    refine (((Real.continuous_exp.comp ?_).mul ?_).continuousOn).mul
      (continuousOn_id.rpow_const fun τ hτ ↦ Or.inl (ne_of_gt hτ))
    · fun_prop
    · exact (continuous_id.sub continuous_const).abs.pow N
  refine (integrableOn_bleistein_domBound hlam N (R := |y|)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
  have hnn : 0 ≤ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) :=
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (abs_nonneg _) _))
      (Real.rpow_nonneg hτ.le _)
  rw [Real.norm_of_nonneg hnn]
  exact bleistein_integrand_bound N le_rfl hτ

/-- For `lam > 0`, the integrand of `bleisteinF lam s y` is integrable on `(0, ∞)`. -/
theorem integrableOn_bleisteinF {lam : ℝ} (hlam : 0 < lam) (s : ℕ) (y : ℝ) :
    IntegrableOn
      (fun τ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)) (Ioi 0) := by
  have hcont : ContinuousOn
      (fun τ : ℝ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)) (Ioi 0) := by
    refine (((Real.continuous_exp.comp ?_).mul ?_).continuousOn).mul
      (continuousOn_id.rpow_const fun τ hτ ↦ Or.inl (ne_of_gt hτ))
    · fun_prop
    · exact (continuous_id.sub continuous_const).pow s
  refine (integrableOn_bleisteinG hlam s y).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
    abs_of_nonneg (Real.rpow_nonneg hτ.le _)]

/-- `bleisteinG lam N y` is nonnegative for all `lam`, `N`, and `y`. -/
theorem bleisteinG_nonneg (lam : ℝ) (N : ℕ) (y : ℝ) : 0 ≤ bleisteinG lam N y := by
  refine setIntegral_nonneg measurableSet_Ioi fun τ (hτ : 0 < τ) ↦ ?_
  exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (abs_nonneg _) _))
    (Real.rpow_nonneg hτ.le _)

/-- For `lam > 0`, `bleisteinG lam N y` is strictly positive for every `N` and `y`. -/
theorem bleisteinG_pos {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (y : ℝ) : 0 < bleisteinG lam N y := by
  rw [bleisteinG_def, setIntegral_pos_iff_support_of_nonneg_ae]
  · let c : ℝ := max y 0 + 1
    have hsub : Ioo c (c + 1) ⊆
        support (fun τ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)) ∩ Ioi 0 := by
      intro τ hτ
      have hc0 : 0 < c := by positivity
      have hτ0 : 0 < τ := hc0.trans hτ.1
      have hτy : y < τ := (le_max_left y 0).trans_lt ((lt_add_one _).trans hτ.1)
      have hpow_ne : |τ - y| ^ N ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr (sub_ne_zero.mpr hτy.ne'))
      refine ⟨mem_support.mpr ?_, hτ0⟩
      exact mul_ne_zero (mul_ne_zero (Real.exp_ne_zero _) hpow_ne)
        (Real.rpow_pos_of_pos hτ0 _).ne'
    have hvol : 0 < volume (Ioo c (c + 1)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    exact hvol.trans_le (measure_mono hsub)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (abs_nonneg _) _))
      (Real.rpow_nonneg hτ.le _)
  · exact integrableOn_bleisteinG hlam N y

/-- Comparison inequality `|bleisteinF lam s y| ≤ bleisteinG lam s y`. -/
theorem abs_bleisteinF_le_bleisteinG (lam : ℝ) (s : ℕ) (y : ℝ) :
    |bleisteinF lam s y| ≤ bleisteinG lam s y := by
  rw [bleisteinF_def, bleisteinG_def, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : 0 < τ) ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
    abs_of_nonneg (Real.rpow_nonneg hτ.le _)]

/-- Continuity of `y ↦ bleisteinF lam s y` on `ℝ` when `lam > 0`. -/
theorem continuous_bleisteinF {lam : ℝ} (hlam : 0 < lam) (s : ℕ) :
    Continuous (bleisteinF lam s) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  refine continuousAt_of_dominated
    (bound := fun τ ↦ Real.exp ((|y₀| + 1) ^ 2) *
      ((τ + (|y₀| + 1)) ^ s * (τ ^ (lam - 1) * Real.exp (-(1 / 4) * τ ^ 2))))
    (Eventually.of_forall fun y ↦ (integrableOn_bleisteinF hlam s y).aestronglyMeasurable)
    ?_ (integrableOn_bleistein_domBound hlam s) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    have hyR : |y| ≤ |y₀| + 1 := by
      have hdist : |y - y₀| < 1 := by simpa [Real.dist_eq] using hy
      linarith [abs_sub_abs_le_abs_sub y y₀]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
      abs_of_nonneg (Real.rpow_nonneg hτ.le _)]
    exact bleistein_integrand_bound s hyR hτ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
    exact (by fun_prop : Continuous fun y : ℝ ↦
      Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)).continuousAt

/-- Continuity of `y ↦ bleisteinG lam N y` on `ℝ` when `lam > 0`. -/
theorem continuous_bleisteinG {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    Continuous (bleisteinG lam N) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  refine continuousAt_of_dominated
    (bound := fun τ ↦ Real.exp ((|y₀| + 1) ^ 2) *
      ((τ + (|y₀| + 1)) ^ N * (τ ^ (lam - 1) * Real.exp (-(1 / 4) * τ ^ 2))))
    (Eventually.of_forall fun y ↦ (integrableOn_bleisteinG hlam N y).aestronglyMeasurable)
    ?_ (integrableOn_bleistein_domBound hlam N) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    have hyR : |y| ≤ |y₀| + 1 := by
      have hdist : |y - y₀| < 1 := by simpa [Real.dist_eq] using hy
      linarith [abs_sub_abs_le_abs_sub y y₀]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
    have hnn : 0 ≤ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) :=
      mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (abs_nonneg _) _))
        (Real.rpow_nonneg hτ.le _)
    rw [Real.norm_of_nonneg hnn]
    exact bleistein_integrand_bound N hyR hτ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
    have hc : Continuous fun y : ℝ ↦
        Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) :=
      ((Real.continuous_exp.comp (by fun_prop)).mul
        ((continuous_const.sub continuous_id).abs.pow N)).mul continuous_const
    exact hc.continuousAt

/-! ### Special values and parity identities -/

/-- At order `N = 0`, `bleisteinG lam 0` coincides with `bleisteinF lam 0`. -/
@[simp]
theorem bleisteinG_zero_eq_bleisteinF (lam y : ℝ) : bleisteinG lam 0 y = bleisteinF lam 0 y := by
  simp [bleisteinG, bleisteinF]

/-- For every even order `2 * m`, `bleisteinG lam (2 * m)` coincides with
`bleisteinF lam (2 * m)`. -/
theorem bleisteinG_two_mul_eq_bleisteinF (lam : ℝ) (m : ℕ) (y : ℝ) :
    bleisteinG lam (2 * m) y = bleisteinF lam (2 * m) y := by
  simp only [bleisteinG_def, bleisteinF_def, pow_mul, sq_abs]

/-- For even `N`, `bleisteinG lam N` coincides with `bleisteinF lam N`. -/
theorem bleisteinG_eq_bleisteinF_of_even {N : ℕ} (hN : Even N) (lam y : ℝ) :
    bleisteinG lam N y = bleisteinF lam N y := by
  rcases hN.exists_two_nsmul with ⟨m, rfl⟩
  simpa [two_nsmul, two_mul] using bleisteinG_two_mul_eq_bleisteinF lam m y

/-- Closed-form evaluation `F₀(0) = 2 ^ (lam / 2 - 1) * Γ(lam / 2)` for `lam > 0`. -/
theorem bleisteinF_zero_zero {lam : ℝ} (hlam : 0 < lam) :
    bleisteinF lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2) := by
  have hcongr : bleisteinF lam 0 0 =
      ∫ τ in Ioi (0 : ℝ), τ ^ (lam - 1) * Real.exp (-(1 / 2) * τ ^ (2 : ℝ)) := by
    rw [bleisteinF_def]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ ↦ ?_
    simp only [zero_mul, add_zero, sub_zero, pow_zero, mul_one, Real.rpow_two]
    rw [mul_comm]
    congr 2
    ring
  rw [hcongr, integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith)
    (by norm_num : (0 : ℝ) < 1 / 2)]
  have hpow : (1 / 2 : ℝ) ^ (-((lam - 1) + 1) / 2) * (1 / 2) = 2 ^ (lam / 2 - 1) := by
    have hexp : -((lam - 1) + 1) / 2 = -(lam / 2) := by ring
    rw [hexp, one_div, Real.inv_rpow zero_le_two, Real.rpow_neg zero_le_two, inv_inv,
      Real.rpow_sub zero_lt_two, Real.rpow_one]
    ring
  rw [hpow]
  congr 2
  ring

/-- Closed-form evaluation `G₀(0) = 2 ^ (lam / 2 - 1) * Γ(lam / 2)` for `lam > 0`. -/
theorem bleisteinG_zero_zero {lam : ℝ} (hlam : 0 < lam) :
    bleisteinG lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2) := by
  rw [bleisteinG_zero_eq_bleisteinF, bleisteinF_zero_zero hlam]

/-- Closed-form evaluation `F₁(y) = 1` when `lam = 1`, for every `y : ℝ`. -/
@[simp]
theorem bleisteinF_one_one (y : ℝ) : bleisteinF 1 1 y = 1 := by
  have hderiv : ∀ τ ∈ Ici (0 : ℝ),
      HasDerivAt (fun u ↦ -Real.exp (-u ^ 2 / 2 + y * u))
        (Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ 1 * τ ^ ((1 : ℝ) - 1)) τ := by
    intro τ _
    have h1 : HasDerivAt (fun u : ℝ ↦ -u ^ 2 / 2) (-τ) τ :=
      (((hasDerivAt_pow 2 τ).neg).div_const 2).congr_deriv (by simp; ring)
    have h2 : HasDerivAt (fun u : ℝ ↦ y * u) y τ := by
      simpa using (hasDerivAt_id τ).const_mul y
    refine (h1.add h2).exp.neg.congr_deriv ?_
    simp only [Pi.add_apply, pow_one, sub_self, Real.rpow_zero, mul_one]
    ring
  have htend_arg : Tendsto (fun τ : ℝ ↦ -τ ^ 2 / 2 + y * τ) atTop atBot := by
    have hlin : Tendsto (fun τ : ℝ ↦ -τ / 2 + y) atTop atBot := by
      have hhalf : Tendsto (fun τ : ℝ ↦ (-1 / 2 : ℝ) * τ) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by norm_num)
      refine (tendsto_atBot_add_const_right _ y hhalf).congr fun τ ↦ by ring
    exact (tendsto_id.atTop_mul_atBot₀ hlin).congr fun τ ↦ by dsimp; ring
  have htend : Tendsto (fun τ : ℝ ↦ -Real.exp (-τ ^ 2 / 2 + y * τ)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp htend_arg).neg
  rw [bleisteinF_def,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_bleisteinF zero_lt_one 1 y) htend]
  simp

/-! ### Rescaling identities and `norm_bleistein_remainder_le` -/

/-- Pointwise rescaling `τ = √x * w` for homogeneous factors `ψ (√x * u) = (√x) ^ n * ψ u`. -/
private lemma exp_bleistein_rescale_eq {lam x a w : ℝ} {ψ : ℝ → ℝ} {n : ℕ}
    (hx : 0 < x) (hw : 0 < w)
    (hψ : ψ (Real.sqrt x * (w - a)) = Real.sqrt x ^ n * ψ (w - a)) :
    Real.exp (-(Real.sqrt x * w) ^ 2 / 2 + (a * Real.sqrt x) * (Real.sqrt x * w)) *
        ψ (Real.sqrt x * w - a * Real.sqrt x) * (Real.sqrt x * w) ^ (lam - 1) =
      (Real.sqrt x ^ n * Real.sqrt x ^ (lam - 1)) *
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * ψ (w - a) * w ^ (lam - 1)) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx
  have hexp : -(Real.sqrt x * w) ^ 2 / 2 + (a * Real.sqrt x) * (Real.sqrt x * w) =
      -x * (w ^ 2 / 2 - a * w) := by
    calc
      -(Real.sqrt x * w) ^ 2 / 2 + (a * Real.sqrt x) * (Real.sqrt x * w)
        = -(Real.sqrt x ^ 2) * w ^ 2 / 2 + a * (Real.sqrt x ^ 2) * w := by ring
      _ = -x * (w ^ 2 / 2 - a * w) := by rw [Real.sq_sqrt hx.le]; ring
  rw [hexp, mul_comm a (Real.sqrt x), ← mul_sub, hψ, Real.mul_rpow hsx.le hw.le]
  ring

/-- Integrability on `(0, ∞)` of a rescaled Bleistein kernel with homogeneous factor `ψ`. -/
private lemma integrableOn_exp_bleistein_of_homog {lam x a : ℝ} {ψ : ℝ → ℝ} {n : ℕ}
    (hx : 0 < x) (hψ : ∀ u, ψ (Real.sqrt x * u) = Real.sqrt x ^ n * ψ u)
    (hint : IntegrableOn
      (fun τ ↦ Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
        ψ (τ - a * Real.sqrt x) * τ ^ (lam - 1)) (Ioi 0)) :
    IntegrableOn
      (fun w ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * ψ (w - a) * w ^ (lam - 1)) (Ioi 0) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx
  let c : ℝ := Real.sqrt x ^ n * Real.sqrt x ^ (lam - 1)
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hsx.ne') (Real.rpow_pos_of_pos hsx _).ne'
  have hcomp := (integrableOn_Ioi_comp_mul_left_iff _ 0 hsx).mpr (by simpa using hint)
  refine IntegrableOn.congr_fun (hcomp.const_mul c⁻¹) (fun w (hw : 0 < w) ↦ ?_) measurableSet_Ioi
  exact (congr_arg (c⁻¹ * ·) (exp_bleistein_rescale_eq hx hw (hψ (w - a)))).trans
    (inv_mul_cancel_left₀ hc _)

/-- Integral on `(0, ∞)` of a rescaled Bleistein kernel with homogeneous factor `ψ`. -/
private lemma integral_exp_bleistein_of_homog {lam x a : ℝ} {ψ : ℝ → ℝ} {n : ℕ}
    (hx : 0 < x) (hψ : ∀ u, ψ (Real.sqrt x * u) = Real.sqrt x ^ n * ψ u) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * ψ (w - a) * w ^ (lam - 1)) =
      x ^ (-((n : ℝ) + lam) / 2) *
        ∫ τ in Ioi (0 : ℝ),
          Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
            ψ (τ - a * Real.sqrt x) * τ ^ (lam - 1) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx
  let c : ℝ := Real.sqrt x ^ n * Real.sqrt x ^ (lam - 1)
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hsx.ne') (Real.rpow_pos_of_pos hsx _).ne'
  have hcomp := integral_comp_mul_left_Ioi
    (fun τ ↦ Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
      ψ (τ - a * Real.sqrt x) * τ ^ (lam - 1)) 0 hsx
  rw [mul_zero, smul_eq_mul] at hcomp
  have hcongr :
      (∫ w in Ioi (0 : ℝ),
        Real.exp (-(Real.sqrt x * w) ^ 2 / 2 + (a * Real.sqrt x) * (Real.sqrt x * w)) *
          ψ (Real.sqrt x * w - a * Real.sqrt x) * (Real.sqrt x * w) ^ (lam - 1)) =
      c * ∫ w in Ioi (0 : ℝ),
        Real.exp (-x * (w ^ 2 / 2 - a * w)) * ψ (w - a) * w ^ (lam - 1) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun w hw ↦
      exp_bleistein_rescale_eq hx hw (hψ (w - a))
  rw [hcongr] at hcomp
  have hrpow : c⁻¹ * (Real.sqrt x)⁻¹ = x ^ (-((n : ℝ) + lam) / 2) := by
    dsimp only [c]
    rw [← mul_inv_rev, mul_comm (Real.sqrt x), Real.sqrt_eq_rpow, ← Real.rpow_natCast _ n,
      ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx,
      ← Real.rpow_neg hx.le]
    congr 1
    ring
  calc
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * ψ (w - a) * w ^ (lam - 1))
      = c⁻¹ * (c * ∫ w in Ioi (0 : ℝ),
          Real.exp (-x * (w ^ 2 / 2 - a * w)) * ψ (w - a) * w ^ (lam - 1)) := by
          rw [inv_mul_cancel_left₀ hc]
    _ = (c⁻¹ * (Real.sqrt x)⁻¹) * ∫ τ in Ioi (0 : ℝ),
          Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
            ψ (τ - a * Real.sqrt x) * τ ^ (lam - 1) := by
          rw [hcomp, mul_assoc]
    _ = x ^ (-((n : ℝ) + lam) / 2) * ∫ τ in Ioi (0 : ℝ),
          Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
            ψ (τ - a * Real.sqrt x) * τ ^ (lam - 1) := by
          rw [hrpow]

/-- Integrability of `w ↦ exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)` on
`(0, ∞)` for `lam > 0` and `x > 0`. -/
theorem integrableOn_exp_bleistein_pow {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (s : ℕ) :
    IntegrableOn
      (fun w ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) (Ioi 0) :=
  integrableOn_exp_bleistein_of_homog (ψ := fun u ↦ u ^ s) hx (fun u ↦ mul_pow _ u s)
    (integrableOn_bleisteinF hlam s (a * Real.sqrt x))

/-- Integrability of `w ↦ exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)` on
`(0, ∞)` for `lam > 0` and `x > 0`. -/
theorem integrableOn_exp_bleistein_abs_pow {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (a : ℝ) (N : ℕ) :
    IntegrableOn
      (fun w ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) (Ioi 0) :=
  integrableOn_exp_bleistein_of_homog (ψ := fun u ↦ |u| ^ N) hx
    (fun u ↦ by rw [abs_mul, abs_of_pos (Real.sqrt_pos_of_pos hx), mul_pow])
    (integrableOn_bleisteinG hlam N (a * Real.sqrt x))

/-- Rescaled integral evaluation on `(0, ∞)` in terms of `bleisteinF`. -/
theorem integral_exp_bleistein_pow {lam x : ℝ} (hx : 0 < x) (a : ℝ) (s : ℕ) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) =
      x ^ (-lam / 2) * (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) := by
  rw [integral_exp_bleistein_of_homog (ψ := fun u ↦ u ^ s) hx (fun u ↦ mul_pow _ u s),
    ← bleisteinF_def]
  have hrpow : x ^ (-((s : ℝ) + lam) / 2) = x ^ (-lam / 2) * x ^ (-(s : ℝ) / 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [hrpow]
  ring

/-- Rescaled integral evaluation on `(0, ∞)` in terms of `bleisteinG`. -/
theorem integral_exp_bleistein_abs_pow {lam x : ℝ} (hx : 0 < x) (a : ℝ) (N : ℕ) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) =
      x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (a * Real.sqrt x) := by
  rw [integral_exp_bleistein_of_homog (ψ := fun u ↦ |u| ^ N) hx
    (fun u ↦ by rw [abs_mul, abs_of_pos (Real.sqrt_pos_of_pos hx), mul_pow]), ← bleisteinG_def]

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrability on `(0, ∞)` of the Bleistein kernel multiplied by a finite Taylor polynomial
around `a`. -/
private lemma integrableOn_exp_bleistein_finsetSum {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (a : ℝ) (N : ℕ) (phi : ℕ → E) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) (Ioi 0) := by
  have hsum : IntegrableOn
      (fun w ↦ ∑ s ∈ Finset.range N,
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) • phi s) (Ioi 0) :=
    integrable_finsetSum (Finset.range N) fun s _ ↦
      (integrableOn_exp_bleistein_pow hlam hx a s).smul_const (phi s)
  refine IntegrableOn.congr_fun hsum (fun w _ ↦ ?_) measurableSet_Ioi
  simp only [Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun s _ ↦ congrArg (· • phi s) (by ring)

/-- If `f` is a.e. strongly measurable on `(0, ∞)` and admits a Taylor-like approximation around
`a` with polynomial remainder `C * |w - a| ^ N` on `(0, ∞)`, then the canonical Bleistein integrand
`(exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w` is integrable on `(0, ∞)` for all
`lam > 0` and `x > 0`. -/
theorem integrableOn_exp_bleistein_smul_of_bound {lam a C x : ℝ} {N : ℕ} {f : ℝ → E}
    {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖ ≤ C * |w - a| ^ N) :
    IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w) (Ioi 0) := by
  let P : ℝ → E := fun w ↦ ∑ s ∈ Finset.range N, (w - a) ^ s • phi s
  have hP_int := integrableOn_exp_bleistein_finsetSum hlam hx a N phi
  have hP_cont : Continuous P := by dsimp [P]; fun_prop
  have hP_meas : AEStronglyMeasurable P (volume.restrict (Ioi 0)) :=
    hP_cont.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hK_meas : AEStronglyMeasurable
      (fun w : ℝ ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1))
      (volume.restrict (Ioi 0)) :=
    (((Real.continuous_exp.comp (by fun_prop)).continuousOn).mul
      (continuousOn_id.rpow_const fun w hw ↦ Or.inl (ne_of_gt hw))).aestronglyMeasurable
      measurableSet_Ioi
  have hR_int : IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • (f w - P w)) (Ioi 0) := by
    refine ((integrableOn_exp_bleistein_abs_pow hlam hx a N).const_mul C).mono'
      (hK_meas.smul (hfm.sub hP_meas)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
    have hK_nn : 0 ≤ Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) :=
      mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hw.le _)
    rw [norm_smul, Real.norm_of_nonneg hK_nn]
    calc
      (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * ‖f w - P w‖
        ≤ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * (C * |w - a| ^ N) :=
          mul_le_mul_of_nonneg_left (hf w hw) hK_nn
      _ = C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by ring
  refine IntegrableOn.congr_fun (hP_int.add hR_int) (fun w _ ↦ ?_) measurableSet_Ioi
  simp [P, ← smul_add]

/-- The uniform Bleistein remainder bound behind DLMF 2.3.32 (`κ = +∞`): if `f` is a.e. strongly
measurable on `(0, ∞)` and `‖f w - ∑_{s < N} (w - a) ^ s • phi s‖ ≤ C * |w - a| ^ N` for all
`w > 0`, then for every `x > 0` the error of the `N`-term Bleistein approximation is bounded by
`C * x ^ (-((N + lam) / 2)) * bleisteinG lam N (a * √x)`. -/
theorem norm_bleistein_remainder_le [CompleteSpace E] {lam a C x : ℝ} {N : ℕ}
    {f : ℝ → E} {phi : ℕ → E} (hlam : 0 < lam) (hx : 0 < x)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖ ≤ C * |w - a| ^ N) :
    ‖(∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w) -
        x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
          (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (a * Real.sqrt x) := by
  let P : ℝ → E := fun w ↦ ∑ s ∈ Finset.range N, (w - a) ^ s • phi s
  have hf_int := integrableOn_exp_bleistein_smul_of_bound hlam hx hfm hf
  have hP_int := integrableOn_exp_bleistein_finsetSum hlam hx a N phi
  have hP_eval :
      (∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • P w) =
        x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
          (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s := by
    have hcongr :
        (∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • P w) =
        ∫ w in Ioi (0 : ℝ), ∑ s ∈ Finset.range N,
          (Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) • phi s := by
      refine setIntegral_congr_fun measurableSet_Ioi fun w _ ↦ ?_
      simp only [P, Finset.smul_sum, smul_smul]
      exact Finset.sum_congr rfl fun s _ ↦ congrArg (· • phi s) (by ring)
    rw [hcongr, integral_finsetSum (Finset.range N) fun s _ ↦
      (integrableOn_exp_bleistein_pow hlam hx a s).smul_const (phi s), Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [integral_smul_const, integral_exp_bleistein_pow hx a s, smul_smul]
  rw [← hP_eval, ← integral_sub hf_int hP_int]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hdom :
      (∫ w in Ioi (0 : ℝ),
        ‖(Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w -
          (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • P w‖) ≤
      ∫ w in Ioi (0 : ℝ),
        C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by
    refine integral_mono_ae (hf_int.sub hP_int).norm
      ((integrableOn_exp_bleistein_abs_pow hlam hx a N).const_mul C) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
    have hK_nn : 0 ≤ Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) :=
      mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hw.le _)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hK_nn]
    calc
      (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * ‖f w - P w‖
        ≤ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * (C * |w - a| ^ N) :=
          mul_le_mul_of_nonneg_left (hf w hw) hK_nn
      _ = C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by ring
  refine hdom.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_bleistein_abs_pow hx a N, mul_assoc]

/-! ### Uniform asymptotic expansion (DLMF 2.3.32) -/

/-- Strong measurability on `(0, ∞)` of `bleisteinAmplitude` when `(0, k)` maps onto `(0, ∞)`. -/
private lemma aestronglyMeasurable_bleisteinAmplitude_of_Ioo {p : ℝ → ℝ} {q : ℝ → E}
    {lam α k : ℝ} {U : Set ℝ} (hk : 0 < k) (hαk : α < k) (hIco : Ico 0 k ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (hq : ContinuousOn q U) (htend : Tendsto p (𝓝[<] k) atTop) :
    AEStronglyMeasurable (bleisteinAmplitude p q lam α U) (volume.restrict (Ioi 0)) := by
  have hw := contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  have himg : Ioi 0 ⊆ bleisteinCoord p α '' U := by
    rw [← image_bleisteinCoord_Ioo_eq_Ioi hk (hw.continuousOn.mono hIco) (hmono.mono hIco)
      (tendsto_bleisteinCoord_nhdsLT_atTop hαk htend)]
    exact image_mono (Ioo_subset_Ico_self.trans hIco)
  exact ((continuousOn_bleisteinAmplitude hU (hIco ⟨le_rfl, hk⟩) hw hmono
    (fun _ ht ↦ deriv_bleisteinCoord_pos_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright ht)
    hq).mono himg).aestronglyMeasurable measurableSet_Ioi

/-- Strong measurability on `(0, ∞)` of `bleisteinAmplitude` when `(0, ∞)` maps onto `(0, ∞)`. -/
private lemma aestronglyMeasurable_bleisteinAmplitude_of_Ioi {p : ℝ → ℝ} {q : ℝ → E}
    {lam α : ℝ} {U : Set ℝ} (hIci : Ici 0 ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (hq : ContinuousOn q U) (htend : Tendsto p atTop atTop) :
    AEStronglyMeasurable (bleisteinAmplitude p q lam α U) (volume.restrict (Ioi 0)) := by
  have hw := contDiffOn_bleisteinCoord_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright
  have hmono := strictMonoOn_bleisteinCoord_of_deriv_sign hconv hα
    (hp.differentiableOn (by norm_num)) hpleft hpright
  have himg : Ioi 0 ⊆ bleisteinCoord p α '' U := by
    rw [← image_bleisteinCoord_Ioi_eq_Ioi (hw.continuousOn.mono hIci) (hmono.mono hIci)
      (tendsto_bleisteinCoord_atTop_atTop htend)]
    exact image_mono (Ioi_subset_Ici_self.trans hIci)
  exact ((continuousOn_bleisteinAmplitude hU (hIci self_mem_Ici) hw hmono
    (fun _ ht ↦ deriv_bleisteinCoord_pos_of_deriv_sign hU hconv hα hp hp'0 hp'' hpleft hpright ht)
    hq).mono himg).aestronglyMeasurable measurableSet_Ioi

/-- Absolute convergence on `(0, k)` (`x > 0`) of the Laplace-type integral `I(α, x)` when
`p t → +∞` as `t → k⁻` (`κ = +∞`) and `bleisteinAmplitude` satisfies a Taylor bound of order `N`. -/
theorem integrableOn_bleistein_Ioo {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E}
    {lam α x k C : ℝ} {N : ℕ} {U : Set ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hk : 0 < k) (hαk : α < k) (hIco : Ico 0 k ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (hq : ContinuousOn q U) (htend : Tendsto p (𝓝[<] k) atTop)
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α U w -
        ∑ s ∈ Finset.range N, (w - bleisteinOffset p α) ^ s • phi s‖ ≤
      C * |w - bleisteinOffset p α| ^ N) :
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioo 0 k) :=
  (integrableOn_bleisteinAmplitude_Ioo_iff_Ioi hk hαk hIco hU hconv hα hp hp'0 hp''
    hpleft hpright htend).mp <| integrableOn_exp_bleistein_smul_of_bound hlam hx
    (aestronglyMeasurable_bleisteinAmplitude_of_Ioo hk hαk hIco hU hconv hα hp hp'0 hp''
      hpleft hpright hq htend) hf

/-- Uniform asymptotic expansion and explicit remainder bound on `(0, k)` for DLMF 2.3.32
(`κ = +∞`). The data `p`, `q`, `phi` may depend arbitrarily on `α`; when `C` is chosen independent
of `α ∈ [α₁, α₂]`, the bound holds uniformly across `α ∈ [α₁, α₂]`. -/
theorem norm_exp_smul_integral_bleistein_Ioo_sub_le [CompleteSpace E]
    {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {lam α x k C : ℝ} {N : ℕ} {U : Set ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hk : 0 < k) (hαk : α < k) (hIco : Ico 0 k ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (hq : ContinuousOn q U) (htend : Tendsto p (𝓝[<] k) atTop)
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α U w -
        ∑ s ∈ Finset.range N, (w - bleisteinOffset p α) ^ s • phi s‖ ≤
      C * |w - bleisteinOffset p α| ^ N) :
    ‖Real.exp (x * p 0) • (∫ t in Ioo 0 k, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
          (bleisteinF lam s (bleisteinOffset p α * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (bleisteinOffset p α * Real.sqrt x) := by
  rw [integral_bleisteinCoord_Ioo_eq_Ioi hk hαk hIco hU hconv hα hp hp'0 hp'' hpleft hpright
    htend, smul_smul, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_smul]
  exact norm_bleistein_remainder_le hlam hx
    (aestronglyMeasurable_bleisteinAmplitude_of_Ioo hk hαk hIco hU hconv hα hp hp'0 hp''
      hpleft hpright hq htend) hf

/-- Absolute convergence on `(0, ∞)` (`x > 0`) of the Laplace-type integral `I(α, x)` when
`p t → +∞` as `t → +∞` (`κ = +∞`) and `bleisteinAmplitude` satisfies a Taylor bound of order `N`. -/
theorem integrableOn_bleistein_Ioi {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E}
    {lam α x C : ℝ} {N : ℕ} {U : Set ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hIci : Ici 0 ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (hq : ContinuousOn q U) (htend : Tendsto p atTop atTop)
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α U w -
        ∑ s ∈ Finset.range N, (w - bleisteinOffset p α) ^ s • phi s‖ ≤
      C * |w - bleisteinOffset p α| ^ N) :
    IntegrableOn (fun t ↦ (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) (Ioi 0) :=
  (integrableOn_bleisteinAmplitude_Ioi_iff_Ioi hIci hU hconv hα hp hp'0 hp''
    hpleft hpright htend).mp <| integrableOn_exp_bleistein_smul_of_bound hlam hx
    (aestronglyMeasurable_bleisteinAmplitude_of_Ioi hIci hU hconv hα hp hp'0 hp''
      hpleft hpright hq htend) hf

/-- Uniform asymptotic expansion and explicit remainder bound on `(0, ∞)` for DLMF 2.3.32
(`κ = +∞`). The data `p`, `q`, `phi` may depend arbitrarily on `α`; when `C` is chosen independent
of `α ∈ [α₁, α₂]`, the bound holds uniformly across `α ∈ [α₁, α₂]`. -/
theorem norm_exp_smul_integral_bleistein_Ioi_sub_le [CompleteSpace E]
    {p : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {lam α x C : ℝ} {N : ℕ} {U : Set ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hIci : Ici 0 ⊆ U)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hα : α ∈ U)
    (hp : ContDiffOn ℝ 2 p U) (hp'0 : deriv p α = 0) (hp'' : 0 < deriv (deriv p) α)
    (hpleft : ∀ t ∈ U, t < α → deriv p t < 0) (hpright : ∀ t ∈ U, α < t → 0 < deriv p t)
    (hq : ContinuousOn q U) (htend : Tendsto p atTop atTop)
    (hf : ∀ w > 0, ‖bleisteinAmplitude p q lam α U w -
        ∑ s ∈ Finset.range N, (w - bleisteinOffset p α) ^ s • phi s‖ ≤
      C * |w - bleisteinOffset p α| ^ N) :
    ‖Real.exp (x * p 0) • (∫ t in Ioi 0, (Real.exp (-x * p t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
          (bleisteinF lam s (bleisteinOffset p α * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (bleisteinOffset p α * Real.sqrt x) := by
  rw [integral_bleisteinCoord_Ioi_eq_Ioi hIci hU hconv hα hp hp'0 hp'' hpleft hpright htend,
    smul_smul, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_smul]
  exact norm_bleistein_remainder_le hlam hx
    (aestronglyMeasurable_bleisteinAmplitude_of_Ioi hIci hU hconv hα hp hp'0 hp''
      hpleft hpright hq htend) hf

end Banach

end TauCeti
