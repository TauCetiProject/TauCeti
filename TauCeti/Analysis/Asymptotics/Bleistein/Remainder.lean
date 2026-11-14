/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.Asymptotics.Bleistein.ChangeOfVariables
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Uniform remainder bound and expansion in Bleistein's method

After Bleistein's canonical change of variables (`TauCeti.bleisteinCoord`), a Laplace-type integral
with an interior or coalescing saddle point `α` and an algebraic endpoint singularity `t ^ (λ - 1)`
at `t = 0` takes the canonical form

  `∫ w in (0, ∞), (exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (λ - 1)) • f w`

when the upper canonical limit is `κ = ∞` (DLMF 2.3.29). Expanding the transformed amplitude `f`
around the canonical saddle `w = a` (`a = bleisteinCenter g α`),

  `f w = ∑ s < N, (w - a) ^ s • φ s + R_N w`,    `‖R_N w‖ ≤ C * |w - a| ^ N`,

produces a uniform asymptotic approximation in terms of the canonical comparison integrals
(DLMF 2.3.33)

* `bleisteinF λ s y = ∫ τ in (0, ∞), exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (λ - 1)`,
* `bleisteinG λ N y = ∫ τ in (0, ∞), exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (λ - 1)`,

which are related to parabolic cylinder functions and remain smooth across the coalescence `y = 0`
(`a = 0`). Because the constant `C` and the data `a`, `φ` are arbitrary, the resulting error bound
`C * x ^ (-(N + λ) / 2) * bleisteinG λ N (a * √x)` holds uniformly across any parameter family on
which `C` is chosen independent of `α` (DLMF 2.3.32). The amplitude `f` takes values in any real
Banach space `E`, so real- and complex-valued integrals are covered simultaneously.

## Main definitions

* `TauCeti.bleisteinF`: the canonical coefficient integrals `F_s(y)` of DLMF 2.3.33.
* `TauCeti.bleisteinG`: the positive comparison integrals `G_N(y)` controlling the remainder.

## Main results

* `TauCeti.integrableOn_bleisteinF`, `TauCeti.integrableOn_bleisteinG`: integrability on `(0, ∞)`
  for `λ > 0` and every `y : ℝ`.
* `TauCeti.continuous_bleisteinF`, `TauCeti.continuous_bleisteinG`: continuity in `y`.
* `TauCeti.bleisteinG_nonneg`, `TauCeti.bleisteinG_pos`, `TauCeti.abs_bleisteinF_le_bleisteinG`:
  positivity of `G_N` and domination `|F_s(y)| ≤ G_s(y)`.
* `TauCeti.bleisteinG_zero`, `TauCeti.bleisteinG_mul_two`, `TauCeti.bleisteinF_zero_zero`,
  `TauCeti.bleisteinG_zero_zero`, `TauCeti.bleisteinF_one_one`: special values and parity identities
  (`G_{2m} = F_{2m}`, `F_0(0) = G_0(0) = 2 ^ (λ / 2 - 1) * Γ(λ / 2)`, and `F_1(y) = 1` for `λ = 1`).
* `TauCeti.norm_bleistein_remainder_le`: the uniform remainder estimate on `(0, ∞)` in any real
  Banach space.
* `TauCeti.integrableOn_bleistein_of_taylor_bound`,
  `TauCeti.integrableOn_bleistein_Ioo_of_taylor_bound`,
  `TauCeti.integrableOn_bleistein_Ioi_of_taylor_bound`,
  `TauCeti.norm_exp_mul_integral_bleistein_sub_le`,
  `TauCeti.norm_exp_mul_integral_bleistein_Ioo_sub_le`,
  `TauCeti.norm_exp_mul_integral_bleistein_Ioi_sub_le`: convergence and explicit uniform remainder
  bound for the original integral `I(α, x)` (DLMF 2.3.32) on `(0, k)` and `(0, ∞)`.

## References

* N. Bleistein, Uniform asymptotic expansions of integrals with stationary point near algebraic
  singularity, *Comm. Pure Appl. Math.* 19 (1966), 353–370.
* N. Bleistein and R. A. Handelsman, *Asymptotic Expansions of Integrals*, Holt, Rinehart and
  Winston, 1975; reprinted Dover, 1986. Chapter 9, §4.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 9, §6.
* R. Wong, *Asymptotic Approximations of Integrals*, Academic Press, 1989; reprinted SIAM, 2001.
  Chapter 7, §2.
* NIST *Digital Library of Mathematical Functions*, §2.3(v), formulas 2.3.31–2.3.33,
  <https://dlmf.nist.gov/2.3#v>.
-/

public section

open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace TauCeti

/-! ### Canonical coefficient and comparison functions -/

/-- The canonical coefficient functions
`F_s(y) = ∫₀^∞ exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (λ - 1) dτ`
of Bleistein's uniform expansion (DLMF 2.3.33). -/
noncomputable def bleisteinF (lam : ℝ) (s : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)

/-- The nonnegative comparison functions
`G_N(y) = ∫₀^∞ exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (λ - 1) dτ`
controlling the remainder in Bleistein's uniform expansion. -/
noncomputable def bleisteinG (lam : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)

/-- Explicit integral formula for `bleisteinF`. -/
theorem bleisteinF_def (lam : ℝ) (s : ℕ) (y : ℝ) :
    bleisteinF lam s y =
      ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1) := by rfl

/-- Explicit integral formula for `bleisteinG`. -/
theorem bleisteinG_def (lam : ℝ) (N : ℕ) (y : ℝ) :
    bleisteinG lam N y =
      ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1) := by rfl

/-- Uniform Gaussian-polynomial dominating function on `(0, ∞)` for `|y| ≤ R`. -/
private noncomputable def bleisteinDom (lam : ℝ) (s : ℕ) (R τ : ℝ) : ℝ :=
  Real.exp (R ^ 2) * ∑ k ∈ Finset.range (s + 1),
    (R ^ (s - k) * s.choose k) * (τ ^ ((k : ℝ) + lam - 1) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2))

/-- Integrability of `bleisteinDom lam s R` on `(0, ∞)` for `λ > 0`. -/
private theorem integrableOn_bleisteinDom {lam : ℝ} (hlam : 0 < lam) (s : ℕ) (R : ℝ) :
    IntegrableOn (bleisteinDom lam s R) (Ioi 0) := by
  unfold bleisteinDom
  refine Integrable.const_mul (integrable_finsetSum _ fun k _ ↦ ?_) _
  have hk : -1 < (k : ℝ) + lam - 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4) hk).const_mul _

/-- Pointwise bound by `bleisteinDom lam s R τ` for `τ > 0` and `|y| ≤ R` (`R ≥ 0`). -/
private theorem le_bleisteinDom {lam y R τ : ℝ} {s : ℕ}
    (hR : 0 ≤ R) (hy : |y| ≤ R) (hτ : 0 < τ) :
    Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ s * τ ^ (lam - 1) ≤ bleisteinDom lam s R τ := by
  have hquad : -τ ^ 2 / 2 + y * τ ≤ -(1 / 4 : ℝ) * τ ^ 2 + R ^ 2 := by
    have hsq : y ^ 2 ≤ R ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hR])
    have hnonneg : 0 ≤ (τ / 2 - y) ^ 2 := sq_nonneg _
    linarith
  have hexp : Real.exp (-τ ^ 2 / 2 + y * τ) ≤
      Real.exp (R ^ 2) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2) := by
    rw [← Real.exp_add, add_comm (R ^ 2)]
    exact Real.exp_le_exp.mpr hquad
  have habs : |τ - y| ≤ τ + R := by
    calc |τ - y| ≤ |τ| + |y| := abs_sub _ _
      _ = τ + |y| := by rw [abs_of_pos hτ]
      _ ≤ τ + R := by linarith
  have hpow : |τ - y| ^ s ≤ (τ + R) ^ s := pow_le_pow_left₀ (abs_nonneg _) habs s
  calc Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ s * τ ^ (lam - 1)
      ≤ (Real.exp (R ^ 2) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2)) *
          (τ + R) ^ s * τ ^ (lam - 1) := by gcongr
    _ = Real.exp (R ^ 2) * (((τ + R) ^ s) *
          (τ ^ (lam - 1) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2))) := by ring
    _ = bleisteinDom lam s R τ := by
        unfold bleisteinDom
        rw [add_pow, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        have hrpow : τ ^ k * τ ^ (lam - 1) = τ ^ ((k : ℝ) + lam - 1) := by
          rw [← Real.rpow_natCast τ k, ← Real.rpow_add hτ, add_sub_assoc]
        calc τ ^ k * R ^ (s - k) * (s.choose k : ℝ) *
              (τ ^ (lam - 1) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2))
            = (R ^ (s - k) * s.choose k) *
                ((τ ^ k * τ ^ (lam - 1)) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2)) := by ring
          _ = (R ^ (s - k) * s.choose k) *
                (τ ^ ((k : ℝ) + lam - 1) * Real.exp (-(1 / 4 : ℝ) * τ ^ 2)) := by rw [hrpow]

/-- Strong measurability of the integrand of `bleisteinF` on `(0, ∞)`. -/
private theorem aestronglyMeasurable_bleisteinF_integrand (lam : ℝ) (s : ℕ) (y : ℝ) :
    AEStronglyMeasurable
      (fun τ : ℝ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1))
      (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine ((Real.continuous_exp.comp (by fun_prop)).continuousOn.mul
    ((continuous_id.sub continuous_const).pow s).continuousOn).mul ?_
  exact continuousOn_id.rpow_const fun τ hτ ↦ Or.inl (mem_Ioi.mp hτ).ne'

/-- Strong measurability of the integrand of `bleisteinG` on `(0, ∞)`. -/
private theorem aestronglyMeasurable_bleisteinG_integrand (lam : ℝ) (N : ℕ) (y : ℝ) :
    AEStronglyMeasurable
      (fun τ : ℝ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1))
      (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine ((Real.continuous_exp.comp (by fun_prop)).continuousOn.mul
    ((continuous_id.sub continuous_const).abs.pow N).continuousOn).mul ?_
  exact continuousOn_id.rpow_const fun τ hτ ↦ Or.inl (mem_Ioi.mp hτ).ne'

/-- Integrability of the integrand of `bleisteinF lam s y` on `(0, ∞)` for `λ > 0`. -/
theorem integrableOn_bleisteinF {lam : ℝ} (hlam : 0 < lam) (s : ℕ) (y : ℝ) :
    IntegrableOn (fun τ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1))
      (Ioi 0) := by
  refine Integrable.mono' (integrableOn_bleisteinDom hlam s |y|)
    (aestronglyMeasurable_bleisteinF_integrand lam s y) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
    abs_of_pos (Real.rpow_pos_of_pos hτ _)]
  exact le_bleisteinDom (abs_nonneg y) le_rfl hτ

/-- Integrability of the integrand of `bleisteinG lam N y` on `(0, ∞)` for `λ > 0`. -/
theorem integrableOn_bleisteinG {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (y : ℝ) :
    IntegrableOn (fun τ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1))
      (Ioi 0) := by
  refine Integrable.mono' (integrableOn_bleisteinDom hlam N |y|)
    (aestronglyMeasurable_bleisteinG_integrand lam N y) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (abs_nonneg _) _)) (Real.rpow_pos_of_pos hτ _).le)]
  exact le_bleisteinDom (abs_nonneg y) le_rfl hτ

/-- Continuity of `bleisteinF lam s` on `ℝ` for `λ > 0`. -/
theorem continuous_bleisteinF {lam : ℝ} (hlam : 0 < lam) (s : ℕ) :
    Continuous (bleisteinF lam s) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  refine continuousAt_of_dominated
    (bound := bleisteinDom lam s (|y₀| + 1))
    (Eventually.of_forall fun y ↦ aestronglyMeasurable_bleisteinF_integrand lam s y) ?_
    (integrableOn_bleisteinDom hlam s (|y₀| + 1)) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    have hyR : |y| ≤ |y₀| + 1 := by
      have hdist : |y - y₀| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hy
      linarith [abs_sub_abs_le_abs_sub y y₀]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
      abs_of_pos (Real.rpow_pos_of_pos hτ _)]
    exact le_bleisteinDom (by positivity) hyR hτ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
    exact (by fun_prop : Continuous fun y ↦
      Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1)).continuousAt

/-- Continuity of `bleisteinG lam N` on `ℝ` for `λ > 0`. -/
theorem continuous_bleisteinG {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    Continuous (bleisteinG lam N) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  refine continuousAt_of_dominated
    (bound := bleisteinDom lam N (|y₀| + 1))
    (Eventually.of_forall fun y ↦ aestronglyMeasurable_bleisteinG_integrand lam N y) ?_
    (integrableOn_bleisteinDom hlam N (|y₀| + 1)) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    have hyR : |y| ≤ |y₀| + 1 := by
      have hdist : |y - y₀| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hy
      linarith [abs_sub_abs_le_abs_sub y y₀]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (abs_nonneg _) _)) (Real.rpow_pos_of_pos hτ _).le)]
    exact le_bleisteinDom (by positivity) hyR hτ
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
    exact (by fun_prop : Continuous fun y ↦
      Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)).continuousAt

/-! ### Positivity, domination, and special values -/

/-- Nonnegativity of `bleisteinG lam N y`. -/
theorem bleisteinG_nonneg (lam : ℝ) (N : ℕ) (y : ℝ) : 0 ≤ bleisteinG lam N y := by
  refine setIntegral_nonneg measurableSet_Ioi fun τ (hτ : 0 < τ) ↦ ?_
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _))
    (Real.rpow_pos_of_pos hτ _).le

/-- Strict positivity of `bleisteinG lam N y` for `λ > 0` and every `y : ℝ`. -/
theorem bleisteinG_pos {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (y : ℝ) :
    0 < bleisteinG lam N y := by
  rw [bleisteinG, setIntegral_pos_iff_support_of_nonneg_ae _ (integrableOn_bleisteinG hlam N y)]
  · set c := max y 0 + 1
    have hsub : Ioi c ⊆ Function.support
        (fun τ : ℝ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1)) ∩ Ioi 0 := by
      intro τ (hτ : c < τ)
      have hτ0 : 0 < τ := by linarith [le_max_right y 0]
      have hτy : y < τ := by linarith [le_max_left y 0]
      refine ⟨?_, hτ0⟩
      rw [Function.mem_support]
      exact mul_ne_zero (mul_ne_zero (Real.exp_ne_zero _)
        (pow_ne_zero N (abs_ne_zero.mpr (sub_ne_zero.mpr hτy.ne'))))
        (Real.rpow_pos_of_pos hτ0 _).ne'
    have hvol : (0 : ENNReal) < volume (Ioi c) := by simp [Real.volume_Ioi]
    exact hvol.trans_le (measure_mono hsub)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _))
      (Real.rpow_pos_of_pos hτ _).le

/-- Domination of `bleisteinF` by `bleisteinG`: `|F_s(y)| ≤ G_s(y)`. -/
theorem abs_bleisteinF_le_bleisteinG (lam : ℝ) (s : ℕ) (y : ℝ) :
    |bleisteinF lam s y| ≤ bleisteinG lam s y := by
  rw [bleisteinF, bleisteinG, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : 0 < τ) ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow,
    abs_of_pos (Real.rpow_pos_of_pos hτ _)]

/-- At order `0`, `bleisteinG` and `bleisteinF` coincide everywhere. -/
@[simp]
theorem bleisteinG_zero (lam y : ℝ) : bleisteinG lam 0 y = bleisteinF lam 0 y := by
  simp [bleisteinG, bleisteinF]

/-- At even orders `2 * m`, `bleisteinG` and `bleisteinF` coincide everywhere. -/
theorem bleisteinG_mul_two (lam : ℝ) (m : ℕ) (y : ℝ) :
    bleisteinG lam (2 * m) y = bleisteinF lam (2 * m) y := by
  simp_rw [bleisteinG, bleisteinF, pow_mul, sq_abs]

/-- Value of `F_0(0)` in terms of the Gamma function:
`bleisteinF lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2)` for `λ > 0`. -/
theorem bleisteinF_zero_zero {lam : ℝ} (hlam : 0 < lam) :
    bleisteinF lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2) := by
  have hcongr : ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + 0 * τ) * (τ - 0) ^ 0 * τ ^ (lam - 1) =
      ∫ τ in Ioi (0 : ℝ), τ ^ (lam - 1) * Real.exp (-(1 / 2 : ℝ) * τ ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ ↦ ?_
    rw [Real.rpow_two]
    ring_nf
  rw [bleisteinF, hcongr,
    integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith : -1 < lam - 1) one_half_pos]
  have h2 : (1 / 2 : ℝ) ^ (-(lam - 1 + 1) / 2) * (1 / 2) = 2 ^ (lam / 2 - 1) := by
    rw [one_div, Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two,
      (by ring : -(-(lam - 1 + 1) / 2) = lam / 2), ← Real.rpow_neg_one 2,
      ← Real.rpow_add two_pos, sub_eq_add_neg]
  rw [h2, (by ring : (lam - 1 + 1) / 2 = lam / 2)]

/-- Value of `G_0(0)` in terms of the Gamma function. -/
theorem bleisteinG_zero_zero {lam : ℝ} (hlam : 0 < lam) :
    bleisteinG lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2) := by
  rw [bleisteinG_zero, bleisteinF_zero_zero hlam]

/-- Exact evaluation `F_1(y) = 1` at `λ = 1` for every real `y`. -/
@[simp]
theorem bleisteinF_one_one (y : ℝ) : bleisteinF 1 1 y = 1 := by
  have hderiv : ∀ τ ∈ Ici (0 : ℝ),
      HasDerivAt (fun u ↦ -Real.exp (-u ^ 2 / 2 + y * u))
        (Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) * τ ^ ((1 : ℝ) - 1)) τ := by
    intro τ _
    have hq : HasDerivAt (fun u ↦ -u ^ 2 / 2 + y * u) (-τ + y) τ :=
      (((hasDerivAt_pow 2 τ).fun_neg.div_const 2).fun_add
        ((hasDerivAt_id τ).const_mul y)).congr_deriv (by norm_num; ring)
    exact ((Real.hasDerivAt_exp _).comp τ hq).fun_neg.congr_deriv (by
      rw [sub_self, Real.rpow_zero]; ring)
  have hlim : Tendsto (fun u ↦ -Real.exp (-u ^ 2 / 2 + y * u)) atTop (𝓝 0) := by
    have hdom : Tendsto (fun u : ℝ ↦ Real.exp (y ^ 2) * Real.exp (-(1 / 4 : ℝ) * u ^ 2))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ ↦ -(1 / 4 : ℝ) * u ^ 2) atTop atBot :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop_of_neg (by norm_num)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (Real.exp (y ^ 2))
    refine squeeze_zero_norm' ?_ hdom
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with u _
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _), ← Real.exp_add, add_comm (y ^ 2)]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ (u / 2 - y) ^ 2 := sq_nonneg _
    linarith
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (by simpa only [pow_one] using integrableOn_bleisteinF zero_lt_one 1 y) hlim
  simpa [bleisteinF, pow_one] using hint

/-! ### Rescaled model integrals and uniform remainder bound -/

/-- Algebraic rescaling `τ = √x * w` in the canonical quadratic phase. -/
private theorem bleistein_rescaled_phase {a x w : ℝ} (hx : 0 ≤ x) :
    -(Real.sqrt x * w) ^ 2 / 2 + a * Real.sqrt x * (Real.sqrt x * w) =
      -x * (w ^ 2 / 2 - a * w) := by
  calc -(Real.sqrt x * w) ^ 2 / 2 + a * Real.sqrt x * (Real.sqrt x * w)
      = -(Real.sqrt x ^ 2 * w ^ 2) / 2 + a * (Real.sqrt x * Real.sqrt x) * w := by ring
    _ = -x * (w ^ 2 / 2 - a * w) := by rw [Real.sq_sqrt hx, Real.mul_self_sqrt hx]; ring

/-- Rescaled integrability on `(0, ∞)` corresponding to `bleisteinF`. -/
private theorem integrableOn_rescaled_bleisteinF {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (s : ℕ) :
    IntegrableOn (fun w ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1))
      (Ioi 0) := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hcomp := (integrableOn_Ioi_comp_mul_left_iff
    (fun τ ↦ Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
      (τ - a * Real.sqrt x) ^ s * τ ^ (lam - 1)) 0 hsq).mpr
    (by simpa using integrableOn_bleisteinF hlam s (a * Real.sqrt x))
  have hc_ne : (Real.sqrt x) ^ s * (Real.sqrt x) ^ (lam - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero s hsq.ne') (Real.rpow_pos_of_pos hsq _).ne'
  refine (integrable_smul_iff hc_ne _).mp (hcomp.congr_fun ?_ measurableSet_Ioi)
  intro w (hw : 0 < w)
  have hpow : (Real.sqrt x * w - a * Real.sqrt x) ^ s = (Real.sqrt x) ^ s * (w - a) ^ s := by
    rw [(by ring : Real.sqrt x * w - a * Real.sqrt x = Real.sqrt x * (w - a)), mul_pow]
  dsimp only [Pi.smul_apply, smul_eq_mul]
  rw [bleistein_rescaled_phase hx.le, hpow, Real.mul_rpow hsq.le hw.le]
  ring

/-- Rescaled integral evaluation in terms of `bleisteinF`. -/
private theorem integral_rescaled_bleisteinF {a x : ℝ} (lam : ℝ) (hx : 0 < x) (s : ℕ) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) =
      x ^ (-lam / 2) * (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hcomp := integral_comp_mul_left_Ioi
    (fun τ ↦ Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
      (τ - a * Real.sqrt x) ^ s * τ ^ (lam - 1)) 0 hsq
  rw [mul_zero, smul_eq_mul, ← bleisteinF_def] at hcomp
  have hcongr : (∫ w in Ioi (0 : ℝ),
        Real.exp (-(Real.sqrt x * w) ^ 2 / 2 + a * Real.sqrt x * (Real.sqrt x * w)) *
          (Real.sqrt x * w - a * Real.sqrt x) ^ s * (Real.sqrt x * w) ^ (lam - 1)) =
      ((Real.sqrt x) ^ s * (Real.sqrt x) ^ (lam - 1)) *
        ∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) ↦ ?_
    have hpow : (Real.sqrt x * w - a * Real.sqrt x) ^ s = (Real.sqrt x) ^ s * (w - a) ^ s := by
      rw [(by ring : Real.sqrt x * w - a * Real.sqrt x = Real.sqrt x * (w - a)), mul_pow]
    rw [bleistein_rescaled_phase hx.le, hpow, Real.mul_rpow hsq.le hw.le]
    ring
  rw [hcongr] at hcomp
  have hc_pos : 0 < (Real.sqrt x) ^ s * (Real.sqrt x) ^ (lam - 1) :=
    mul_pos (pow_pos hsq s) (Real.rpow_pos_of_pos hsq _)
  have hscale : ((Real.sqrt x) ^ s * (Real.sqrt x) ^ (lam - 1))⁻¹ * (Real.sqrt x)⁻¹ =
      x ^ (-lam / 2) * x ^ (-(s : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ s, ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le,
      ← Real.rpow_add hx, ← Real.rpow_neg hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_add hx,
      ← Real.rpow_add hx]
    congr 1
    ring
  calc (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1))
      = ((Real.sqrt x) ^ s * (Real.sqrt x) ^ (lam - 1))⁻¹ *
          (((Real.sqrt x) ^ s * (Real.sqrt x) ^ (lam - 1)) *
            ∫ w in Ioi (0 : ℝ),
              Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) := by
        rw [inv_mul_cancel_left₀ hc_pos.ne']
    _ = (((Real.sqrt x) ^ s * (Real.sqrt x) ^ (lam - 1))⁻¹ * (Real.sqrt x)⁻¹) *
          bleisteinF lam s (a * Real.sqrt x) := by
        rw [hcomp, mul_assoc]
    _ = x ^ (-lam / 2) * (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) := by
        rw [hscale]; ring

/-- Rescaled integrability on `(0, ∞)` corresponding to `bleisteinG`. -/
private theorem integrableOn_rescaled_bleisteinG {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (N : ℕ) :
    IntegrableOn (fun w ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1))
      (Ioi 0) := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hcomp := (integrableOn_Ioi_comp_mul_left_iff
    (fun τ ↦ Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
      |τ - a * Real.sqrt x| ^ N * τ ^ (lam - 1)) 0 hsq).mpr
    (by simpa using integrableOn_bleisteinG hlam N (a * Real.sqrt x))
  have hc_ne : (Real.sqrt x) ^ N * (Real.sqrt x) ^ (lam - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero N hsq.ne') (Real.rpow_pos_of_pos hsq _).ne'
  refine (integrable_smul_iff hc_ne _).mp (hcomp.congr_fun ?_ measurableSet_Ioi)
  intro w (hw : 0 < w)
  have hpow : |Real.sqrt x * w - a * Real.sqrt x| ^ N = (Real.sqrt x) ^ N * |w - a| ^ N := by
    rw [(by ring : Real.sqrt x * w - a * Real.sqrt x = Real.sqrt x * (w - a)),
      abs_mul, abs_of_pos hsq, mul_pow]
  dsimp only [Pi.smul_apply, smul_eq_mul]
  rw [bleistein_rescaled_phase hx.le, hpow, Real.mul_rpow hsq.le hw.le]
  ring

/-- Rescaled integral evaluation in terms of `bleisteinG`. -/
private theorem integral_rescaled_bleisteinG {a x : ℝ} (lam : ℝ) (hx : 0 < x) (N : ℕ) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) =
      x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (a * Real.sqrt x) := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hcomp := integral_comp_mul_left_Ioi
    (fun τ ↦ Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
      |τ - a * Real.sqrt x| ^ N * τ ^ (lam - 1)) 0 hsq
  rw [mul_zero, smul_eq_mul, ← bleisteinG_def] at hcomp
  have hcongr : (∫ w in Ioi (0 : ℝ),
        Real.exp (-(Real.sqrt x * w) ^ 2 / 2 + a * Real.sqrt x * (Real.sqrt x * w)) *
          |Real.sqrt x * w - a * Real.sqrt x| ^ N * (Real.sqrt x * w) ^ (lam - 1)) =
      ((Real.sqrt x) ^ N * (Real.sqrt x) ^ (lam - 1)) *
        ∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) ↦ ?_
    have hpow : |Real.sqrt x * w - a * Real.sqrt x| ^ N = (Real.sqrt x) ^ N * |w - a| ^ N := by
      rw [(by ring : Real.sqrt x * w - a * Real.sqrt x = Real.sqrt x * (w - a)),
        abs_mul, abs_of_pos hsq, mul_pow]
    rw [bleistein_rescaled_phase hx.le, hpow, Real.mul_rpow hsq.le hw.le]
    ring
  rw [hcongr] at hcomp
  have hc_pos : 0 < (Real.sqrt x) ^ N * (Real.sqrt x) ^ (lam - 1) :=
    mul_pos (pow_pos hsq N) (Real.rpow_pos_of_pos hsq _)
  have hscale : ((Real.sqrt x) ^ N * (Real.sqrt x) ^ (lam - 1))⁻¹ * (Real.sqrt x)⁻¹ =
      x ^ (-((N : ℝ) + lam) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ N, ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le,
      ← Real.rpow_add hx, ← Real.rpow_neg hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 1
    ring
  calc (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1))
      = ((Real.sqrt x) ^ N * (Real.sqrt x) ^ (lam - 1))⁻¹ *
          (((Real.sqrt x) ^ N * (Real.sqrt x) ^ (lam - 1)) *
            ∫ w in Ioi (0 : ℝ),
              Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by
        rw [inv_mul_cancel_left₀ hc_pos.ne']
    _ = (((Real.sqrt x) ^ N * (Real.sqrt x) ^ (lam - 1))⁻¹ * (Real.sqrt x)⁻¹) *
          bleisteinG lam N (a * Real.sqrt x) := by
        rw [hcomp, mul_assoc]
    _ = x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (a * Real.sqrt x) := by
        rw [hscale]

/-- Integrability of the truncated Taylor polynomial against Bleistein's canonical kernel. -/
private theorem integrableOn_bleistein_poly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (N : ℕ) (phi : ℕ → E) :
    IntegrableOn (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
      ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) (Ioi 0) := by
  refine IntegrableOn.congr_fun
    (integrable_finsetSum (Finset.range N) fun s _ ↦
      (integrableOn_rescaled_bleisteinF hlam hx a s).smul_const (phi s))
    (fun w _ ↦ ?_) measurableSet_Ioi
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [smul_smul]
  congr 1
  ring

/-- Evaluation of the integral of the truncated Taylor polynomial against Bleistein's kernel. -/
private theorem integral_bleistein_poly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (N : ℕ) (phi : ℕ → E) :
    (∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) =
      x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
        (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s := by
  have hcongr : (∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) =
      ∫ w in Ioi (0 : ℝ), ∑ s ∈ Finset.range N,
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) • phi s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ ↦ ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [smul_smul]
    congr 1
    ring
  rw [hcongr, integral_finsetSum (Finset.range N) fun s _ ↦
    (integrableOn_rescaled_bleisteinF hlam hx a s).smul_const (phi s), Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [integral_smul_const, integral_rescaled_bleisteinF lam hx s, smul_smul]

/-- Integrability of Bleistein's canonical integral on `(0, ∞)` whenever `f` satisfies a polynomial
remainder bound around `w = a`. -/
theorem integrableOn_bleistein_model_of_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam a C x : ℝ} {N : ℕ} {f : ℝ → E} {phi : ℕ → E}
    (hlam : 0 < lam) (hx : 0 < x)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖ ≤ C * |w - a| ^ N) :
    IntegrableOn (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w)
      (Ioi 0) := by
  have hkern_meas : AEStronglyMeasurable
      (fun w : ℝ ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (Real.continuous_exp.comp (by fun_prop)).continuousOn.mul
      (continuousOn_id.rpow_const fun w hw ↦ Or.inl (mem_Ioi.mp hw).ne')
  have hpoly_meas : AEStronglyMeasurable
      (fun w : ℝ ↦ ∑ s ∈ Finset.range N, (w - a) ^ s • phi s)
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous fun w : ℝ ↦
      ∑ s ∈ Finset.range N, (w - a) ^ s • phi s).aestronglyMeasurable
  have hrem_int : IntegrableOn
      (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        (f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_rescaled_bleisteinG hlam hx a N).const_mul C)
      (hkern_meas.smul (hfm.sub hpoly_meas)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
    have hpos : 0 ≤ Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hw _).le
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
    calc (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) *
          ‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖
        ≤ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * (C * |w - a| ^ N) :=
          mul_le_mul_of_nonneg_left (hf w hw) hpos
      _ = C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by ring
  refine (hrem_int.add (integrableOn_bleistein_poly hlam hx a N phi)).congr_fun
    (fun w _ ↦ ?_) measurableSet_Ioi
  simp [smul_sub]

/-- **Bleistein's uniform remainder bound** on `(0, ∞)` (behind DLMF 2.3.32, `κ = ∞`), for an
amplitude `f` valued in a real Banach space `E`. The constant `C` and the data `a`, `phi` may
depend on an external parameter `α`; the estimate is uniform across any parameter set on which `C`
is chosen independent of `α`. -/
theorem norm_bleistein_remainder_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {lam a C x : ℝ} {N : ℕ} {f : ℝ → E} {phi : ℕ → E}
    (hlam : 0 < lam) (hx : 0 < x)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ w > 0, ‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖ ≤ C * |w - a| ^ N) :
    ‖(∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w) -
        x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
          (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (a * Real.sqrt x) := by
  have hf_int := integrableOn_bleistein_model_of_bound hlam hx hfm hf
  have hpoly_int := integrableOn_bleistein_poly hlam hx a N phi
  rw [← integral_bleistein_poly hlam hx a N phi, ← integral_sub hf_int hpoly_int]
  have hsub_congr : (∫ w in Ioi (0 : ℝ),
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w -
          (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
            ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) =
      ∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        (f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) :=
    setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ (smul_sub _ _ _).symm
  rw [hsub_congr]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hdom_int := (integrableOn_rescaled_bleisteinG hlam hx a N).const_mul C
  refine (integral_mono_ae ((hf_int.sub hpoly_int).congr_fun
      (fun _ _ ↦ (smul_sub _ _ _).symm) measurableSet_Ioi).norm hdom_int ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
    have hpos : 0 ≤ Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hw _).le
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
    calc (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) *
          ‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖
        ≤ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * (C * |w - a| ^ N) :=
          mul_le_mul_of_nonneg_left (hf w hw) hpos
      _ = C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by ring
  · rw [integral_const_mul, integral_rescaled_bleisteinG lam hx N, mul_assoc]

/-! ### Uniform expansion of Laplace-type integrals (DLMF 2.3.32) -/

/-- Convergence (Bochner integrability, hence absolute convergence) of the original integral
`I(α, x) = ∫ t in s, (exp (-x * g t) * t ^ (λ - 1)) • q t` under the hypotheses of Bleistein's
method when `bleisteinCoord g α '' s = (0, ∞)` and the transformed amplitude satisfies a Taylor
remainder bound. -/
theorem integrableOn_bleistein_of_taylor_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam C x : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U s : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hs : IsOpen s) (hsU : s ⊆ U) (hs0 : s ⊆ Ioi 0)
    (hα : α ∈ U) (h0 : 0 ∈ U) (hg : ContDiffOn ℝ 2 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd1 : deriv g α = 0) (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ s, t ≠ α → deriv g t ≠ 0)
    (hq : ContinuousOn q s) (himg : bleisteinCoord g α '' s = Ioi 0)
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q s α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    IntegrableOn (fun t ↦ (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) s := by
  have hw_c1 := contDiffOn_bleisteinCoord hU hα hg hanti hmono hd1 hd2
  have hinj : InjOn (bleisteinCoord g α) s :=
    (strictMonoOn_bleisteinCoord hα hanti hmono).injOn.mono hsU
  have hw_pos : ∀ t ∈ s, 0 < bleisteinCoord g α t := fun t ht ↦
    bleisteinCoord_pos hα h0 hanti hmono (hsU ht) (hs0 ht)
  have hdpos : ∀ t ∈ s, 0 < deriv (bleisteinCoord g α) t := fun t ht ↦
    deriv_bleisteinCoord_pos hU hα hg hanti hmono hd1 hd2 (hsU ht) (hreg t ht)
  have hw_diff : DifferentiableOn ℝ (bleisteinCoord g α) U :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hU).mp hw_c1).1
  have hderiv : ∀ t ∈ s, HasDerivWithinAt (bleisteinCoord g α) (deriv (bleisteinCoord g α) t) s t :=
    fun t ht ↦ (hw_diff.differentiableAt (hU.mem_nhds (hsU ht))).hasDerivAt.hasDerivWithinAt
  have hf_cont : ContinuousOn (bleisteinAmplitude lam g q s α) (Ioi 0) :=
    himg ▸ continuousOn_bleisteinAmplitude hU hs hsU hs0 hw_c1 hinj hw_pos
      (fun t ht ↦ (hdpos t ht).ne') hq
  have hmin : ∀ t ∈ U, g α ≤ g t := fun t ht ↦
    (le_total t α).elim (fun h ↦ hanti.antitoneOn ⟨ht, h⟩ ⟨hα, le_rfl⟩ h)
      (fun h ↦ hmono.monotoneOn ⟨hα, le_rfl⟩ ⟨ht, h⟩ h)
  rw [← integrableOn_bleistein_iff hs.measurableSet hs0 (hmin 0 h0) (fun t ht ↦ hmin t (hsU ht))
    hw_pos hinj hderiv hdpos, himg]
  exact integrableOn_bleistein_model_of_bound hlam hx
    (hf_cont.aestronglyMeasurable measurableSet_Ioi) hf

/-- **Uniform Bleistein expansion with explicit remainder** (DLMF 2.3.32, `κ = ∞`), on an open
integration domain `s ⊆ (0, ∞)` mapped onto `(0, ∞)` by `bleisteinCoord g α`. -/
theorem norm_exp_mul_integral_bleistein_sub_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam C x : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U s : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hs : IsOpen s) (hsU : s ⊆ U) (hs0 : s ⊆ Ioi 0)
    (hα : α ∈ U) (h0 : 0 ∈ U) (hg : ContDiffOn ℝ 2 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd1 : deriv g α = 0) (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ s, t ≠ α → deriv g t ≠ 0)
    (hq : ContinuousOn q s) (himg : bleisteinCoord g α '' s = Ioi 0)
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q s α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    ‖Real.exp (x * g 0) • (∫ t in s, (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ n ∈ Finset.range N,
          (bleisteinF lam n (bleisteinCenter g α * Real.sqrt x) * x ^ (-(n : ℝ) / 2)) • phi n‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) *
        bleisteinG lam N (bleisteinCenter g α * Real.sqrt x) := by
  have hw_c1 := contDiffOn_bleisteinCoord hU hα hg hanti hmono hd1 hd2
  have hinj : InjOn (bleisteinCoord g α) s :=
    (strictMonoOn_bleisteinCoord hα hanti hmono).injOn.mono hsU
  have hw_pos : ∀ t ∈ s, 0 < bleisteinCoord g α t := fun t ht ↦
    bleisteinCoord_pos hα h0 hanti hmono (hsU ht) (hs0 ht)
  have hdpos : ∀ t ∈ s, 0 < deriv (bleisteinCoord g α) t := fun t ht ↦
    deriv_bleisteinCoord_pos hU hα hg hanti hmono hd1 hd2 (hsU ht) (hreg t ht)
  have hw_diff : DifferentiableOn ℝ (bleisteinCoord g α) U :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hU).mp hw_c1).1
  have hderiv : ∀ t ∈ s, HasDerivWithinAt (bleisteinCoord g α) (deriv (bleisteinCoord g α) t) s t :=
    fun t ht ↦ (hw_diff.differentiableAt (hU.mem_nhds (hsU ht))).hasDerivAt.hasDerivWithinAt
  have hf_cont : ContinuousOn (bleisteinAmplitude lam g q s α) (Ioi 0) :=
    himg ▸ continuousOn_bleisteinAmplitude hU hs hsU hs0 hw_c1 hinj hw_pos
      (fun t ht ↦ (hdpos t ht).ne') hq
  have hmin : ∀ t ∈ U, g α ≤ g t := fun t ht ↦
    (le_total t α).elim (fun h ↦ hanti.antitoneOn ⟨ht, h⟩ ⟨hα, le_rfl⟩ h)
      (fun h ↦ hmono.monotoneOn ⟨hα, le_rfl⟩ ⟨ht, h⟩ h)
  rw [exp_mul_integral_bleistein_eq hs.measurableSet hs0 (hmin 0 h0) (fun t ht ↦ hmin t (hsU ht))
    hw_pos hinj hderiv hdpos, himg]
  exact norm_bleistein_remainder_le hlam hx (hf_cont.aestronglyMeasurable measurableSet_Ioi) hf

/-- Convergence (Bochner integrability) of the Bleistein integral on `(0, k)` when
`g(t) → ∞` as `t → k⁻`. -/
theorem integrableOn_bleistein_Ioo_of_taylor_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam C x k : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U : Set ℝ} {α : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hI : Ico 0 k ⊆ U) (hα : α ∈ U) (hg : ContDiffOn ℝ 2 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd1 : deriv g α = 0) (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ Ioo 0 k, t ≠ α → deriv g t ≠ 0)
    (htop : Tendsto g (𝓝[<] k) atTop) (hq : ContinuousOn q (Ioo 0 k))
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q (Ioo 0 k) α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    IntegrableOn (fun t ↦ (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) (Ioo 0 k) :=
  integrableOn_bleistein_of_taylor_bound hlam hx hU isOpen_Ioo
    (Ioo_subset_Ico_self.trans hI) (fun _ h ↦ h.1) hα (hI (left_mem_Ico.mpr hk))
    hg hanti hmono hd1 hd2 hreg hq
    (image_bleisteinCoord_Ioo_of_tendsto_atTop hk hα hI hg.continuousOn hanti hmono htop) hf

/-- **Uniform Bleistein expansion on `(0, k)`** (DLMF 2.3.32) when `g(t) → ∞` as `t → k⁻`. -/
theorem norm_exp_mul_integral_bleistein_Ioo_sub_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam C x k : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U : Set ℝ} {α : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hI : Ico 0 k ⊆ U) (hα : α ∈ U) (hg : ContDiffOn ℝ 2 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd1 : deriv g α = 0) (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ Ioo 0 k, t ≠ α → deriv g t ≠ 0)
    (htop : Tendsto g (𝓝[<] k) atTop) (hq : ContinuousOn q (Ioo 0 k))
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q (Ioo 0 k) α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    ‖Real.exp (x * g 0) • (∫ t in Ioo 0 k, (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ n ∈ Finset.range N,
          (bleisteinF lam n (bleisteinCenter g α * Real.sqrt x) * x ^ (-(n : ℝ) / 2)) • phi n‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) *
        bleisteinG lam N (bleisteinCenter g α * Real.sqrt x) :=
  norm_exp_mul_integral_bleistein_sub_le hlam hx hU isOpen_Ioo
    (Ioo_subset_Ico_self.trans hI) (fun _ h ↦ h.1) hα (hI (left_mem_Ico.mpr hk))
    hg hanti hmono hd1 hd2 hreg hq
    (image_bleisteinCoord_Ioo_of_tendsto_atTop hk hα hI hg.continuousOn hanti hmono htop) hf

/-- Convergence (Bochner integrability) of the Bleistein integral on `(0, ∞)` when
`g(t) → ∞` as `t → ∞`. -/
theorem integrableOn_bleistein_Ioi_of_taylor_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam C x : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hI : Ici 0 ⊆ U) (hα : α ∈ U) (hg : ContDiffOn ℝ 2 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd1 : deriv g α = 0) (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ Ioi 0, t ≠ α → deriv g t ≠ 0)
    (htop : Tendsto g atTop atTop) (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q (Ioi 0) α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    IntegrableOn (fun t ↦ (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) (Ioi 0) :=
  integrableOn_bleistein_of_taylor_bound hlam hx hU isOpen_Ioi
    (Ioi_subset_Ici_self.trans hI) Subset.rfl hα (hI self_mem_Ici)
    hg hanti hmono hd1 hd2 hreg hq
    (image_bleisteinCoord_Ioi_of_tendsto_atTop hα hI hg.continuousOn hanti hmono htop) hf

/-- **Uniform Bleistein expansion on `(0, ∞)`** (DLMF 2.3.32) when `g(t) → ∞` as `t → ∞`. -/
theorem norm_exp_mul_integral_bleistein_Ioi_sub_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam C x : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hI : Ici 0 ⊆ U) (hα : α ∈ U) (hg : ContDiffOn ℝ 2 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd1 : deriv g α = 0) (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ Ioi 0, t ≠ α → deriv g t ≠ 0)
    (htop : Tendsto g atTop atTop) (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q (Ioi 0) α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    ‖Real.exp (x * g 0) • (∫ t in Ioi (0 : ℝ), (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) -
        x ^ (-lam / 2) • ∑ n ∈ Finset.range N,
          (bleisteinF lam n (bleisteinCenter g α * Real.sqrt x) * x ^ (-(n : ℝ) / 2)) • phi n‖ ≤
      C * x ^ (-((N : ℝ) + lam) / 2) *
        bleisteinG lam N (bleisteinCenter g α * Real.sqrt x) :=
  norm_exp_mul_integral_bleistein_sub_le hlam hx hU isOpen_Ioi
    (Ioi_subset_Ici_self.trans hI) Subset.rfl hα (hI self_mem_Ici)
    hg hanti hmono hd1 hd2 hreg hq
    (image_bleisteinCoord_Ioi_of_tendsto_atTop hα hI hg.continuousOn hanti hmono htop) hf

end TauCeti
