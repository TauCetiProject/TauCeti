/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.Asymptotics.Bleistein.ChangeOfVariables
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Order.Monotone.Basic

/-!
# Uniform remainder bound and expansion in Bleistein's method

After Bleistein's canonical change of variables (`TauCeti.bleisteinCoord`), a Laplace-type integral
`I(α, x) = ∫ t in s, (exp (-x * g t) * t ^ (λ - 1)) • q t` with an interior or coalescing saddle
point `α` and an algebraic endpoint singularity `t ^ (λ - 1)` at `t = 0` takes the canonical form

  `exp (-x * g 0) • ∫ w in (0, ∞), (exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (λ - 1)) • f w`

when the upper canonical limit is `κ = ∞` (DLMF 2.3.29), so `exp (x * g 0) • I(α, x)` equals the
unprefactored integral on the right. Expanding the transformed amplitude `f` around the canonical
saddle `w = a` (`a = bleisteinCenter g α`),

  `f w = ∑ s < N, (w - a) ^ s • φ s + R_N w`,    `‖R_N w‖ ≤ C * |w - a| ^ N`,

produces a uniform asymptotic approximation in terms of two families of canonical integrals:

* `bleisteinF λ s y = ∫ τ in (0, ∞), exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (λ - 1)`
  (DLMF 2.3.33), the canonical coefficient functions (related to parabolic cylinder functions);
* `bleisteinG λ N y = ∫ τ in (0, ∞), exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (λ - 1)`,
  the nonnegative comparison integrals controlling the remainder (which agree with `bleisteinF`
  at even `N` and at `y = 0`).

For `λ > 0`, both `bleisteinF λ s` and `bleisteinG λ N` are proved continuous on all of `ℝ`
(including across the coalescence `y = 0`, `a = 0`), with `bleisteinG λ N` strictly positive.
Because the constant `C` and the data `a`, `φ` are arbitrary, the resulting error bound
`C * x ^ (-(N + λ) / 2) * bleisteinG λ N (a * √x)` holds uniformly across any parameter family on
which `C` is chosen independent of `α` (DLMF 2.3.32). The amplitude `f` takes values in any real
Banach space `E`, so real- and complex-valued integrals are covered simultaneously.

## Main definitions

* `TauCeti.bleisteinF`: the canonical coefficient integrals `F_s(y)` of DLMF 2.3.33.
* `TauCeti.bleisteinG`: the positive comparison integrals `G_N(y)` controlling the remainder.

## Main results

* `TauCeti.integrableOn_bleisteinF_integrand`, `TauCeti.integrableOn_bleisteinG_integrand`:
  integrability of the defining integrands on `(0, ∞)` for `λ > 0` and every `y : ℝ`.
* `TauCeti.continuous_bleisteinF`, `TauCeti.continuous_bleisteinG`: continuity in `y`.
* `TauCeti.bleisteinG_nonneg`, `TauCeti.bleisteinG_pos`, `TauCeti.abs_bleisteinF_le_bleisteinG`:
  positivity of `G_N` and domination `|F_s(y)| ≤ G_s(y)`.
* `TauCeti.bleisteinG_zero`, `TauCeti.bleisteinG_two_mul_eq_bleisteinF`,
  `TauCeti.bleisteinG_apply_zero_eq_bleisteinF`, `TauCeti.bleisteinF_apply_zero`,
  `TauCeti.bleisteinF_zero_apply_zero`, `TauCeti.bleisteinG_zero_apply_zero`,
  `TauCeti.bleisteinF_one_one`: special values and parity identities (`G_{2m} = F_{2m}`,
  `G_N(0) = F_N(0) = 2 ^ ((λ + N) / 2 - 1) * Γ((λ + N) / 2)`, and `F_1(y) = 1` for `λ = 1`).
* `TauCeti.integrableOn_exp_mul_sub_pow_mul_rpow`,
  `TauCeti.integrableOn_exp_mul_abs_sub_pow_mul_rpow`,
  `TauCeti.integral_exp_mul_sub_pow_mul_rpow_eq_bleisteinF`,
  `TauCeti.integral_exp_mul_abs_sub_pow_mul_rpow_eq_bleisteinG`,
  `TauCeti.integral_exp_mul_rpow_smul_sum_eq_bleisteinF`: rescaling identities expressing canonical
  monomial, absolute-power, and polynomial integrals in terms of `bleisteinF` and `bleisteinG`.
* `TauCeti.norm_bleistein_remainder_le`: the uniform remainder estimate on `(0, ∞)` in any real
  Banach space.
* `TauCeti.integrableOn_bleistein_of_taylor_bound`,
  `TauCeti.integrableOn_bleistein_Ioo_of_taylor_bound`,
  `TauCeti.integrableOn_bleistein_Ioi_of_taylor_bound`,
  `TauCeti.norm_exp_smul_integral_bleistein_sub_le`,
  `TauCeti.norm_exp_smul_integral_bleistein_Ioo_sub_le`,
  `TauCeti.norm_exp_smul_integral_bleistein_Ioi_sub_le`: convergence and explicit uniform remainder
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

/-- Pointwise bound by `bleisteinDom lam s R τ` for `τ > 0` and `|y| ≤ R`. -/
private theorem le_bleisteinDom {lam y R τ : ℝ} {s : ℕ}
    (hy : |y| ≤ R) (hτ : 0 < τ) :
    Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ s * τ ^ (lam - 1) ≤ bleisteinDom lam s R τ := by
  have hquad : -τ ^ 2 / 2 + y * τ ≤ -(1 / 4 : ℝ) * τ ^ 2 + R ^ 2 := by
    have hsq : y ^ 2 ≤ R ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg ((abs_nonneg y).trans hy)])
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

/-- Strong measurability on `(0, ∞)` of `τ ↦ exp (-τ ^ 2 / 2 + y * τ) * h (τ - y) * τ ^ (λ - 1)`
for any continuous factor `h`. -/
private theorem aestronglyMeasurable_bleistein_integrand (lam : ℝ) {h : ℝ → ℝ}
    (hh : Continuous h) (y : ℝ) :
    AEStronglyMeasurable
      (fun τ : ℝ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * h (τ - y) * τ ^ (lam - 1))
      (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine ((Real.continuous_exp.comp (by fun_prop)).continuousOn.mul
    (hh.comp (continuous_id.sub continuous_const)).continuousOn).mul ?_
  exact continuousOn_id.rpow_const fun τ hτ ↦ Or.inl (mem_Ioi.mp hτ).ne'

/-- Almost-everywhere norm domination on `(0, ∞)` of the Bleistein integrand for a factor `h`
satisfying `|h u| ≤ |u| ^ s`, uniformly for `|y| ≤ R`. -/
private theorem ae_norm_bleistein_integrand_le {lam y R : ℝ} {s : ℕ} {h : ℝ → ℝ}
    (hh_le : ∀ u, |h u| ≤ |u| ^ s) (hy : |y| ≤ R) :
    ∀ᵐ τ ∂volume.restrict (Ioi 0),
      ‖Real.exp (-τ ^ 2 / 2 + y * τ) * h (τ - y) * τ ^ (lam - 1)‖ ≤
        bleisteinDom lam s R τ := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.rpow_pos_of_pos hτ _)]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hh_le (τ - y)) (Real.exp_pos _).le)
    (Real.rpow_pos_of_pos hτ _).le).trans (le_bleisteinDom hy hτ)

/-- Integrability on `(0, ∞)` of `τ ↦ exp (-τ ^ 2 / 2 + y * τ) * h (τ - y) * τ ^ (λ - 1)` when `h`
is continuous and satisfies `|h u| ≤ |u| ^ s`. -/
private theorem integrableOn_bleistein_integrand_of_le {lam : ℝ} (hlam : 0 < lam) {s : ℕ}
    {h : ℝ → ℝ} (hh_cont : Continuous h) (hh_le : ∀ u, |h u| ≤ |u| ^ s) (y : ℝ) :
    IntegrableOn (fun τ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * h (τ - y) * τ ^ (lam - 1))
      (Ioi 0) :=
  Integrable.mono' (integrableOn_bleisteinDom hlam s |y|)
    (aestronglyMeasurable_bleistein_integrand lam hh_cont y)
    (ae_norm_bleistein_integrand_le hh_le le_rfl)

/-- Dominated continuity in `y` of `∫₀^∞ exp (-τ ^ 2 / 2 + y * τ) * h (τ - y) * τ ^ (λ - 1) dτ`
when `h` is continuous and satisfies `|h u| ≤ |u| ^ s`. -/
private theorem continuous_integral_bleistein_of_le {lam : ℝ} (hlam : 0 < lam) {s : ℕ}
    {h : ℝ → ℝ} (hh_cont : Continuous h) (hh_le : ∀ u, |h u| ≤ |u| ^ s) :
    Continuous (fun y ↦
      ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + y * τ) * h (τ - y) * τ ^ (lam - 1)) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  refine continuousAt_of_dominated
    (bound := bleisteinDom lam s (|y₀| + 1))
    (Eventually.of_forall fun y ↦ aestronglyMeasurable_bleistein_integrand lam hh_cont y) ?_
    (integrableOn_bleisteinDom hlam s (|y₀| + 1)) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    have hyR : |y| ≤ |y₀| + 1 := by
      have hdist : |y - y₀| < 1 := by simpa [Real.dist_eq] using Metric.mem_ball.mp hy
      linarith [abs_sub_abs_le_abs_sub y y₀]
    exact ae_norm_bleistein_integrand_le hh_le hyR
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ _
    exact ((Real.continuous_exp.comp (by fun_prop)).mul
      (hh_cont.comp (continuous_const.sub continuous_id)) |>.mul continuous_const).continuousAt

/-- Integrability of the integrand of `bleisteinF lam s y` on `(0, ∞)` for `λ > 0`. -/
theorem integrableOn_bleisteinF_integrand {lam : ℝ} (hlam : 0 < lam) (s : ℕ) (y : ℝ) :
    IntegrableOn (fun τ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * (τ - y) ^ s * τ ^ (lam - 1))
      (Ioi 0) :=
  integrableOn_bleistein_integrand_of_le hlam (continuous_pow s) (fun u ↦ (abs_pow u s).le) y

/-- Integrability of the integrand of `bleisteinG lam N y` on `(0, ∞)` for `λ > 0`. -/
theorem integrableOn_bleisteinG_integrand {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (y : ℝ) :
    IntegrableOn (fun τ ↦ Real.exp (-τ ^ 2 / 2 + y * τ) * |τ - y| ^ N * τ ^ (lam - 1))
      (Ioi 0) :=
  integrableOn_bleistein_integrand_of_le (h := fun u ↦ |u| ^ N) hlam (continuous_abs.pow N)
    (fun u ↦ by rw [abs_pow, abs_abs]) y

/-- Continuity of `bleisteinF lam s` on `ℝ` for `λ > 0`. -/
theorem continuous_bleisteinF {lam : ℝ} (hlam : 0 < lam) (s : ℕ) :
    Continuous (bleisteinF lam s) := by
  rw [funext (bleisteinF_def lam s)]
  exact continuous_integral_bleistein_of_le hlam (continuous_pow s) (fun u ↦ (abs_pow u s).le)

/-- Continuity of `bleisteinG lam N` on `ℝ` for `λ > 0`. -/
theorem continuous_bleisteinG {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    Continuous (bleisteinG lam N) := by
  rw [funext (bleisteinG_def lam N)]
  exact continuous_integral_bleistein_of_le (h := fun u ↦ |u| ^ N) hlam (continuous_abs.pow N)
    (fun u ↦ by rw [abs_pow, abs_abs])

/-! ### Positivity, domination, and special values -/

/-- Nonnegativity of `bleisteinG lam N y`. -/
theorem bleisteinG_nonneg (lam : ℝ) (N : ℕ) (y : ℝ) : 0 ≤ bleisteinG lam N y := by
  refine setIntegral_nonneg measurableSet_Ioi fun τ (hτ : 0 < τ) ↦ ?_
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _))
    (Real.rpow_pos_of_pos hτ _).le

/-- Strict positivity of `bleisteinG lam N y` for `λ > 0` and every `y : ℝ`. -/
theorem bleisteinG_pos {lam : ℝ} (hlam : 0 < lam) (N : ℕ) (y : ℝ) :
    0 < bleisteinG lam N y := by
  rw [bleisteinG,
    setIntegral_pos_iff_support_of_nonneg_ae _ (integrableOn_bleisteinG_integrand hlam N y)]
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
@[simp]
theorem bleisteinG_two_mul_eq_bleisteinF (lam : ℝ) (m : ℕ) (y : ℝ) :
    bleisteinG lam (2 * m) y = bleisteinF lam (2 * m) y := by
  simp_rw [bleisteinG, bleisteinF, pow_mul, sq_abs]

/-- At `y = 0`, `bleisteinG` and `bleisteinF` coincide for every order `N`. -/
@[simp]
theorem bleisteinG_apply_zero_eq_bleisteinF (lam : ℝ) (N : ℕ) :
    bleisteinG lam N 0 = bleisteinF lam N 0 := by
  rw [bleisteinG_def, bleisteinF_def]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : 0 < τ) ↦ ?_
  rw [sub_zero, abs_of_pos hτ]

/-- Value of `F_s(0)` at the coalescence point `y = 0` in terms of the Gamma function:
`bleisteinF lam s 0 = 2 ^ ((lam + s) / 2 - 1) * Real.Gamma ((lam + s) / 2)` for `0 < λ + s`. -/
theorem bleisteinF_apply_zero {lam : ℝ} {s : ℕ} (h : 0 < lam + s) :
    bleisteinF lam s 0 = 2 ^ ((lam + s) / 2 - 1) * Real.Gamma ((lam + s) / 2) := by
  have hcongr : ∫ τ in Ioi (0 : ℝ), Real.exp (-τ ^ 2 / 2 + 0 * τ) * (τ - 0) ^ s * τ ^ (lam - 1) =
      ∫ τ in Ioi (0 : ℝ), τ ^ (lam + s - 1) * Real.exp (-(1 / 2 : ℝ) * τ ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : 0 < τ) ↦ ?_
    rw [sub_zero, zero_mul, add_zero, Real.rpow_two, ← Real.rpow_natCast τ s]
    have hmul : τ ^ (s : ℝ) * τ ^ (lam - 1) = τ ^ (lam + s - 1) := by
      rw [← Real.rpow_add hτ]
      congr 1
      ring
    calc Real.exp (-τ ^ 2 / 2) * τ ^ (s : ℝ) * τ ^ (lam - 1)
        = (τ ^ (s : ℝ) * τ ^ (lam - 1)) * Real.exp (-(1 / 2 : ℝ) * τ ^ 2) := by ring_nf
      _ = τ ^ (lam + s - 1) * Real.exp (-(1 / 2 : ℝ) * τ ^ 2) := by rw [hmul]
  rw [bleisteinF, hcongr,
    integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith : -1 < lam + s - 1) one_half_pos]
  have h2 : (1 / 2 : ℝ) ^ (-(lam + s - 1 + 1) / 2) * (1 / 2) = 2 ^ ((lam + s) / 2 - 1) := by
    have : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
    rw [this, ← Real.rpow_mul zero_le_two, ← Real.rpow_add two_pos]
    congr 1
    ring
  rw [h2, (by ring : (lam + s - 1 + 1) / 2 = (lam + s) / 2)]

/-- Value of `F_0(0)` in terms of the Gamma function:
`bleisteinF lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2)` for `λ > 0`. -/
theorem bleisteinF_zero_apply_zero {lam : ℝ} (hlam : 0 < lam) :
    bleisteinF lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2) := by
  simpa using bleisteinF_apply_zero (s := 0) (by simpa using hlam)

/-- Value of `G_0(0)` in terms of the Gamma function. -/
theorem bleisteinG_zero_apply_zero {lam : ℝ} (hlam : 0 < lam) :
    bleisteinG lam 0 0 = 2 ^ (lam / 2 - 1) * Real.Gamma (lam / 2) := by
  rw [bleisteinG_zero, bleisteinF_zero_apply_zero hlam]

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
    (by simpa only [pow_one] using integrableOn_bleisteinF_integrand zero_lt_one 1 y) hlim
  simpa [bleisteinF, pow_one] using hint

/-! ### Rescaled model integrals and uniform remainder bound -/

/-- Pointwise rescaling `τ = √x * w` of the canonical integrand for a homogeneous factor `h`. -/
private theorem bleistein_rescaled_integrand {lam a x w : ℝ} {n : ℕ} {h : ℝ → ℝ}
    (hx : 0 < x) (hw : 0 < w) (hh : ∀ c > 0, ∀ u, h (c * u) = c ^ n * h u) :
    Real.exp (-(Real.sqrt x * w) ^ 2 / 2 + a * Real.sqrt x * (Real.sqrt x * w)) *
        h (Real.sqrt x * w - a * Real.sqrt x) * (Real.sqrt x * w) ^ (lam - 1) =
      ((Real.sqrt x) ^ n * (Real.sqrt x) ^ (lam - 1)) *
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * h (w - a) * w ^ (lam - 1)) := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hphase : -(Real.sqrt x * w) ^ 2 / 2 + a * Real.sqrt x * (Real.sqrt x * w) =
      -x * (w ^ 2 / 2 - a * w) := by
    calc -(Real.sqrt x * w) ^ 2 / 2 + a * Real.sqrt x * (Real.sqrt x * w)
        = -(Real.sqrt x ^ 2 * w ^ 2) / 2 + a * (Real.sqrt x * Real.sqrt x) * w := by ring
      _ = -x * (w ^ 2 / 2 - a * w) := by rw [Real.sq_sqrt hx.le, Real.mul_self_sqrt hx.le]; ring
  have hhom : h (Real.sqrt x * w - a * Real.sqrt x) = (Real.sqrt x) ^ n * h (w - a) := by
    rw [(by ring : Real.sqrt x * w - a * Real.sqrt x = Real.sqrt x * (w - a)), hh _ hsq]
  rw [hphase, hhom, Real.mul_rpow hsq.le hw.le]
  ring

/-- Rescaled integrability on `(0, ∞)` for a factor `h` homogeneous of degree `n` on `(0, ∞)`. -/
private theorem integrableOn_exp_mul_homog_mul_rpow {lam x : ℝ} {n : ℕ} {h : ℝ → ℝ}
    (hx : 0 < x) (a : ℝ) (hh : ∀ c > 0, ∀ u, h (c * u) = c ^ n * h u)
    (hint : IntegrableOn (fun τ ↦
      Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) * h (τ - a * Real.sqrt x) * τ ^ (lam - 1))
      (Ioi 0)) :
    IntegrableOn (fun w ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * h (w - a) * w ^ (lam - 1))
      (Ioi 0) := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hcomp := (integrableOn_Ioi_comp_mul_left_iff
    (fun τ ↦ Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
      h (τ - a * Real.sqrt x) * τ ^ (lam - 1)) 0 hsq).mpr
    (by simpa only [mul_zero] using hint)
  have hc_ne : (Real.sqrt x) ^ n * (Real.sqrt x) ^ (lam - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero n hsq.ne') (Real.rpow_pos_of_pos hsq _).ne'
  refine (integrable_smul_iff hc_ne _).mp (hcomp.congr_fun ?_ measurableSet_Ioi)
  intro w (hw : 0 < w)
  exact bleistein_rescaled_integrand hx hw hh

/-- Rescaled integral identity on `(0, ∞)` for a factor `h` homogeneous of degree `n` on
`(0, ∞)`. -/
private theorem integral_exp_mul_homog_mul_rpow {x : ℝ} (lam : ℝ) (hx : 0 < x) (a : ℝ) {n : ℕ}
    {h : ℝ → ℝ} (hh : ∀ c > 0, ∀ u, h (c * u) = c ^ n * h u) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * h (w - a) * w ^ (lam - 1)) =
      x ^ (-((n : ℝ) + lam) / 2) *
        ∫ τ in Ioi (0 : ℝ),
          Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) * h (τ - a * Real.sqrt x) *
            τ ^ (lam - 1) := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hcomp := integral_comp_mul_left_Ioi
    (fun τ ↦ Real.exp (-τ ^ 2 / 2 + (a * Real.sqrt x) * τ) *
      h (τ - a * Real.sqrt x) * τ ^ (lam - 1)) 0 hsq
  rw [mul_zero, smul_eq_mul] at hcomp
  have hcongr : (∫ w in Ioi (0 : ℝ),
        Real.exp (-(Real.sqrt x * w) ^ 2 / 2 + a * Real.sqrt x * (Real.sqrt x * w)) *
          h (Real.sqrt x * w - a * Real.sqrt x) * (Real.sqrt x * w) ^ (lam - 1)) =
      ((Real.sqrt x) ^ n * (Real.sqrt x) ^ (lam - 1)) *
        ∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * h (w - a) * w ^ (lam - 1) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun w hw ↦
      bleistein_rescaled_integrand hx hw hh
  rw [hcongr] at hcomp
  have hc_pos : 0 < (Real.sqrt x) ^ n * (Real.sqrt x) ^ (lam - 1) :=
    mul_pos (pow_pos hsq n) (Real.rpow_pos_of_pos hsq _)
  have hsqrt (r : ℝ) : Real.sqrt x ^ r = x ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    ring_nf
  have hscale : ((Real.sqrt x) ^ n * (Real.sqrt x) ^ (lam - 1))⁻¹ * (Real.sqrt x)⁻¹ =
      x ^ (-((n : ℝ) + lam) / 2) := by
    rw [← Real.rpow_natCast, hsqrt, hsqrt, Real.sqrt_eq_rpow]
    simp only [← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 1
    ring
  rw [← hscale, mul_assoc, ← hcomp, inv_mul_cancel_left₀ hc_pos.ne']

/-- Integrability on `(0, ∞)` of the rescaled canonical monomial integrand
`w ↦ exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (λ - 1)` for `λ > 0` and `x > 0`. -/
theorem integrableOn_exp_mul_sub_pow_mul_rpow {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (s : ℕ) :
    IntegrableOn (fun w ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1))
      (Ioi 0) :=
  integrableOn_exp_mul_homog_mul_rpow hx a (fun _ _ _ ↦ mul_pow _ _ s)
    (integrableOn_bleisteinF_integrand hlam s (a * Real.sqrt x))

/-- Change-of-scale identity expressing the canonical monomial integral on `(0, ∞)` in terms of
`bleisteinF` for `x > 0` (behind DLMF 2.3.32–2.3.33). -/
theorem integral_exp_mul_sub_pow_mul_rpow_eq_bleisteinF {x : ℝ}
    (lam : ℝ) (hx : 0 < x) (a : ℝ) (s : ℕ) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) =
      x ^ (-lam / 2) * (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) := by
  rw [integral_exp_mul_homog_mul_rpow (h := (· ^ s)) lam hx a (fun _ _ _ ↦ mul_pow _ _ s),
    ← bleisteinF_def, (by ring : -((s : ℝ) + lam) / 2 = -lam / 2 + -(s : ℝ) / 2),
    Real.rpow_add hx]
  ring

/-- Integrability on `(0, ∞)` of the rescaled canonical comparison integrand
`w ↦ exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (λ - 1)` for `λ > 0` and `x > 0`. -/
theorem integrableOn_exp_mul_abs_sub_pow_mul_rpow {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (N : ℕ) :
    IntegrableOn (fun w ↦ Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1))
      (Ioi 0) :=
  integrableOn_exp_mul_homog_mul_rpow (h := fun u ↦ |u| ^ N) hx a
    (fun c hc u ↦ by rw [abs_mul, abs_of_pos hc, mul_pow])
    (integrableOn_bleisteinG_integrand hlam N (a * Real.sqrt x))

/-- Change-of-scale identity expressing the canonical absolute-power comparison integral on `(0, ∞)`
in terms of `bleisteinG` for `x > 0`. -/
theorem integral_exp_mul_abs_sub_pow_mul_rpow_eq_bleisteinG {x : ℝ}
    (lam : ℝ) (hx : 0 < x) (a : ℝ) (N : ℕ) :
    (∫ w in Ioi (0 : ℝ), Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) =
      x ^ (-((N : ℝ) + lam) / 2) * bleisteinG lam N (a * Real.sqrt x) := by
  rw [integral_exp_mul_homog_mul_rpow (h := fun u ↦ |u| ^ N) lam hx a
    (fun c hc u ↦ by rw [abs_mul, abs_of_pos hc, mul_pow]), ← bleisteinG_def]

/-- Pointwise distribution of Bleistein's canonical kernel across a truncated polynomial sum. -/
private theorem bleistein_poly_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lam x a w : ℝ) (N : ℕ) (phi : ℕ → E) :
    (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        ∑ s ∈ Finset.range N, (w - a) ^ s • phi s =
      ∑ s ∈ Finset.range N,
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * (w - a) ^ s * w ^ (lam - 1)) • phi s := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [smul_smul]
  congr 1
  ring

/-- Integrability of the truncated Taylor polynomial against Bleistein's canonical kernel. -/
private theorem integrableOn_bleistein_poly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (N : ℕ) (phi : ℕ → E) :
    IntegrableOn (fun w ↦ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
      ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) (Ioi 0) :=
  IntegrableOn.congr_fun
    (integrable_finsetSum (Finset.range N) fun s _ ↦
      (integrableOn_exp_mul_sub_pow_mul_rpow hlam hx a s).smul_const (phi s))
    (fun w _ ↦ (bleistein_poly_smul_eq lam x a w N phi).symm) measurableSet_Ioi

/-- Integral on `(0, ∞)` of a truncated Taylor polynomial around `w = a` against Bleistein's
canonical kernel, expressed in terms of `bleisteinF` (the polynomial part of DLMF 2.3.32). -/
theorem integral_exp_mul_rpow_smul_sum_eq_bleisteinF {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) (a : ℝ) (N : ℕ) (phi : ℕ → E) :
    (∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) =
      x ^ (-lam / 2) • ∑ s ∈ Finset.range N,
        (bleisteinF lam s (a * Real.sqrt x) * x ^ (-(s : ℝ) / 2)) • phi s := by
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun w _ ↦ bleistein_poly_smul_eq lam x a w N phi),
    integral_finsetSum (Finset.range N) fun s _ ↦
      (integrableOn_exp_mul_sub_pow_mul_rpow hlam hx a s).smul_const (phi s),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [integral_smul_const, integral_exp_mul_sub_pow_mul_rpow_eq_bleisteinF lam hx a s, smul_smul]

/-- Almost-everywhere norm domination of Bleistein's weighted Taylor remainder on `(0, ∞)`. -/
private theorem ae_norm_bleistein_remainder_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam a C x : ℝ} {N : ℕ} {f : ℝ → E} {phi : ℕ → E}
    (hf : ∀ w > 0, ‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖ ≤ C * |w - a| ^ N) :
    ∀ᵐ w ∂volume.restrict (Ioi 0),
      ‖(Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
          (f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s)‖ ≤
        C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w (hw : 0 < w)
  have hpos : 0 ≤ Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hw _).le
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
  calc (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) *
        ‖f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s‖
      ≤ (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) * (C * |w - a| ^ N) :=
        mul_le_mul_of_nonneg_left (hf w hw) hpos
    _ = C * (Real.exp (-x * (w ^ 2 / 2 - a * w)) * |w - a| ^ N * w ^ (lam - 1)) := by ring

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
        (f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s)) (Ioi 0) :=
    Integrable.mono' ((integrableOn_exp_mul_abs_sub_pow_mul_rpow hlam hx a N).const_mul C)
      (hkern_meas.smul (hfm.sub hpoly_meas)) (ae_norm_bleistein_remainder_le hf)
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
  rw [← integral_exp_mul_rpow_smul_sum_eq_bleisteinF hlam hx a N phi,
    ← integral_sub hf_int hpoly_int]
  have hsub_congr : (∫ w in Ioi (0 : ℝ),
        (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) • f w -
          (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
            ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) =
      ∫ w in Ioi (0 : ℝ), (Real.exp (-x * (w ^ 2 / 2 - a * w)) * w ^ (lam - 1)) •
        (f w - ∑ s ∈ Finset.range N, (w - a) ^ s • phi s) :=
    setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ (smul_sub _ _ _).symm
  rw [hsub_congr]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hdom_int := (integrableOn_exp_mul_abs_sub_pow_mul_rpow hlam hx a N).const_mul C
  refine (integral_mono_ae ((hf_int.sub hpoly_int).congr_fun
      (fun _ _ ↦ (smul_sub _ _ _).symm) measurableSet_Ioi).norm hdom_int
      (ae_norm_bleistein_remainder_le hf)).trans_eq ?_
  rw [integral_const_mul, integral_exp_mul_abs_sub_pow_mul_rpow_eq_bleisteinG lam hx a N, mul_assoc]

/-! ### Uniform expansion of Laplace-type integrals (DLMF 2.3.32) -/

/-- Shared change-of-variables setup deriving openness and positivity of `s`, phase lower bounds,
positivity and injectivity of `bleisteinCoord`, positive derivative, and continuity of
`bleisteinAmplitude` on `(0, ∞)`. -/
private theorem bleistein_changeOfVariables_setup {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam : ℝ} {g : ℝ → ℝ} {q : ℝ → E} {U s : Set ℝ} {α : ℝ}
    (hU : IsOpen U) (hsU : s ⊆ U)
    (hα : α ∈ U) (h0 : 0 ∈ U) (hg : ContDiffOn ℝ 1 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ s, t ≠ α → deriv g t ≠ 0)
    (hq : ContinuousOn q s) (himg : bleisteinCoord g α '' s = Ioi 0) :
    IsOpen s ∧ s ⊆ Ioi 0 ∧ g α ≤ g 0 ∧ (∀ t ∈ s, g α ≤ g t) ∧
      (∀ t ∈ s, 0 < bleisteinCoord g α t) ∧ InjOn (bleisteinCoord g α) s ∧
      (∀ t ∈ s, 0 < deriv (bleisteinCoord g α) t) ∧
      ContinuousOn (bleisteinAmplitude lam g q s α) (Ioi 0) := by
  have hw_mono := strictMonoOn_bleisteinCoord hα hanti hmono
  have hs_eq : s = U ∩ Ioi 0 := by
    ext t
    constructor
    · intro ht
      have hwt : 0 < bleisteinCoord g α t := by
        have hmem : bleisteinCoord g α t ∈ bleisteinCoord g α '' s := ⟨t, ht, rfl⟩
        rwa [himg] at hmem
      rw [← bleisteinCoord_zero g α] at hwt
      exact ⟨hsU ht, (hw_mono.lt_iff_lt h0 (hsU ht)).mp hwt⟩
    · rintro ⟨htU, ht0⟩
      have hwt : bleisteinCoord g α t ∈ bleisteinCoord g α '' s := by
        rw [himg, mem_Ioi, ← bleisteinCoord_zero g α]
        exact hw_mono h0 htU ht0
      rcases hwt with ⟨t', ht', heq⟩
      exact hw_mono.injOn (hsU ht') htU heq ▸ ht'
  have hs : IsOpen s := hs_eq ▸ hU.inter isOpen_Ioi
  have hs0 : s ⊆ Ioi 0 := hs_eq ▸ inter_subset_right
  have hw_c1 := contDiffOn_bleisteinCoord hU hα hg
    (fun _ ht hne ↦ lt_of_strictAntiOn_strictMonoOn hα hanti hmono ht hne) hd2
  have hinj : InjOn (bleisteinCoord g α) s := hw_mono.injOn.mono hsU
  have hw_pos : ∀ t ∈ s, 0 < bleisteinCoord g α t := fun t ht ↦
    bleisteinCoord_pos hα h0 hanti hmono (hsU ht) (hs0 ht)
  have hdpos : ∀ t ∈ s, 0 < deriv (bleisteinCoord g α) t := fun t ht ↦
    deriv_bleisteinCoord_pos hU hα (hg.differentiableOn one_ne_zero) hanti hmono hd2 (hsU ht)
      (hreg t ht)
  have hf_cont : ContinuousOn (bleisteinAmplitude lam g q s α) (Ioi 0) :=
    himg ▸ continuousOn_bleisteinAmplitude hs hs0 (hw_c1.mono hsU) hinj hw_pos
      (fun t ht ↦ (hdpos t ht).ne') hq
  have hmin : ∀ t ∈ U, g α ≤ g t :=
    fun _ ht ↦ le_of_antitoneOn_monotoneOn hα hanti.antitoneOn hmono.monotoneOn ht
  exact ⟨hs, hs0, hmin 0 h0, fun t ht ↦ hmin t (hsU ht), hw_pos, hinj, hdpos, hf_cont⟩

/-- Convergence (Bochner integrability, hence absolute convergence) of the original integral
`I(α, x) = ∫ t in s, (exp (-x * g t) * t ^ (λ - 1)) • q t` under the hypotheses of Bleistein's
method when `bleisteinCoord g α '' s = (0, ∞)` and the transformed amplitude satisfies a Taylor
remainder bound. -/
theorem integrableOn_bleistein_of_taylor_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam C x : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U s : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hsU : s ⊆ U)
    (hα : α ∈ U) (h0 : 0 ∈ U) (hg : ContDiffOn ℝ 1 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ s, t ≠ α → deriv g t ≠ 0)
    (hq : ContinuousOn q s) (himg : bleisteinCoord g α '' s = Ioi 0)
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q s α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    IntegrableOn (fun t ↦ (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) s := by
  obtain ⟨hs, hs0, h0_min, hmin, hw_pos, hinj, hdpos, hf_cont⟩ :=
    bleistein_changeOfVariables_setup hU hsU hα h0 hg hanti hmono hd2 hreg hq himg
  rw [← integrableOn_bleistein_iff hs.measurableSet hs0 h0_min hmin hw_pos hinj hdpos, himg]
  exact integrableOn_bleistein_model_of_bound hlam hx
    (hf_cont.aestronglyMeasurable measurableSet_Ioi) hf

/-- **Uniform Bleistein expansion with explicit remainder** (DLMF 2.3.32, `κ = ∞`), on a domain
`s ⊆ U` mapped onto `(0, ∞)` by `bleisteinCoord g α`. -/
theorem norm_exp_smul_integral_bleistein_sub_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam C x : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U s : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hsU : s ⊆ U)
    (hα : α ∈ U) (h0 : 0 ∈ U) (hg : ContDiffOn ℝ 1 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd2 : 0 < deriv (deriv g) α)
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
  obtain ⟨hs, hs0, h0_min, hmin, hw_pos, hinj, hdpos, hf_cont⟩ :=
    bleistein_changeOfVariables_setup hU hsU hα h0 hg hanti hmono hd2 hreg hq himg
  rw [exp_smul_integral_bleistein_eq hs.measurableSet hs0 h0_min hmin hw_pos hinj hdpos, himg]
  exact norm_bleistein_remainder_le hlam hx (hf_cont.aestronglyMeasurable measurableSet_Ioi) hf

/-- Convergence (Bochner integrability) of the Bleistein integral on `(0, k)` when
`g(t) → ∞` as `t → k⁻`. -/
theorem integrableOn_bleistein_Ioo_of_taylor_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam C x k : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U : Set ℝ} {α : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hI : Ico 0 k ⊆ U) (hα : α ∈ U) (hg : ContDiffOn ℝ 1 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ Ioo 0 k, t ≠ α → deriv g t ≠ 0)
    (htop : Tendsto g (𝓝[<] k) atTop) (hq : ContinuousOn q (Ioo 0 k))
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q (Ioo 0 k) α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    IntegrableOn (fun t ↦ (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) (Ioo 0 k) :=
  integrableOn_bleistein_of_taylor_bound hlam hx hU
    (Ioo_subset_Ico_self.trans hI) hα (hI (left_mem_Ico.mpr hk))
    hg hanti hmono hd2 hreg hq
    (image_bleisteinCoord_Ioo_of_tendsto_atTop hk hα hI (hg.continuousOn.mono hI) hanti hmono htop)
    hf

/-- **Uniform Bleistein expansion on `(0, k)`** (DLMF 2.3.32) when `g(t) → ∞` as `t → k⁻`. -/
theorem norm_exp_smul_integral_bleistein_Ioo_sub_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam C x k : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U : Set ℝ} {α : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hI : Ico 0 k ⊆ U) (hα : α ∈ U) (hg : ContDiffOn ℝ 1 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd2 : 0 < deriv (deriv g) α)
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
  norm_exp_smul_integral_bleistein_sub_le hlam hx hU
    (Ioo_subset_Ico_self.trans hI) hα (hI (left_mem_Ico.mpr hk))
    hg hanti hmono hd2 hreg hq
    (image_bleisteinCoord_Ioo_of_tendsto_atTop hk hα hI (hg.continuousOn.mono hI) hanti hmono htop)
    hf

/-- Convergence (Bochner integrability) of the Bleistein integral on `(0, ∞)` when
`g(t) → ∞` as `t → ∞`. -/
theorem integrableOn_bleistein_Ioi_of_taylor_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam C x : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hI : Ici 0 ⊆ U) (hα : α ∈ U) (hg : ContDiffOn ℝ 1 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd2 : 0 < deriv (deriv g) α)
    (hreg : ∀ t ∈ Ioi 0, t ≠ α → deriv g t ≠ 0)
    (htop : Tendsto g atTop atTop) (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ w > 0, ‖bleisteinAmplitude lam g q (Ioi 0) α w -
        ∑ n ∈ Finset.range N, (w - bleisteinCenter g α) ^ n • phi n‖ ≤
      C * |w - bleisteinCenter g α| ^ N) :
    IntegrableOn (fun t ↦ (Real.exp (-x * g t) * t ^ (lam - 1)) • q t) (Ioi 0) :=
  integrableOn_bleistein_of_taylor_bound hlam hx hU
    (Ioi_subset_Ici_self.trans hI) hα (hI self_mem_Ici)
    hg hanti hmono hd2 hreg hq
    (image_bleisteinCoord_Ioi_of_tendsto_atTop hα hI (hg.continuousOn.mono hI) hanti hmono htop) hf

/-- **Uniform Bleistein expansion on `(0, ∞)`** (DLMF 2.3.32) when `g(t) → ∞` as `t → ∞`. -/
theorem norm_exp_smul_integral_bleistein_Ioi_sub_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {lam C x : ℝ} {N : ℕ} {g : ℝ → ℝ} {q : ℝ → E} {phi : ℕ → E} {U : Set ℝ} {α : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hU : IsOpen U) (hI : Ici 0 ⊆ U) (hα : α ∈ U) (hg : ContDiffOn ℝ 1 g U)
    (hanti : StrictAntiOn g (U ∩ Iic α)) (hmono : StrictMonoOn g (U ∩ Ici α))
    (hd2 : 0 < deriv (deriv g) α)
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
  norm_exp_smul_integral_bleistein_sub_le hlam hx hU
    (Ioi_subset_Ici_self.trans hI) hα (hI self_mem_Ici)
    hg hanti hmono hd2 hreg hq
    (image_bleisteinCoord_Ioi_of_tendsto_atTop hα hI (hg.continuousOn.mono hI) hanti hmono htop) hf

end TauCeti
