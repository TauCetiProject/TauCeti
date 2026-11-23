/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Complex
import TauCeti.NumberTheory.LSeries.Continuity
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.Twist

/-!
# The Dirichlet series of the divisor power sum `σ_ν`

For complex `ν`, the Dirichlet series of `σ_ν(n) = ∑_{d ∣ n} d ^ ν` is `ζ(s) ζ(s - ν)`, and it
converges absolutely exactly on `Re s > max(1, 1 + Re ν)`.

## Main results

* `TauCeti.LSeries.LSeries_cpow`: the series of `n ↦ n ^ ν` is `ζ(s - ν)` on `Re s > 1 + Re ν`.
* `TauCeti.LSeries.LSeries_sigmaC`: `L(σ_ν, s) = ζ(s) ζ(s - ν)` for `Re s > max(1, 1 + Re ν)`.
* `TauCeti.LSeries.LSeriesSummable_sigmaC_iff` and `TauCeti.LSeries.abscissaOfAbsConv_sigmaC`:
  the series of `σ_ν` converges absolutely exactly on `Re s > max(1, 1 + Re ν)`.

The upper bound on the abscissa comes from `σ_ν = ζ * (n ↦ n ^ ν)`. For the lower bound, the
reflection `σ_ν(n) = σ_{-ν}(n) n ^ ν` shifts the series by `ν` and reduces to `Re ν ≤ 0`, where
the abscissa is `1`. If the series converged absolutely at `s = 1`, it would be continuous there
along the reals, so `(x - 1) ζ(x) ζ(x - ν)` would tend to `0` as `x → 1⁺`; but
`(x - 1) ζ(x) → 1` and `ζ(x - ν) → ζ(1 - ν) ≠ 0` for `ν ≠ 0`, while for `ν = 0` the square
`((x - 1) ζ(x)) ^ 2` tends to `1`.

## References

* Alex Kontorovich, Terence Tao and contributors,
  [Prime Number Theorem and More][PNTDivisorPowerSum], `IwaniecKowalskiCh1.lean`,
  `ArithmeticFunction.LSeries_powR_eq`, `ArithmeticFunction.abscissa_powR_le` and
  `ArithmeticFunction.LSeries_sigma_eq_riemannZeta_mul`, for the series and its upper abscissa
  bound.

[PNTDivisorPowerSum]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a90b1493fe9af9011c800856033c1ba7ac5fcc84/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
-/

public section

open LSeries Filter Topology ArithmeticFunction TauCeti.ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction.zeta

namespace TauCeti.LSeries

/-- Away from `0`, `cpow ν` is the constant series `1` twisted by `n ^ ν`. -/
private theorem cpow_eq_one_mul_natCast_cpow (ν : ℂ) {n : ℕ} (hn : n ≠ 0) :
    cpow ν n = (1 : ℕ → ℂ) n * (n : ℂ) ^ ν := by
  simp [hn]

/-- The series of `n ↦ n ^ ν` converges absolutely exactly on `Re s > 1 + Re ν`. -/
theorem LSeriesSummable_cpow_iff {ν s : ℂ} : LSeriesSummable ↗(cpow ν) s ↔ 1 + ν.re < s.re := by
  rw [LSeriesSummable_congr s (cpow_eq_one_mul_natCast_cpow ν),
    LSeriesSummable_mul_natCast_cpow_iff, LSeriesSummable_one_iff, Complex.sub_re,
    lt_sub_iff_add_lt]

/-- The series of `n ↦ n ^ ν` is `ζ(s - ν)` on `Re s > 1 + Re ν`. -/
theorem LSeries_cpow {ν s : ℂ} (hs : 1 + ν.re < s.re) :
    LSeries ↗(cpow ν) s = riemannZeta (s - ν) := by
  rw [LSeries_congr (cpow_eq_one_mul_natCast_cpow ν) s, LSeries_mul_natCast_cpow,
    LSeries_one_eq_riemannZeta (by rwa [Complex.sub_re, lt_sub_iff_add_lt])]

/-- The abscissa of absolute convergence of the series of `n ↦ n ^ ν` is `1 + Re ν`. -/
theorem abscissaOfAbsConv_cpow (ν : ℂ) : abscissaOfAbsConv ↗(cpow ν) = (1 + ν.re : ℝ) :=
  abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦ LSeriesSummable_cpow_iff

/-- `∑ σ_ν(n) n ^ {-s} = ζ(s) ζ(s - ν)` for `Re s > max(1, 1 + Re ν)`. -/
theorem LSeries_sigmaC {ν s : ℂ} (hs : max 1 (1 + ν.re) < s.re) :
    LSeries ↗(sigmaC ν) s = riemannZeta s * riemannZeta (s - ν) := by
  rw [max_lt_iff] at hs
  have hζ : LSeriesSummable (fun n ↦ (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s := by
    simpa only [natCoe_apply] using LSeriesSummable_zeta_iff.mpr hs.1
  rw [sigmaC_eq_zeta_mul_cpow, LSeries_mul' hζ
    (LSeriesSummable_cpow_iff.mpr hs.2), LSeries_cpow hs.2]
  simp only [natCoe_apply]
  rw [LSeries_zeta_eq_riemannZeta hs.1]

/-- For `Re ν ≤ 0`, the series of `σ_ν` does not converge absolutely at `s = 1`. -/
private theorem not_LSeriesSummable_sigmaC_one {ν : ℂ} (hν : ν.re ≤ 0) :
    ¬ LSeriesSummable ↗(sigmaC ν) 1 := by
  intro h
  have hsub : Tendsto (fun x : ℝ ↦ (x : ℂ) - 1) (𝓝[>] 1) (𝓝 0) :=
    ((Complex.continuous_ofReal.sub continuous_const).tendsto' 1 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  -- The absolutely convergent series is continuous at `1` along `x ≥ 1`, so
  -- `(x - 1) L(σ_ν, x) → 0` as `x → 1⁺`.
  have hL : Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * LSeries ↗(sigmaC ν) x) (𝓝[>] 1) (𝓝 0) := by
    simpa only [zero_mul] using hsub.mul <|
      (LSeriesSummable.tendsto_LSeries_nhdsGE (σ := 1) (by rwa [Complex.ofReal_one])).mono_left
        (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  -- On `x > 1`, `L(σ_ν, x) = ζ(x) ζ(x - ν)`.
  have heq : (fun x : ℝ ↦ ((x : ℂ) - 1) * riemannZeta x * riemannZeta (x - ν)) =ᶠ[𝓝[>] 1]
      fun x ↦ ((x : ℂ) - 1) * LSeries ↗(sigmaC ν) x := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    rw [LSeries_sigmaC (by simp [hx, hν]), mul_assoc]
  have hres := TauCeti.tendsto_sub_one_mul_riemannZeta_nhdsGT
  rcases eq_or_ne ν 0 with rfl | hν0
  · -- For `ν = 0`, `(x - 1) ((x - 1) L(σ_0, x)) = ((x - 1) ζ(x)) ^ 2` tends to both `0` and `1`.
    have h0 : Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * (((x : ℂ) - 1) * LSeries ↗(sigmaC 0) x))
        (𝓝[>] 1) (𝓝 0) := by
      simpa only [mul_zero] using hsub.mul hL
    have h1 : Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * (((x : ℂ) - 1) * LSeries ↗(sigmaC 0) x))
        (𝓝[>] 1) (𝓝 1) := by
      have hsq : Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * riemannZeta x * (((x : ℂ) - 1) *
          riemannZeta x)) (𝓝[>] 1) (𝓝 1) := by
        simpa only [mul_one] using hres.mul hres
      refine hsq.congr' ?_
      filter_upwards [heq] with x hx
      rw [← hx, sub_zero]
      ring
    exact one_ne_zero (tendsto_nhds_unique h1 h0)
  · -- For `ν ≠ 0`, `ζ(x - ν) → ζ(1 - ν)`, which is nonzero.
    have hcont : Tendsto (fun x : ℝ ↦ riemannZeta (x - ν)) (𝓝[>] 1) (𝓝 (riemannZeta (1 - ν))) :=
      ((differentiableAt_riemannZeta (by simpa using hν0)).continuousAt.tendsto.comp
        (Continuous.tendsto' (f := fun x : ℝ ↦ (x : ℂ) - ν) (by fun_prop) 1 (1 - ν) (by simp)))
        |>.mono_left nhdsWithin_le_nhds
    have h1 := (by simpa only [one_mul] using hres.mul hcont :
      Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * riemannZeta x * riemannZeta (x - ν)) (𝓝[>] 1)
        (𝓝 (riemannZeta (1 - ν)))).congr' heq
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using hν) (tendsto_nhds_unique h1 hL)

/-- The series of `σ_ν` does not converge absolutely at the real point `max(1, 1 + Re ν)`. -/
private theorem not_LSeriesSummable_sigmaC_max (ν : ℂ) :
    ¬ LSeriesSummable ↗(sigmaC ν) (max 1 (1 + ν.re) : ℝ) := by
  rcases le_or_gt ν.re 0 with hν | hν
  · rw [max_eq_left (by linarith)]
    exact_mod_cast not_LSeriesSummable_sigmaC_one hν
  · -- The reflection `σ_ν(n) = σ_{-ν}(n) n ^ ν` shifts the series by `ν`.
    intro h
    rw [LSeriesSummable_congr _ (g := fun n ↦ sigmaC (-ν) n * (n : ℂ) ^ ν) fun hn ↦ by
      rw [sigmaC_eq_cpow_pmul_sigmaC_neg ν, pmul_apply, cpow_apply ν hn, mul_comm],
      LSeriesSummable_mul_natCast_cpow_iff] at h
    exact not_LSeriesSummable_sigmaC_one (by simpa using hν.le)
      (h.of_re_le_re (by simp [max_eq_right (by linarith : 1 ≤ 1 + ν.re)]))

/-- The series of `σ_ν` converges absolutely exactly on `Re s > max(1, 1 + Re ν)`. -/
theorem LSeriesSummable_sigmaC_iff {ν s : ℂ} :
    LSeriesSummable ↗(sigmaC ν) s ↔ max 1 (1 + ν.re) < s.re := by
  refine ⟨fun h ↦ not_le.mp fun hs ↦ not_LSeriesSummable_sigmaC_max ν
    (h.of_re_le_re (by simpa using hs)), fun hs ↦ ?_⟩
  rw [max_lt_iff] at hs
  rw [sigmaC_eq_zeta_mul_cpow]
  have hζ : LSeriesSummable (fun n ↦ (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s := by
    simpa only [natCoe_apply] using LSeriesSummable_zeta_iff.mpr hs.1
  exact LSeriesSummable_mul hζ (LSeriesSummable_cpow_iff.mpr hs.2)

/-- The abscissa of absolute convergence of the series of `σ_ν` is `max(1, 1 + Re ν)`. -/
theorem abscissaOfAbsConv_sigmaC (ν : ℂ) :
    abscissaOfAbsConv ↗(sigmaC ν) = (max 1 (1 + ν.re) : ℝ) :=
  abscissaOfAbsConv_eq_of_LSeriesSummable_iff fun _ ↦ LSeriesSummable_sigmaC_iff

/-! ### Examples -/

/-- `σ_1(6) = 1 + 2 + 3 + 6 = 12`, in agreement with `ArithmeticFunction.sigma 1 6`. -/
example : sigmaC 1 6 = 12 ∧ sigmaC 1 6 = (ArithmeticFunction.sigma 1 6 : ℂ) := by
  have h : sigmaC 1 6 = (ArithmeticFunction.sigma 1 6 : ℂ) := by
    simpa using congrArg (· 6) (sigmaC_natCast 1)
  have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  refine ⟨h.trans ?_, h⟩
  rw [ArithmeticFunction.sigma_apply, hdiv]
  norm_num

/-- `σ_{-1}(6) = 1 + 1/2 + 1/3 + 1/6 = 2 = σ_1(6) / 6`. -/
example : sigmaC (-1) 6 = 2 := by
  have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [sigmaC_apply, hdiv]
  norm_num [Complex.cpow_neg_one]

/-- The abscissa is `max(1, 1 + Re ν)`, not `1 + Re ν`: for `ν = -2` it is `1`, since
`σ_{-2}(p) ≥ 1`. -/
example : abscissaOfAbsConv ↗(sigmaC 2) = (3 : ℝ) ∧ abscissaOfAbsConv ↗(sigmaC (-2)) = (1 : ℝ) := by
  rw [abscissaOfAbsConv_sigmaC, abscissaOfAbsConv_sigmaC]
  norm_num

/-- `∑ σ_1(n) n ^ {-3} = ζ(3) ζ(2)`. -/
example : LSeries ↗(sigmaC 1) 3 = riemannZeta 3 * riemannZeta 2 := by
  rw [LSeries_sigmaC (by norm_num)]
  norm_num

end TauCeti.LSeries
