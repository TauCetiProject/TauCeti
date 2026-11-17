/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Complex
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# The Dirichlet series of the divisor power sum `σ_ν`

For complex `ν`, the Dirichlet series of `σ_ν(n) = ∑_{d ∣ n} d ^ ν` is `ζ(s) ζ(s - ν)`, and it
converges absolutely exactly on `Re s > max(1, 1 + Re ν)`.

## Main results

* `ArithmeticFunction.LSeries_cpow`: the series of `n ↦ n ^ ν` is `ζ(s - ν)` on `Re s > 1 + Re ν`.
* `ArithmeticFunction.LSeries_sigmaC`: `L(σ_ν, s) = ζ(s) ζ(s - ν)` for `Re s > max(1, 1 + Re ν)`.
* `ArithmeticFunction.abscissaOfAbsConv_sigmaC`: the abscissa of absolute convergence of `σ_ν` is
  `max(1, 1 + Re ν)`.

The upper bound on the abscissa comes from `σ_ν = ζ * (n ↦ n ^ ν)`. For the lower bound, the
reflection `σ_ν(n) n ^ {-s} = σ_{-ν}(n) n ^ {-(s - ν)}` reduces to `Re ν ≤ 0`, where the abscissa
is `1`. If the series converged absolutely at `s = 1`, then `(x - 1) ζ(x) ζ(x - ν)` would tend to
`0` as `x → 1⁺`; but `(x - 1) ζ(x) → 1` and `ζ(x - ν) → ζ(1 - ν) ≠ 0` for `ν ≠ 0`, while for
`ν = 0` the square `((x - 1) ζ(x)) ^ 2` already tends to `1`.

## References

* Alex Kontorovich, Terence Tao and contributors,
  [Prime Number Theorem and More][PNTDivisorPowerSum], `IwaniecKowalskiCh1.lean`,
  `ArithmeticFunction.LSeries_powR_eq`, `ArithmeticFunction.abscissa_powR_le` and
  `ArithmeticFunction.LSeries_sigma_eq_riemannZeta_mul`, for the series and its upper abscissa
  bound.

[PNTDivisorPowerSum]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/a90b1493fe9af9011c800856033c1ba7ac5fcc84/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
-/

public section

open LSeries Filter Topology
open scoped LSeries.notation ArithmeticFunction.zeta

namespace ArithmeticFunction

/-- The terms of the series of `n ↦ n ^ ν` at `s` are those of the series of `1` at `s - ν`. -/
theorem term_cpow (ν s : ℂ) (n : ℕ) : term ↗(cpow ν) s n = term 1 (s - ν) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hn, Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn)]

/-- The series of `n ↦ n ^ ν` converges absolutely exactly on `Re s > 1 + Re ν`. -/
theorem LSeriesSummable_cpow_iff {ν s : ℂ} : LSeriesSummable ↗(cpow ν) s ↔ 1 + ν.re < s.re := by
  rw [LSeriesSummable, funext (term_cpow ν s), ← LSeriesSummable, LSeriesSummable_one_iff,
    Complex.sub_re]
  constructor <;> intro <;> linarith

/-- The series of `n ↦ n ^ ν` is `ζ(s - ν)` on `Re s > 1 + Re ν`. -/
theorem LSeries_cpow {ν s : ℂ} (hs : 1 + ν.re < s.re) :
    LSeries ↗(cpow ν) s = riemannZeta (s - ν) := by
  rw [LSeries, funext (term_cpow ν s), ← LSeries,
    LSeries_one_eq_riemannZeta (by rw [Complex.sub_re]; linarith)]

/-- The series of `σ_ν` converges absolutely on `Re s > max(1, 1 + Re ν)`. -/
theorem LSeriesSummable_sigmaC {ν s : ℂ} (hs : max 1 (1 + ν.re) < s.re) :
    LSeriesSummable ↗(sigmaC ν) s := by
  rw [max_lt_iff] at hs
  rw [sigmaC_eq_zeta_mul_cpow]
  exact LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs.1) (LSeriesSummable_cpow_iff.mpr hs.2)

/-- `∑ σ_ν(n) n ^ {-s} = ζ(s) ζ(s - ν)` for `Re s > max(1, 1 + Re ν)`. -/
theorem LSeries_sigmaC {ν s : ℂ} (hs : max 1 (1 + ν.re) < s.re) :
    LSeries ↗(sigmaC ν) s = riemannZeta s * riemannZeta (s - ν) := by
  rw [max_lt_iff] at hs
  have hζ : LSeriesSummable ↗(ζ : ArithmeticFunction ℂ) s := LSeriesSummable_zeta_iff.mpr hs.1
  rw [sigmaC_eq_zeta_mul_cpow, LSeries_mul' hζ (LSeriesSummable_cpow_iff.mpr hs.2),
    LSeries_cpow hs.2]
  congr 1
  simpa using LSeries_zeta_eq_riemannZeta hs.1

/-- Reflection of the exponent in the terms of the series:
`σ_ν(n) n ^ {-s} = σ_{-ν}(n) n ^ {-(s - ν)}`. -/
theorem term_sigmaC_eq_term_sigmaC_neg (ν s : ℂ) (n : ℕ) :
    term ↗(sigmaC ν) s n = term ↗(sigmaC (-ν)) (s - ν) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [term_of_ne_zero hn, term_of_ne_zero hn, sigmaC_eq_cpow_mul_sigmaC_neg ν n,
    Complex.cpow_sub _ _ hn']
  rw [div_div_eq_mul_div, mul_comm]

/-- For `Re ν ≤ 0`, the series of `σ_ν` does not converge absolutely at `s = 1`. -/
private theorem not_LSeriesSummable_sigmaC_one {ν : ℂ} (hν : ν.re ≤ 0) :
    ¬ LSeriesSummable ↗(sigmaC ν) 1 := by
  intro h
  set C := ∑' n, ‖term ↗(sigmaC ν) 1 n‖
  have hnorm {x : ℝ} (hx : 1 < x) : ‖((x : ℂ) - 1)‖ = x - 1 := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  -- On `x > 1`, the product `ζ(x) ζ(x - ν)` is bounded by the absolute series at `1`.
  have hbound : ∀ᶠ x : ℝ in 𝓝[>] 1,
      ‖((x : ℂ) - 1) * riemannZeta x‖ * ‖riemannZeta (x - ν)‖ ≤ (x - 1) * C := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    have hre : (1 : ℂ).re ≤ (x : ℂ).re := by simpa using hx.le
    rw [← norm_mul, mul_assoc, norm_mul, ← LSeries_sigmaC (by simp [hx, hν]), hnorm hx]
    refine mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm (h.of_re_le_re hre).norm).trans
      (Summable.tsum_le_tsum (fun n ↦ norm_term_le_of_re_le_re _ hre n)
        (h.of_re_le_re hre).norm h.norm)) (by linarith)
  have hzero : Tendsto (fun x : ℝ ↦ (x - 1) * C) (𝓝[>] 1) (𝓝 0) :=
    (Continuous.tendsto' (f := fun x : ℝ ↦ (x - 1) * C) (by fun_prop) 1 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  have hres : Tendsto (fun x : ℝ ↦ ‖((x : ℂ) - 1) * riemannZeta x‖) (𝓝[>] 1) (𝓝 1) := by
    simpa using TauCeti.tendsto_sub_one_mul_riemannZeta_nhdsGT.norm
  rcases eq_or_ne ν 0 with rfl | hν0
  · -- For `ν = 0`, `((x - 1) ζ(x)) ^ 2 → 1` while it is at most `(x - 1) ^ 2 C`.
    have hzero' : Tendsto (fun x : ℝ ↦ (x - 1) * ((x - 1) * C)) (𝓝[>] 1) (𝓝 0) :=
      (Continuous.tendsto' (f := fun x : ℝ ↦ (x - 1) * ((x - 1) * C)) (by fun_prop) 1 0
        (by simp)).mono_left nhdsWithin_le_nhds
    have : (1 : ℝ) ≤ 0 := by
      refine le_of_tendsto_of_tendsto (mul_one (1 : ℝ) ▸ hres.mul hres) hzero' ?_
      filter_upwards [hbound, self_mem_nhdsWithin] with x hx (hx1 : 1 < x)
      calc ‖((x : ℂ) - 1) * riemannZeta x‖ * ‖((x : ℂ) - 1) * riemannZeta x‖
          = (x - 1) * (‖((x : ℂ) - 1) * riemannZeta x‖ * ‖riemannZeta (x - 0)‖) := by
            rw [sub_zero, norm_mul ((x : ℂ) - 1), hnorm hx1]; ring
        _ ≤ (x - 1) * ((x - 1) * C) := mul_le_mul_of_nonneg_left hx (by linarith)
    linarith
  · -- For `ν ≠ 0`, `ζ(x - ν) → ζ(1 - ν)`, which is nonzero.
    have hcont : Tendsto (fun x : ℝ ↦ riemannZeta (x - ν)) (𝓝[>] 1) (𝓝 (riemannZeta (1 - ν))) :=
      ((differentiableAt_riemannZeta (by simpa using hν0)).continuousAt.tendsto.comp
        (Continuous.tendsto' (f := fun x : ℝ ↦ (x : ℂ) - ν) (by fun_prop) 1 (1 - ν) (by simp)))
        |>.mono_left nhdsWithin_le_nhds
    have hle := le_of_tendsto_of_tendsto (one_mul ‖riemannZeta (1 - ν)‖ ▸ hres.mul hcont.norm)
      hzero hbound
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using hν) (norm_le_zero_iff.mp hle)

/-- The series of `σ_ν` does not converge absolutely at the real point `max(1, 1 + Re ν)`. -/
theorem not_LSeriesSummable_sigmaC (ν : ℂ) :
    ¬ LSeriesSummable ↗(sigmaC ν) (max 1 (1 + ν.re) : ℝ) := by
  rcases le_or_gt ν.re 0 with hν | hν
  · rw [max_eq_left (by linarith)]
    exact_mod_cast not_LSeriesSummable_sigmaC_one hν
  · intro h
    rw [LSeriesSummable, funext (term_sigmaC_eq_term_sigmaC_neg ν _), ← LSeriesSummable] at h
    exact not_LSeriesSummable_sigmaC_one (by simpa using hν.le)
      (h.of_re_le_re (by simp [max_eq_right (by linarith : 1 ≤ 1 + ν.re)]))

/-- The abscissa of absolute convergence of the series of `σ_ν` is `max(1, 1 + Re ν)`. -/
theorem abscissaOfAbsConv_sigmaC (ν : ℂ) :
    abscissaOfAbsConv ↗(sigmaC ν) = (max 1 (1 + ν.re) : ℝ) := by
  refine le_antisymm (abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
    LSeriesSummable_sigmaC (by simpa using hy)) (not_lt.mp fun h ↦ ?_)
  exact not_LSeriesSummable_sigmaC ν (LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using h))

/-! ### Examples -/

/-- `σ_1(6) = 1 + 2 + 3 + 6 = 12`, in agreement with `ArithmeticFunction.sigma 1 6`. -/
example : sigmaC 1 6 = 12 ∧ sigmaC 1 6 = (ArithmeticFunction.sigma 1 6 : ℂ) := by
  have h : sigmaC 1 6 = (ArithmeticFunction.sigma 1 6 : ℂ) := by
    simpa using congrArg (· 6) (sigmaC_natCast 1)
  refine ⟨h.trans ?_, h⟩
  rw [ArithmeticFunction.sigma_apply, show Nat.divisors 6 = {1, 2, 3, 6} by decide]
  norm_num

/-- `σ_{-1}(6) = 1 + 1/2 + 1/3 + 1/6 = 2 = σ_1(6) / 6`. -/
example : sigmaC (-1) 6 = 2 := by
  rw [sigmaC_apply, show Nat.divisors 6 = {1, 2, 3, 6} by decide]
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

end ArithmeticFunction
