/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Complex.AbelLimit
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.CircleOfConvergence
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Gauss's summation theorem

For `Re(c − a − b) > 0` the Gauss hypergeometric series converges absolutely at `z = 1`, and its
sum is given by Gauss's summation theorem (DLMF 15.4.20):

`₂F₁(a, b; c; 1) = Γ(c) Γ(c − a − b) / (Γ(c − a) Γ(c − b))`  for `c ∉ {0, −1, −2, …}`,

or, in regularized form, `𝐅(a, b; c; 1) = Γ(c − a − b) / (Γ(c − a) Γ(c − b))` for every `c`.

The value of `𝐅(a, b; c; z)` as `z → 1` inside the unit disk is
`Complex.tendsto_regularizedGaussHGFun_nhdsWithin_ball_one`, proved from Euler's integral. The
regularized series converges absolutely at `z = 1`
(`Complex.summable_norm_coeff_regularizedGaussHGFunSeries_mul_pow_of_re_pos`), so by Abel's limit
theorem its sum at `1` is the limit of its values as `z → 1⁻`, which is this limit.

## Main results

* `Complex.hasSum_coeff_regularizedGaussHGFunSeries_one`: the coefficients
  `(a)ₙ (b)ₙ / (n! Γ(c + n))` of `𝐅(a, b; c; ·)` sum to `Γ(c − a − b) / (Γ(c − a) Γ(c − b))`, for
  every `c`.
* `Complex.regularizedGaussHGFun_one`: DLMF 15.4.20 for `𝐅(a, b; c; 1)`, for every `c`.
* `Complex.ordinaryHypergeometric_one`: DLMF 15.4.20 for `₂F₁(a, b; c; 1)`.

## References

* NIST Digital Library of Mathematical Functions, 15.4.20, <https://dlmf.nist.gov/15.4.E20>.
* G. E. Andrews, R. Askey and R. Roy, *Special Functions*, Theorem 2.2.2.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/Hypergeometric/Boundary.lean` and `DLMF/Hypergeometric/EulerIntegral.lean`.
-/

public section

open Filter
open scoped Topology

namespace Complex

/-- **Gauss's summation theorem for the regularized coefficients** (DLMF 15.4.20). When
`Re(c − a − b) > 0`, the coefficients `(a)ₙ (b)ₙ / (n! Γ(c + n))` of `𝐅(a, b; c; ·)` sum to
`Γ(c − a − b) / (Γ(c − a) Γ(c − b))`, for every `c`, including the poles of `Γ`. -/
theorem hasSum_coeff_regularizedGaussHGFunSeries_one {a b c : ℂ} (h : 0 < (c - a - b).re) :
    HasSum (fun n => (regularizedGaussHGFunSeries a b c).coeff n)
      (Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b))) := by
  have hs : Summable fun n => (regularizedGaussHGFunSeries a b c).coeff n := by
    simpa using (summable_norm_coeff_regularizedGaussHGFunSeries_mul_pow_of_re_pos
      (z := 1) (by simp) h).of_norm
  -- Abel's limit theorem along the real segment `(-1, 1)`.
  have hA := tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
  simp_rw [← regularizedGaussHGFun_eq_tsum_coeff_mul_pow] at hA
  have hball : Tendsto ofReal (𝓝[<] 1) (𝓝[Metric.ball 0 1] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with x hx
      simpa [abs_lt] using hx
  have hlim := (tendsto_regularizedGaussHGFun_nhdsWithin_ball_one (a := a) (b := b) (c := c)
    (by simp only [sub_re, add_re] at h ⊢; linarith)).mono_left hball
  rw [← tendsto_nhds_unique hA hlim]
  exact hs.hasSum

/-- **Gauss's summation theorem, regularized form** (DLMF 15.4.20). When `Re(c − a − b) > 0`,
`𝐅(a, b; c; 1) = Γ(c − a − b) / (Γ(c − a) Γ(c − b))`, for every `c`. -/
theorem regularizedGaussHGFun_one {a b c : ℂ} (h : 0 < (c - a - b).re) :
    regularizedGaussHGFun a b c 1 = Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
  simpa [regularizedGaussHGFun_eq_tsum_coeff_mul_pow] using
    (hasSum_coeff_regularizedGaussHGFunSeries_one h).tsum_eq

/-- **Gauss's summation theorem** (DLMF 15.4.20). When `c ∉ {0, −1, −2, …}` and
`Re(c − a − b) > 0`, `₂F₁(a, b; c; 1) = Γ(c) Γ(c − a − b) / (Γ(c − a) Γ(c − b))`. -/
theorem ordinaryHypergeometric_one {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k)
    (h : 0 < (c - a - b).re) :
    ordinaryHypergeometric a b c (1 : ℂ) =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
  rw [mul_div_assoc, ← regularizedGaussHGFun_one h, ← ordinaryHypergeometric_div_Gamma_eq hc,
    mul_div_cancel₀ _ (Gamma_ne_zero hc)]

end Complex
