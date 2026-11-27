/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.NumberTheory.Padics.Exp.Disc

/-!
# Exponential polynomials `Q (X) exp (ψ X)` over a normed field over `ℚ_p`

Let `L` be a normed field over `ℚ_[p]` and `ρ = p ^ (-1 / (p - 1))` the radius of the `p`-adic
exponential. For a polynomial `Q` over `L` and `ψ ∈ L`, the exponential polynomial
`Q (X) exp (ψ X)` is the formal power series `Q * rescale ψ (exp L)`. This file bounds its
coefficients and evaluates it.

* If the coefficients of `Q` satisfy `‖Q_j‖ r ^ j ≤ M` and `‖ψ‖ r ≤ ρ`, then the coefficients `c_k`
  of `Q (X) exp (ψ X)` satisfy `‖c_k‖ r ^ k ≤ M`. The reason is that the coefficients
  `ψ ^ k / k!` of `exp (ψ X)` satisfy `‖ψ ^ k / k!‖ r ^ k ≤ 1` there, by Legendre's bound for
  `‖k!‖`, and that the norm is ultrametric. The disc `‖ψ‖ r ≤ ρ` is closed: at its boundary the
  weighted coefficients of `exp (ψ X)` stay bounded by `1` although they no longer tend to `0`.
* If `L` is complete and `‖ψ x‖ < ρ`, the series `∑ c_k x ^ k` converges to
  `Q (x) exp (ψ x)`, with Mathlib's `NormedSpace.exp`.

Together with `PowerSeries.iterate_derivative_coe_mul_rescale_exp`, which computes the
derivatives of `Q (X) exp (ψ X)` as exponential polynomials with the same frequency `ψ`, these are
the bounds and values of the series with which Baker's method over `ℂ_p` works on a disc of
radius `r > 1`.

## Main results

* `PowerSeries.norm_coeff_coe_mul_rescale_exp_mul_pow_le`: the coefficient bound for
  `Q (X) exp (ψ X)`.
* `PowerSeries.hasSum_coeff_coe_mul_rescale_exp`: the value `Q (x) exp (ψ x)` for `‖ψ x‖ < ρ`.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 2.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58,
  Chapter IV, §1.
* M. Karatarakis, `Mathlib/NumberTheory/Transcendental/Baker/Padic/ExpSeries.lean` on the
  `baker-padic` branch of `mkaratarakis/mathlib4` (commit `65cdef5722`), which formalizes these
  series as `expPolySeq`.
-/

public section

open Finset
open scoped Polynomial

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime] {L : Type*} [NormedField L] [Algebra ℚ L]
  [NormedAlgebra ℚ_[p] L]

/-- **The coefficients of `Q (X) exp (ψ X)`.** If `‖Q_j‖ r ^ j ≤ M` for every `j` and
`‖ψ‖ r ≤ p ^ (-1 / (p - 1))`, then every coefficient `c_k` of `Q (X) exp (ψ X)` satisfies
`‖c_k‖ r ^ k ≤ M`. -/
theorem norm_coeff_coe_mul_rescale_exp_mul_pow_le {Q : L[X]} {ψ : L} {r M : ℝ} (hr : 0 ≤ r)
    (hQ : ∀ j, ‖Q.coeff j‖ * r ^ j ≤ M) (hψ : ‖ψ‖ * r ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) (k : ℕ) :
    ‖coeff k ((Q : L⟦X⟧) * rescale ψ (exp L))‖ * r ^ k ≤ M := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  have hQ' : (Q : L⟦X⟧).HasGaussNorm norm r :=
    ⟨M, Set.forall_mem_range.2 fun j ↦ by simpa [Polynomial.coeff_coe] using hQ j⟩
  have hE := hasGaussNorm_rescale_exp (p := p) hr hψ
  -- the Gauss norm at `r` is submultiplicative, and that of `exp (ψ X)` is `1`
  calc _ ≤ ((Q : L⟦X⟧) * rescale ψ (exp L)).gaussNorm norm r :=
        le_gaussNorm norm r _ (TauCeti.PowerSeries.hasGaussNorm_mul hr hQ' hE) k
    _ ≤ (Q : L⟦X⟧).gaussNorm norm r * (rescale ψ (exp L)).gaussNorm norm r :=
        TauCeti.PowerSeries.gaussNorm_mul_le hr hQ' hE
    _ ≤ M := by
      rw [gaussNorm_rescale_exp hr hψ, mul_one, gaussNorm_eq]
      exact ciSup_le fun j ↦ by simpa [Polynomial.coeff_coe] using hQ j

variable [CompleteSpace L]

/-- For `‖ψ x‖ < p ^ (-1 / (p - 1))`, the series `exp (ψ X)` converges at `x` to
`NormedSpace.exp (ψ x)`. -/
private theorem hasSum_coeff_rescale_exp_mul_pow {ψ x : L}
    (hψx : ‖ψ * x‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    HasSum (fun k ↦ coeff k (rescale ψ (exp L)) * x ^ k) (NormedSpace.exp (ψ * x)) := by
  have hρ : TauCeti.amiceRadius p 0 = (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
    simp [TauCeti.amiceRadius_def]
  convert TauCeti.expSeries_hasSum_exp_of_norm_lt (hρ ▸ hψx) using 1
  funext k
  simp only [coeff_rescale, coeff_exp, one_div, map_inv₀, map_natCast, Algebra.smul_def, mul_pow]
  ring

/-- The series `X ^ i exp (ψ X)` converges at `x` to `x ^ i exp (ψ x)`. -/
private theorem hasSum_coeff_X_pow_mul_rescale_exp_mul_pow (i : ℕ) {ψ x : L}
    (hψx : ‖ψ * x‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    HasSum (fun k ↦ coeff k (X ^ i * rescale ψ (exp L)) * x ^ k)
      (x ^ i * NormedSpace.exp (ψ * x)) := by
  rw [← hasSum_nat_add_iff' i]
  convert (hasSum_coeff_rescale_exp_mul_pow hψx).mul_left (x ^ i) using 1
  · funext k
    simp only [coeff_X_pow_mul', Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]
    ring
  · rw [sum_eq_zero fun j hj ↦ by simp [coeff_X_pow_mul', (mem_range.1 hj).not_ge], sub_zero]

/-- **The value of `Q (X) exp (ψ X)`.** Over a complete normed field over `ℚ_[p]`, if
`‖ψ x‖ < p ^ (-1 / (p - 1))`, the coefficients `c_k` of `Q (X) exp (ψ X)` satisfy
`∑ c_k x ^ k = Q (x) exp (ψ x)`. -/
theorem hasSum_coeff_coe_mul_rescale_exp (Q : L[X]) {ψ x : L}
    (hψx : ‖ψ * x‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    HasSum (fun k ↦ coeff k ((Q : L⟦X⟧) * rescale ψ (exp L)) * x ^ k)
      (Q.eval x * NormedSpace.exp (ψ * x)) := by
  have hQ : (Q : L⟦X⟧) = ∑ i ∈ range (Q.natDegree + 1), C (Q.coeff i) * X ^ i := by
    conv_lhs => rw [Q.as_sum_range_C_mul_X_pow]
    simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [Polynomial.coeToPowerSeries.ringHom_apply]
  rw [hQ, Polynomial.eval_eq_sum_range, sum_mul]
  convert hasSum_sum (s := range (Q.natDegree + 1)) fun i _ ↦
    (hasSum_coeff_X_pow_mul_rescale_exp_mul_pow i hψx).mul_left (Q.coeff i) using 1
  · funext k
    simp only [sum_mul, map_sum, mul_assoc, coeff_C_mul]
  · simp only [sum_mul, mul_assoc]

end PowerSeries
