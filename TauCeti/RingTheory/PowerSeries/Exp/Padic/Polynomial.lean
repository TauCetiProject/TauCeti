/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.RingTheory.PowerSeries.Exp.Eval
import TauCeti.RingTheory.PowerSeries.Restricted

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

/-- **The value of `Q (X) exp (ψ X)`.** Over a complete normed field over `ℚ_[p]`, if
`‖ψ x‖ < p ^ (-1 / (p - 1))`, the coefficients `c_k` of `Q (X) exp (ψ X)` satisfy
`∑ c_k x ^ k = Q (x) exp (ψ x)`. -/
theorem hasSum_coeff_coe_mul_rescale_exp (Q : L[X]) {ψ x : L}
    (hψx : ‖ψ * x‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    HasSum (fun k ↦ coeff k ((Q : L⟦X⟧) * rescale ψ (exp L)) * x ^ k)
      (Q.eval x * NormedSpace.exp (ψ * x)) := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  -- both factors are restricted at `‖x‖`, and evaluation there is multiplicative
  have hE := isRestricted_rescale_exp (p := p) (norm_nonneg x) (by rwa [← norm_mul])
  have hQ := TauCeti.PowerSeries.isRestricted_polynomial (c := ‖x‖) Q
  have hQE : ((Q : L⟦X⟧) * rescale ψ (exp L)).IsRestricted ‖x‖ := hQ.mul hE
  have h := hQE.hasSum_evalAt le_rfl
  rw [IsRestricted.evalAt_mul hQ hE le_rfl, evalAt_coe, evalAt_rescale, evalAt_exp] at h
  simpa only [smul_eq_mul, Polynomial.coe_aeval_eq_eval] using h

end PowerSeries
