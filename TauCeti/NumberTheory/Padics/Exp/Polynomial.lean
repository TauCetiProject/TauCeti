/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Polynomial.Ultra
import TauCeti.NumberTheory.Padics.Exp.Basic
import TauCeti.RingTheory.PowerSeries.EvalAt
import TauCeti.RingTheory.PowerSeries.Exp.Padic
import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Exponential polynomials over `p`-adic fields

In a normed field `L` over `ℚ_[p]` (retaining its rational algebra structure `[Algebra ℚ L]` used
by `PowerSeries.exp`), an exponential polynomial `Q(X) exp(ψ X)` is represented formally as the
power series `(Q : PowerSeries L) * PowerSeries.rescale ψ (PowerSeries.exp L)`. By the Gauss-norm
estimate `PowerSeries.gaussNorm_rescale_exp` of `TauCeti.RingTheory.PowerSeries.Exp.Padic`,
whenever `0 ≤ r` and `‖ψ‖ * r ≤ p ^ (-1 / (p - 1))`, the rescaled exponential `exp(ψ X)` has
Gauss norm `1` at radius `r`. By submultiplicativity of the ultrametric Gauss norm
(`TauCeti.PowerSeries.gaussNorm_mul_le`), multiplying `(Q : PowerSeries L)` by `exp(ψ X)` preserves
any `r`-weighted bound `∀ j, ‖Q.coeff j‖ * r ^ j ≤ M`
(`PowerSeries.norm_coeff_coe_mul_rescale_exp_mul_pow_le`).

When `L` is complete and `‖ψ * x‖ < p ^ (-1 / (p - 1))`, both `(Q : PowerSeries L)` and
`rescale ψ (exp L)` are restricted at radius `‖x‖` (`PowerSeries.isRestricted_rescale_exp`), so
`PowerSeries.IsRestricted.hasSum_evalAt` and `PowerSeries.IsRestricted.evalAt_mul` show that
`(Q : PowerSeries L) * rescale ψ (exp L)` converges at `x` to `Q.eval x * NormedSpace.exp (ψ * x)`
(`PowerSeries.hasSum_coeff_coe_mul_rescale_exp`), and its `m`-th formal derivative evaluates via
`FormalMultilinearSeries.ofScalarsSum` to
`(Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x)`
(`PowerSeries.ofScalarsSum_coeff_iterate_derivative_coe_mul_rescale_exp`).

## Main results

* `PowerSeries.norm_coeff_coe_mul_rescale_exp_mul_pow_le`,
  `PowerSeries.norm_coeff_iterate_derivative_coe_mul_rescale_exp_mul_pow_le`: weighted coefficient
  bounds for `(Q : L⟦X⟧) * exp(ψ X)` and its `m`-th formal derivative.
* `PowerSeries.hasSum_coeff_coe_mul_rescale_exp`,
  `PowerSeries.hasSum_coeff_iterate_derivative_coe_mul_rescale_exp`: for
  `‖ψ * x‖ < p ^ (-(p - 1)⁻¹)` in complete `L`, `∑ coeff k (Q(X) exp(ψ X)) * x ^ k` sums to
  `Q.eval x * NormedSpace.exp (ψ * x)` (and analogously for the `m`-th formal derivative).
* `PowerSeries.ofScalarsSum_coeff_coe_mul_rescale_exp`,
  `PowerSeries.ofScalarsSum_coeff_iterate_derivative_coe_mul_rescale_exp`: evaluation via
  `FormalMultilinearSeries.ofScalarsSum` for `Q(X) exp(ψ X)` and its `m`-th formal derivative.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press (1975), Chapter 2.
* M. Karatarakis, `ExpSeries.lean` in `mkaratarakis/mathlib4`, commit
  `65cdef5722194f07709ab40ff46eede531f52f5d`, `Mathlib/NumberTheory/Transcendental/Baker/Padic/`.
-/

public section

namespace PowerSeries

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

-- Retain the caller's rational algebra structure, which occurs in `PowerSeries.exp`.
variable {L : Type*} [NormedField L] [Algebra ℚ L] [NormedAlgebra ℚ_[p] L]

/-- **Coefficient bound for a `p`-adic exponential polynomial.** If `‖Q.coeff j‖ * r ^ j ≤ M` for
all `j` and `‖ψ‖ * r ≤ p ^ (-1 / (p - 1))` (`r ≥ 0`), then the coefficients of `Q(X) exp(ψ X)`
satisfy the same `r`-weighted bound `M`. -/
theorem norm_coeff_coe_mul_rescale_exp_mul_pow_le (Q : L[X]) {ψ : L}
    {r M : ℝ} (hr : 0 ≤ r) (hψ : ‖ψ‖ * r ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hQ : ∀ j, ‖Q.coeff j‖ * r ^ j ≤ M) (k : ℕ) :
    ‖coeff k ((Q : PowerSeries L) * rescale ψ (exp L))‖ * r ^ k ≤ M := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  have hQ_has : (Q : PowerSeries L).HasGaussNorm norm r :=
    ⟨M, Set.forall_mem_range.mpr fun j ↦ by simpa [Polynomial.coeff_coe] using hQ j⟩
  have hQ_le : (Q : PowerSeries L).gaussNorm norm r ≤ M := by
    rw [gaussNorm_eq]
    exact ciSup_le fun j ↦ by simpa [Polynomial.coeff_coe] using hQ j
  have hψ' : ‖ψ‖ * r ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by simpa using hψ
  have hE_has : (rescale ψ (exp L)).HasGaussNorm norm r := hasGaussNorm_rescale_exp hr hψ'
  have hE_eq : (rescale ψ (exp L)).gaussNorm norm r = 1 := gaussNorm_rescale_exp hr hψ'
  calc
    ‖coeff k ((Q : PowerSeries L) * rescale ψ (exp L))‖ * r ^ k
        ≤ ((Q : PowerSeries L) * rescale ψ (exp L)).gaussNorm norm r :=
          le_gaussNorm norm r _ (TauCeti.PowerSeries.hasGaussNorm_mul hr hQ_has hE_has) k
    _ ≤ (Q : PowerSeries L).gaussNorm norm r * (rescale ψ (exp L)).gaussNorm norm r :=
          TauCeti.PowerSeries.gaussNorm_mul_le hr hQ_has hE_has
    _ = (Q : PowerSeries L).gaussNorm norm r := by rw [hE_eq, mul_one]
    _ ≤ M := hQ_le

/-- Weighted coefficient bound for the `m`-th formal derivative of a `p`-adic exponential
polynomial `Q(X) exp(ψ X)`: if `0 < r`, `‖ψ‖ * r ≤ p ^ (-1 / (p - 1))`, and
`∀ j, ‖Q.coeff j‖ * r ^ j ≤ M`, then every `r`-weighted coefficient of
`(d⁄dX)^[m] (Q(X) exp(ψ X))` is at most `max r⁻¹ ‖ψ‖ ^ m * M`. -/
theorem norm_coeff_iterate_derivative_coe_mul_rescale_exp_mul_pow_le (Q : L[X])
    {ψ : L} {r M : ℝ} (hr : 0 < r) (hψ : ‖ψ‖ * r ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hQ : ∀ j, ‖Q.coeff j‖ * r ^ j ≤ M) (m k : ℕ) :
    ‖coeff k ((d⁄dX)^[m] ((Q : PowerSeries L) * rescale ψ (exp L)))‖ * r ^ k ≤
      max r⁻¹ ‖ψ‖ ^ m * M := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  rw [iterate_derivative_coe_mul_rescale_exp]
  exact norm_coeff_coe_mul_rescale_exp_mul_pow_le (Polynomial.expDerivFactor ψ m Q) hr.le hψ
    (Polynomial.norm_coeff_expDerivFactor_mul_pow_le ψ hr hQ m) k

/-- **Value of a `p`-adic exponential polynomial** inside the disc of convergence: when `L` is
complete and `‖ψ * x‖ < p ^ (-1 / (p - 1))`, the power series `Q(X) exp(ψ X)` evaluated at `x`
converges to `Q.eval x * NormedSpace.exp (ψ * x)`. -/
theorem hasSum_coeff_coe_mul_rescale_exp [CompleteSpace L] (Q : L[X]) {ψ x : L}
    (h : ‖ψ * x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    HasSum (fun k => coeff k ((Q : PowerSeries L) * rescale ψ (exp L)) * x ^ k)
      (Q.eval x * NormedSpace.exp (ψ * x)) := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  have hQ_res : (Q : PowerSeries L).IsRestricted ‖x‖ :=
    TauCeti.PowerSeries.isRestricted_polynomial Q
  have hE_res : (rescale ψ (exp L)).IsRestricted ‖x‖ :=
    isRestricted_rescale_exp (norm_nonneg x) (by simpa [norm_mul] using h)
  have hmul_res : ((Q : PowerSeries L) * rescale ψ (exp L)).IsRestricted ‖x‖ :=
    (IsRestricted.subring ‖x‖).mul_mem hQ_res hE_res
  have hE_eval : (rescale ψ (exp L)).evalAt x = NormedSpace.exp (ψ * x) := by
    rw [evalAt_rescale, smul_eq_mul, evalAt_def,
      ← (TauCeti.PadicExp.hasSum_exp (by simpa [TauCeti.amiceRadius_zero] using h)).tsum_eq]
    refine tsum_congr fun n ↦ ?_
    simp [coeff_exp, inv_mul_eq_div]
  simpa only [smul_eq_mul, hQ_res.evalAt_mul hE_res le_rfl, evalAt_coe,
    Polynomial.coe_aeval_eq_eval, hE_eval] using hmul_res.hasSum_evalAt (b := x) le_rfl

/-- Inside `‖ψ * x‖ < p ^ (-1 / (p - 1))`, the `m`-th formal derivative of `Q(X) exp(ψ X)`
converges at `x` to `(Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x)`. -/
theorem hasSum_coeff_iterate_derivative_coe_mul_rescale_exp [CompleteSpace L]
    (Q : L[X]) {ψ x : L} (m : ℕ) (h : ‖ψ * x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    HasSum (fun k => coeff k ((d⁄dX)^[m] ((Q : PowerSeries L) * rescale ψ (exp L))) * x ^ k)
      ((Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x)) := by
  simp_rw [iterate_derivative_coe_mul_rescale_exp]
  exact hasSum_coeff_coe_mul_rescale_exp (Polynomial.expDerivFactor ψ m Q) h

/-- Evaluating `Q(X) exp(ψ X)` via `FormalMultilinearSeries.ofScalarsSum` at `x` with
`‖ψ * x‖ < p ^ (-1 / (p - 1))` gives `Q.eval x * NormedSpace.exp (ψ * x)`. -/
theorem ofScalarsSum_coeff_coe_mul_rescale_exp [CompleteSpace L] (Q : L[X]) {ψ x : L}
    (h : ‖ψ * x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    FormalMultilinearSeries.ofScalarsSum (E := L)
        (fun k => coeff k ((Q : PowerSeries L) * rescale ψ (exp L))) x =
      Q.eval x * NormedSpace.exp (ψ * x) := by
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using (hasSum_coeff_coe_mul_rescale_exp Q h).tsum_eq

/-- Evaluating the `m`-th formal derivative of `Q(X) exp(ψ X)` via
`FormalMultilinearSeries.ofScalarsSum` at `x` with `‖ψ * x‖ < p ^ (-1 / (p - 1))` gives
`(Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x)`. -/
theorem ofScalarsSum_coeff_iterate_derivative_coe_mul_rescale_exp [CompleteSpace L]
    (Q : L[X]) {ψ x : L} (m : ℕ) (h : ‖ψ * x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    FormalMultilinearSeries.ofScalarsSum (E := L)
        (fun k => coeff k ((d⁄dX)^[m] ((Q : PowerSeries L) * rescale ψ (exp L)))) x =
      (Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x) := by
  simp_rw [iterate_derivative_coe_mul_rescale_exp]
  exact ofScalarsSum_coeff_coe_mul_rescale_exp (Polynomial.expDerivFactor ψ m Q) h

end PowerSeries
