/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.Algebra.Polynomial.ExpDerivFactor
public import TauCeti.RingTheory.PowerSeries.Exp.Derivative
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.NumberTheory.Padics.Exp.Basic
import TauCeti.RingTheory.PowerSeries.Exp.Eval
import TauCeti.RingTheory.PowerSeries.Exp.Padic.Basic
import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Exponential polynomials over `p`-adic algebras

In an ultrametric seminormed commutative `ℚ_[p]`-algebra `A` with `‖(1 : A)‖ = 1` (retaining its
rational algebra structure `[Algebra ℚ A]` used by `PowerSeries.exp`), an exponential polynomial
`Q(X) exp(ψ X)` is represented formally as the power series
`(Q : PowerSeries A) * PowerSeries.rescale ψ (PowerSeries.exp A)`. By the Gauss-norm estimate
`PowerSeries.gaussNorm_rescale_exp` of `TauCeti.RingTheory.PowerSeries.Exp.Padic.Basic`, whenever
`0 ≤ r` and `‖ψ‖ * r ≤ p ^ (-1 / (p - 1))`, the rescaled exponential `exp(ψ X)` has Gauss norm
`1` at radius `r`. By submultiplicativity of the ultrametric Gauss norm
(`TauCeti.PowerSeries.gaussNorm_mul_le`), multiplying `(Q : PowerSeries A)` by `exp(ψ X)` preserves
any `r`-weighted bound `∀ j, ‖Q.coeff j‖ * r ^ j ≤ M`
(`PowerSeries.norm_coeff_coe_mul_rescale_exp_mul_pow_le`).

When `A` is a complete normed commutative `ℚ_[p]`-algebra with `[Algebra ℚ A]` and
`‖ψ * x‖ < p ^ (-1 / (p - 1))`, the Cauchy product via `PowerSeries.evalAt_mul_of_summable_norm`
shows that `(Q : PowerSeries A) * rescale ψ (exp A)` converges at `x` to
`Q.eval x * NormedSpace.exp (ψ * x)` (`PowerSeries.hasSum_coeff_coe_mul_rescale_exp`), and its
`m`-th formal derivative converges to
`(Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x)`
(`PowerSeries.hasSum_coeff_iterate_derivative_coe_mul_rescale_exp`).

## Main results

* `PowerSeries.norm_coeff_coe_mul_rescale_exp_mul_pow_le`,
  `PowerSeries.norm_coeff_iterate_derivative_coe_mul_rescale_exp_mul_pow_le`: weighted coefficient
  bounds for `(Q : A⟦X⟧) * exp(ψ X)` and its `m`-th formal derivative.
* `PowerSeries.hasSum_coeff_coe_mul_rescale_exp`,
  `PowerSeries.hasSum_coeff_iterate_derivative_coe_mul_rescale_exp`: for
  `‖ψ * x‖ < p ^ (-(p - 1)⁻¹)` in complete `A`, `∑ coeff k (Q(X) exp(ψ X)) * x ^ k` sums to
  `Q.eval x * NormedSpace.exp (ψ * x)` (and analogously for the `m`-th formal derivative).

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press (1975), Chapter 2.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58,
  Chapter IV, §1.
* M. Karatarakis, `ExpSeries.lean` in `mkaratarakis/mathlib4`, commit
  `65cdef5722194f07709ab40ff46eede531f52f5d`, `Mathlib/NumberTheory/Transcendental/Baker/Padic/`.
-/

public section

namespace PowerSeries

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

section SeminormedCommRing

-- Retain the caller's rational algebra structure, which occurs in `PowerSeries.exp`.
variable {A : Type*} [SeminormedCommRing A] [NormOneClass A] [IsUltrametricDist A]
  [Algebra ℚ A] [NormedAlgebra ℚ_[p] A]

/-- **Coefficient bound for a `p`-adic exponential polynomial.** If `‖Q.coeff j‖ * r ^ j ≤ M` for
all `j` and `‖ψ‖ * r ≤ p ^ (-1 / (p - 1))` (`r ≥ 0`), then the coefficients of `Q(X) exp(ψ X)`
satisfy the same `r`-weighted bound `M`. -/
theorem norm_coeff_coe_mul_rescale_exp_mul_pow_le (Q : A[X]) {ψ : A}
    {r M : ℝ} (hr : 0 ≤ r) (hψ : ‖ψ‖ * r ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hQ : ∀ j, ‖Q.coeff j‖ * r ^ j ≤ M) (k : ℕ) :
    ‖coeff k ((Q : PowerSeries A) * rescale ψ (exp A))‖ * r ^ k ≤ M := by
  have hQ_has : (Q : PowerSeries A).HasGaussNorm norm r :=
    ⟨M, Set.forall_mem_range.mpr fun j ↦ by simpa [Polynomial.coeff_coe] using hQ j⟩
  have hQ_le : (Q : PowerSeries A).gaussNorm norm r ≤ M := by
    rw [gaussNorm_eq]
    exact ciSup_le fun j ↦ by simpa [Polynomial.coeff_coe] using hQ j
  have hψ' : ‖ψ‖ * r ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by simpa using hψ
  have hE_has : (rescale ψ (exp A)).HasGaussNorm norm r := hasGaussNorm_rescale_exp hr hψ'
  have hE_eq : (rescale ψ (exp A)).gaussNorm norm r = 1 := gaussNorm_rescale_exp hr hψ'
  calc
    ‖coeff k ((Q : PowerSeries A) * rescale ψ (exp A))‖ * r ^ k
        ≤ ((Q : PowerSeries A) * rescale ψ (exp A)).gaussNorm norm r :=
          le_gaussNorm norm r _ (TauCeti.PowerSeries.hasGaussNorm_mul hr hQ_has hE_has) k
    _ ≤ (Q : PowerSeries A).gaussNorm norm r * (rescale ψ (exp A)).gaussNorm norm r :=
          TauCeti.PowerSeries.gaussNorm_mul_le hr hQ_has hE_has
    _ = (Q : PowerSeries A).gaussNorm norm r := by rw [hE_eq, mul_one]
    _ ≤ M := hQ_le

/-- Weighted coefficient bound for the `m`-th formal derivative of a `p`-adic exponential
polynomial `Q(X) exp(ψ X)`: if `0 < r`, `‖ψ‖ * r ≤ p ^ (-1 / (p - 1))`, and
`∀ j, ‖Q.coeff j‖ * r ^ j ≤ M`, then every `r`-weighted coefficient of
`(d⁄dX)^[m] (Q(X) exp(ψ X))` is at most `max r⁻¹ ‖ψ‖ ^ m * M`. -/
theorem norm_coeff_iterate_derivative_coe_mul_rescale_exp_mul_pow_le (Q : A[X])
    {ψ : A} {r M : ℝ} (hr : 0 < r) (hψ : ‖ψ‖ * r ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hQ : ∀ j, ‖Q.coeff j‖ * r ^ j ≤ M) (m k : ℕ) :
    ‖coeff k ((d⁄dX)^[m] ((Q : PowerSeries A) * rescale ψ (exp A)))‖ * r ^ k ≤
      max r⁻¹ ‖ψ‖ ^ m * M := by
  rw [iterate_derivative_coe_mul_rescale_exp]
  exact norm_coeff_coe_mul_rescale_exp_mul_pow_le (Polynomial.expDerivFactor ψ m Q) hr.le hψ
    (Polynomial.norm_coeff_expDerivFactor_mul_pow_le ψ hr hQ m) k

end SeminormedCommRing

section NormedCommRing

-- Retain the caller's rational algebra structure, which occurs in `PowerSeries.exp`.
variable {A : Type*} [NormedCommRing A] [Algebra ℚ A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]

/-- **Value of a `p`-adic exponential polynomial** inside the disc of convergence: when `A` is
complete and `‖ψ * x‖ < p ^ (-1 / (p - 1))`, the power series `Q(X) exp(ψ X)` evaluated at `x`
converges to `Q.eval x * NormedSpace.exp (ψ * x)`. -/
theorem hasSum_coeff_coe_mul_rescale_exp (Q : A[X]) {ψ x : A}
    (h : ‖ψ * x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    HasSum (fun k => coeff k ((Q : PowerSeries A) * rescale ψ (exp A)) * x ^ k)
      (Q.eval x * NormedSpace.exp (ψ * x)) := by
  have hf_norm : Summable fun i => ‖coeff i (Q : PowerSeries A) • x ^ i‖ :=
    summable_of_ne_finset_zero (s := Finset.range (Q.natDegree + 1)) fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]
  have hmem : ψ * x ∈ Metric.eball (0 : A) (NormedSpace.expSeries ℚ_[p] A).radius :=
    TauCeti.PadicExp.mem_eball_expSeries_of_norm_lt (K := ℚ_[p])
      (by simpa [TauCeti.amiceRadius_zero] using h)
  have hg_norm : Summable fun j => ‖coeff j (rescale ψ (exp A)) • x ^ j‖ := by
    refine (NormedSpace.norm_expSeries_summable_of_mem_ball' (ψ * x) hmem).congr fun j => ?_
    apply congrArg norm
    simp only [coeff_rescale, coeff_exp, smul_eq_mul,
      ← RingHom.map_rat_algebraMap (algebraMap ℚ_[p] A), Algebra.smul_def, map_inv₀,
      map_natCast, one_div, mul_pow]
    ring
  have hmul : Summable fun k => ‖coeff k ((Q : PowerSeries A) * rescale ψ (exp A)) • x ^ k‖ := by
    refine (summable_norm_sum_mul_antidiagonal_of_summable_norm hf_norm hg_norm).congr fun k => ?_
    apply congrArg norm
    rw [coeff_mul, Finset.sum_smul]
    exact Finset.sum_congr rfl fun p hp => by
      rw [← Finset.mem_antidiagonal.mp hp, pow_add, smul_mul_smul_comm]
  have hsum := hasSum_evalAt_of_summable_norm hmul
  rw [evalAt_mul_of_summable_norm hf_norm hg_norm, evalAt_coe, Polynomial.coe_aeval_eq_eval,
    evalAt_rescale, smul_eq_mul, evalAt_exp] at hsum
  simpa only [smul_eq_mul] using hsum

/-- Inside `‖ψ * x‖ < p ^ (-1 / (p - 1))`, the `m`-th formal derivative of `Q(X) exp(ψ X)`
converges at `x` to `(Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x)`. -/
theorem hasSum_coeff_iterate_derivative_coe_mul_rescale_exp (Q : A[X]) {ψ x : A} (m : ℕ)
    (h : ‖ψ * x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    HasSum (fun k => coeff k ((d⁄dX)^[m] ((Q : PowerSeries A) * rescale ψ (exp A))) * x ^ k)
      ((Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x)) := by
  simp_rw [iterate_derivative_coe_mul_rescale_exp]
  exact hasSum_coeff_coe_mul_rescale_exp (Polynomial.expDerivFactor ψ m Q) h

end NormedCommRing

end PowerSeries
