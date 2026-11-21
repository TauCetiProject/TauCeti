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
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.Analysis.Polynomial.Ultra
import TauCeti.NumberTheory.Padics.Exp.Basic
import TauCeti.NumberTheory.Padics.Factorial

/-!
# Exponential polynomials over `p`-adic fields

In a normed field `L` over `ℚ_[p]` (retaining its rational algebra structure `[Algebra ℚ L]` used
by `PowerSeries.exp`), an exponential polynomial `Q(X) exp(ψ X)` is represented formally as the
power series `(Q : PowerSeries L) * PowerSeries.rescale ψ (PowerSeries.exp L)`. By Legendre's
factorial bound (`TauCeti.norm_inv_factorial_mul_pow_le`), in any seminormed commutative
`ℚ_[p]`-algebra `A` with `‖(1 : A)‖ = 1` and `[Algebra ℚ A]`, whenever `0 ≤ r` and
`‖ψ‖ * r ≤ p ^ (-1 / (p - 1))`, the rescaled exponential `exp(ψ X)` has `r`-weighted coefficients
bounded by `1` (`PowerSeries.norm_coeff_rescale_exp_mul_pow_le`). Over a normed field `L` over
`ℚ_[p]`, multiplying `(Q : PowerSeries L)` by `exp(ψ X)` therefore preserves any `r`-weighted bound
`∀ j, ‖Q.coeff j‖ * r ^ j ≤ M` (`PowerSeries.norm_coeff_coe_mul_rescale_exp_mul_pow_le`).

When `L` is complete and `‖ψ * x‖ < p ^ (-1 / (p - 1))`, the Cauchy product of the finite polynomial
sum `Q.eval x` with the convergent exponential series `NormedSpace.exp (ψ * x)` shows that the
power series `(Q : PowerSeries L) * rescale ψ (exp L)` converges at `x` to
`Q.eval x * NormedSpace.exp (ψ * x)` (`PowerSeries.hasSum_coeff_coe_mul_rescale_exp`), and its
`m`-th formal derivative evaluates via `FormalMultilinearSeries.ofScalarsSum` to
`(Polynomial.expDerivFactor ψ m Q).eval x * NormedSpace.exp (ψ * x)`
(`PowerSeries.ofScalarsSum_coeff_iterate_derivative_coe_mul_rescale_exp`).

## Main results

* `PowerSeries.norm_coeff_rescale_exp_mul_pow_le`: in any seminormed commutative `ℚ_[p]`-algebra `A`
  with `‖(1 : A)‖ = 1` and `[Algebra ℚ A]`, if `0 ≤ r` and `‖ψ‖ * r ≤ p ^ (-(p - 1)⁻¹)`, then
  `‖coeff k (rescale ψ (exp A))‖ * r ^ k ≤ 1`.
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

/-- In a seminormed commutative `ℚ_[p]`-algebra `A` with `‖(1 : A)‖ = 1` and `[Algebra ℚ A]`, if
`0 ≤ r` and `‖ψ‖ * r ≤ p ^ (-1 / (p - 1))`, then every `r`-weighted coefficient of `exp(ψ X)` has
norm at most `1`. -/
theorem norm_coeff_rescale_exp_mul_pow_le {A : Type*} [SeminormedCommRing A] [NormOneClass A]
    [Algebra ℚ A] [NormedAlgebra ℚ_[p] A] {ψ : A} {r : ℝ} (hr : 0 ≤ r)
    (hψ : ‖ψ‖ * r ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (k : ℕ) :
    ‖coeff k (rescale ψ (exp A))‖ * r ^ k ≤ 1 := by
  rw [coeff_rescale, coeff_exp, ← RingHom.map_rat_algebraMap (algebraMap ℚ_[p] A)]
  have hnorm : ‖algebraMap ℚ_[p] A (algebraMap ℚ ℚ_[p] (1 / (k.factorial : ℚ)))‖ =
      ‖(k.factorial : ℚ_[p])⁻¹‖ := by
    rw [norm_algebraMap']
    simp
  calc
    ‖ψ ^ k * algebraMap ℚ_[p] A (algebraMap ℚ ℚ_[p] (1 / (k.factorial : ℚ)))‖ * r ^ k
        ≤ (‖ψ‖ ^ k * ‖(k.factorial : ℚ_[p])⁻¹‖) * r ^ k := by
          gcongr
          exact (norm_mul_le _ _).trans <|
            mul_le_mul (norm_pow_le _ _) hnorm.le (norm_nonneg _) (by positivity)
    _ = ‖(k.factorial : ℚ_[p])⁻¹‖ * (‖ψ‖ * r) ^ k := by rw [mul_pow]; ring
    _ ≤ 1 := TauCeti.norm_inv_factorial_mul_pow_le (mul_nonneg (norm_nonneg ψ) hr) hψ k

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
  have hM : 0 ≤ M := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hQ 0)
  rcases hr.eq_or_lt with rfl | hr_pos
  · rcases k with _ | k
    · simpa [coeff_mul, coeff_rescale, coeff_exp] using hQ 0
    · simpa [zero_pow (Nat.succ_ne_zero k)] using hM
  · rw [coeff_mul, ← le_div_iff₀ (pow_pos hr_pos k)]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (div_nonneg hM (pow_nonneg hr k)) fun ij hij ↦ ?_
    rw [le_div_iff₀ (pow_pos hr_pos k), ← Finset.mem_antidiagonal.mp hij, pow_add, norm_mul,
      Polynomial.coeff_coe]
    calc
      ‖Q.coeff ij.1‖ * ‖coeff ij.2 (rescale ψ (exp L))‖ * (r ^ ij.1 * r ^ ij.2)
          = (‖Q.coeff ij.1‖ * r ^ ij.1) * (‖coeff ij.2 (rescale ψ (exp L))‖ * r ^ ij.2) := by ring
      _ ≤ M * 1 := mul_le_mul (hQ ij.1) (norm_coeff_rescale_exp_mul_pow_le hr hψ ij.2)
            (mul_nonneg (norm_nonneg _) (pow_nonneg hr _)) hM
      _ = M := mul_one M

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
  let f : ℕ → L := fun i ↦ Q.coeff i * x ^ i
  let g : ℕ → L := fun j ↦ (ψ * x) ^ j / (j.factorial : L)
  have hf_zero : ∀ i ∉ Finset.range (Q.natDegree + 1), f i = 0 := fun i hi ↦ by
    rw [Finset.mem_range, not_lt] at hi
    simp [f, Polynomial.coeff_eq_zero_of_natDegree_lt hi]
  have hf_sum : HasSum f (Q.eval x) := by
    rw [Polynomial.eval_eq_sum_range]
    exact hasSum_sum_of_ne_finset_zero hf_zero
  have hf_norm : Summable fun i ↦ ‖f i‖ :=
    summable_of_ne_finset_zero (s := Finset.range (Q.natDegree + 1)) fun i hi ↦ by
      simp [hf_zero i hi]
  have hg_sum : HasSum g (NormedSpace.exp (ψ * x)) := TauCeti.PadicExp.hasSum_exp h
  have hg_norm : Summable fun j ↦ ‖g j‖ := TauCeti.PadicExp.summable_norm_pow_div_factorial h
  have hc_summable : Summable fun k ↦ ∑ ij ∈ Finset.antidiagonal k, f ij.1 * g ij.2 :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hf_norm hg_norm).of_norm
  have hc_tsum : (∑' k, ∑ ij ∈ Finset.antidiagonal k, f ij.1 * g ij.2) =
      Q.eval x * NormedSpace.exp (ψ * x) := by
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf_norm hg_norm,
      hf_sum.tsum_eq, hg_sum.tsum_eq]
  have hterm : (fun k ↦ coeff k ((Q : PowerSeries L) * rescale ψ (exp L)) * x ^ k) =
      fun k ↦ ∑ ij ∈ Finset.antidiagonal k, f ij.1 * g ij.2 := by
    ext k
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    have hcast : (algebraMap ℚ L (1 / (ij.2.factorial : ℚ))) = (ij.2.factorial : L)⁻¹ := by simp
    rw [Polynomial.coeff_coe, coeff_rescale, coeff_exp, ← Finset.mem_antidiagonal.mp hij,
      pow_add, hcast]
    simp only [f, g, mul_pow, div_eq_mul_inv]
    ring
  rw [hterm, ← hc_tsum]
  exact hc_summable.hasSum

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
