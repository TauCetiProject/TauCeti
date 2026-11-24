/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The projection theorem for standardized statistics

Let `S` be the `L²` projection of a statistic `T` onto a closed linear space of statistics
containing the constants. Then the residual `T - S` is orthogonal to `S` and to `1`, that is
`E((T - S) S) = 0` and `E(T - S) = 0`. These two relations alone give `cov(T, S) = Var S` and
the Pythagorean identity `Var T = Var(T - S) + Var S`, and hence
`E((T - E T)/sd T - (S - E S)/sd S)² = 2 - 2 sd S / sd T`.

Consequently, if `Var Tₙ / Var Sₙ → 1` along a filter, then the standardized statistics are
asymptotically equivalent in `L²`: `(Tₙ - E Tₙ)/sd Tₙ - (Sₙ - E Sₙ)/sd Sₙ → 0` in squared `L²`
norm (van der Vaart, Theorem 11.2).

The identities need only a finite measure, with integrals in place of expectations and
`Var`, `cov` as in Mathlib; for a probability measure they are the statements above.

## Main results

* `TauCeti.covariance_eq_variance_of_isProjection`: `cov(T, S) = Var S`.
* `TauCeti.variance_eq_variance_sub_add_variance_of_isProjection`:
  `Var T = Var(T - S) + Var S`.
* `TauCeti.integral_sq_standardized_sub_of_isProjection`: the squared `L²` distance of the
  standardized statistics is `2 - 2 √(Var S / Var T)`.
* `TauCeti.tendsto_integral_sq_standardized_sub_of_isProjection`: the projection theorem.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Theorem 11.2.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace TauCeti

section Projection

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {T S : Ω → ℝ}

/-- If the residual `T - S` is orthogonal to `S` and to the constants, then the covariance of `T`
and `S` is the variance of `S`. -/
theorem covariance_eq_variance_of_isProjection (hT : MemLp T 2 μ) (hS : MemLp S 2 μ)
    (horth : ∫ ω, (T ω - S ω) * S ω ∂μ = 0) (hconst : ∫ ω, (T ω - S ω) ∂μ = 0) :
    cov[T, S; μ] = Var[S; μ] := by
  have h : cov[T - S, S; μ] = 0 := by
    have hD : Integrable (fun ω ↦ T ω - S ω) μ := (hT.sub hS).integrable one_le_two
    have hDS : Integrable (fun ω ↦ (T ω - S ω) * S ω) μ := (hT.sub hS).integrable_mul hS
    simp only [covariance, Pi.sub_apply, hconst, sub_zero, mul_sub]
    rw [integral_sub hDS (hD.mul_const _), integral_mul_const, horth, hconst, zero_mul, sub_zero]
  rw [covariance_sub_left hT hS hS, covariance_self hS.aemeasurable] at h
  linarith

/-- **Pythagoras for a projection.** If the residual `T - S` is orthogonal to `S` and to the
constants, then `Var T = Var(T - S) + Var S`. -/
theorem variance_eq_variance_sub_add_variance_of_isProjection (hT : MemLp T 2 μ)
    (hS : MemLp S 2 μ) (horth : ∫ ω, (T ω - S ω) * S ω ∂μ = 0)
    (hconst : ∫ ω, (T ω - S ω) ∂μ = 0) :
    Var[T; μ] = Var[T - S; μ] + Var[S; μ] := by
  have h := variance_add (hT.sub hS) hS
  rw [covariance_sub_left hT hS hS, covariance_eq_variance_of_isProjection hT hS horth hconst,
    covariance_self hS.aemeasurable, sub_add_cancel] at h
  linarith

/-- **The standardized distance to a projection.** If the residual `T - S` of a square-integrable
`T` is orthogonal to `S` and to the constants, and `S` has nonzero variance, then
`E((T - E T)/sd T - (S - E S)/sd S)² = 2 - 2 √(Var S / Var T)`. The variance of `S` is nonzero
and `S` is almost everywhere strongly measurable, so `S` is square-integrable. -/
theorem integral_sq_standardized_sub_of_isProjection (hT : MemLp T 2 μ)
    (hS : AEStronglyMeasurable S μ) (horth : ∫ ω, (T ω - S ω) * S ω ∂μ = 0)
    (hconst : ∫ ω, (T ω - S ω) ∂μ = 0) (hS0 : Var[S; μ] ≠ 0) :
    ∫ ω, ((T ω - ∫ ω', T ω' ∂μ) / Real.sqrt Var[T; μ] -
      (S ω - ∫ ω', S ω' ∂μ) / Real.sqrt Var[S; μ]) ^ 2 ∂μ =
      2 - 2 * Real.sqrt (Var[S; μ] / Var[T; μ]) := by
  have hS2 : MemLp S 2 μ := memLp_two_of_variance_ne_zero hS hS0
  have hcov := covariance_eq_variance_of_isProjection hT hS2 horth hconst
  have hle : Var[S; μ] ≤ Var[T; μ] := by
    rw [variance_eq_variance_sub_add_variance_of_isProjection hT hS2 horth hconst]
    linarith [variance_nonneg (T - S) μ]
  -- Write the variances as squares of the standard deviations `a` and `b`.
  have hb : 0 < Real.sqrt Var[S; μ] :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg S μ) (Ne.symm hS0))
  have ha : 0 < Real.sqrt Var[T; μ] := hb.trans_le (Real.sqrt_le_sqrt hle)
  have hA := Real.sq_sqrt (variance_nonneg T μ)
  have hB := Real.sq_sqrt (variance_nonneg S μ)
  generalize Real.sqrt Var[T; μ] = a at ha hA ⊢
  generalize Real.sqrt Var[S; μ] = b at hb hB ⊢
  -- The integrand is the squared centred value of `Z = T a⁻¹ - S b⁻¹`.
  have hT' := hT.mul_const a⁻¹
  have hS' := hS2.mul_const b⁻¹
  have hmean : ∫ ω, (T ω * a⁻¹ - S ω * b⁻¹) ∂μ = (∫ ω, T ω ∂μ) * a⁻¹ - (∫ ω, S ω ∂μ) * b⁻¹ := by
    rw [integral_sub (hT'.integrable one_le_two) (hS'.integrable one_le_two), integral_mul_const,
      integral_mul_const]
  have hvar := variance_eq_integral (μ := μ) (hT'.sub hS').aemeasurable
  rw [variance_sub hT' hS', covariance_mul_const_left, covariance_mul_const_right, hcov,
    variance_mul_const, variance_mul_const] at hvar
  simp only [Pi.sub_apply] at hvar
  rw [hmean] at hvar
  rw [← hA, ← hB, ← div_pow, Real.sqrt_sq (div_nonneg hb.le ha.le)]
  calc ∫ ω, ((T ω - ∫ ω', T ω' ∂μ) / a - (S ω - ∫ ω', S ω' ∂μ) / b) ^ 2 ∂μ
      = ∫ ω, (T ω * a⁻¹ - S ω * b⁻¹ - ((∫ ω', T ω' ∂μ) * a⁻¹ - (∫ ω', S ω' ∂μ) * b⁻¹)) ^ 2 ∂μ := by
        congr with ω
        ring
    _ = 2 - 2 * (b / a) := by
        rw [← hvar, ← hA, ← hB]
        field_simp
        ring

end Projection

/-- **The projection theorem** (van der Vaart, Theorem 11.2). Let `Sₙ` be the projection of `Tₙ`
onto a closed subspace of `L²` containing the constants, so that `Tₙ - Sₙ` is orthogonal to `Sₙ`
and to `1`. If `Var Tₙ / Var Sₙ → 1`, then the standardized statistics are asymptotically
equivalent: `E((Tₙ - E Tₙ)/sd Tₙ - (Sₙ - E Sₙ)/sd Sₙ)² → 0`. Only almost everywhere strong
measurability of `Tₙ` and `Sₙ` is assumed: since the variance ratio tends to `1`, both variances
are eventually nonzero, so both statistics are eventually square-integrable. -/
theorem tendsto_integral_sq_standardized_sub_of_isProjection {κ : Type*} {l : Filter κ}
    {Ωn : κ → Type*} [∀ n, MeasurableSpace (Ωn n)] (μ : ∀ n, Measure (Ωn n))
    [∀ n, IsFiniteMeasure (μ n)] (T S : ∀ n, Ωn n → ℝ)
    (hT : ∀ n, AEStronglyMeasurable (T n) (μ n)) (hS : ∀ n, AEStronglyMeasurable (S n) (μ n))
    (horth : ∀ n, ∫ ω, (T n ω - S n ω) * S n ω ∂(μ n) = 0)
    (hconst : ∀ n, ∫ ω, (T n ω - S n ω) ∂(μ n) = 0)
    (hvar : Tendsto (fun n ↦ Var[T n; μ n] / Var[S n; μ n]) l (𝓝 1)) :
    Tendsto (fun n ↦ ∫ ω, ((T n ω - ∫ ω', T n ω' ∂(μ n)) / Real.sqrt Var[T n; μ n] -
      (S n ω - ∫ ω', S n ω' ∂(μ n)) / Real.sqrt Var[S n; μ n]) ^ 2 ∂(μ n)) l (𝓝 0) := by
  have hlim : Tendsto (fun n ↦ 2 - 2 * Real.sqrt (Var[S n; μ n] / Var[T n; μ n])) l (𝓝 0) := by
    have h := ((hvar.inv₀ one_ne_zero).sqrt.const_mul 2).const_sub 2
    simpa [inv_div] using h
  refine hlim.congr' ?_
  filter_upwards [hvar.eventually_ne one_ne_zero] with n hn
  have hT0 : Var[T n; μ n] ≠ 0 := fun h ↦ hn (by simp [h])
  have hS0 : Var[S n; μ n] ≠ 0 := fun h ↦ hn (by simp [h])
  exact (integral_sq_standardized_sub_of_isProjection (memLp_two_of_variance_ne_zero (hT n) hT0)
    (hS n) (horth n) (hconst n) hS0).symm

end TauCeti
