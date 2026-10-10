/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T20.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Probability/Moments/` (new file
`SampleMean.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space


/-! # Mean-squared error of the sample mean

For a sample `X 0, …, X (r-1)` of square-integrable random vectors valued in a
finite-dimensional real inner product space, with common mean `μ`, the
mean-squared error of the sample mean `r⁻¹ ∑ₖ Xₖ` about `μ` is `r⁻²` times the
sum of the individual mean-squared errors:

`∫ ‖r⁻¹ ∑ₖ Xₖ − μ‖² = r⁻² ∑ₖ ∫ ‖Xₖ − μ‖²`.

Only **pairwise** independence and a **common mean** are needed; the cross terms
vanish by independence (no identical-distribution hypothesis). Specialized to an
identically-distributed sample this is the classical `trace(Σ) / r` rate, and an
upper bound on each individual error gives the `γ / r` decay used throughout
concentration arguments.

Mathlib's `ProbabilityTheory.variance` is `ℝ`-valued; the covariance API in
`Mathlib/Probability/Moments/CovarianceBilin.lean` has no trace identity and no
sample-mean lemmas. The scalar engine here is `IndepFun.variance_sum`; the work
is the coordinatewise reduction over an orthonormal basis.

## Main results

* `TauCeti.integral_sq_scaledSum_sub_of_pairwise_indep`: scalar identity
  `∫ (r⁻¹ ∑ₖ Zₖ − c)² = r⁻² ∑ₖ ∫ (Zₖ − c)²` for pairwise-independent,
  common-mean real random variables.
* `TauCeti.integral_norm_sq_average_sub_eq_sum`: the vector identity above on
  a finite-dimensional real inner product space.
* `TauCeti.integral_norm_sq_average_sub_of_iid`: identically-distributed
  collapse to `r⁻¹ ∫ ‖X 0 − μ‖²`.
* `TauCeti.integral_norm_sq_average_sub_le_of_bound`: the `γ / r` bound.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Probability.Moments.SampleMean`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `e9379f2`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/--
**Scalar variance-of-the-mean identity.** For pairwise-independent,
square-integrable real random variables `Z 0, …, Z (r-1)` sharing a common mean
`c` (each `∫ Z k = c`), the second moment of the scaled sum about `c` is `r⁻²`
times the sum of the per-variable second moments about `c`:

`∫ (r⁻¹ ∑ₖ Zₖ − c)² = r⁻² ∑ₖ ∫ (Zₖ − c)²`.

The common-mean hypothesis is genuinely needed: without centring each `Z k` at
`c` an extra bias term `(E[mean] − c)²` appears. The proof routes through
`ProbabilityTheory.variance` (which absorbs the centring) and
`ProbabilityTheory.IndepFun.variance_sum`.
-/
theorem integral_sq_scaledSum_sub_of_pairwise_indep
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (Z : Fin r → Ω → ℝ) (c : ℝ)
    (hL2 : ∀ k, MemLp (Z k) 2 P)
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = c)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (Z i) (Z j) P) :
    ∫ ω, ((r : ℝ)⁻¹ * (∑ k, Z k ω) - c) ^ 2 ∂P
      = (r : ℝ)⁻¹ ^ 2 * ∑ k, ∫ ω, (Z k ω - c) ^ 2 ∂P := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  -- The scaled sum has mean `c`.
  have hmean_sum : P[fun ω => (r : ℝ)⁻¹ * (∑ k, Z k ω)] = c := by
    rw [integral_const_mul, integral_finsetSum]
    · simp_rw [hmean]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · exact fun k _ => (hL2 k).integrable one_le_two
  -- Measurability of the scaled sum.
  have hmeasS : AEMeasurable (fun ω => (r : ℝ)⁻¹ * (∑ k, Z k ω)) P := by
    refine AEMeasurable.const_mul ?_ _
    have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin r))
      (fun k _ => (hL2 k).aemeasurable)
    have heq : (fun ω => ∑ k, Z k ω) = (∑ i : Fin r, Z i) := by
      ext ω; simp [Finset.sum_apply]
    rw [heq]; exact h
  -- LHS is the variance of the scaled sum (since its mean is `c`).
  have hLHS : ∫ ω, ((r : ℝ)⁻¹ * (∑ k, Z k ω) - c) ^ 2 ∂P
      = variance (fun ω => (r : ℝ)⁻¹ * (∑ k, Z k ω)) P := by
    rw [variance_eq_integral hmeasS, hmean_sum]
  rw [hLHS, variance_const_mul]
  -- Variance of a sum of pairwise-independent variables is the sum of variances.
  have hvarsum : variance (fun ω => ∑ k, Z k ω) P = ∑ k, variance (Z k) P := by
    have hsum := IndepFun.variance_sum (X := Z) (s := Finset.univ)
      (fun i _ => hL2 i)
      (fun i _ j _ hij => hindep (Set.mem_univ i) (Set.mem_univ j) hij)
    rw [← hsum]
    congr 1
    ext ω
    simp [Finset.sum_apply]
  rw [hvarsum]
  -- Each variance is the second moment about `c`.
  have hvark : ∀ k, variance (Z k) P = ∫ ω, (Z k ω - c) ^ 2 ∂P := by
    intro k
    rw [variance_eq_integral (hL2 k).aemeasurable, hmean k]
  simp_rw [hvark]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/--
**Mean-squared error of the sample mean (additive form).**

Let `X : Fin r → Ω → E` be pairwise-independent, square-integrable random
vectors in a finite-dimensional real inner product space, with common mean
`μ` (each Bochner integral `∫ X k = μ`). Then the mean-squared error of the
sample mean equals `r⁻²` times the sum of the individual mean-squared errors:

`∫ ‖r⁻¹ ∑ₖ Xₖ − μ‖² = r⁻² ∑ₖ ∫ ‖Xₖ − μ‖²`.

Only pairwise independence and identical centring are required (not identical
distribution); the cross terms vanish by independence. The proof reduces
coordinatewise via `stdOrthonormalBasis` to the scalar identity
`integral_sq_scaledSum_sub_of_pairwise_indep`.
-/
theorem integral_norm_sq_average_sub_eq_sum
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (X : Fin r → Ω → E) (μ : E)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k, ∫ ω, X k ω ∂P = μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P) :
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : ℝ)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P := by
  set b := stdOrthonormalBasis ℝ E with hb
  -- The coordinate functional `x ↦ ⟪b c, x⟫` as a continuous linear map.
  let φ : Fin (Module.finrank ℝ E) → (E →L[ℝ] ℝ) := fun c => innerSL ℝ (b c)
  have hφ : ∀ c x, φ c x = ⟪b c, x⟫_ℝ := fun _ _ => rfl
  -- Per-coordinate square-integrability of `X k`.
  have hL2c : ∀ (k : Fin r) (c), MemLp (fun ω => ⟪b c, X k ω⟫_ℝ) 2 P := by
    intro k c
    have := (hL2 k).continuousLinearMap_comp (φ c)
    simpa [hφ] using this
  -- Per-coordinate common mean, from the Bochner mean via `integral_inner`.
  have hmeanc : ∀ (k : Fin r) (c), ∫ ω, ⟪b c, X k ω⟫_ℝ ∂P = ⟪b c, μ⟫_ℝ := by
    intro k c
    rw [integral_inner ((hL2 k).integrable one_le_two) (b c), hmean k]
  -- Per-coordinate pairwise independence, by composing with the functional.
  have hindepc : ∀ c, Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (fun ω => ⟪b c, X i ω⟫_ℝ) (fun ω => ⟪b c, X j ω⟫_ℝ) P := by
    intro c i hi j hj hij
    have hmeas : Measurable fun x : E => ⟪b c, x⟫_ℝ := (φ c).continuous.measurable
    exact (hindep hi hj hij).comp hmeas hmeas
  -- Per-coordinate integrability of the deviation squares (for `∫ Σ = Σ ∫`).
  have hintc : ∀ c, Integrable
      (fun ω => ((r : ℝ)⁻¹ * (∑ k, ⟪b c, X k ω⟫_ℝ) - ⟪b c, μ⟫_ℝ) ^ 2) P := by
    intro c
    have h1 : MemLp (fun ω => ∑ k, ⟪b c, X k ω⟫_ℝ) 2 P :=
      memLp_finsetSum (Finset.univ : Finset (Fin r)) (fun k _ => hL2c k c)
    exact (((h1.const_mul _).sub (memLp_const _))).integrable_sq
  have hintkc : ∀ (k : Fin r) c,
      Integrable (fun ω => (⟪b c, X k ω⟫_ℝ - ⟪b c, μ⟫_ℝ) ^ 2) P :=
    fun k c => ((hL2c k c).sub (memLp_const _)).integrable_sq
  -- Norm-square as a sum over basis coordinates (real Parseval).
  have hpar : ∀ v : E, ‖v‖ ^ 2 = ∑ c, ⟪b c, v⟫_ℝ ^ 2 := by
    intro v
    rw [← b.sum_sq_norm_inner_right v]
    exact Finset.sum_congr rfl fun c _ => by rw [Real.norm_eq_abs, sq_abs]
  -- Coordinate of the (centred) sample mean.
  have hcoordS : ∀ (ω : Ω) c,
      ⟪b c, (r : ℝ)⁻¹ • (∑ k, X k ω) - μ⟫_ℝ
        = (r : ℝ)⁻¹ * (∑ k, ⟪b c, X k ω⟫_ℝ) - ⟪b c, μ⟫_ℝ := by
    intro ω c
    rw [inner_sub_right, inner_smul_right, inner_sum]
  calc
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
        = ∫ ω, ∑ c, ((r : ℝ)⁻¹ * (∑ k, ⟪b c, X k ω⟫_ℝ) - ⟪b c, μ⟫_ℝ) ^ 2 ∂P := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          dsimp only
          rw [hpar]
          exact Finset.sum_congr rfl fun c _ => by rw [hcoordS ω c]
    _ = ∑ c, ∫ ω, ((r : ℝ)⁻¹ * (∑ k, ⟪b c, X k ω⟫_ℝ) - ⟪b c, μ⟫_ℝ) ^ 2 ∂P := by
          rw [integral_finsetSum]; exact fun c _ => hintc c
    _ = ∑ c, (r : ℝ)⁻¹ ^ 2 * ∑ k, ∫ ω, (⟪b c, X k ω⟫_ℝ - ⟪b c, μ⟫_ℝ) ^ 2 ∂P := by
          refine Finset.sum_congr rfl fun c _ => ?_
          exact integral_sq_scaledSum_sub_of_pairwise_indep P hr
            (fun k ω => ⟪b c, X k ω⟫_ℝ) (⟪b c, μ⟫_ℝ) (fun k => hL2c k c)
            (fun k => hmeanc k c) (hindepc c)
    _ = (r : ℝ)⁻¹ ^ 2 * ∑ k, ∑ c, ∫ ω, (⟪b c, X k ω⟫_ℝ - ⟪b c, μ⟫_ℝ) ^ 2 ∂P := by
          rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (r : ℝ)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← integral_finsetSum Finset.univ (fun c _ => hintkc k c)]
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          dsimp only
          rw [hpar (X k ω - μ)]
          exact Finset.sum_congr rfl fun c _ => by rw [inner_sub_right]

/--
**Identically-distributed collapse.** If in addition the per-sample
mean-squared errors are identical (`∫ ‖X k − μ‖² = ∫ ‖X 0 − μ‖²` for all `k`,
automatic for an iid sample), the additive identity collapses to the classical
`trace(Σ) / r` rate: `∫ ‖r⁻¹ ∑ₖ Xₖ − μ‖² = r⁻¹ ∫ ‖X 0 − μ‖²`.
-/
theorem integral_norm_sq_average_sub_of_iid
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (X : Fin r → Ω → E) (μ : E)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k, ∫ ω, X k ω ∂P = μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)
    (hident : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P = ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P) :
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P
      = (r : ℝ)⁻¹ * ∫ ω, ‖X ⟨0, hr⟩ ω - μ‖ ^ 2 ∂P := by
  rw [integral_norm_sq_average_sub_eq_sum P hr X μ hL2 hmean hindep]
  simp_rw [hident]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

/--
**`γ / r` decay.** If each per-sample mean-squared error is bounded by `γ`
(`γ = trace(Σ)` in the iid case), then the sample-mean mean-squared error
decays at rate `γ / r`: `∫ ‖r⁻¹ ∑ₖ Xₖ − μ‖² ≤ γ / r`.
-/
theorem integral_norm_sq_average_sub_le_of_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℕ} (hr : 0 < r) (X : Fin r → Ω → E) (μ : E)
    (hL2 : ∀ k, MemLp (X k) 2 P)
    (hmean : ∀ k, ∫ ω, X k ω ∂P = μ)
    (hindep : Set.Pairwise (Set.univ : Set (Fin r))
      fun i j => IndepFun (X i) (X j) P)
    {γ : ℝ} (hbound : ∀ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P ≤ γ) :
    ∫ ω, ‖(r : ℝ)⁻¹ • (∑ k, X k ω) - μ‖ ^ 2 ∂P ≤ γ / r := by
  rw [integral_norm_sq_average_sub_eq_sum P hr X μ hL2 hmean hindep]
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hsum_le : (∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P) ≤ (r : ℝ) * γ := by
    calc (∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P)
          ≤ ∑ _k : Fin r, γ := Finset.sum_le_sum fun k _ => hbound k
      _ = (r : ℝ) * γ := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (r : ℝ)⁻¹ ^ 2 * ∑ k, ∫ ω, ‖X k ω - μ‖ ^ 2 ∂P
        ≤ (r : ℝ)⁻¹ ^ 2 * ((r : ℝ) * γ) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = γ / r := by
          rw [sq, mul_assoc, inv_mul_cancel_left₀ hr0.ne', div_eq_inv_mul]

end TauCeti
