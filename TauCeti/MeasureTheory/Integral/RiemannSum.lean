/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.MeasurableSpace.Metric

/-!
# Uniform Riemann sums over a totally bounded set

Let `S` be a measurable totally bounded subset of a pseudometric space carrying a measure `μ`, and
let `a` be a scalar weight integrable on `S`. Cutting `S` into finitely many measurable cells, each
within distance `δ` of a tag in `S`, replaces the weighted integral `∫ x in S, a x • φ x ∂μ` by
the Riemann sum `∑ i, c i • φ (ζ i)`, where `c i` is the integral of `a` over the `i`-th cell, so
that `∑ i, ‖c i‖ ≤ ∫ x in S, ‖a x‖ ∂μ`. The tags and the weights depend only on `S`, `a`, `μ` and
`δ`, not on `φ` or on its target. For every `φ` with values in a Banach space `E` such that
`x ↦ a x • φ x` is integrable on `S` and `φ` oscillates by at most `η` between points of `S` at
distance less than `δ`, the error is at most `η * ∫ x in S, ‖a x‖ ∂μ`
(`TotallyBounded.exists_norm_setIntegral_smul_sub_sum_le`).

Because the quadrature rule is fixed before `φ` is chosen, one rule serves a whole equicontinuous
family at once. This is how an integral representation over a compact set, such as the
Cauchy–Pompeiu representation of a holomorphic function through a cutoff, becomes an
approximation through finitely many point evaluations that is uniform over a bounded family of
functions.
-/

public section

open MeasureTheory Metric Set

variable {X 𝕜 : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [RCLike 𝕜]

/-- **Uniform Riemann sums over a totally bounded set.** For a measurable totally bounded set `S`,
a scalar weight `a` integrable on `S` and a mesh `δ > 0`, there are finitely many tags `ζ i ∈ S`
and weights `c i` with `∑ i, ‖c i‖ ≤ ∫ x in S, ‖a x‖ ∂μ` such that the following holds for every
`φ` with values in a Banach space `E` for which `x ↦ a x • φ x` is integrable on `S`. If the values
of `φ` at points of `S` within distance `δ` of each other differ by at most `η`, then the Riemann
sum `∑ i, c i • φ (ζ i)` is within `η * ∫ x in S, ‖a x‖ ∂μ` of the weighted integral
`∫ x in S, a x • φ x ∂μ`. -/
theorem TotallyBounded.exists_norm_setIntegral_smul_sub_sum_le {S : Set X}
    (hS : TotallyBounded S) (hSm : MeasurableSet S) {a : X → 𝕜} (ha : IntegrableOn a S μ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (N : ℕ) (ζ : Fin N → X) (c : Fin N → 𝕜), (∀ i, ζ i ∈ S) ∧
      ∑ i, ‖c i‖ ≤ ∫ x in S, ‖a x‖ ∂μ ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
        (φ : X → E) (η : ℝ), IntegrableOn (fun x ↦ a x • φ x) S μ →
        (∀ x ∈ S, ∀ y ∈ S, dist x y < δ → ‖φ x - φ y‖ ≤ η) →
          ‖∫ x in S, a x • φ x ∂μ - ∑ i, c i • φ (ζ i)‖ ≤ η * ∫ x in S, ‖a x‖ ∂μ := by
  -- The cells: a measurable partition of `S` into pieces of `δ`-balls around the tags.
  obtain ⟨N, ζ, P, hζS, hPm, hPsub, hPd, hPU⟩ := hS.exists_measurable_partition_ball hSm hδ
  have haP (i : Fin N) : IntegrableOn a (P i) μ :=
    ha.mono_set ((hPsub i).trans inter_subset_left)
  refine ⟨N, ζ, fun i ↦ ∫ x in P i, a x ∂μ, hζS, ?_, fun {E} _ _ _ _ φ η hφ hosc ↦ ?_⟩
  · calc ∑ i, ‖∫ x in P i, a x ∂μ‖
        ≤ ∑ i, ∫ x in P i, ‖a x‖ ∂μ :=
          Finset.sum_le_sum fun i _ ↦ norm_integral_le_integral_norm _
      _ = ∫ x in S, ‖a x‖ ∂μ := by
          rw [← integral_iUnion_fintype hPm hPd fun i ↦ (haP i).norm, hPU]
  have hφP (i : Fin N) : IntegrableOn (fun x ↦ a x • φ x) (P i) μ :=
    hφ.mono_set ((hPsub i).trans inter_subset_left)
  -- On each cell, the error is the integral of `a x • (φ x - φ (ζ i))`.
  have hcell (i : Fin N) :
      ‖∫ x in P i, a x • φ x ∂μ - (∫ x in P i, a x ∂μ) • φ (ζ i)‖ ≤
        ∫ x in P i, ‖a x‖ * η ∂μ := by
    rw [← integral_smul_const, ← integral_sub (hφP i) ((haP i).smul_const _)]
    refine norm_integral_le_of_norm_le ((haP i).norm.mul_const η) ?_
    filter_upwards [ae_restrict_mem (hPm i)] with x hx
    rw [← smul_sub, norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hosc x ((hPsub i hx).1) (ζ i) (hζS i) (mem_ball.1 (hPsub i hx).2)) (norm_nonneg _)
  calc ‖∫ x in S, a x • φ x ∂μ - ∑ i, (∫ x in P i, a x ∂μ) • φ (ζ i)‖
      = ‖∑ i, (∫ x in P i, a x • φ x ∂μ - (∫ x in P i, a x ∂μ) • φ (ζ i))‖ := by
        rw [Finset.sum_sub_distrib, ← hPU, integral_iUnion_fintype hPm hPd hφP]
    _ ≤ ∑ i, ∫ x in P i, ‖a x‖ * η ∂μ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hcell i)
    _ = η * ∫ x in S, ‖a x‖ ∂μ := by
        rw [← integral_iUnion_fintype hPm hPd fun i ↦ (haP i).norm.mul_const η, hPU,
          integral_mul_const, mul_comm]
