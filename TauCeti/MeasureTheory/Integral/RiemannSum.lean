/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.Disjointed
import Mathlib.Order.Interval.Finset.Fin

/-!
# Uniform Riemann sums over a compact set

Let `S` be a compact subset of a metric space carrying a measure `μ`, and let `a` be a scalar
weight integrable on `S`. Cutting `S` into finitely many measurable cells, each within distance
`δ` of a tag in `S`, replaces the weighted integral `∫ x in S, a x • φ x ∂μ` by the Riemann sum
`∑ i, c i • φ (ζ i)`, where `c i` is the integral of `a` over the `i`-th cell. The tags and the
weights depend only on `S`, `a`, `μ` and `δ`, not on `φ`, and the error is at most
`η * ∫ x in S, ‖a x‖ ∂μ` for every `φ` that oscillates by at most `η` between points of `S` at
distance less than `δ` (`IsCompact.exists_norm_setIntegral_smul_sub_sum_le`).

Because the quadrature rule is fixed before `φ` is chosen, one rule serves a whole equicontinuous
family at once. This is how an integral representation over a compact set, such as the
Cauchy–Pompeiu representation of a holomorphic function through a cutoff, becomes a finite-rank
approximation that is uniform over a bounded family of functions.
-/

public section

open MeasureTheory Metric Set
open scoped Function

variable {X 𝕜 E : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- **Uniform Riemann sums over a compact set.** For a compact set `S`, a scalar weight `a`
integrable on `S` and a mesh `δ > 0`, there are finitely many tags `ζ i ∈ S` and weights `c i`
such that for every `φ` whose values at points of `S` within distance `δ` of each other differ by
at most `η`, the Riemann sum `∑ i, c i • φ (ζ i)` is within `η * ∫ x in S, ‖a x‖ ∂μ` of the
weighted integral `∫ x in S, a x • φ x ∂μ`. -/
theorem IsCompact.exists_norm_setIntegral_smul_sub_sum_le {S : Set X} (hS : IsCompact S)
    {a : X → 𝕜} (ha : IntegrableOn a S μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (ζ : Fin N → X) (c : Fin N → 𝕜), (∀ i, ζ i ∈ S) ∧
      ∀ (φ : X → E) (η : ℝ), IntegrableOn (fun x ↦ a x • φ x) S μ →
        (∀ x ∈ S, ∀ y ∈ S, dist x y < δ → ‖φ x - φ y‖ ≤ η) →
          ‖∫ x in S, a x • φ x ∂μ - ∑ i, c i • φ (ζ i)‖ ≤ η * ∫ x in S, ‖a x‖ ∂μ := by
  obtain ⟨t, htS, hcover⟩ := hS.elim_nhds_subcover (fun x ↦ ball x δ) fun x _ ↦ ball_mem_nhds x hδ
  let ζ : Fin t.card → X := fun i ↦ t.equivFin.symm i
  have hζS (i : Fin t.card) : ζ i ∈ S := htS _ (t.equivFin.symm i).2
  -- The cells: the trace of `S` on the balls around the tags, made pairwise disjoint.
  let P : Fin t.card → Set X := disjointed fun i ↦ S ∩ ball (ζ i) δ
  have hPsub (i : Fin t.card) : P i ⊆ S ∩ ball (ζ i) δ := disjointed_subset _ i
  have hPm (i : Fin t.card) : MeasurableSet (P i) := by
    have hm (j : Fin t.card) : MeasurableSet (S ∩ ball (ζ j) δ) :=
      hS.measurableSet.inter measurableSet_ball
    simp only [P, disjointed_eq_inter_compl]
    exact (hm i).inter (.iInter fun j ↦ .iInter fun _ ↦ (hm j).compl)
  have hPd : Pairwise (Disjoint on P) := disjoint_disjointed _
  have hPU : ⋃ i, P i = S := by
    refine iUnion_disjointed.trans (Subset.antisymm (iUnion_subset fun _ ↦ inter_subset_left) ?_)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcover hx)
    refine mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, hx, ?_⟩
    simpa [ζ] using hxy
  refine ⟨t.card, ζ, fun i ↦ ∫ x in P i, a x ∂μ, hζS, fun φ η hφ hosc ↦ ?_⟩
  have hφP (i : Fin t.card) : IntegrableOn (fun x ↦ a x • φ x) (P i) μ :=
    hφ.mono_set ((hPsub i).trans inter_subset_left)
  have haP (i : Fin t.card) : IntegrableOn a (P i) μ :=
    ha.mono_set ((hPsub i).trans inter_subset_left)
  -- On each cell, the error is the integral of `a x • (φ x - φ (ζ i))`.
  have hcell (i : Fin t.card) :
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
