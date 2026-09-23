/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.CutNormLimit
public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.UnitIntervalModel
import TauCeti.MeasureTheory.OptimalTransport.Chain

/-!
# Completeness of unit-interval graphons

Strict graphons on the unit interval form a complete pseudometric space for the cut distance.
The realignment theorem below also makes a sequence of graphons with controlled consecutive
cut distances available on a common carrier with the same cut-norm control.

## Main results

* `TauCeti.DenseGraphLimits.exists_isProbabilityMeasure_cutNorm_comap_sub_lt` -- realigns a
  sequence of graphons onto one path-space carrier;
* `TauCeti.DenseGraphLimits.Graphon.instCompleteSpaceUnitInterval` -- completeness for the
  cut-distance pseudometric on unit-interval graphons.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Theorem 9.23.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Section 6 (cut distance through couplings).
* `TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Complete.lean`: the formal chain-measure
  gluing argument used as a model for realignment.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology unitInterval

namespace TauCeti

namespace DenseGraphLimits

section Realignment

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **Realignment of a sequence of graphons on one carrier.** If consecutive terms of a sequence of
graphons on a standard Borel carrier are within cut distance `ε n`, then there is a probability
measure `P` on the path space `ℕ → Ω`, whose every coordinate projection is measure preserving onto
`μ`, along which the pulled-back terms are consecutively within `ε n` in cut norm.

Each pulled-back term is at cut distance zero from the original one (`cutDist_comap_right`), so the
sequence is unchanged up to cut distance, but now lives on one carrier, where the cut norm of a
difference is available. -/
theorem exists_isProbabilityMeasure_cutNorm_comap_sub_lt (W : ℕ → Graphon Ω μ) {ε : ℕ → ℝ}
    (hW : ∀ n, cutDist (W n) (W (n + 1)) < ε n) :
    ∃ (P : Measure (ℕ → Ω)) (_ : IsProbabilityMeasure P),
      (∀ n, MeasurePreserving (fun x : ℕ → Ω => x n) P μ) ∧
      ∀ n, cutNorm P ((W n).toSymmKernel.comap (fun x => x n) (measurable_pi_apply n) P -
        (W (n + 1)).toSymmKernel.comap (fun x => x (n + 1)) (measurable_pi_apply (n + 1)) P) <
          ε n := by
  choose π hπ hlt using fun n => exists_isCoupling_cutNorm_lt (W n) (W (n + 1)) (hW n)
  have : ∀ n, IsProbabilityMeasure (π n) := fun n => (hπ n).isProbabilityMeasure
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  -- Glue the chosen couplings of consecutive terms into one law on the path space.
  set P : Measure (ℕ → Ω) := TauCeti.Measure.chainMeasure (X := fun _ => Ω) π
  have hmatch : ∀ n, (π n).snd = (π (n + 1)).fst := fun n => by
    rw [(hπ n).snd_eq, (hπ (n + 1)).fst_eq]
  have hpair : ∀ n, MeasurePreserving (fun x : ℕ → Ω => (x n, x (n + 1))) P (π n) := fun n =>
    ⟨by fun_prop, TauCeti.Measure.map_adjacent_chainMeasure π hmatch n⟩
  refine ⟨P, inferInstance, fun n => ⟨measurable_pi_apply n, ?_⟩, fun n => ?_⟩
  · rw [TauCeti.Measure.map_eval_chainMeasure π hmatch n, (hπ n).fst_eq]
  · rw [← cutNorm_overlayDiff_map_prodMk (W n) (W (n + 1)) _ _ (hpair n)]
    exact hlt n

end Realignment

section Complete

/-- If consecutive differences of a sequence of kernels are bounded by `2⁻ⁿ` in cut norm, then
the term `n` is within `2 * 2⁻ⁿ` in cut norm of every later term. -/
private theorem cutNorm_sub_le_of_cutNorm_sub_succ_lt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (K : ℕ → SymmKernel Ω μ)
    (hK : ∀ n, cutNorm μ (K n - K (n + 1)) < (1 / 2) ^ n) (n k : ℕ) :
    cutNorm μ (K n - K (n + k)) ≤ 2 * (1 / 2) ^ n := by
  suffices h : cutNorm μ (K n - K (n + k)) ≤ 2 * (1 / 2) ^ n - 2 * (1 / 2) ^ (n + k) by
    have : (0 : ℝ) ≤ 2 * (1 / 2) ^ (n + k) := by positivity
    linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := cutNorm_sub_le_cutNorm_sub_add_cutNorm_sub μ (K n) (K (n + k)) (K (n + k + 1))
    have hlast := hK (n + k)
    rw [← add_assoc]
    have hpow : (1 / 2 : ℝ) ^ (n + k + 1) = (1 / 2) ^ (n + k) / 2 := by
      rw [pow_succ]
      ring
    rw [hpow]
    linarith

/-- **Completeness of unit-interval graphons.** Every Cauchy sequence of strict graphons on the
unit interval converges in cut distance to a strict unit-interval graphon. -/
instance Graphon.instCompleteSpaceUnitInterval :
    CompleteSpace (Graphon I (volume : Measure I)) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2 : ℝ) ^ n)
    (fun n => by positivity) fun u hu => ?_
  have hstep : ∀ n, cutDist (u n) (u (n + 1)) < (1 / 2) ^ n := fun n => by
    simpa using hu n n (n + 1) le_rfl n.le_succ
  obtain ⟨P, _, hP, hPlt⟩ := exists_isProbabilityMeasure_cutNorm_comap_sub_lt u hstep
  set V : ℕ → Graphon (ℕ → I) P := fun n => (u n).comap (fun x => x n) (measurable_pi_apply n) P
  have hVlt : ∀ n, cutNorm P ((V n).toSymmKernel - (V (n + 1)).toSymmKernel) < (1 / 2) ^ n :=
    fun n => by simpa only [V, Graphon.toSymmKernel_comap] using hPlt n
  -- The realigned sequence is Cauchy in cut norm.
  have hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      cutNorm P ((V m).toSymmKernel - (V n).toSymmKernel) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hbound := cutNorm_sub_le_of_cutNorm_sub_succ_lt (fun n => (V n).toSymmKernel) hVlt N
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hn
    calc cutNorm P ((V (N + k)).toSymmKernel - (V (N + l)).toSymmKernel)
        ≤ cutNorm P ((V (N + k)).toSymmKernel - (V N).toSymmKernel) +
            cutNorm P ((V N).toSymmKernel - (V (N + l)).toSymmKernel) :=
          cutNorm_sub_le_cutNorm_sub_add_cutNorm_sub P _ _ _
      _ ≤ 2 * (1 / 2) ^ N + 2 * (1 / 2) ^ N := by
          rw [cutNorm_sub_rev]
          exact add_le_add (hbound k) (hbound l)
      _ < ε := by linarith
  obtain ⟨U, hU⟩ := exists_graphon_tendsto_cutNorm_of_cauchy_cutNorm V hcauchy
  obtain ⟨X, hX⟩ := exists_graphon_unitInterval_cutDist_eq_zero U
  refine ⟨X, tendsto_iff_dist_tendsto_zero.2 <|
    squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hU⟩
  -- `u n` is at cut distance zero from its realignment `V n`, and `U` from `X`.
  have huV : cutDist (u n) (V n) = 0 := by
    rw [cutDist_comap_right (u n) (u n) (hP n), cutDist_self]
  calc dist (u n) X = cutDist (u n) X := Graphon.dist_eq_cutDist _ _
    _ ≤ cutDist (u n) (V n) + cutDist (V n) X := cutDist_triangle _ _ _
    _ ≤ cutDist (u n) (V n) + (cutDist (V n) U + cutDist U X) :=
        add_le_add le_rfl (cutDist_triangle _ _ _)
    _ ≤ cutNorm P ((V n).toSymmKernel - U.toSymmKernel) := by
        rw [huV, hX, zero_add, add_zero]
        exact cutDist_le_cutNorm_sub _ _

end Complete

end DenseGraphLimits

end TauCeti
