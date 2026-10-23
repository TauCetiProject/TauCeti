/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.MetricSpace.PiNat
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Explicit metrics on weak-star compact sets

A sequence dense in the predual closed unit ball separates continuous linear functionals.
On a weak-star compact set, evaluation on that sequence is a topological embedding into a
countable product of scalar fields. Pulling back Mathlib's `PiCountable.metricSpace` gives
the explicit distance
`∑' n, min (2⁻¹ ^ n) ‖f (u n) - g (u n)‖`.

`WeakDual.metricSpaceOfDenseSeq` equips any weak-star compact set with this metric, keeping
its existing topology. In particular, all choices of dense sequence induce the same topology.
`StrongDual.weakStarClosedBallMetricSpace` uses `denseSeq` in the predual unit ball to supply
a metric on every dual closed ball when the predual is separable. No completeness of the
predual is needed. Convergence can be checked just on the chosen sequence, using
`WeakDual.tendsto_iff_forall_eval_denseSeq`.

The construction follows the usual proof of weak-star metrizability; see Megginson,
*An Introduction to Banach Space Theory*, §2.6. It uses Mathlib's countable-product metric
and Banach--Alaoglu theorem, rather than constructing another product metric.
-/

public section

noncomputable section

open Set Metric Topology Filter TopologicalSpace

namespace WeakDual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Continuous linear functionals agreeing on a sequence dense in the closed unit ball
are equal. -/
theorem ext_of_denseRange_unitBall {u : ℕ → closedBall (0 : E) 1} (hu : DenseRange u)
    {f g : WeakDual 𝕜 E} (h : ∀ n, f (u n) = g (u n)) : f = g := by
  have heq : ∀ x : closedBall (0 : E) 1, f x = g x :=
    congrFun (hu.equalizer ((map_continuous f).comp continuous_subtype_val)
      ((map_continuous g).comp continuous_subtype_val) (funext h))
  have hn : ‖toStrongDual f - toStrongDual g‖ ≤ 0 := by
    refine ContinuousLinearMap.opNorm_le_of_ball (ε := 1) zero_lt_one le_rfl ?_
    intro x hx
    simp [heq ⟨x, ball_subset_closedBall hx⟩]
  exact sub_eq_zero.mp ((toStrongDual f - toStrongDual g).opNorm_zero_iff'.mp
    (le_antisymm hn (norm_nonneg _)))

/-- Evaluation on a sequence dense in the predual unit ball embeds a weak-star compact set
into the countable product of scalar fields. -/
theorem isEmbedding_eval_denseSeq {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K)
    {u : ℕ → closedBall (0 : E) 1} (hu : DenseRange u) :
    Topology.IsEmbedding (fun f : K ↦ fun n ↦ (f : WeakDual 𝕜 E) (u n)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun f : K ↦ fun n ↦ (f : WeakDual 𝕜 E) (u n)) :=
    continuous_pi fun n ↦ (eval_continuous (u n : E)).comp continuous_subtype_val
  exact (hc.isClosedEmbedding fun f g hfg ↦
    Subtype.ext (ext_of_denseRange_unitBall hu (congrFun hfg))).isEmbedding

/-- The metric on a weak-star compact set obtained by evaluating on a sequence dense in the
predual closed unit ball. Its topology is the original weak-star subspace topology. This is
not a global instance, since the distance depends on the chosen sequence. -/
@[instance_reducible]
def metricSpaceOfDenseSeq {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K)
    {u : ℕ → closedBall (0 : E) 1} (hu : DenseRange u) : MetricSpace K := by
  letI : MetricSpace (ℕ → 𝕜) := PiCountable.metricSpace
  exact (isEmbedding_eval_denseSeq hK hu).comapMetricSpace _

/-- The distance is the convergent sum of the truncated evaluation distances. -/
theorem metricSpaceOfDenseSeq_dist {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K)
    {u : ℕ → closedBall (0 : E) 1} (hu : DenseRange u) (f g : K) :
    @dist K (metricSpaceOfDenseSeq hK hu).toDist f g =
      ∑' n : ℕ, min (2⁻¹ ^ n) ‖(f : WeakDual 𝕜 E) (u n) - (g : WeakDual 𝕜 E) (u n)‖ := by
  simp_rw [← dist_eq_norm]
  rfl

/-- Every dense sequence produces the existing weak-star topology. Thus the topology is
independent of the sequence used to define the metric. -/
@[simp]
theorem metricSpaceOfDenseSeq_toTopologicalSpace {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K)
    {u : ℕ → closedBall (0 : E) 1} (hu : DenseRange u) :
    (metricSpaceOfDenseSeq hK hu).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace K) := (rfl)

/-- On a weak-star compact set, convergence on a dense sequence in the predual unit ball
is equivalent to weak-star convergence, for any filter. -/
theorem tendsto_iff_forall_eval_denseSeq {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K)
    {u : ℕ → closedBall (0 : E) 1} (hu : DenseRange u)
    {ι : Type*} {l : Filter ι} {f : ι → K} {g : K} :
    Tendsto f l (𝓝 g) ↔
      ∀ n, Tendsto (fun i ↦ (f i : WeakDual 𝕜 E) (u n)) l
        (𝓝 ((g : WeakDual 𝕜 E) (u n))) :=
  (isEmbedding_eval_denseSeq hK hu).tendsto_nhds_iff.trans tendsto_pi_nhds

end WeakDual

namespace StrongDual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [ProperSpace 𝕜] [SeparableSpace E]

/-- An explicit metric for the weak-star topology of a dual closed ball, using a dense
sequence in the predual closed unit ball. The predual need not be complete. -/
@[instance_reducible]
def weakStarClosedBallMetricSpace (f : StrongDual 𝕜 E) (r : ℝ) :
    MetricSpace (WeakDual.toStrongDual ⁻¹' closedBall f r : Set (WeakDual 𝕜 E)) := by
  letI : Nonempty (closedBall (0 : E) 1) := ⟨⟨0, by simp⟩⟩
  exact WeakDual.metricSpaceOfDenseSeq (WeakDual.isCompact_closedBall f r)
    (denseRange_denseSeq (closedBall (0 : E) 1))

/-- The dual-ball distance uses the chosen dense sequence in the predual closed unit ball. -/
theorem weakStarClosedBallMetricSpace_dist (f : StrongDual 𝕜 E) (r : ℝ)
    (g h : (WeakDual.toStrongDual ⁻¹' closedBall f r : Set (WeakDual 𝕜 E))) :
    letI : Nonempty (closedBall (0 : E) 1) := ⟨⟨0, by simp⟩⟩
    @dist _ (weakStarClosedBallMetricSpace f r).toDist g h =
      ∑' n : ℕ, min (2⁻¹ ^ n)
        ‖(g : WeakDual 𝕜 E) (denseSeq (closedBall (0 : E) 1) n) -
          (h : WeakDual 𝕜 E) (denseSeq (closedBall (0 : E) 1) n)‖ := by
  let : Nonempty (closedBall (0 : E) 1) := ⟨⟨0, by simp⟩⟩
  exact WeakDual.metricSpaceOfDenseSeq_dist (WeakDual.isCompact_closedBall f r)
    (denseRange_denseSeq (closedBall (0 : E) 1)) g h

end StrongDual
