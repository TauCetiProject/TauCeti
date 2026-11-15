/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Parameter
import TauCeti.Analysis.Normed.Group.UniformContinuity
public import TauCeti.Probability.BrownianMotion.QuadraticVariation

/-!
# Spatial Taylor remainders along Brownian partitions with varying parameters

The spatial second-order remainder of a time-dependent function vanishes in probability
along every deterministic vanishing-mesh partition of a compact time interval. The spatial
slices are C² and their second derivatives are jointly continuous. Parameters can be arbitrary
deterministic tags in a compact set, not just the left endpoints of the partition.

No third spatial derivative, time derivative, growth bound, moment of the transformed
process, or filtration hypothesis is needed. This is the spatial-remainder passage in the
time-dependent Itô formula, not identification of its stochastic or time integrals.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProbabilityTheory.IsBrownianReal

/-- Spatial Taylor remainders with arbitrary deterministic compact-valued parameters vanish
in probability along Brownian partitions. Joint continuity is required of the spatial second
derivative, not second or mixed derivatives in the parameter. Repeated dates and empty grids
are allowed, and no nestedness or integrability of the transformed process is assumed. -/
theorem tendstoInMeasure_sum_sub_taylorWithinEval_two_param
    {Ω A : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [PseudoMetricSpace A] {s : Set A} (hs : IsCompact s)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {f : A → ℝ → ℝ}
    (hf : ∀ u ∈ s, ContDiff ℝ 2 (f u))
    (h₂ : ContinuousOn (fun p : A × ℝ ↦ iteratedDeriv 2 (f p.1) p.2) (s ×ˢ univ))
    {N : ℕ → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
    {a b : ℝ≥0} (ht : ∀ k, Monotone (grid k)) (ha : ∀ k, grid k 0 = a)
    (hb : ∀ k, grid k (Fin.last (N k)) = b) {δ : ℕ → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), (grid k i.succ : ℝ) - grid k i.castSucc ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0))
    (u : ∀ k, Fin (N k) → A) (hu : ∀ k i, u k i ∈ s) :
    TendstoInMeasure P (fun k ω ↦ ∑ i, (f (u k i) (B (grid k i.succ) ω) -
      taylorWithinEval (f (u k i)) 2 univ (B (grid k i.castSucc) ω)
        (B (grid k i.succ) ω))) atTop 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  -- Fixed-time measurability uses only continuity of each spatial slice and its derivatives.
  have hm (k : ℕ) : AEStronglyMeasurable (fun ω ↦ ∑ i, (f (u k i) (B (grid k i.succ) ω) -
      taylorWithinEval (f (u k i)) 2 univ (B (grid k i.castSucc) ω)
        (B (grid k i.succ) ω))) P := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    simp only [TauCeti.taylorWithinEval_univ_two]
    have hfi := hf _ (hu k i)
    have hX := (hB.aemeasurable (grid k i.castSucc)).aestronglyMeasurable
    have hY := (hB.aemeasurable (grid k i.succ)).aestronglyMeasurable
    have hfirst := (hfi.continuous_deriv (by norm_num)).comp_aestronglyMeasurable hX
    have hsecond := (hfi.deriv'.continuous_deriv_one).comp_aestronglyMeasurable hX
    exact (hfi.continuous.comp_aestronglyMeasurable hY).sub
      (((hfi.continuous.comp_aestronglyMeasurable hX).add (hfirst.mul (hY.sub hX))).add
        ((aestronglyMeasurable_const.mul hsecond).mul ((hY.sub hX).pow 2)))
  -- On a further subsequence the quadratic sums are bounded pathwise; localize the state
  -- to the compact image of that continuous sample path, rather than impose moment bounds.
  apply (exists_seq_tendstoInMeasure_atTop_iff hm).2
  intro φ hφ
  obtain ⟨ψ, hψ, hQ⟩ := ((hB.toIsPreBrownianReal.tendstoInMeasure_quadraticSum
    ht ha hb hmesh hδ).comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hB.cont, hQ] with ω hc hQω
  let k := fun j ↦ φ (ψ j)
  have hk : Tendsto k atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  obtain ⟨L, hL⟩ := (isCompact_Icc.image hc).bddBelow
  obtain ⟨R, hR⟩ := (isCompact_Icc.image hc).bddAbove
  have hgrid (j : ℕ) (i : Fin (N (k j) + 1)) : grid (k j) i ∈ Icc a b := by
    simpa only [ha, hb] using (ht (k j)).mapsTo_Icc ⟨Fin.zero_le i, Fin.le_last i⟩
  have hstate (j : ℕ) (i : Fin (N (k j) + 1)) : B (grid (k j) i) ω ∈ Icc L R :=
    ⟨hL ⟨_, hgrid j i, rfl⟩, hR ⟨_, hgrid j i, rfl⟩⟩
  -- Uniform continuity controls all increments simultaneously, even on nonnested grids.
  let d := fun j ↦ ‖fun i : Fin (N (k j)) ↦
    B (grid (k j) i.succ) ω - B (grid (k j) i.castSucc) ω‖
  have hd : Tendsto d atTop (𝓝 0) :=
    (isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn).tendsto_norm_sub_of_dist_le
      (Eventually.of_forall fun j i ↦ hgrid j i.castSucc)
      (Eventually.of_forall fun j i ↦ hgrid j i.succ)
      (Eventually.of_forall fun j i ↦ by
        rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by
          exact_mod_cast ht (k j) (Fin.castSucc_le_succ i)))]
        exact hmesh (k j) i) (hδ.comp hk)
  have hbound : ∀ᶠ j in atTop, ∑ i : Fin (N (k j)),
      (B (grid (k j) i.succ) ω - B (grid (k j) i.castSucc) ω) ^ 2 ≤ (b : ℝ) - a + 1 :=
    ((tendsto_order.1 hQω).2 _ (lt_add_one _)).mono fun j h ↦ by
      simpa only [Function.comp_apply, TauCeti.Probability.quadraticSum_def] using h.le
  exact TauCeti.tendsto_sum_sub_taylorWithinEval_two_param hs
    (fun v hv z _ ↦ (hf v hv).contDiffAt)
    (h₂.mono (prod_mono_right (subset_univ _)))
    (Eventually.of_forall fun j i ↦ hu _ i)
    (Eventually.of_forall fun j i ↦ hstate j i.castSucc)
    (Eventually.of_forall fun j i ↦ hstate j i.succ)
    (Eventually.of_forall fun j i ↦ by
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (fun i : Fin (N (k j)) ↦
          B (grid (k j) i.succ) ω - B (grid (k j) i.castSucc) ω) i) hd hbound

end ProbabilityTheory.IsBrownianReal
