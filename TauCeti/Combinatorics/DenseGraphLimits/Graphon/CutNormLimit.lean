/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Approximation
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.CutNorm
import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Energy

/-!
# Cut-norm limits of graphon sequences

On a countably generated probability carrier, a sequence of graphons that is Cauchy in the cut
norm converges in the cut norm to a graphon: the space of graphons on a fixed such carrier is
complete for the cut norm.

The limit is built from block averages.  Along the canonical refining finite partitions of the
carrier, the block averages of a cut-norm Cauchy sequence converge blockwise, because each block
average is a cut-norm Lipschitz function of the graphon.  The limiting block values define a
sequence of step graphons which is a bounded martingale for the square filtration of the canonical
partitions, hence converges almost everywhere and in `L¹`; its limit, symmetrised and clamped, is
the limiting graphon.  The cut-norm convergence of the original sequence then follows from the
cut-norm contraction of block averaging, which makes the block approximation uniform along the
Cauchy sequence.

This is the analytic input to the compactness of the space of graphons: after the terms of a
Cauchy sequence in cut distance have been realised on one carrier, this theorem supplies the
limit.

## Main result

* `TauCeti.DenseGraphLimits.exists_graphon_tendsto_cutNorm_of_cauchy_cutNorm` -- a cut-norm
  Cauchy sequence of graphons converges in cut norm to a graphon.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.3.
* L. Lovász and B. Szegedy, *Szemerédi's Lemma for the Analyst*, GAFA 17 (2007), §5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

namespace TauCeti.DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

section LimitStep

variable (V : ℕ → Graphon Ω μ)

/-- The limit of the block averages of the sequence over a block of the level-`n` canonical
partition, as a point of `[0, 1]`; meaningful once the block averages converge. -/
private def limitBlock (n : ℕ) (p q : (Finpartition.countablePartition Ω n).parts) :
    Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one
    (limUnder atTop fun k => (blockAverage (Finpartition.countablePartition Ω n) (V k) p q : ℝ))

private theorem limitBlock_comm (n : ℕ) (p q : (Finpartition.countablePartition Ω n).parts) :
    limitBlock V n p q = limitBlock V n q p := by
  simp only [limitBlock, blockAverage_comm]

/-- The step graphon of the limiting block values on the level-`n` canonical partition. -/
private def limitStep (n : ℕ) : Graphon Ω μ :=
  stepGraphon (Finpartition.countablePartition Ω n)
    (fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp)
    (limitBlock V n) (limitBlock_comm V n)

/-- Along a cut-norm Cauchy sequence, every block average converges to the limiting block value.
-/
private theorem tendsto_blockAverage_limitBlock
    (hV : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      cutNorm μ ((V m).toSymmKernel - (V n).toSymmKernel) < ε)
    (n : ℕ) (p q : (Finpartition.countablePartition Ω n).parts) :
    Tendsto (fun k => (blockAverage (Finpartition.countablePartition Ω n) (V k) p q : ℝ)) atTop
      (𝓝 (limitBlock V n p q)) := by
  set c : ℝ := (μ.real (p : Set Ω) * μ.real (q : Set Ω))⁻¹
  have hc0 : 0 ≤ c := by positivity
  have hcauchy :
      CauchySeq fun k => (blockAverage (Finpartition.countablePartition Ω n) (V k) p q : ℝ) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hV (ε / (c + 1)) (by positivity)
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [Real.dist_eq]
    calc |(blockAverage (Finpartition.countablePartition Ω n) (V i) p q : ℝ) -
          blockAverage (Finpartition.countablePartition Ω n) (V j) p q|
        ≤ c * cutNorm μ ((V i).toSymmKernel - (V j).toSymmKernel) :=
          abs_blockAverage_sub_blockAverage_le _
            (fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp) _ _ p q
      _ ≤ c * (ε / (c + 1)) := by gcongr; exact (hN i hi j hj).le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxmem : x ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall fun k =>
      (blockAverage (Finpartition.countablePartition Ω n) (V k) p q).property)
  have hlim : limitBlock V n p q = ⟨x, hxmem⟩ := by
    rw [limitBlock, hx.limUnder_eq, Set.projIcc_of_mem]
  rw [hlim]
  exact hx

/-- Along a cut-norm Cauchy sequence, the level-`n` block averages converge in cut norm to the
limiting step graphon. -/
private theorem tendsto_cutNorm_countableStepGraphonAvg_sub_limitStep
    (hV : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      cutNorm μ ((V m).toSymmKernel - (V n).toSymmKernel) < ε) (n : ℕ) :
    Tendsto (fun k => cutNorm μ ((countableStepGraphonAvg (V k) n).toSymmKernel -
      (limitStep V n).toSymmKernel)) atTop (𝓝 0) := by
  set P := Finpartition.countablePartition Ω n
  have hsum : Tendsto (fun k => ∑ p : P.parts, ∑ q : P.parts,
      |(blockAverage P (V k) p q : ℝ) - limitBlock V n p q|) atTop (𝓝 0) := by
    have h := fun p q : P.parts =>
      ((tendsto_blockAverage_limitBlock V hV n p q).sub_const (limitBlock V n p q : ℝ)).abs
    simpa using tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ => h p q
  refine squeeze_zero (fun _ => cutNorm_nonneg μ _) (fun k => ?_) hsum
  refine cutNorm_le_of_forall_abs_le μ _ fun x y => ?_
  have hx := P.indexedPartition.mem_index x
  have hy := P.indexedPartition.mem_index y
  have h₁ : countableStepGraphonAvg (V k) n x y =
      (blockAverage P (V k) (P.indexedPartition.index x) (P.indexedPartition.index y) : ℝ) :=
    (countableStepGraphonAvg_apply (V k) n x y).trans
      ((stepGraphonAvg_apply _ _ _ hx hy).trans (coe_blockAverage _ _ _ _).symm)
  have h₂ : limitStep V n x y =
      limitBlock V n (P.indexedPartition.index x) (P.indexedPartition.index y) :=
    stepGraphon_apply _ _ _ _ hx hy
  rw [SymmKernel.coe_sub, Pi.sub_apply, Pi.sub_apply, Graphon.coe_toSymmKernel,
    Graphon.coe_toSymmKernel, h₁, h₂]
  calc |(blockAverage P (V k) (P.indexedPartition.index x) (P.indexedPartition.index y) : ℝ) -
        limitBlock V n (P.indexedPartition.index x) (P.indexedPartition.index y)|
      ≤ ∑ q : P.parts, |(blockAverage P (V k) (P.indexedPartition.index x) q : ℝ) -
          limitBlock V n (P.indexedPartition.index x) q| :=
        Finset.single_le_sum (f := fun q => |(blockAverage P (V k) (P.indexedPartition.index x) q :
          ℝ) - limitBlock V n (P.indexedPartition.index x) q|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ _)
    _ ≤ ∑ p : P.parts, ∑ q : P.parts, |(blockAverage P (V k) p q : ℝ) - limitBlock V n p q| :=
        Finset.single_le_sum (f := fun p => ∑ q : P.parts,
          |(blockAverage P (V k) p q : ℝ) - limitBlock V n p q|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

/-- The limiting step graphons are consistent under block averaging: averaging the level-`n + 1`
limit over the level-`n` partition gives the level-`n` limit. -/
private theorem stepGraphonAvg_limitStep_succ
    (hV : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      cutNorm μ ((V m).toSymmKernel - (V n).toSymmKernel) < ε) (n : ℕ) :
    stepGraphonAvg (μ := μ) (Finpartition.countablePartition Ω n)
      (fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp)
      (limitStep V (n + 1)) = limitStep V n := by
  set P := Finpartition.countablePartition Ω n
  set hP : ∀ p ∈ P.parts, MeasurableSet p :=
    fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp
  have hle : Finpartition.countablePartition Ω (n + 1) ≤ P :=
    Finpartition.countablePartition_antitone Ω (Nat.le_succ n)
  rw [stepGraphonAvg_def]
  refine (stepGraphon_inj P hP _ (limitBlock V n) _ (limitBlock_comm V n)).2 ?_
  funext p q
  apply Subtype.ext
  set c : ℝ := (μ.real (p : Set Ω) * μ.real (q : Set Ω))⁻¹
  -- The level-`n` block averages of the level-`n + 1` block averages are those of the sequence.
  have hsame : ∀ k, (blockAverage P (countableStepGraphonAvg (V k) (n + 1)) p q : ℝ) =
      blockAverage P (V k) p q := by
    intro k
    rw [coe_blockAverage_eq_inv_mul_rectIntegral, coe_blockAverage_eq_inv_mul_rectIntegral,
      countableStepGraphonAvg_def, stepGraphonAvg_rectIntegral_of_le_of_le μ p q _ hle hle]
  have h₁ : Tendsto (fun k => (blockAverage P (countableStepGraphonAvg (V k) (n + 1)) p q : ℝ))
      atTop (𝓝 (limitBlock V n p q)) :=
    (tendsto_blockAverage_limitBlock V hV n p q).congr fun k => (hsame k).symm
  -- They also converge to the block average of the level-`n + 1` limit, by the Lipschitz bound.
  have h₂ : Tendsto (fun k => (blockAverage P (countableStepGraphonAvg (V k) (n + 1)) p q : ℝ))
      atTop (𝓝 (blockAverage P (limitStep V (n + 1)) p q)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 := (tendsto_cutNorm_countableStepGraphonAvg_sub_limitStep V hV (n + 1)).const_mul c
    rw [mul_zero] at h0
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h0
    rw [Real.norm_eq_abs]
    exact abs_blockAverage_sub_blockAverage_le P hP _ _ p q
  exact tendsto_nhds_unique h₂ h₁

private theorem stronglyMeasurable_limitStep (n : ℕ) :
    StronglyMeasurable[TauCeti.MeasureTheory.countableSquareFiltration Ω n]
      (fun z : Ω × Ω => limitStep V n z.1 z.2) := by
  rw [TauCeti.MeasureTheory.countableSquareFiltration_eq_comap]
  exact stronglyMeasurable_comap_stepGraphon _ _ _ _

/-- The limiting step graphons form a martingale for the square filtration of the canonical
partitions. -/
private theorem martingale_limitStep
    (hV : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      cutNorm μ ((V m).toSymmKernel - (V n).toSymmKernel) < ε) :
    Martingale (fun n (z : Ω × Ω) => limitStep V n z.1 z.2)
      (TauCeti.MeasureTheory.countableSquareFiltration Ω) (μ.prod μ) := by
  refine martingale_nat (fun n => stronglyMeasurable_limitStep V n)
    (fun n => (limitStep V n).toSymmKernel.integrable_uncurry μ) fun n => ?_
  rw [TauCeti.MeasureTheory.countableSquareFiltration_eq_comap]
  have h := stepGraphonAvg_ae_eq_condExp (Finpartition.countablePartition Ω n)
    (fun _ hp => Finpartition.measurableSet_of_mem_countablePartition Ω n hp)
    (limitStep V (n + 1))
  rwa [stepGraphonAvg_limitStep_succ V hV n] at h

/-- The limiting step graphons are uniformly bounded by one, hence uniformly integrable. -/
private theorem uniformIntegrable_limitStep :
    UniformIntegrable (fun n (z : Ω × Ω) => limitStep V n z.1 z.2) 1 (μ.prod μ) := by
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (limitStep V n).measurable.aestronglyMeasurable) fun ε _ => ⟨2, fun n => ?_⟩
  have hempty : {z : Ω × Ω | (2 : ℝ≥0) ≤ ‖limitStep V n z.1 z.2‖₊} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun z hz => ?_
    have hz' : (2 : ℝ≥0) ≤ ‖limitStep V n z.1 z.2‖₊ := hz
    have h1 : ‖limitStep V n z.1 z.2‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
      exact abs_le.2 ⟨by linarith [(limitStep V n).nonneg z.1 z.2], (limitStep V n).le_one z.1 z.2⟩
    exact absurd (hz'.trans h1) (by norm_num)
  simp [hempty]

end LimitStep

/-- **Cut-norm Cauchy sequences of graphons converge in cut norm.** On a countably generated
probability carrier, a sequence of graphons that is Cauchy for the cut norm has a graphon limit
in the cut norm.  Together with the realisation of cut-distance Cauchy sequences on one carrier,
this is the analytic input to the compactness of the space of graphons. -/
theorem exists_graphon_tendsto_cutNorm_of_cauchy_cutNorm (V : ℕ → Graphon Ω μ)
    (hV : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      cutNorm μ ((V m).toSymmKernel - (V n).toSymmKernel) < ε) :
    ∃ U : Graphon Ω μ,
      Tendsto (fun n => cutNorm μ ((V n).toSymmKernel - U.toSymmKernel)) atTop (𝓝 0) := by
  set ℱ := TauCeti.MeasureTheory.countableSquareFiltration Ω
  set A : ℕ → Ω × Ω → ℝ := fun n z => limitStep V n z.1 z.2 with hA
  set U₀ : Ω × Ω → ℝ := ℱ.limitProcess A (μ.prod μ)
  have hmart := martingale_limitStep V hV
  have hUI := uniformIntegrable_limitStep V
  have hL1 : Tendsto (fun n => (eLpNorm (A n - U₀) 1 (μ.prod μ)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hmart.submartingale.tendsto_eLpNorm_one_limitProcess hUI)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h
  have hae : ∀ᵐ z ∂(μ.prod μ), Tendsto (fun n => A n z) atTop (𝓝 (U₀ z)) :=
    hmart.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hUI
  have hU₀meas : Measurable U₀ := Filtration.stronglyMeasurable_limit_process'.measurable
  -- The strict limiting graphon: the martingale limit, symmetrised and clamped to `[0, 1]`.
  set U : Graphon Ω μ := Graphon.clampSymm μ (fun x y => U₀ (x, y))
    (hU₀meas.comp (measurable_fst.prodMk measurable_snd))
  have hUae : (fun z : Ω × Ω => U z.1 z.2) =ᵐ[μ.prod μ] U₀ := by
    have hswap : ∀ᵐ z ∂(μ.prod μ), Tendsto (fun n => A n z.swap) atTop (𝓝 (U₀ z.swap)) :=
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hae
    filter_upwards [hae, hswap] with z hz hzs
    rcases z with ⟨x, y⟩
    have hmem : U₀ (x, y) ∈ Set.Icc (0 : ℝ) 1 :=
      isClosed_Icc.mem_of_tendsto hz (Eventually.of_forall fun n => (limitStep V n).mem_Icc x y)
    have hsymm : U₀ (x, y) = U₀ (y, x) := by
      refine tendsto_nhds_unique hz (hzs.congr fun n => ?_)
      simp only [hA, Prod.swap_prod_mk, Graphon.symm]
    exact Graphon.clampSymm_apply_of_symm_of_mem μ _ _ hsymm hmem
  refine ⟨U, ?_⟩
  -- The limiting step graphons converge to `U` in cut norm.
  have hAU : Tendsto (fun n => cutNorm μ ((limitStep V n).toSymmKernel - U.toSymmKernel)) atTop
      (𝓝 0) := by
    refine squeeze_zero (fun _ => cutNorm_nonneg μ _) (fun n => ?_) hL1
    refine (cutNorm_le_toReal_eLpNorm μ _).trans (le_of_eq ?_)
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hUae] with z hz
    simp only [SymmKernel.coe_sub, Pi.sub_apply, Graphon.coe_toSymmKernel, hA, hz]
  -- The cut-norm bound `cutNorm_le_toReal_eLpNorm` in the form the `L¹` block approximation gives.
  have hVE : ∀ N, Tendsto (fun n => cutNorm μ ((V N).toSymmKernel -
      (countableStepGraphonAvg (V N) n).toSymmKernel)) atTop (𝓝 0) := by
    intro N
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_eLpNorm_countableStepGraphonAvg (V N))
    simp only [Function.comp_def, ENNReal.toReal_zero] at h
    refine squeeze_zero (fun _ => cutNorm_nonneg μ _) (fun n => ?_) h
    refine (cutNorm_le_toReal_eLpNorm μ _).trans (le_of_eq ?_)
    rw [← eLpNorm_neg]
    congr 2
    funext z
    simp only [SymmKernel.coe_sub, Pi.sub_apply, Pi.neg_apply, Graphon.coe_toSymmKernel, neg_sub]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h5 : (0 : ℝ) < ε / 5 := by positivity
  obtain ⟨N, hN⟩ := hV (ε / 5) h5
  -- Fix a level `M` at which `V N` is well approximated by its block averages and the limiting
  -- step graphon is close to `U`, then a late index `K` whose block averages are close to that
  -- limiting step graphon.
  obtain ⟨M, hM₁, hM₂⟩ := (((hVE N).eventually_lt_const h5).and (hAU.eventually_lt_const h5)).exists
  have hK := (tendsto_cutNorm_countableStepGraphonAvg_sub_limitStep V hV M).eventually_lt_const h5
  obtain ⟨K, hK₁, hKN⟩ := (hK.and (eventually_ge_atTop N)).exists
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (cutNorm_nonneg μ _)]
  have hcontr : cutNorm μ ((countableStepGraphonAvg (V N) M).toSymmKernel -
      (countableStepGraphonAvg (V K) M).toSymmKernel) < ε / 5 := by
    rw [countableStepGraphonAvg_def, countableStepGraphonAvg_def]
    exact (cutNorm_stepGraphonAvg_sub_stepGraphonAvg_le _ _ _ _).trans_lt (hN N le_rfl K hKN)
  calc cutNorm μ ((V n).toSymmKernel - U.toSymmKernel)
      ≤ cutNorm μ ((V n).toSymmKernel - (V N).toSymmKernel) +
          cutNorm μ ((V N).toSymmKernel - U.toSymmKernel) :=
        cutNorm_sub_le_cutNorm_sub_add_cutNorm_sub μ _ _ _
    _ ≤ cutNorm μ ((V n).toSymmKernel - (V N).toSymmKernel) +
          (cutNorm μ ((V N).toSymmKernel - (countableStepGraphonAvg (V N) M).toSymmKernel) +
            (cutNorm μ ((countableStepGraphonAvg (V N) M).toSymmKernel -
                (countableStepGraphonAvg (V K) M).toSymmKernel) +
              (cutNorm μ ((countableStepGraphonAvg (V K) M).toSymmKernel -
                  (limitStep V M).toSymmKernel) +
                cutNorm μ ((limitStep V M).toSymmKernel - U.toSymmKernel)))) := by
        gcongr
        refine (cutNorm_sub_le_cutNorm_sub_add_cutNorm_sub μ _ _ _).trans (add_le_add le_rfl
          ((cutNorm_sub_le_cutNorm_sub_add_cutNorm_sub μ _ _ _).trans
            (add_le_add le_rfl (cutNorm_sub_le_cutNorm_sub_add_cutNorm_sub μ _ _ _))))
    _ < ε / 5 + (ε / 5 + (ε / 5 + (ε / 5 + ε / 5))) := by
        gcongr
        exact hN n hn N le_rfl
    _ = ε := by ring

end TauCeti.DenseGraphLimits
