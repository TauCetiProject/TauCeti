/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Projection
public import TauCeti.MeasureTheory.Measure.Decomposition.Prod
public import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
public import TauCeti.MeasureTheory.MeasurableSpace.Metric
public import TauCeti.MeasureTheory.OptimalTransport.Compactness
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.Basic

/-!
# The zero-temperature limit of entropic optimal transport

As the temperature `ε` decreases to `0`, the entropically regularised transport cost
`TauCeti.entropicTransportCost c ε μ ν`, the infimum of `∫⁻ c dπ + ε * klDiv π (μ ⊗ ν)` over the
couplings `π` of `μ` and `ν`, decreases. This file identifies its limit and shows that limits of
entropic optimizers are optimal transport plans.

The limit is always the infimum of `∫⁻ c dπ` over the couplings `π` of **finite** relative entropy
with respect to `μ ⊗ ν`. This holds with no hypothesis on the cost or the spaces; it can be
strictly larger than the transport cost, for instance for two copies of the uniform law on
`[0, 1]` and the cost `0` on the diagonal and `∞` off it, where the only coupling of finite cost is
the diagonal one, which is singular with respect to `μ ⊗ ν`.

The limit is the transport cost as soon as the cost can be discretised: if for every `η > 0` there
are finite measurable partitions of `X` and `Y` such that `c` varies by at most `η` on each product
cell, then every coupling `π` is approximated by a coupling of finite relative entropy that costs
at most `η` per unit of mass more. That coupling is the *block approximation* of `π`: on each
product cell `A × B` it has the mass `π (A × B)`, spread proportionally to `μ ⊗ ν`. It is the
relative-entropy projection `(μ.prod ν).fitLaw Q (π.map Q)` of `μ ⊗ ν` onto the measures with the
same cell masses as `π`, where `Q` sends a point to its cell, so its relative entropy is that of a
discrete law on finitely many cells. A uniformly continuous real cost on totally bounded
pseudometric spaces, and in particular a continuous one on compact spaces, can be discretised.

## Main statements

* `TauCeti.IsCoupling.isCoupling_fitLaw_prodMap`: the projection of `μ ⊗ ν` onto the measures with
  the cell masses of a coupling `π`, along product maps `p` and `q`, is again a coupling of `μ` and
  `ν`.
* `TauCeti.IsCoupling.exists_isCoupling_klDiv_ne_top_map_prodMap_eq`: for measurable maps to
  finite types, every coupling has the cell masses of a coupling of finite relative entropy.
* `TauCeti.IsCoupling.exists_isCoupling_klDiv_ne_top_lintegral_le`: if the cost varies by at most
  `η` on every cell, that coupling costs at most `η * μ univ` more.
* `TauCeti.iInf_entropicTransportCost` and `TauCeti.tendsto_entropicTransportCost_nhdsGT_zero`: as
  `ε → 0⁺`, the regularised cost decreases to the infimum of the costs of the couplings of finite
  relative entropy.
* `TauCeti.tendsto_entropicTransportCost_transportCost`: for a cost that can be discretised, the
  limit is the transport cost;
  `TauCeti.tendsto_entropicTransportCost_transportCost_of_uniformContinuous` and
  `TauCeti.tendsto_entropicTransportCost_transportCost_of_continuous` are the totally bounded and
  compact cases.
* `TauCeti.isOptimalCoupling_of_tendsto_of_entropicTransportCost`: when the values converge to the
  transport cost and the cost is lower semicontinuous, every weak limit of entropic optimizers at
  temperatures `ε → 0⁺` is an optimal transport plan.

## References

* G. Carlier, V. Duval, G. Peyré, B. Schmitzer, *Convergence of entropic schemes for optimal
  transport and gradient flows*, SIAM J. Math. Anal. 49 (2017), 1385–1418, for the block
  approximation of a coupling and the convergence of entropic transport as `ε → 0`.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probability 3 (1975), 146–158, for the relative-entropy projection onto prescribed cell
  masses.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}

/-! ### The block approximation of a coupling -/

section BlockApproximation

variable {ι κ : Type*} [MeasurableSpace ι] [MeasurableSpace κ] {p : X → ι} {q : Y → κ}

/-- **The block approximation is a coupling.** Let `π` couple finite measures `μ` and `ν`, and let
`p` and `q` be measurable maps to the cell labels. If the cell masses of `π` are absolutely
continuous with respect to those of `μ ⊗ ν`, the relative-entropy projection of `μ ⊗ ν` onto the
measures with the cell masses of `π` is again a coupling of `μ` and `ν`. On each cell it is
`μ ⊗ ν` rescaled to the mass that `π` gives the cell. -/
theorem IsCoupling.isCoupling_fitLaw_prodMap [IsFiniteMeasure μ] (hπ : IsCoupling π μ ν)
    (hp : Measurable p) (hq : Measurable q)
    (hac : π.map (Prod.map p q) ≪ (μ.prod ν).map (Prod.map p q)) :
    IsCoupling ((μ.prod ν).fitLaw (Prod.map p q) (π.map (Prod.map p q))) μ ν := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  have hQ : Measurable (Prod.map p q) := hp.prodMap hq
  have hn : (μ.prod ν).map (Prod.map p q) = (μ.map p).prod (ν.map q) :=
    (Measure.map_prod_map μ ν hp hq).symm
  rw [hn] at hac
  -- The cell masses of `π` have the cell masses of `μ` and `ν` as marginals.
  have hfst : (π.map (Prod.map p q)).fst = μ.map p := Measure.ext fun T hT ↦ by
    rw [Measure.fst_apply hT, ← prod_univ, Measure.map_apply hQ (hT.prod MeasurableSet.univ),
      preimage_prod_map_prod, preimage_univ, hπ.measure_prod_univ (hp hT),
      Measure.map_apply hp hT]
  have hsnd : (π.map (Prod.map p q)).snd = ν.map q := Measure.ext fun T hT ↦ by
    rw [Measure.snd_apply hT, ← univ_prod, Measure.map_apply hQ (MeasurableSet.univ.prod hT),
      preimage_prod_map_prod, preimage_univ, hπ.measure_univ_prod (hq hT),
      Measure.map_apply hq hT]
  have hA := ae_of_ae_map hp.aemeasurable (Measure.ae_lintegral_rnDeriv_prod_right_eq_one hfst hac)
  have hB := ae_of_ae_map hq.aemeasurable (Measure.ae_lintegral_rnDeriv_prod_left_eq_one hsnd hac)
  have hd : Measurable fun z : X × Y ↦
      (π.map (Prod.map p q)).rnDeriv ((μ.map p).prod (ν.map q)) (Prod.map p q z) :=
    (Measure.measurable_rnDeriv _ _).comp hQ
  refine isCoupling_of_measure_prod_univ_of_measure_univ_prod (fun S hS ↦ ?_) (fun S hS ↦ ?_)
  · rw [Measure.fitLaw_def, hn, withDensity_apply _ (hS.prod MeasurableSet.univ),
      setLIntegral_prod _ hd.aemeasurable, Measure.restrict_univ]
    rw [← setLIntegral_one]
    refine setLIntegral_congr_fun_ae hS (hA.mono fun x hx _ ↦ ?_)
    rw [← hx, lintegral_map ?_ hq]
    · simp only [Prod.map_apply]
    · exact (Measure.measurable_rnDeriv _ _).comp measurable_prodMk_left
  · rw [Measure.fitLaw_def, hn, withDensity_apply _ (MeasurableSet.univ.prod hS),
      ← Measure.prod_restrict, lintegral_prod_symm _ hd.aemeasurable, Measure.restrict_univ]
    rw [← setLIntegral_one]
    refine setLIntegral_congr_fun_ae hS (hB.mono fun y hy _ ↦ ?_)
    rw [← hy, lintegral_map ?_ hp]
    · simp only [Prod.map_apply]
    · exact (Measure.measurable_rnDeriv _ _).comp measurable_prodMk_right

variable [Finite ι] [Finite κ] [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]

/-- **Couplings of finite relative entropy with prescribed cell masses.** For measurable maps `p`
and `q` to finite types, every coupling `π` of finite measures `μ` and `ν` has the same cell masses
as some coupling of `μ` and `ν` of finite relative entropy with respect to `μ ⊗ ν`: its block
approximation. -/
theorem IsCoupling.exists_isCoupling_klDiv_ne_top_map_prodMap_eq [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) (hp : Measurable p) (hq : Measurable q) :
    ∃ σ, IsCoupling σ μ ν ∧ klDiv σ (μ.prod ν) ≠ ∞ ∧
      σ.map (Prod.map p q) = π.map (Prod.map p q) := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  have hQ : Measurable (Prod.map p q) := hp.prodMap hq
  -- A cell of `μ ⊗ ν`-mass zero has `μ`- or `ν`-mass zero in one factor, so `π` does not charge it.
  have hac : π.map (Prod.map p q) ≪ (μ.prod ν).map (Prod.map p q) := fun S hS ↦ by
    rw [← biUnion_of_singleton S, measure_biUnion_null_iff S.to_countable] at hS ⊢
    rintro ⟨i, j⟩ hij
    have h0 := hS (i, j) hij
    rw [Measure.map_apply hQ (measurableSet_singleton _), ← singleton_prod_singleton,
      preimage_prod_map_prod, Measure.prod_prod, mul_eq_zero] at h0
    rw [Measure.map_apply hQ (measurableSet_singleton _), ← singleton_prod_singleton,
      preimage_prod_map_prod]
    rcases h0 with h0 | h0
    · refine measure_mono_null (prod_mono subset_rfl (subset_univ _)) ?_
      rwa [hπ.measure_prod_univ (hp (measurableSet_singleton i))]
    · refine measure_mono_null (prod_mono (subset_univ _) subset_rfl) ?_
      rwa [hπ.measure_univ_prod (hq (measurableSet_singleton j))]
  refine ⟨_, hπ.isCoupling_fitLaw_prodMap hp hq hac, ?_,
    Measure.map_fitLaw_of_absolutelyContinuous hQ hac⟩
  rw [klDiv_fitLaw hQ hac]
  exact klDiv_ne_top hac Integrable.of_finite

/-- **Block approximation of the cost.** If the cost varies by at most `η` on every product cell
of measurable maps `p` and `q` to finite types, then every coupling `π` of finite measures `μ` and
`ν` is approximated by a coupling of finite relative entropy with respect to `μ ⊗ ν` whose cost
exceeds that of `π` by at most `η` per unit of mass. No measurability of the cost is needed. -/
theorem IsCoupling.exists_isCoupling_klDiv_ne_top_lintegral_le [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) (hp : Measurable p) (hq : Measurable q) {η : ℝ≥0∞}
    (hc : ∀ x x' y y', p x = p x' → q y = q y' → c (x, y) ≤ c (x', y') + η) :
    ∃ σ, IsCoupling σ μ ν ∧ klDiv σ (μ.prod ν) ≠ ∞ ∧
      ∫⁻ z, c z ∂σ ≤ ∫⁻ z, c z ∂π + η * μ univ := by
  obtain ⟨σ, hσ, hkl, hmap⟩ := hπ.exists_isCoupling_klDiv_ne_top_map_prodMap_eq hp hq
  have hQ : Measurable (Prod.map p q) := hp.prodMap hq
  -- the largest cost on each cell
  set s : ι × κ → ℝ≥0∞ := fun w ↦ ⨆ (z) (_ : Prod.map p q z = w), c z
  have hs : Measurable s := measurable_of_finite s
  refine ⟨σ, hσ, hkl, ?_⟩
  calc ∫⁻ z, c z ∂σ ≤ ∫⁻ z, s (Prod.map p q z) ∂σ :=
        lintegral_mono fun z ↦
          le_iSup₂ (f := fun z' (_ : Prod.map p q z' = Prod.map p q z) ↦ c z') z rfl
    _ = ∫⁻ z, s (Prod.map p q z) ∂π := by
        rw [← lintegral_map hs hQ, hmap, lintegral_map hs hQ]
    _ ≤ ∫⁻ z, (c z + η) ∂π := by
        refine lintegral_mono fun z' ↦ iSup₂_le fun z hz ↦ hc _ _ _ _ ?_ ?_
        · simpa using congrArg Prod.fst hz
        · simpa using congrArg Prod.snd hz
    _ = ∫⁻ z, c z ∂π + η * μ univ := by
        rw [lintegral_add_right' _ aemeasurable_const, lintegral_const, hπ.measure_univ_left,
          mul_comm]

end BlockApproximation

/-! ### The limit of the regularised cost -/

/-- **The zero-temperature value.** The infimum over positive temperatures of the regularised
transport cost is the infimum of the costs of the couplings of finite relative entropy with
respect to `μ ⊗ ν`. -/
theorem iInf_entropicTransportCost (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) :
    ⨅ (ε : ℝ≥0) (_ : 0 < ε), entropicTransportCost c ε μ ν =
      ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν) (_ : klDiv π (μ.prod ν) ≠ ∞),
        ∫⁻ z, c z ∂π := by
  refine le_antisymm (le_iInf₂ fun π hπ ↦ le_iInf fun hkl ↦ ?_)
    (le_iInf₂ fun ε hε ↦ le_entropicTransportCost fun π hπ ↦ ?_)
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    obtain ⟨ε, hε, hεδ⟩ := ENNReal.exists_nnreal_pos_mul_lt hkl (ENNReal.coe_ne_zero.2 hδ.ne')
    exact ((iInf₂_le ε hε).trans (entropicTransportCost_le hπ c ε)).trans
      (by gcongr)
  · by_cases hkl : klDiv π (μ.prod ν) = ∞
    · rw [hkl, ENNReal.mul_top (by exact_mod_cast hε.ne'), add_top]
      exact le_top
    · exact ((iInf₂_le π hπ).trans (iInf_le _ hkl)).trans le_self_add

/-- **The zero-temperature limit.** As `ε → 0⁺`, the regularised transport cost converges to the
infimum of the costs of the couplings of finite relative entropy with respect to `μ ⊗ ν`. -/
theorem tendsto_entropicTransportCost_nhdsGT_zero (c : X × Y → ℝ≥0∞) (μ : Measure X)
    (ν : Measure Y) :
    Tendsto (fun ε ↦ entropicTransportCost c ε μ ν) (𝓝[>] 0)
      (𝓝 (⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν) (_ : klDiv π (μ.prod ν) ≠ ∞),
        ∫⁻ z, c z ∂π)) := by
  have hmono : Monotone fun ε ↦ entropicTransportCost c ε μ ν := fun _ _ h ↦
    entropicTransportCost_mono le_rfl h
  rw [← iInf_entropicTransportCost]
  simpa [sInf_image] using hmono.tendsto_nhdsGT 0

/-- **Convergence to the transport cost.** If for every `η > 0` the cost varies by at most `η` on
the product cells of some measurable maps from `X` and `Y` to finite types, then as `ε → 0⁺` the
regularised transport cost of finite measures converges to the transport cost. -/
theorem tendsto_entropicTransportCost_transportCost [IsFiniteMeasure μ]
    (hc : ∀ η : ℝ≥0, 0 < η → ∃ (n m : ℕ) (p : X → Fin n) (q : Y → Fin m),
      Measurable p ∧ Measurable q ∧
        ∀ x x' y y', p x = p x' → q y = q y' → c (x, y) ≤ c (x', y') + η) :
    Tendsto (fun ε ↦ entropicTransportCost c ε μ ν) (𝓝[>] 0) (𝓝 (transportCost c μ ν)) := by
  convert tendsto_entropicTransportCost_nhdsGT_zero c μ ν using 2
  refine le_antisymm ?_ ?_
  · rw [transportCost_def]
    exact iInf₂_mono fun π hπ ↦ le_iInf fun _ ↦ le_rfl
  · rw [transportCost_def]
    refine le_iInf₂ fun π hπ ↦ ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    obtain ⟨η, hη, hηδ⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (measure_ne_top μ univ) (ENNReal.coe_ne_zero.2 hδ.ne')
    obtain ⟨n, m, p, q, hp, hq, hpq⟩ := hc η hη
    obtain ⟨σ, hσ, hkl, hle⟩ := hπ.exists_isCoupling_klDiv_ne_top_lintegral_le hp hq hpq
    exact ((iInf₂_le σ hσ).trans (iInf_le _ hkl)).trans (hle.trans (by gcongr))

section Metric

variable {X Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- **Convergence to the transport cost on totally bounded spaces.** For a uniformly continuous
real cost on totally bounded pseudometric spaces, the regularised transport cost of finite measures
converges to the transport cost as `ε → 0⁺`. -/
theorem tendsto_entropicTransportCost_transportCost_of_uniformContinuous
    (hX : TotallyBounded (univ : Set X)) (hY : TotallyBounded (univ : Set Y)) {c : X × Y → ℝ≥0}
    (hc : UniformContinuous c) (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) :
    Tendsto (fun ε ↦ entropicTransportCost (fun z ↦ c z) ε μ ν) (𝓝[>] 0)
      (𝓝 (transportCost (fun z ↦ c z) μ ν)) := by
  refine tendsto_entropicTransportCost_transportCost fun η hη ↦ ?_
  obtain ⟨δ, hδ, hcδ⟩ := Metric.uniformContinuous_iff.1 hc η (NNReal.coe_pos.2 hη)
  obtain ⟨n, v, p, hp, hpv⟩ := exists_measurable_dist_lt X hX (half_pos hδ)
  obtain ⟨m, w, q, hq, hqw⟩ := exists_measurable_dist_lt Y hY (half_pos hδ)
  refine ⟨n, m, p, q, hp, hq, fun x x' y y' hpx hqy ↦ ?_⟩
  -- two points with the same label are `δ`-close, so their costs are `η`-close
  have hx : dist x x' < δ := calc
    dist x x' ≤ dist x (v (p x)) + dist x' (v (p x')) := hpx ▸ dist_triangle_right _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add (hpv x) (hpv x')
    _ = δ := add_halves δ
  have hy : dist y y' < δ := calc
    dist y y' ≤ dist y (w (q y)) + dist y' (w (q y')) := hqy ▸ dist_triangle_right _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add (hqw y) (hqw y')
    _ = δ := add_halves δ
  have hd := hcδ (show dist (x, y) (x', y') < δ by rw [Prod.dist_eq]; exact max_lt hx hy)
  rw [NNReal.dist_eq] at hd
  have hle : c (x, y) ≤ c (x', y') + η := by
    rw [← NNReal.coe_le_coe, NNReal.coe_add]
    linarith [(abs_lt.1 hd).2]
  exact_mod_cast hle

/-- **Convergence to the transport cost on compact spaces.** For a continuous real cost on compact
pseudometric spaces, the regularised transport cost of finite measures converges to the transport
cost as `ε → 0⁺`. -/
theorem tendsto_entropicTransportCost_transportCost_of_continuous [CompactSpace X]
    [CompactSpace Y] {c : X × Y → ℝ≥0} (hc : Continuous c) (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) :
    Tendsto (fun ε ↦ entropicTransportCost (fun z ↦ c z) ε μ ν) (𝓝[>] 0)
      (𝓝 (transportCost (fun z ↦ c z) μ ν)) :=
  tendsto_entropicTransportCost_transportCost_of_uniformContinuous isCompact_univ.totallyBounded
    isCompact_univ.totallyBounded (CompactSpace.uniformContinuous_of_continuous hc) μ ν

end Metric

/-! ### Weak limits of entropic optimizers -/

section ClusterPoints

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T1Space (ProbabilityMeasure X)] [TopologicalSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [T1Space (ProbabilityMeasure Y)] [OpensMeasurableSpace (X × Y)]
  [TopologicalSpace.PseudoMetrizableSpace (X × Y)]

/-- **Weak limits of entropic optimizers are optimal.** Let the regularised transport cost of
probability measures `μ` and `ν` converge to the transport cost as `ε → 0⁺`, as it does under
`TauCeti.tendsto_entropicTransportCost_transportCost`, and let the cost be lower semicontinuous.
If the plans `πs i` are eventually optimal for the regularised problems at temperatures `εs i`
tending to `0⁺`, then every weak limit of the plans is an optimal transport plan. -/
theorem isOptimalCoupling_of_tendsto_of_entropicTransportCost {c : X × Y → ℝ≥0∞}
    (hc : LowerSemicontinuous c) {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (hval : Tendsto (fun ε ↦ entropicTransportCost c ε μ.toMeasure ν.toMeasure) (𝓝[>] 0)
      (𝓝 (transportCost c μ.toMeasure ν.toMeasure)))
    {l : Filter ι} [l.NeBot] {εs : ι → ℝ≥0} (hεs : Tendsto εs l (𝓝[>] 0))
    {πs : ι → ProbabilityMeasure (X × Y)} {π : ProbabilityMeasure (X × Y)}
    (hopt : ∀ᶠ i in l, IsCoupling (πs i).toMeasure μ.toMeasure ν.toMeasure ∧
      ∫⁻ z, c z ∂(πs i).toMeasure + εs i * klDiv (πs i).toMeasure (μ.toMeasure.prod ν.toMeasure) =
        entropicTransportCost c (εs i) μ.toMeasure ν.toMeasure)
    (hπ : Tendsto πs l (𝓝 π)) :
    IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure := by
  -- The lower semicontinuity theorem is phrased for a chosen compatible pseudometric.
  let : PseudoMetricSpace (X × Y) := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X × Y)
  have hcoup : IsCoupling π.toMeasure μ.toMeasure ν.toMeasure :=
    (isClosed_setOfPred_isCoupling μ ν).mem_of_tendsto hπ (hopt.mono fun i hi ↦ hi.1)
  refine ⟨hcoup, le_antisymm ?_ (transportCost_le_lintegral hcoup c)⟩
  calc ∫⁻ z, c z ∂π.toMeasure ≤ liminf (fun i ↦ ∫⁻ z, c z ∂(πs i).toMeasure) l :=
        le_liminf_lintegral_of_tendsto_probabilityMeasure hc hπ
    _ ≤ liminf (fun i ↦ entropicTransportCost c (εs i) μ.toMeasure ν.toMeasure) l :=
        liminf_le_liminf (hopt.mono fun i hi ↦ hi.2 ▸ le_self_add)
    _ = transportCost c μ.toMeasure ν.toMeasure := (hval.comp hεs).liminf_eq

end ClusterPoints

end TauCeti
