/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Projection
public import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence
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

On noncompact spaces a continuous cost need not be discretisable, but the limit is still the
transport cost when the cost has an integrable split upper bound `c (x, y) ≤ cX x + cY y` and the
marginals are tight, as all finite Borel measures on complete separable pseudometric spaces are. The
bound gives a level `M` above which the cost carries little mass under every coupling at once, and
tightness gives a compact rectangle `K ×ˢ L` outside which every coupling has little mass. The cost
truncated at `M` is uniformly continuous on `K ×ˢ L` and is discretised there. The complements of
`K` and `L` each receive one further label in the partitions of `X` and `Y`, and the truncated cost
is replaced by `M` on every resulting product cell outside `K ×ˢ L`.

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
* `TauCeti.tendsto_entropicTransportCost_transportCost_of_forall_exists`: if every coupling is
  approximated in cost by couplings of finite relative entropy, the limit is the transport cost.
* `TauCeti.tendsto_entropicTransportCost_transportCost`: for a cost that can be discretised, the
  limit is the transport cost;
  `TauCeti.tendsto_entropicTransportCost_transportCost_of_uniformContinuous` and
  `TauCeti.tendsto_entropicTransportCost_transportCost_of_continuous` are the totally bounded and
  compact cases.
* `TauCeti.IsCoupling.exists_isCoupling_klDiv_ne_top_lintegral_le_of_le_add` and
  `TauCeti.tendsto_entropicTransportCost_transportCost_of_le_add`: for a continuous cost with an
  integrable split upper bound and tight marginals, every coupling is approximated by couplings of
  finite relative entropy, and the limit is the transport cost.
* `TauCeti.isOptimalCoupling_of_tendsto_of_entropicTransportCost`: when the values converge to the
  transport cost and the cost is lower semicontinuous, every weak limit of entropic optimizers at
  temperatures `ε → 0⁺` is an optimal transport plan.

## References

* G. Carlier, V. Duval, G. Peyré, B. Schmitzer, *Convergence of entropic schemes for optimal
  transport and gradient flows*, SIAM J. Math. Anal. 49 (2017), 1385–1418, for the block
  approximation of a coupling and the convergence of entropic transport as `ε → 0`.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  for the convergence of entropic optimal transport as `ε → 0` on noncompact spaces.
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

/-- **The block approximation is a coupling.** Let `π` couple measures `μ` and `ν`, and let `p`
and `q` be measurable maps to the cell labels along which `μ` and `ν` push forward to σ-finite
measures (for instance, `μ` and `ν` finite). If the cell masses of `π` are absolutely
continuous with respect to those of `μ ⊗ ν`, the relative-entropy projection of `μ ⊗ ν` onto the
measures with the cell masses of `π` is again a coupling of `μ` and `ν`. On each cell it is
`μ ⊗ ν` rescaled to the mass that `π` gives the cell. -/
theorem IsCoupling.isCoupling_fitLaw_prodMap [SigmaFinite (μ.map p)] [SigmaFinite (ν.map q)]
    (hπ : IsCoupling π μ ν) (hp : Measurable p) (hq : Measurable q)
    (hac : π.map (Prod.map p q) ≪ (μ.prod ν).map (Prod.map p q)) :
    IsCoupling ((μ.prod ν).fitLaw (Prod.map p q) (π.map (Prod.map p q))) μ ν := by
  have : SigmaFinite μ := .of_map μ hp.aemeasurable inferInstance
  have : SigmaFinite ν := .of_map ν hq.aemeasurable inferInstance
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

/-- **Convergence from finite-entropy approximation.** If every coupling of `μ` and `ν` is
approximated in cost, up to any positive error, by a coupling of finite relative entropy with
respect to `μ ⊗ ν`, then as `ε → 0⁺` the regularised transport cost converges to the transport
cost. -/
theorem tendsto_entropicTransportCost_transportCost_of_forall_exists
    (h : ∀ π, IsCoupling π μ ν → ∀ δ : ℝ≥0, 0 < δ → ∃ σ, IsCoupling σ μ ν ∧
      klDiv σ (μ.prod ν) ≠ ∞ ∧ ∫⁻ z, c z ∂σ ≤ ∫⁻ z, c z ∂π + δ) :
    Tendsto (fun ε ↦ entropicTransportCost c ε μ ν) (𝓝[>] 0) (𝓝 (transportCost c μ ν)) := by
  convert tendsto_entropicTransportCost_nhdsGT_zero c μ ν using 2
  refine le_antisymm ?_ ?_
  · rw [transportCost_def]
    exact iInf₂_mono fun π hπ ↦ le_iInf fun _ ↦ le_rfl
  · rw [transportCost_def]
    refine le_iInf₂ fun π hπ ↦ ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    obtain ⟨σ, hσ, hkl, hle⟩ := h π hπ δ hδ
    exact ((iInf₂_le σ hσ).trans (iInf_le _ hkl)).trans hle

/-- **Convergence to the transport cost.** If for every `η > 0` the cost varies by at most `η` on
the product cells of some measurable maps from `X` and `Y` to finite types, then as `ε → 0⁺` the
regularised transport cost of finite measures converges to the transport cost. -/
theorem tendsto_entropicTransportCost_transportCost [IsFiniteMeasure μ]
    (hc : ∀ η : ℝ≥0, 0 < η → ∃ (n m : ℕ) (p : X → Fin n) (q : Y → Fin m),
      Measurable p ∧ Measurable q ∧
        ∀ x x' y y', p x = p x' → q y = q y' → c (x, y) ≤ c (x', y') + η) :
    Tendsto (fun ε ↦ entropicTransportCost c ε μ ν) (𝓝[>] 0) (𝓝 (transportCost c μ ν)) := by
  refine tendsto_entropicTransportCost_transportCost_of_forall_exists fun π hπ δ hδ ↦ ?_
  obtain ⟨η, hη, hηδ⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt (measure_ne_top μ univ) (ENNReal.coe_ne_zero.2 hδ.ne')
  obtain ⟨n, m, p, q, hp, hq, hpq⟩ := hc η hη
  obtain ⟨σ, hσ, hkl, hle⟩ := hπ.exists_isCoupling_klDiv_ne_top_lintegral_le hp hq hpq
  exact ⟨σ, hσ, hkl, hle.trans (add_le_add le_rfl hηδ.le)⟩

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
  have hxy : dist (x, y) (x', y') < δ := by rw [Prod.dist_eq]; exact max_lt hx hy
  have hd := hcδ hxy
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

/-- The block approximation for a continuous cost truncated at a finite level `M`, with the
partition taken fine only on a compact rectangle `K ×ˢ L`: the mass of the coupling off the
rectangle is charged at most `M` per unit. -/
private theorem IsCoupling.exists_isCoupling_klDiv_ne_top_lintegral_min_le {π : Measure (X × Y)}
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] (hπ : IsCoupling π μ ν) {c : X × Y → ℝ≥0}
    (hc : Continuous c) {K : Set X} {L : Set Y} (hK : IsCompact K) (hKm : MeasurableSet K)
    (hL : IsCompact L) (hLm : MeasurableSet L) (M : ℝ≥0∞) {η : ℝ≥0} (hη : 0 < η) :
    ∃ σ, IsCoupling σ μ ν ∧ klDiv σ (μ.prod ν) ≠ ∞ ∧
      ∫⁻ z, min (c z : ℝ≥0∞) M ∂σ ≤ ∫⁻ z, c z ∂π + M * (μ Kᶜ + ν Lᶜ) + η * μ univ := by
  classical
  -- On `K ×ˢ L` the cost is uniformly continuous, so it varies by less than `η` on small cells.
  obtain ⟨ρ, hρ, hcρ⟩ := Metric.uniformContinuousOn_iff.1
    ((hK.prod hL).uniformContinuousOn_of_continuous hc.continuousOn) η (NNReal.coe_pos.2 hη)
  obtain ⟨n, p, hp, hpK, hpρ⟩ := hK.totallyBounded.exists_measurable_dist_lt hKm hρ
  obtain ⟨m, q, hq, hqL, hqρ⟩ := hL.totallyBounded.exists_measurable_dist_lt hLm hρ
  -- The cost truncated at `M` on `K ×ˢ L` and equal to `M` off it varies by at most `η` on every
  -- product cell, so the block approximation applies to it.
  obtain ⟨c', hc'⟩ : ∃ c' : X × Y → ℝ≥0∞,
      ∀ z, c' z = if z ∈ K ×ˢ L then min (c z : ℝ≥0∞) M else M := ⟨_, fun _ ↦ rfl⟩
  have hvar : ∀ x x' y y', p x = p x' → q y = q y' → c' (x, y) ≤ c' (x', y') + η := by
    intro x x' y y' hpx hqy
    have hxK : x ∈ K ↔ x' ∈ K := by rw [← not_iff_not, ← hpK, ← hpK, hpx]
    have hyL : y ∈ L ↔ y' ∈ L := by rw [← not_iff_not, ← hqL, ← hqL, hqy]
    by_cases hxy : x ∈ K ∧ y ∈ L
    · have hx' := hxK.1 hxy.1
      have hy' := hyL.1 hxy.2
      have hd : dist (x, y) (x', y') < ρ := by
        rw [Prod.dist_eq]
        exact max_lt (hpρ x hxy.1 x' hx' hpx) (hqρ y hxy.2 y' hy' hqy)
      have hcd := hcρ (x, y) ⟨hxy.1, hxy.2⟩ (x', y') ⟨hx', hy'⟩ hd
      rw [NNReal.dist_eq] at hcd
      have h1 : (c (x, y) : ℝ≥0∞) ≤ c (x', y') + η := by
        rw [← ENNReal.coe_add, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add]
        linarith [(abs_lt.1 hcd).2]
      rw [hc', hc', ite_eq_left (mk_mem_prod hxy.1 hxy.2), ite_eq_left (mk_mem_prod hx' hy'),
        ← min_add_add_right]
      exact min_le_min h1 le_self_add
    · have hxy' : ¬(x' ∈ K ∧ y' ∈ L) := by rwa [← hxK, ← hyL]
      rw [hc', hc', ite_eq_right (by simpa using hxy), ite_eq_right (by simpa using hxy')]
      exact le_self_add
  obtain ⟨σ, hσ, hkl, hσc'⟩ := hπ.exists_isCoupling_klDiv_ne_top_lintegral_le hp hq hvar
  refine ⟨σ, hσ, hkl, ?_⟩
  have hKL : MeasurableSet (K ×ˢ L)ᶜ := (hKm.prod hLm).compl
  -- The truncated cost lies below `c'`, which exceeds `c` only off `K ×ˢ L`, by at most `M`.
  have hmin : ∀ z, min (c z : ℝ≥0∞) M ≤ c' z := fun z ↦ by
    rw [hc']
    split_ifs
    exacts [le_rfl, min_le_right _ _]
  have hc'le : ∀ z, c' z ≤ c z + (K ×ˢ L)ᶜ.indicator (fun _ ↦ M) z := fun z ↦ by
    by_cases hz : z ∈ K ×ˢ L
    · rw [hc', ite_eq_left hz, indicator_of_notMem (notMem_compl_iff.2 hz), add_zero]
      exact min_le_left _ _
    · rw [hc', ite_eq_right hz, indicator_of_mem (mem_compl hz)]
      exact le_add_self
  have hmass : π (K ×ˢ L)ᶜ ≤ μ Kᶜ + ν Lᶜ := by
    rw [compl_prod_eq_union, ← hπ.measure_prod_univ hKm.compl, ← hπ.measure_univ_prod hLm.compl]
    exact measure_union_le _ _
  calc ∫⁻ z, min (c z : ℝ≥0∞) M ∂σ ≤ ∫⁻ z, c' z ∂σ := lintegral_mono hmin
    _ ≤ ∫⁻ z, c' z ∂π + η * μ univ := hσc'
    _ ≤ ∫⁻ z, c z + (K ×ˢ L)ᶜ.indicator (fun _ ↦ M) z ∂π + η * μ univ := by
      gcongr with z
      exact hc'le z
    _ = ∫⁻ z, c z ∂π + M * π (K ×ˢ L)ᶜ + η * μ univ := by
      rw [lintegral_add_right' _ (measurable_const.indicator hKL).aemeasurable,
        lintegral_indicator_const hKL]
    _ ≤ ∫⁻ z, c z ∂π + M * (μ Kᶜ + ν Lᶜ) + η * μ univ := by gcongr

/-- **Finite-entropy approximation under an integrable split upper bound.** Let `c` be a
continuous real cost on pseudometric spaces, bounded above by `cX x + cY y` for almost everywhere
measurable functions `cX : X → ℝ≥0∞` and `cY : Y → ℝ≥0∞` of finite Lebesgue integral against tight
finite measures `μ` and `ν`. Then every coupling `π` of `μ` and `ν` is approximated,
up to any positive error in cost, by a coupling of finite relative entropy with respect to
`μ ⊗ ν`. -/
theorem IsCoupling.exists_isCoupling_klDiv_ne_top_lintegral_le_of_le_add {π : Measure (X × Y)}
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] (hμ : IsTightMeasureSet {μ})
    (hν : IsTightMeasureSet {ν}) {c : X × Y → ℝ≥0} (hc : Continuous c) {cX : X → ℝ≥0∞}
    {cY : Y → ℝ≥0∞} (hcX : AEMeasurable cX μ) (hcXi : ∫⁻ x, cX x ∂μ ≠ ∞) (hcY : AEMeasurable cY ν)
    (hcYi : ∫⁻ y, cY y ∂ν ≠ ∞) (hle : ∀ x y, (c (x, y) : ℝ≥0∞) ≤ cX x + cY y)
    (hπ : IsCoupling π μ ν) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ σ, IsCoupling σ μ ν ∧ klDiv σ (μ.prod ν) ≠ ∞ ∧ ∫⁻ z, c z ∂σ ≤ ∫⁻ z, c z ∂π + δ := by
  -- The error is split into four parts `δ / 4`: the two tails of the cost above a level `M`, the
  -- mass outside a compact rectangle charged at `M`, and the discretisation error on it.
  have hδ' : δ / 4 ≠ 0 := (ENNReal.div_pos hδ (by norm_num)).ne'
  -- Above a large finite level `M = M₁ + M₂`, the cost exceeds `M` by at most `a x + b y`, where
  -- `a` and `b` are the excesses of `cX` and `cY` over `M₁` and `M₂`, of integrals at most `δ / 4`.
  have hδ0 : (0 : ℝ≥0∞) < δ / 4 := pos_iff_ne_zero.2 hδ'
  obtain ⟨M₁, hai⟩ := ((tendsto_lintegral_tsub_atTop hcX hcXi).eventually
    (eventually_le_nhds hδ0)).exists
  obtain ⟨M₂, hbi⟩ := ((tendsto_lintegral_tsub_atTop hcY hcYi).eventually
    (eventually_le_nhds hδ0)).exists
  set a : X → ℝ≥0∞ := fun x ↦ cX x - M₁
  set b : Y → ℝ≥0∞ := fun y ↦ cY y - M₂
  have ha : AEMeasurable a μ := hcX.sub aemeasurable_const
  have hb : AEMeasurable b ν := hcY.sub aemeasurable_const
  set M : ℝ≥0∞ := ((M₁ + M₂ : ℝ≥0) : ℝ≥0∞) with hM_def
  have hM : M ≠ ∞ := ENNReal.coe_ne_top
  have hab (x : X) (y : Y) : (c (x, y) : ℝ≥0∞) - M ≤ a x + b y :=
    calc (c (x, y) : ℝ≥0∞) - M ≤ cX x + cY y - (M₁ + M₂) := by
          rw [hM_def, ENNReal.coe_add]
          exact tsub_le_tsub_right (hle x y) _
      _ ≤ a x + b y := add_tsub_add_le_tsub_add_tsub
  obtain ⟨t, ht, htM⟩ := ENNReal.exists_nnreal_pos_mul_lt hM hδ'
  have ht2 : 0 < (t : ℝ≥0∞) / 2 := ENNReal.half_pos (ENNReal.coe_ne_zero.2 ht.ne')
  obtain ⟨K, hK, hμK⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hμ _ ht2
  obtain ⟨L, hL, hνL⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hν _ ht2
  -- Closures make the compact sets measurable without enlarging their complements' mass.
  have hμK' : μ (closure K)ᶜ ≤ t / 2 :=
    (measure_mono (compl_subset_compl.2 subset_closure)).trans (hμK μ (mem_singleton μ))
  have hνL' : ν (closure L)ᶜ ≤ t / 2 :=
    (measure_mono (compl_subset_compl.2 subset_closure)).trans (hνL ν (mem_singleton ν))
  obtain ⟨η, hη, hημ⟩ := ENNReal.exists_nnreal_pos_mul_lt (measure_ne_top μ univ) hδ'
  obtain ⟨σ, hσ, hkl, hσc⟩ := hπ.exists_isCoupling_klDiv_ne_top_lintegral_min_le hc hK.closure
    isClosed_closure.measurableSet hL.closure isClosed_closure.measurableSet M hη
  refine ⟨σ, hσ, hkl, ?_⟩
  have haσ : AEMeasurable (fun z : X × Y ↦ a z.1) σ :=
    ha.comp_quasiMeasurePreserving hσ.measurePreserving_fst.quasiMeasurePreserving
  have hbσ : AEMeasurable (fun z : X × Y ↦ b z.2) σ :=
    hb.comp_quasiMeasurePreserving hσ.measurePreserving_snd.quasiMeasurePreserving
  have hmass : M * (μ (closure K)ᶜ + ν (closure L)ᶜ) ≤ δ / 4 :=
    calc M * (μ (closure K)ᶜ + ν (closure L)ᶜ) ≤ M * (t / 2 + t / 2) := by gcongr
      _ = t * M := by rw [ENNReal.add_halves, mul_comm]
      _ ≤ δ / 4 := htM.le
  -- Pointwise, the cost is its truncation at `M` plus its excess over `M`.
  have hsplit (z : X × Y) : (c z : ℝ≥0∞) ≤ min (c z : ℝ≥0∞) M + (a z.1 + b z.2) :=
    calc (c z : ℝ≥0∞) = min (c z : ℝ≥0∞) M + ((c z : ℝ≥0∞) - M) := by rw [add_comm, tsub_add_min]
      _ ≤ _ := add_le_add le_rfl (hab z.1 z.2)
  have habσ : AEMeasurable (fun z : X × Y ↦ a z.1 + b z.2) σ := haσ.add hbσ
  calc ∫⁻ z, (c z : ℝ≥0∞) ∂σ ≤ ∫⁻ z, min (c z : ℝ≥0∞) M + (a z.1 + b z.2) ∂σ :=
        lintegral_mono hsplit
    _ = ∫⁻ z, min (c z : ℝ≥0∞) M ∂σ + (∫⁻ x, a x ∂μ + ∫⁻ y, b y ∂ν) := by
      rw [lintegral_add_right' _ habσ, lintegral_add_right' _ hbσ,
        hσ.lintegral_comp_fst ha, hσ.lintegral_comp_snd hb]
    _ ≤ ∫⁻ z, c z ∂π + δ / 4 + δ / 4 + (δ / 4 + δ / 4) := by
      gcongr
      exact hσc.trans (add_le_add (add_le_add le_rfl hmass) hημ.le)
    _ = ∫⁻ z, c z ∂π + δ / 4 * 4 := by ring
    _ = ∫⁻ z, c z ∂π + δ := by rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

/-- **The zero-temperature limit under an integrable split upper bound.** Let `c` be a continuous
real cost on pseudometric spaces, bounded above by `cX x + cY y` for almost everywhere measurable
functions `cX : X → ℝ≥0∞` and `cY : Y → ℝ≥0∞` of finite Lebesgue integral against tight finite
measures `μ` and `ν`. Then as `ε → 0⁺` the regularised transport cost
converges to the transport cost.

Finite Borel measures on complete separable pseudometric spaces are tight
(`MeasureTheory.isTightMeasureSet_singleton`), so this covers, for instance, the cost `‖x - y‖ ^ p`
between laws on `ℝⁿ` with finite `p`-th moments. With
`TauCeti.isOptimalCoupling_of_tendsto_of_entropicTransportCost` it shows that weak limits of
entropic optimizers are optimal transport plans. -/
theorem tendsto_entropicTransportCost_transportCost_of_le_add {μ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ] (hμ : IsTightMeasureSet {μ}) (hν : IsTightMeasureSet {ν})
    {c : X × Y → ℝ≥0} (hc : Continuous c) {cX : X → ℝ≥0∞} {cY : Y → ℝ≥0∞}
    (hcX : AEMeasurable cX μ) (hcXi : ∫⁻ x, cX x ∂μ ≠ ∞) (hcY : AEMeasurable cY ν)
    (hcYi : ∫⁻ y, cY y ∂ν ≠ ∞) (hle : ∀ x y, (c (x, y) : ℝ≥0∞) ≤ cX x + cY y) :
    Tendsto (fun ε ↦ entropicTransportCost (fun z ↦ c z) ε μ ν) (𝓝[>] 0)
      (𝓝 (transportCost (fun z ↦ c z) μ ν)) :=
  tendsto_entropicTransportCost_transportCost_of_forall_exists fun _ hπ _ hδ ↦
    hπ.exists_isCoupling_klDiv_ne_top_lintegral_le_of_le_add hμ hν hc hcX hcXi hcY hcYi hle
      (ENNReal.coe_ne_zero.2 hδ.ne')

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
