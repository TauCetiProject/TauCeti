/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Variational
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.ZeroTemperature
public import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic

/-!
# Entropy selection at zero temperature

When the optimal transport cost is finite and an optimal plan has finite relative entropy
against the product of the marginals, entropic regularization selects the unique optimal plan
of least relative entropy. The optimal transport plan itself need not be unique.

The comparison with an unregularized optimizer bounds the entropy of every positive-temperature
optimizer by its entropy. Lower semicontinuity then shows that any weak limit minimizes entropy
on the optimal face. Strict convexity gives uniqueness, and compactness of the coupling set
upgrades this to convergence of the whole family as the temperature tends to zero.

The comparison and uniqueness results hold for finite measures on arbitrary measurable spaces.
Existence and convergence are stated for Borel probability laws on Polish spaces and
nonnegative lower semicontinuous costs, which may take infinite values. Finite primal value is
essential for cancelling the unregularized cost in the entropy comparison.

## References

* G. Carlier, V. Duval, G. Peyré, B. Schmitzer, *Convergence of entropic schemes for optimal
  transport and gradient flows*, SIAM J. Math. Anal. 49 (2017), 1385–1418.
* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, 2021.
-/

public section

open MeasureTheory InformationTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Measurable

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {c : X × Y → ℝ≥0∞}
  {π σ : Measure (X × Y)} {ε : ℝ≥0}

/-- The entropy of an entropic optimizer is at most that of any unregularized optimizer,
provided the primal value is finite and the temperature is positive. -/
theorem IsCoupling.klDiv_le_of_entropicTransportCost_eq (hπ : IsCoupling π μ ν)
    (hπval : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν)
    (hσ : IsOptimalCoupling c σ μ ν) (hcost : transportCost c μ ν ≠ ∞) (hε : ε ≠ 0) :
    klDiv π (μ.prod ν) ≤ klDiv σ (μ.prod ν) := by
  have hle : transportCost c μ ν + ε * klDiv π (μ.prod ν) ≤
      transportCost c μ ν + ε * klDiv σ (μ.prod ν) :=
    calc _ ≤ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) :=
          add_le_add (transportCost_le_lintegral hπ c) le_rfl
      _ = entropicTransportCost c ε μ ν := hπval
      _ ≤ ∫⁻ z, c z ∂σ + ε * klDiv σ (μ.prod ν) :=
          entropicTransportCost_le hσ.toIsCoupling c ε
      _ = _ := by rw [hσ.lintegral_eq]
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.2 hε) ENNReal.coe_ne_top).1
    (ENNReal.le_of_add_le_add_left hcost hle)

/-- There is at most one finite-entropy minimizer on the optimal transport face. No topology
or measurability assumption on the cost is needed. -/
theorem IsOptimalCoupling.eq_of_isMinOn_klDiv [IsFiniteMeasure μ]
    (hπ : IsOptimalCoupling c π μ ν) (hσ : IsOptimalCoupling c σ μ ν)
    (hπmin : IsMinOn (fun γ ↦ klDiv γ (μ.prod ν)) {γ | IsOptimalCoupling c γ μ ν} π)
    (hσmin : IsMinOn (fun γ ↦ klDiv γ (μ.prod ν)) {γ | IsOptimalCoupling c γ μ ν} σ)
    (hπfin : klDiv π (μ.prod ν) ≠ ∞) : π = σ := by
  have := hπ.toIsCoupling.isFiniteMeasure
  have := hσ.toIsCoupling.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.toIsCoupling.snd_eq ▸ inferInstance
  have heq : klDiv σ (μ.prod ν) = klDiv π (μ.prod ν) :=
    le_antisymm (hσmin hπ) (hπmin hσ)
  by_contra hne
  have hmix := hπ.smul_add_smul hσ (a := 2⁻¹) (b := 2⁻¹) (by norm_num)
  have hlt := klDiv_smul_add_smul_lt
    (a := (2⁻¹ : ℝ≥0)) (b := (2⁻¹ : ℝ≥0)) (by norm_num) (by norm_num) (by norm_num)
    hπfin (heq ▸ hπfin) hne
  rw [heq, ← add_mul, ← ENNReal.coe_add, (by norm_num : (2⁻¹ : ℝ≥0) + 2⁻¹ = 1),
    ENNReal.coe_one, one_mul] at hlt
  exact (not_lt_of_ge (hπmin hmix)) hlt

/-- One finite-entropy optimal plan suffices for convergence of the entropic values to the
primal value. No approximation of other couplings is required. -/
theorem IsOptimalCoupling.tendsto_entropicTransportCost (hσ : IsOptimalCoupling c σ μ ν)
    (hσfin : klDiv σ (μ.prod ν) ≠ ∞) :
    Tendsto (fun ε ↦ entropicTransportCost c ε μ ν) (𝓝[>] 0)
      (𝓝 (transportCost c μ ν)) := by
  have hlim := tendsto_entropicTransportCost_nhdsGT_zero c μ ν
  convert hlim using 2
  refine le_antisymm ?_ ?_
  · exact le_iInf₂ fun γ hγ ↦ le_iInf fun _ ↦ transportCost_le_lintegral hγ c
  · exact ((iInf₂_le σ hσ.toIsCoupling).trans (iInf_le _ hσfin)).trans_eq hσ.lintegral_eq

end Measurable

section Polish

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [PolishSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [PolishSpace Y] [BorelSpace Y]
  {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} {c : X × Y → ℝ≥0∞}

/-- If the optimal face contains a finite-entropy plan, it has a unique minimum-entropy plan.
This existence theorem also allows infinite primal value. -/
theorem existsUnique_isOptimalCoupling_isMinOn_klDiv (hc : LowerSemicontinuous c)
    (hfin : ∃ σ, IsOptimalCoupling c σ μ.toMeasure ν.toMeasure ∧
      klDiv σ (μ.toMeasure.prod ν.toMeasure) ≠ ∞) :
    ∃! π : ProbabilityMeasure (X × Y),
      IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure ∧
      IsMinOn (fun γ : ProbabilityMeasure (X × Y) ↦
        klDiv γ.toMeasure (μ.toMeasure.prod ν.toMeasure))
        {γ | IsOptimalCoupling c γ.toMeasure μ.toMeasure ν.toMeasure} π := by
  obtain ⟨σ, hσ, hσfin⟩ := hfin
  have hσprob := hσ.toIsCoupling.isProbabilityMeasure
  let R : ProbabilityMeasure (X × Y) := ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩
  have hkl : LowerSemicontinuous fun γ : ProbabilityMeasure (X × Y) ↦
      klDiv γ.toMeasure (μ.toMeasure.prod ν.toMeasure) :=
    lowerSemicontinuous_klDiv_probabilityMeasure.comp
      (continuous_id.prodMk (continuous_const (y := R)))
  obtain ⟨π, hπ, hπmin⟩ := (hkl.lowerSemicontinuousOn _).exists_isMinOn
    ⟨⟨σ, hσprob⟩, hσ⟩
    (isCompact_setOfPred_isOptimalCoupling isTightMeasureSet_singleton
      isTightMeasureSet_singleton hc)
  have hπfin := ne_top_of_le_ne_top hσfin (hπmin (a := ⟨σ, hσprob⟩) hσ)
  have raw_min {γ : ProbabilityMeasure (X × Y)}
      (hγmin : IsMinOn (fun δ : ProbabilityMeasure (X × Y) ↦
        klDiv δ.toMeasure (μ.toMeasure.prod ν.toMeasure))
        {δ | IsOptimalCoupling c δ.toMeasure μ.toMeasure ν.toMeasure} γ) :
      IsMinOn (fun δ ↦ klDiv δ (μ.toMeasure.prod ν.toMeasure))
        {δ | IsOptimalCoupling c δ μ.toMeasure ν.toMeasure} γ.toMeasure := by
    intro δ hδ
    have hδprob := hδ.toIsCoupling.isProbabilityMeasure
    exact hγmin (a := ⟨δ, hδprob⟩) hδ
  refine ⟨π, ⟨hπ, hπmin⟩, fun γ hγ ↦ ?_⟩
  exact ProbabilityMeasure.toMeasure_injective
    (hπ.eq_of_isMinOn_klDiv hγ.1 (raw_min hπmin) (raw_min hγ.2) hπfin).symm

/-- Every weak limit of entropic optimizers minimizes relative entropy on the optimal face,
when the primal value is finite and the face contains a finite-entropy plan. -/
theorem isOptimalCoupling_isMinOn_klDiv_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (hc : LowerSemicontinuous c) (hcost : transportCost c μ.toMeasure ν.toMeasure ≠ ∞)
    (hfin : ∃ σ, IsOptimalCoupling c σ μ.toMeasure ν.toMeasure ∧
      klDiv σ (μ.toMeasure.prod ν.toMeasure) ≠ ∞)
    {εs : ι → ℝ≥0} (hεs : Tendsto εs l (𝓝[>] 0))
    {πs : ι → ProbabilityMeasure (X × Y)} {π : ProbabilityMeasure (X × Y)}
    (hopt : ∀ᶠ i in l, IsCoupling (πs i).toMeasure μ.toMeasure ν.toMeasure ∧
      ∫⁻ z, c z ∂(πs i).toMeasure + εs i * klDiv (πs i).toMeasure
        (μ.toMeasure.prod ν.toMeasure) = entropicTransportCost c (εs i) μ.toMeasure ν.toMeasure)
    (hπ : Tendsto πs l (𝓝 π)) :
    IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure ∧
      IsMinOn (fun γ : ProbabilityMeasure (X × Y) ↦
        klDiv γ.toMeasure (μ.toMeasure.prod ν.toMeasure))
        {γ | IsOptimalCoupling c γ.toMeasure μ.toMeasure ν.toMeasure} π := by
  obtain ⟨σ, hσ, hσfin⟩ := hfin
  refine ⟨isOptimalCoupling_of_tendsto_of_entropicTransportCost hc
    (hσ.tendsto_entropicTransportCost hσfin) hεs hopt hπ, ?_⟩
  intro γ hγ
  have hεpos : ∀ᶠ i in l, εs i ≠ 0 :=
    (hεs.eventually self_mem_nhdsWithin).mono fun i hi ↦ ne_of_gt hi
  have hbound : ∀ᶠ i in l, klDiv (πs i).toMeasure (μ.toMeasure.prod ν.toMeasure) ≤
      klDiv γ.toMeasure (μ.toMeasure.prod ν.toMeasure) := by
    filter_upwards [hopt, hεpos] with i hi hε
    exact hi.1.klDiv_le_of_entropicTransportCost_eq hi.2 hγ hcost hε
  let R : ProbabilityMeasure (X × Y) := ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩
  have hkl : LowerSemicontinuous fun δ : ProbabilityMeasure (X × Y) ↦
      klDiv δ.toMeasure (μ.toMeasure.prod ν.toMeasure) :=
    lowerSemicontinuous_klDiv_probabilityMeasure.comp
      (continuous_id.prodMk (continuous_const (y := R)))
  exact ((hkl.le_liminf π).trans hπ.liminf_le_liminf_comp).trans
    (by simpa only [Function.comp_def, liminf_const] using liminf_le_liminf hbound)

/-- Entropic optimizers converge to the minimum-entropy optimal plan as their positive
temperatures tend to zero. This is convergence of the whole family, not only a subsequence. -/
theorem tendsto_of_entropicTransportCost_eq {ι : Type*} {l : Filter ι}
    (hc : LowerSemicontinuous c) (hcost : transportCost c μ.toMeasure ν.toMeasure ≠ ∞)
    (hfin : ∃ σ, IsOptimalCoupling c σ μ.toMeasure ν.toMeasure ∧
      klDiv σ (μ.toMeasure.prod ν.toMeasure) ≠ ∞)
    {εs : ι → ℝ≥0} (hεs : Tendsto εs l (𝓝[>] 0))
    {πs : ι → ProbabilityMeasure (X × Y)}
    (hopt : ∀ᶠ i in l, IsCoupling (πs i).toMeasure μ.toMeasure ν.toMeasure ∧
      ∫⁻ z, c z ∂(πs i).toMeasure + εs i * klDiv (πs i).toMeasure
        (μ.toMeasure.prod ν.toMeasure) = entropicTransportCost c (εs i) μ.toMeasure ν.toMeasure)
    {π : ProbabilityMeasure (X × Y)}
    (hπ : IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure)
    (hπmin : IsMinOn (fun γ : ProbabilityMeasure (X × Y) ↦
      klDiv γ.toMeasure (μ.toMeasure.prod ν.toMeasure))
      {γ | IsOptimalCoupling c γ.toMeasure μ.toMeasure ν.toMeasure} π) :
    Tendsto πs l (𝓝 π) := by
  obtain ⟨σ, -, hσuniq⟩ := existsUnique_isOptimalCoupling_isMinOn_klDiv hc hfin
  have hπσ := hσuniq π ⟨hπ, hπmin⟩
  refine (isCompact_setOfPred_isCoupling_of_polishSpace μ ν).tendsto_nhds_of_unique_mapClusterPt
    (hopt.mono fun i hi ↦ hi.1) fun γ _ hγ ↦ ?_
  -- Restrict to a nontrivial refinement along which this cluster point is a weak limit.
  have hne : (l ⊓ Filter.comap πs (𝓝 γ)).NeBot :=
    Filter.neBot_inf_comap_iff_map.2 (by simpa only [MapClusterPt, ClusterPt, inf_comm] using hγ)
  have hconv : Tendsto πs (l ⊓ Filter.comap πs (𝓝 γ)) (𝓝 γ) :=
    Filter.tendsto_iff_comap.2 inf_le_right
  have hγsel := isOptimalCoupling_isMinOn_klDiv_of_tendsto hc hcost hfin
    (hεs.mono_left inf_le_left) (hopt.filter_mono inf_le_left) hconv
  exact (hσuniq γ hγsel).trans hπσ.symm

end Polish

end TauCeti
