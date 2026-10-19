/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Monge
public import TauCeti.MeasureTheory.OptimalTransport.Realization
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence
import TauCeti.MeasureTheory.OptimalTransport.Cost.Partial.Integrable

/-!
# Density of graph plans among couplings

If the source law is atomless and the source and target are Polish, every coupling is a weak limit
of graph plans of measurable, law-preserving maps. A countable quantization of the source changes
each point by a uniformly small distance. Realizing the coupling exactly after this quantization
then makes its graph realization close in the Lévy--Prokhorov metric.

This is the measure-theoretic approximation used to compare the Monge and Kantorovich problems.
It does not assert that a limiting coupling is itself a graph plan.

For a bounded continuous cost, integration against a weakly convergent family of plans converges,
so the Monge and Kantorovich values agree. The same holds for a continuous cost with an integrable
split upper envelope `c (x, y) ≤ a x + b y`: below a level `R` the truncated cost is bounded
continuous, and above it the envelope makes the cost uniformly small over all couplings, graph
plans included. For continuous costs without such an envelope, possibly infinite, the equality of
the two values is Pratelli's Theorem B, which is not proved here.

## Main statements

* `TauCeti.Coupling.dense_graphPlans` — graph plans are dense among the couplings of an atomless
  source law;
* `TauCeti.mongeCost_eq_transportCost_boundedContinuous` — Monge equals Kantorovich for bounded
  continuous costs;
* `TauCeti.IsCoupling.exists_hasLaw_transportMapCost_le` — under an integrable split upper
  envelope, transport maps approach the cost of every coupling;
* `TauCeti.mongeCost_eq_transportCost_of_le_split` — Monge equals Kantorovich for continuous costs
  with an integrable split upper envelope.
* `TauCeti.mongeCost_eq_transportCost_boundedContinuous_of_measure_univ_eq` and
  `TauCeti.mongeCost_eq_transportCost_of_le_split_of_measure_univ_eq` — the corresponding
  equalities for finite equal-mass measures, with a separate zero-mass branch.

## References

* A. Pratelli, *On the equality between Monge's infimum and Kantorovich's minimum in optimal mass
  transportation*, Ann. I. H. Poincaré Probab. Statist. 43 (2007), 1--13; the realization step
  follows §1.1, and Theorem B there is the general continuous-cost equality.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MetricSpace X] [MetricSpace Y] [PolishSpace X] [PolishSpace Y]
  [BorelSpace X] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}

section Probability

variable [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Every coupling with an atomless source has a graph realization arbitrarily close in the
Lévy--Prokhorov metric. The source and target marginals of the realization are exact. -/
theorem exists_graphPlan_levyProkhorovEDist_lt (hπ : IsCoupling π μ ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : X → Y, MeasurePreserving T μ ν ∧
      levyProkhorovEDist π (graphPlan T μ) < ENNReal.ofReal ε := by
  let : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hπ.snd_eq ▸ inferInstance
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  classical
  let u : ℕ → X := TopologicalSpace.denseSeq X
  have hu : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  let r : ℝ := ε * ε / 32
  have hr : 0 < r := by dsimp [r]; positivity
  have hidx : ∀ x : X, ∃ i, dist x (u i) < r :=
    fun x ↦ Metric.denseRange_iff.1 hu x r hr
  let q : X → ℕ := fun x ↦ Nat.find (hidx x)
  have hq : Measurable q := measurable_find hidx fun _ ↦ measurableSet_ball
  let F : X × Y → X × Y := Prod.map (u ∘ q) id
  have hF : Measurable F := (Measurable.of_discrete.comp hq).prodMap measurable_id
  have hdist (z : X × Y) : edist z (F z) ≤ ENNReal.ofReal r := by
    rcases z with ⟨x, y⟩
    simpa [F, Prod.edist_eq, edist_dist] using
      (ENNReal.ofReal_le_ofReal (Nat.find_spec (hidx x)).le)
  obtain ⟨T, hT, hqmap⟩ := hπ.exists_measurePreserving_map_graphPlan_eq hq
  have hmap : π.map F = (graphPlan T μ).map F := by
    have hu' : Measurable (Prod.map u (id : Y → Y)) :=
      (Measurable.of_discrete).prodMap measurable_id
    have hcomp : (Prod.map u (id : Y → Y)) ∘ (Prod.map q id) = F := by
      funext z
      rfl
    calc
      π.map F = (π.map (Prod.map q id)).map (Prod.map u id) := by
        rw [Measure.map_map hu' (hq.prodMap measurable_id), hcomp]
      _ = ((graphPlan T μ).map (Prod.map q id)).map (Prod.map u id) := by
        rw [hqmap]
      _ = (graphPlan T μ).map F := by
        rw [Measure.map_map hu' (hq.prodMap measurable_id), hcomp]
  have hleft : wassersteinEDist 1 π (π.map F) ≤ ENNReal.ofReal r :=
    wassersteinEDist_map_le_of_edist_le π hF.aemeasurable (Filter.Eventually.of_forall hdist)
  have hright : wassersteinEDist 1 (graphPlan T μ) ((graphPlan T μ).map F) ≤
      ENNReal.ofReal r :=
    wassersteinEDist_map_le_of_edist_le (graphPlan T μ) hF.aemeasurable
      (Filter.Eventually.of_forall hdist)
  have hrbound : ENNReal.ofReal r < ENNReal.ofReal (ε / 4) * ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ε / 4)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < ε / 4 * (ε / 4))).2
      (by dsimp [r]; nlinarith [sq_pos_of_pos hε])
  have hdistleft : levyProkhorovEDist π (π.map F) ≤ ENNReal.ofReal (ε / 4) :=
    levyProkhorovEDist_le_of_wassersteinEDist_lt_mul_self measurable_edist
      (by norm_num : (1 : ℝ≥0∞) ≤ 1) (hleft.trans_lt hrbound)
  have hdistright : levyProkhorovEDist (graphPlan T μ) ((graphPlan T μ).map F) ≤
      ENNReal.ofReal (ε / 4) :=
    levyProkhorovEDist_le_of_wassersteinEDist_lt_mul_self measurable_edist
      (by norm_num : (1 : ℝ≥0∞) ≤ 1) (hright.trans_lt hrbound)
  refine ⟨T, hT, ?_⟩
  calc
    levyProkhorovEDist π (graphPlan T μ) ≤
        levyProkhorovEDist π (π.map F) +
          levyProkhorovEDist (π.map F) (graphPlan T μ) :=
      levyProkhorovEDist_triangle _ _ _
    _ = levyProkhorovEDist π (π.map F) +
          levyProkhorovEDist (graphPlan T μ) ((graphPlan T μ).map F) := by
      rw [hmap, levyProkhorovEDist_comm (graphPlan T μ) ((graphPlan T μ).map F)]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
      add_le_add hdistleft hdistright
    _ = ENNReal.ofReal (ε / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

/-- Graph plans of law-preserving measurable maps are narrowly dense among couplings with
nonatomic source. The closure is taken in the weak topology of probability measures on the
product; every approximating graph plan has exactly the prescribed marginals. -/
theorem Coupling.mem_closure_graphPlans {μ₀ : ProbabilityMeasure X}
    {ν₀ : ProbabilityMeasure Y} (π₀ : Coupling μ₀ ν₀)
    [NullSingletonClass (μ₀ : Measure X)] :
    (π₀.1 : ProbabilityMeasure (X × Y)) ∈
      closure {ρ : ProbabilityMeasure (X × Y) |
        ∃ T : X → Y, MeasurePreserving T (μ₀ : Measure X) (ν₀ : Measure Y) ∧
          ρ.toMeasure = graphPlan T (μ₀ : Measure X)} := by
  let G : Set (ProbabilityMeasure (X × Y)) :=
    {ρ | ∃ T : X → Y, MeasurePreserving T (μ₀ : Measure X) (ν₀ : Measure Y) ∧
      ρ.toMeasure = graphPlan T (μ₀ : Measure X)}
  let e := LevyProkhorov.probabilityMeasureHomeomorph (Ω := X × Y)
  have he : e π₀.1 ∈ closure (e '' G) := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨T, hT, hdist⟩ :=
      exists_graphPlan_levyProkhorovEDist_lt π₀.2 hε
    let ρ : ProbabilityMeasure (X × Y) := ⟨graphPlan T (μ₀ : Measure X), inferInstance⟩
    refine ⟨e ρ, ⟨ρ, ⟨T, hT, rfl⟩, rfl⟩, ?_⟩
    rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist]
    exact ENNReal.toReal_lt_of_lt_ofReal hdist
  have : π₀.1 ∈ e ⁻¹' closure (e '' G) := he
  rw [e.preimage_closure, Set.preimage_image_eq _ e.injective] at this
  exact this

/-- With the topology inherited from probability measures, graph couplings are dense in the
space of couplings of an atomless source law with a prescribed target law. -/
theorem Coupling.dense_graphPlans {μ₀ : ProbabilityMeasure X} {ν₀ : ProbabilityMeasure Y}
    [NullSingletonClass (μ₀ : Measure X)] :
    Dense {π₀ : Coupling μ₀ ν₀ |
      ∃ T : X → Y, MeasurePreserving T (μ₀ : Measure X) (ν₀ : Measure Y) ∧
        π₀.1.toMeasure = graphPlan T (μ₀ : Measure X)} := by
  refine Topology.IsEmbedding.subtypeVal.isInducing.dense_iff.2 ?_
  rintro ⟨ρ, hρ⟩
  have hclosure := Coupling.mem_closure_graphPlans (⟨ρ, hρ⟩ : Coupling μ₀ ν₀)
  apply closure_mono _ hclosure
  intro σ hσ
  obtain ⟨T, hT, hσ⟩ := hσ
  refine ⟨⟨σ, ?_⟩, ⟨T, hT, hσ⟩, rfl⟩
  exact hσ.symm ▸ isCoupling_graphPlan hT.hasLaw

/-- For an atomless source, the Monge and Kantorovich values agree for every bounded continuous
nonnegative cost. The graph plans from `Coupling.mem_closure_graphPlans` approach every
coupling in the weak topology, where integration of this cost is continuous. -/
theorem mongeCost_eq_transportCost_boundedContinuous
    {μ₀ : ProbabilityMeasure X} {ν₀ : ProbabilityMeasure Y}
    [NullSingletonClass (μ₀ : Measure X)] (f : BoundedContinuousFunction (X × Y) NNReal) :
    mongeCost (fun z ↦ (f z : ℝ≥0∞)) (μ₀ : Measure X) (ν₀ : Measure Y) =
      transportCost (fun z ↦ (f z : ℝ≥0∞)) (μ₀ : Measure X) (ν₀ : Measure Y) := by
  apply le_antisymm ?_ (transportCost_le_mongeCost _ _ _)
  apply le_transportCost
  intro π hπ
  let ρ : ProbabilityMeasure (X × Y) := ⟨π, hπ.isProbabilityMeasure⟩
  let π₀ : Coupling μ₀ ν₀ := ⟨ρ, hπ⟩
  have hclosure := Coupling.mem_closure_graphPlans π₀
  have hcont : Continuous (fun σ : ProbabilityMeasure (X × Y) ↦ ∫⁻ z, f z ∂σ) :=
    ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction f
  have hclosed : IsClosed {σ : ProbabilityMeasure (X × Y) |
      mongeCost (fun z ↦ (f z : ℝ≥0∞)) (μ₀ : Measure X) (ν₀ : Measure Y) ≤
        ∫⁻ z, f z ∂σ} := isClosed_le continuous_const hcont
  have hsubset :
      {σ : ProbabilityMeasure (X × Y) |
        ∃ T : X → Y, MeasurePreserving T (μ₀ : Measure X) (ν₀ : Measure Y) ∧
          σ.toMeasure = graphPlan T (μ₀ : Measure X)} ⊆
      {σ : ProbabilityMeasure (X × Y) |
        mongeCost (fun z ↦ (f z : ℝ≥0∞)) (μ₀ : Measure X) (ν₀ : Measure Y) ≤
          ∫⁻ z, f z ∂σ} := by
    intro σ hσ
    obtain ⟨T, hT, hσ⟩ := hσ
    calc
      mongeCost (fun z ↦ (f z : ℝ≥0∞)) (μ₀ : Measure X) (ν₀ : Measure Y) ≤
          transportMapCost (fun z ↦ (f z : ℝ≥0∞)) (μ₀ : Measure X) T :=
        mongeCost_le_transportMapCost hT.hasLaw _
      _ = ∫⁻ z, f z ∂graphPlan T (μ₀ : Measure X) :=
        transportMapCost_eq_lintegral_graphPlan hT.aemeasurable
          (measurable_coe_nnreal_ennreal.comp f.continuous.measurable).aemeasurable
      _ = ∫⁻ z, f z ∂σ := by rw [hσ]
  have hmem : ρ ∈ {σ : ProbabilityMeasure (X × Y) |
      mongeCost (fun z ↦ (f z : ℝ≥0∞)) (μ₀ : Measure X) (ν₀ : Measure Y) ≤
        ∫⁻ z, f z ∂σ} := hclosed.closure_subset (closure_mono hsubset hclosure)
  exact hmem

/-! ### Costs with an integrable split upper envelope -/

section SplitEnvelope

open ProbabilityTheory

variable {c : X × Y → ℝ≥0∞} {a : X → ℝ≥0∞} {b : Y → ℝ≥0∞}

/-- The truncation `min c R` of a continuous cost at a finite level is a bounded continuous cost,
so transport maps approach its integral against every coupling. -/
private theorem IsCoupling.exists_hasLaw_lintegral_min_lt (hπ : IsCoupling π μ ν)
    (hc : Continuous c) (R : NNReal) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ T : X → Y, HasLaw T ν μ ∧
      ∫⁻ z, min (c z) R ∂graphPlan T μ < ∫⁻ z, min (c z) R ∂π + η := by
  let : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hπ.snd_eq ▸ inferInstance
  have hfin (z : X × Y) : min (c z) R ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hle (z : X × Y) : (min (c z) R).toNNReal ≤ R := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hfin z)]
    exact min_le_right _ _
  let f : BoundedContinuousFunction (X × Y) NNReal := BoundedContinuousFunction.mkOfBound
    ⟨fun z ↦ (min (c z) R).toNNReal,
      ENNReal.continuousOn_toNNReal.comp_continuous (hc.min continuous_const) hfin⟩ R
    fun z w ↦ by
      rw [NNReal.dist_eq]
      exact abs_sub_le_of_nonneg_of_le (by positivity) (by exact_mod_cast hle z)
        (by positivity) (by exact_mod_cast hle w)
  have hf : (fun z ↦ (f z : ℝ≥0∞)) = fun z ↦ min (c z) R :=
    funext fun z ↦ ENNReal.coe_toNNReal (hfin z)
  have hfπ : ∫⁻ z, f z ∂π ≠ ∞ := by
    rw [hf]
    exact ne_top_of_le_ne_top (by simp) (lintegral_mono fun z ↦ min_le_right (c z) R)
  -- The bounded-cost theorem takes bundled laws; the coercion of `μ₀` is `μ` itself.
  let μ₀ : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  have : NullSingletonClass (μ₀ : Measure X) := ‹NullSingletonClass μ›
  have hfm : Measurable fun z ↦ (f z : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp f.continuous.measurable
  obtain ⟨T, hT, hTlt⟩ : ∃ T : X → Y, HasLaw T ν μ ∧
      transportMapCost (fun z ↦ (f z : ℝ≥0∞)) μ T < ∫⁻ z, f z ∂π + η :=
    mongeCost_lt_iff.1 <|
      ((mongeCost_eq_transportCost_boundedContinuous (μ₀ := μ₀) (ν₀ := ⟨ν, inferInstance⟩)
        f).trans_le (transportCost_le_lintegral hπ _)).trans_lt (ENNReal.lt_add_right hfπ hη)
  refine ⟨T, hT, ?_⟩
  rwa [transportMapCost_eq_lintegral_graphPlan hT.aemeasurable hfm.aemeasurable, hf] at hTlt

/-- **Transport maps approximate the cost of every coupling.** Let the cost be continuous and
bounded by an integrable split envelope `c (x, y) ≤ a x + b y`. For an atomless source, the cost
of every coupling `π` is approached from above by the costs of transport maps: for every `η > 0`
some transport map costs at most `∫⁻ c ∂π + η`. -/
theorem IsCoupling.exists_hasLaw_transportMapCost_le (hπ : IsCoupling π μ ν) (hc : Continuous c)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b ν) (haint : ∫⁻ x, a x ∂μ ≠ ∞)
    (hbint : ∫⁻ y, b y ∂ν ≠ ∞) (hcab : ∀ z, c z ≤ a z.1 + b z.2) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ T : X → Y, HasLaw T ν μ ∧ transportMapCost c μ T ≤ ∫⁻ z, c z ∂π + η := by
  have hcm : Measurable c := hc.measurable
  -- Above a level `R` every coupling, in particular every graph plan, spends at most `η / 2`.
  obtain ⟨R, hR⟩ := exists_forall_setLIntegral_le_of_le_split ha hb haint hbint hcab
    (ENNReal.half_pos hη.ne')
  -- Below `R` the cost is bounded continuous, so some transport map matches `π` up to `η / 2`.
  obtain ⟨T, hT, hTlt⟩ := hπ.exists_hasLaw_lintegral_min_lt hc R (ENNReal.half_pos hη.ne').ne'
  refine ⟨T, hT, ?_⟩
  calc transportMapCost c μ T = ∫⁻ z, c z ∂graphPlan T μ :=
        transportMapCost_eq_lintegral_graphPlan hT.aemeasurable hcm.aemeasurable
    _ ≤ ∫⁻ z, min (c z) R + {z | (R : ℝ≥0∞) ≤ c z}.indicator c z ∂graphPlan T μ := by
        refine lintegral_mono fun z ↦ ?_
        by_cases hz : (R : ℝ≥0∞) ≤ c z
        · simp [hz]
        · simp [hz, (not_le.1 hz).le]
    _ = ∫⁻ z, min (c z) R ∂graphPlan T μ +
          ∫⁻ z in {z | (R : ℝ≥0∞) ≤ c z}, c z ∂graphPlan T μ := by
        rw [lintegral_add_left (hcm.min measurable_const),
          lintegral_indicator (measurableSet_le measurable_const hcm)]
    _ ≤ (∫⁻ z, min (c z) R ∂π + η / 2) + η / 2 :=
        add_le_add hTlt.le
          (hR _ (isCoupling_graphPlan hT).fst_eq.le (isCoupling_graphPlan hT).snd_eq.le)
    _ ≤ ∫⁻ z, c z ∂π + η := by
        rw [add_assoc, ENNReal.add_halves]
        gcongr with z
        exact min_le_left _ _

/-- **Monge's and Kantorovich's values agree for continuous costs with an integrable split upper
envelope.** For an atomless source law, a continuous cost bounded by `a x + b y` with finite
marginal integrals has the same Monge and Kantorovich values. The Monge infimum need not be
attained. -/
theorem mongeCost_eq_transportCost_of_le_split (hc : Continuous c)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b ν) (haint : ∫⁻ x, a x ∂μ ≠ ∞)
    (hbint : ∫⁻ y, b y ∂ν ≠ ∞) (hcab : ∀ z, c z ≤ a z.1 + b z.2) :
    mongeCost c μ ν = transportCost c μ ν := by
  refine le_antisymm (le_transportCost fun π hπ ↦ ?_) (transportCost_le_mongeCost c μ ν)
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ ↦ ?_
  obtain ⟨T, hT, hle⟩ := hπ.exists_hasLaw_transportMapCost_le hc ha hb haint hbint hcab
    (η := η) (by exact_mod_cast hη)
  exact (mongeCost_le_transportMapCost hT c).trans hle

end SplitEnvelope

end Probability

/-! ### Finite equal-mass measures -/

section FiniteEqualMass

variable [IsFiniteMeasure μ] [NullSingletonClass μ] [Nonempty Y]

/-- For finite measures of equal mass with an atomless source and a nonempty target type, the
Monge and Kantorovich values agree for every bounded continuous nonnegative cost. The zero-mass
case is handled without normalization. -/
theorem mongeCost_eq_transportCost_boundedContinuous_of_measure_univ_eq
    (hmass : μ univ = ν univ) (f : BoundedContinuousFunction (X × Y) NNReal) :
    mongeCost (fun z ↦ (f z : ℝ≥0∞)) μ ν =
      transportCost (fun z ↦ (f z : ℝ≥0∞)) μ ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.1 <| by
      rw [← hmass, hμ]
      simp
    rw [hμ, hν]
    exact mongeCost_eq_transportCost_zero_measure _
  have hm₀ : μ univ ≠ 0 := mt Measure.measure_univ_eq_zero.1 hμ
  have hm_top : μ univ ≠ ∞ := measure_ne_top μ univ
  let μ' := (μ univ)⁻¹ • μ
  let ν' := (μ univ)⁻¹ • ν
  let : NeZero μ := ⟨hμ⟩
  let : IsProbabilityMeasure μ' := inferInstance
  let : NullSingletonClass μ' := ⟨fun x ↦ by simp [μ', Measure.smul_apply]⟩
  let : IsProbabilityMeasure ν' := ⟨by
    simp only [ν', Measure.smul_apply, smul_eq_mul, ← hmass,
      ENNReal.inv_mul_cancel hm₀ hm_top]⟩
  let μ₀ : ProbabilityMeasure X := ⟨μ', inferInstance⟩
  let ν₀ : ProbabilityMeasure Y := ⟨ν', inferInstance⟩
  -- Instance search does not unfold the coercion `(μ₀ : Measure X)` to `μ'`, so the
  -- atomlessness instance for `μ'` is transported along this definitional equality explicitly.
  let : NullSingletonClass (μ₀ : Measure X) := inferInstanceAs (NullSingletonClass μ')
  apply mongeCost_eq_transportCost_of_normalized hμ
  exact mongeCost_eq_transportCost_boundedContinuous
    (μ₀ := μ₀) (ν₀ := ν₀) f

/-- For finite measures of equal mass with an atomless source and a nonempty target type, Monge's
and Kantorovich's values agree for a continuous cost with an integrable split upper envelope. The
zero-mass case is handled without normalization. -/
theorem mongeCost_eq_transportCost_of_le_split_of_measure_univ_eq {c : X × Y → ℝ≥0∞}
    {a : X → ℝ≥0∞} {b : Y → ℝ≥0∞} (hmass : μ univ = ν univ) (hc : Continuous c)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b ν) (haint : ∫⁻ x, a x ∂μ ≠ ∞)
    (hbint : ∫⁻ y, b y ∂ν ≠ ∞) (hcab : ∀ z, c z ≤ a z.1 + b z.2) :
    mongeCost c μ ν = transportCost c μ ν := by
  by_cases hμ : μ = 0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.1 <| by
      rw [← hmass, hμ]
      simp
    rw [hμ, hν]
    exact mongeCost_eq_transportCost_zero_measure _
  have hm₀ : μ univ ≠ 0 := mt Measure.measure_univ_eq_zero.1 hμ
  have hm_top : μ univ ≠ ∞ := measure_ne_top μ univ
  have hinv₀ : (μ univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hm_top
  let μ' := (μ univ)⁻¹ • μ
  let ν' := (μ univ)⁻¹ • ν
  let : NeZero μ := ⟨hμ⟩
  let : IsProbabilityMeasure μ' := inferInstance
  let : NullSingletonClass μ' := ⟨fun x ↦ by simp [μ', Measure.smul_apply]⟩
  let : IsProbabilityMeasure ν' := ⟨by
    simp only [ν', Measure.smul_apply, smul_eq_mul, ← hmass,
      ENNReal.inv_mul_cancel hm₀ hm_top]⟩
  have ha' : AEMeasurable a μ' := (aemeasurable_smul_measure_iff hinv₀).2 ha
  have hb' : AEMeasurable b ν' := (aemeasurable_smul_measure_iff hinv₀).2 hb
  have haint' : ∫⁻ x, a x ∂μ' ≠ ∞ := by
    simp only [μ', lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm₀) haint
  have hbint' : ∫⁻ y, b y ∂ν' ≠ ∞ := by
    simp only [ν', lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm₀) hbint
  apply mongeCost_eq_transportCost_of_normalized hμ
  exact mongeCost_eq_transportCost_of_le_split hc ha' hb' haint' hbint' hcab

end FiniteEqualMass

end TauCeti
