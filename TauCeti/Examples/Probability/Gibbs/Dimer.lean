/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Combinatorics.SimpleGraph.Matching.Dimer
public import TauCeti.Probability.Gibbs.Dimer.Specification

/-!
# Checks for the dimer specification and dimer Gibbs measures

* **The line.** On the nearest-neighbour graph of `ℤ`, two dimer configurations agreeing off a
  finite set are equal (`eq_of_isDimerConfiguration_int`), so every completion set is a singleton
  (`dimerCompletionSet_int`), the Boltzmann laws are point masses (`dimerBoltzmann_int`) and every
  measure on `𝔛(ℤ)`, for example `(δ_even + δ_odd)/2`, is Gibbs for the dimer specification
  (`isGibbs_dimerSpecificationInt`).
* **The null clause is needed.** On the line, the point mass at the configuration with no edge
  satisfies every cylinder identity (`dimerCylinderIdentity_dirac_noEdge`), but leaves every vertex
  uncovered, so it is not dimer Gibbs (`not_isDimerGibbs_dirac_noEdge`).
* **The hexagon.** On the `6`-cycle, the nearest-neighbour graph of `ZMod 6`, with matchings
  `M_a = hexConfig true = {e₀, e₂, e₄}` and `M_b = hexConfig false = {e₁, e₃, e₅}`, a dimer Gibbs
  measure gives the two matchings total mass one (`measure_hexConfig_add`), and taking `F = E` the
  six edges, the cylinder identity reads `w(M_b) μ{M_a} = w(M_a) μ{M_b}`
  (`ofReal_mul_measure_hexConfig`). With unit weights each matching has mass `1/2`
  (`measure_hexConfig_true_of_one`); with `w(e₀) = 2` and `w = 1` elsewhere, `μ{M_a} = 2/3`
  (`measure_hexConfig_true_of_weightTwo`), the Boltzmann value `w(M_a)/(w(M_a) + w(M_b))`, so the
  weights in `SimpleGraph.IsDimerGibbs` enter in the right direction (the reversed reading would
  give `1/3`).
* **Gauge.** A gauge transformation multiplies the weights of both matchings of the hexagon by the
  same factor `∏_v g(v)` (`dimerWeight_gaugeWeight_hexConfig`), so the weights are not determined
  by the specification.
-/

public section

noncomputable section

open SimpleGraph MeasureTheory Set Function
open scoped ENNReal

namespace TauCeti.Examples.DimerGibbs

open TauCeti.Examples.DimerConfiguration

/-! ### The line -/

/-- The edges of the line are countable. -/
instance instCountableEdgeSetNNGraphInt : Countable (nnGraph ℤ).edgeSet :=
  Function.Surjective.countable (f := edge) fun e => exists_edge_eq e

/-- The line has infinitely many edges. -/
instance instInfiniteEdgeSetNNGraphInt : Infinite (nnGraph ℤ).edgeSet :=
  Infinite.of_injective edge (edge_injective (by decide))

/-- On the line, two dimer configurations agreeing off a finite set are equal: the even and the odd
edges differ on every edge. -/
theorem eq_of_isDimerConfiguration_int {F : Finset (nnGraph ℤ).edgeSet}
    {ω ω' : (nnGraph ℤ).edgeSet → Bool} (hω : (nnGraph ℤ).IsDimerConfiguration ω)
    (hω' : (nnGraph ℤ).IsDimerConfiguration ω') (h : ∀ e ∉ F, ω e = ω' e) : ω = ω' := by
  obtain ⟨e, he⟩ := Infinite.exists_notMem_finset F
  obtain ⟨a, rfl⟩ := exists_edge_eq e
  have h₁ : ω ∈ ({evenConfig, oddConfig} : Set _) := setOf_isDimerConfiguration_int ▸ hω
  have h₂ : ω' ∈ ({evenConfig, oddConfig} : Set _) := setOf_isDimerConfiguration_int ▸ hω'
  have ha := h _ he
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> try rfl
  all_goals
    rcases Int.even_or_odd a with h | h <;>
      simp_all [← Int.not_even_iff_odd]

/-- On the line, the completion set of a dimer configuration at any finite set is the singleton of
it. -/
theorem dimerCompletionSet_int (F : Finset (nnGraph ℤ).edgeSet)
    {ω : (nnGraph ℤ).edgeSet → Bool} (hω : (nnGraph ℤ).IsDimerConfiguration ω) :
    (nnGraph ℤ).dimerCompletionSet F ω = {ω} := by
  ext ω'
  simp only [mem_dimerCompletionSet, mem_singleton_iff]
  exact ⟨fun ⟨h', h⟩ => eq_of_isDimerConfiguration_int h' hω h,
    by rintro rfl; exact ⟨hω, fun _ _ => rfl⟩⟩

/-- On the line, the Boltzmann law of a dimer configuration at any finite set is the point mass at
it. -/
theorem dimerBoltzmann_int {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (F : Finset (nnGraph ℤ).edgeSet) {ω : (nnGraph ℤ).edgeSet → Bool}
    (hω : (nnGraph ℤ).IsDimerConfiguration ω) :
    (nnGraph ℤ).dimerBoltzmann w F ω = Measure.dirac ω := by
  have hfin : ((nnGraph ℤ).finite_dimerCompletionSet F ω).toFinset = {ω} := by
    ext ω'
    simp [dimerCompletionSet_int F hω]
  rw [dimerBoltzmann_def, dimerPartitionFunction_def, hfin, Finset.sum_singleton,
    Finset.sum_singleton, div_self (dimerWeight_pos hw F ω).ne', ENNReal.ofReal_one, one_smul]

/-- **On the line every measure is Gibbs**: for `2ℤ` acting by translations, the kernels of the
dimer specification are the point masses `γ^w_F(· | ω) = δ_ω`, so resampling changes nothing. In
particular `(δ_even + δ_odd)/2` is Gibbs. -/
theorem isGibbs_dimerSpecificationInt {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (μ : Measure ((nnGraph ℤ).dimerSubshift (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)))) :
    ((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).IsGibbs μ := by
  refine TauCeti.Specification.isGibbs_iff.2 fun F => ?_
  have hk : ⇑(((nnGraph ℤ).dimerSpecification (Multiplicative ℤ)
      (Iso.exists_compHom_smul_eq_mapEdgeSet (zpowersHom _ shiftTwo)) hw).kernel F) =
        Measure.dirac := by
    funext ω
    ext C
    rw [dimerSpecification_kernel, dimerKernel_apply,
      dimerBoltzmann_int hw F (mem_dimerSubshift.1 ω.property), Measure.dirac_apply,
      Measure.dirac_apply]
    by_cases h : ω ∈ C <;> simp [h]
  rw [hk, Measure.bind_dirac]

/-- The configuration of the line with no edge. -/
def noEdge (_ : (nnGraph ℤ).edgeSet) : Bool :=
  false

/-- The configuration with no edge leaves every vertex uncovered: it is not a dimer
configuration. -/
theorem not_isDimerConfiguration_noEdge : ¬ (nnGraph ℤ).IsDimerConfiguration noEdge := by
  rw [isDimerConfiguration_nnGraph_iff (by decide)]
  intro h
  simpa [noEdge] using h 0

/-- **The point mass at the configuration with no edge satisfies every cylinder identity**: two
dimer configurations of the line agreeing off a finite set are equal. -/
theorem dimerCylinderIdentity_dirac_noEdge (w : (nnGraph ℤ).edgeSet → ℝ)
    (F E : Finset (nnGraph ℤ).edgeSet) {ω ω' : (nnGraph ℤ).edgeSet → Bool}
    (hω : (nnGraph ℤ).IsDimerConfiguration ω) (hω' : (nnGraph ℤ).IsDimerConfiguration ω')
    (h : ∀ e ∉ F, ω e = ω' e) :
    ENNReal.ofReal ((nnGraph ℤ).dimerWeight w F ω') *
        Measure.dirac noEdge {η | ∀ e ∈ E, η e = ω e} =
      ENNReal.ofReal ((nnGraph ℤ).dimerWeight w F ω) *
        Measure.dirac noEdge {η | ∀ e ∈ E, η e = ω' e} := by
  obtain rfl := eq_of_isDimerConfiguration_int hω hω' h
  rfl

/-- **The null clause is needed**: the point mass at the configuration with no edge is not dimer
Gibbs, although it satisfies every cylinder identity. -/
theorem not_isDimerGibbs_dirac_noEdge (w : (nnGraph ℤ).edgeSet → ℝ) :
    ¬ (nnGraph ℤ).IsDimerGibbs w (Measure.dirac noEdge) := fun h => by
  have h0 := h.measure_setOf_not_isDimerConfiguration
  rw [Measure.dirac_apply_of_mem (by exact not_isDimerConfiguration_noEdge)] at h0
  exact one_ne_zero h0

/-! ### The hexagon -/

/-- `1 < 6`, so that `ZMod 6` is nontrivial. -/
local instance fact_one_lt_six : Fact (1 < 6) :=
  ⟨by decide⟩

/-- The hexagon is locally finite. -/
instance instLocallyFiniteNNGraphZModSix : (nnGraph (ZMod 6)).LocallyFinite :=
  fun _ => Fintype.ofFinite _

/-- The edges of the hexagon are finite. -/
instance instFintypeEdgeSetNNGraphZModSix : Fintype (nnGraph (ZMod 6)).edgeSet :=
  Fintype.ofFinite _

/-- The edge `{a, a + 1}` of the hexagon, as a bijection from `ZMod 6`. -/
theorem bijective_edge_zmod_six : Bijective (edge (R := ZMod 6)) :=
  ⟨edge_injective (by decide), fun e => exists_edge_eq e⟩

/-- A configuration of the hexagon is determined by its values on the edges `{a, a + 1}`. -/
theorem prod_edgeSet_zmod_six (f : (nnGraph (ZMod 6)).edgeSet → ℝ) :
    ∏ e, f e = ∏ a : ZMod 6, f (edge a) :=
  (Fintype.prod_bijective _ bijective_edge_zmod_six _ _ fun _ => rfl).symm

/-- The cylinder of a configuration of the hexagon over all six edges is its singleton. -/
theorem setOf_forall_mem_univ_eq (ω : (nnGraph (ZMod 6)).edgeSet → Bool) :
    {η : (nnGraph (ZMod 6)).edgeSet → Bool | ∀ e ∈ Finset.univ, η e = ω e} = {ω} := by
  ext η
  simp [funext_iff]

/-- **The two matchings of the hexagon carry a dimer Gibbs measure.** -/
theorem measure_hexConfig_add {w : (nnGraph (ZMod 6)).edgeSet → ℝ}
    {μ : Measure ((nnGraph (ZMod 6)).edgeSet → Bool)} (h : (nnGraph (ZMod 6)).IsDimerGibbs w μ) :
    μ {hexConfig true} + μ {hexConfig false} = 1 := by
  have := h.isProbabilityMeasure
  have hD : μ {ω | (nnGraph (ZMod 6)).IsDimerConfiguration ω} = 1 := by
    rw [← prob_compl_eq_zero_iff measurableSet_setOf_isDimerConfiguration, compl_ofPred]
    exact h.measure_setOf_not_isDimerConfiguration
  rw [setOf_isDimerConfiguration_zmod_six, ← singleton_union] at hD
  rw [← hD, measure_union _ (measurableSet_singleton _)]
  exact disjoint_singleton.2 fun h => by simpa using hexConfig_injective h

/-- **The cylinder identity of the hexagon** with `F = E` all six edges, `ω = M_a` and
`ω' = M_b`: `w(M_b) μ{M_a} = w(M_a) μ{M_b}`. -/
theorem ofReal_mul_measure_hexConfig {w : (nnGraph (ZMod 6)).edgeSet → ℝ}
    {μ : Measure ((nnGraph (ZMod 6)).edgeSet → Bool)} (h : (nnGraph (ZMod 6)).IsDimerGibbs w μ) :
    ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig false)) *
        μ {hexConfig true} =
      ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig true)) *
        μ {hexConfig false} := by
  have hD (b : Bool) : (nnGraph (ZMod 6)).IsDimerConfiguration (hexConfig b) := by
    have : hexConfig b ∈ {ω | (nnGraph (ZMod 6)).IsDimerConfiguration ω} := by
      rw [setOf_isDimerConfiguration_zmod_six]
      cases b <;> simp
    exact this
  have := h.cylinder (F := Finset.univ) (E := Finset.univ) (hD true) (hD false)
    (fun e he => absurd (Finset.mem_univ e) he) fun _ _ e' _ => Finset.mem_univ e'
  rwa [setOf_forall_mem_univ_eq, setOf_forall_mem_univ_eq] at this

/-- The weight on all six edges of a configuration of the hexagon, as a product over
`ZMod 6`. -/
theorem dimerWeight_univ_hexConfig (w : (nnGraph (ZMod 6)).edgeSet → ℝ) (b : Bool) :
    (nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig b) =
      ∏ a : ZMod 6, if (b ^^ decide (a.val % 2 = 1)) = true then w (edge a) else 1 := by
  rw [dimerWeight_def, Finset.prod_filter, prod_edgeSet_zmod_six]
  simp only [hexConfig_edge]

/-- **Unit weights on the hexagon**: every dimer Gibbs measure gives each matching mass `1/2`. -/
theorem measure_hexConfig_true_of_one {μ : Measure ((nnGraph (ZMod 6)).edgeSet → Bool)}
    (h : (nnGraph (ZMod 6)).IsDimerGibbs 1 μ) :
    μ {hexConfig true} = 2⁻¹ ∧ μ {hexConfig false} = 2⁻¹ := by
  have h₁ := ofReal_mul_measure_hexConfig h
  simp only [dimerWeight_one, ENNReal.ofReal_one, one_mul] at h₁
  have h₂ := measure_hexConfig_add h
  rw [h₁, ← two_mul] at h₂
  refine ⟨?_, ?_⟩ <;>
    [rw [h₁]; skip] <;>
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])

/-- The weight `w(e₀) = 2` and `w = 1` on the other edges of the hexagon. -/
def weightTwo (e : (nnGraph (ZMod 6)).edgeSet) : ℝ :=
  if e = DimerConfiguration.edge (0 : ZMod 6) then 2 else 1

/-- **The direction of the weights**: for `w(e₀) = 2` and `w = 1` elsewhere, every dimer Gibbs
measure gives the matching `M_a ∋ e₀` the Boltzmann mass `2/3`. -/
theorem measure_hexConfig_true_of_weightTwo {μ : Measure ((nnGraph (ZMod 6)).edgeSet → Bool)}
    (h : (nnGraph (ZMod 6)).IsDimerGibbs weightTwo μ) :
    μ {hexConfig true} = 2 / 3 ∧ μ {hexConfig false} = 1 / 3 := by
  have hw (a : ZMod 6) : weightTwo (edge a) = if a = 0 then 2 else 1 := by
    simp only [weightTwo, (edge_injective (R := ZMod 6) (by decide)).eq_iff]
  have hT : (nnGraph (ZMod 6)).dimerWeight weightTwo Finset.univ (hexConfig true) = 2 := by
    rw [dimerWeight_univ_hexConfig, Finset.prod_eq_single_of_mem 0 (Finset.mem_univ _)
      fun a _ ha => by simp [hw, ha]]
    simp [hw]
  have hF : (nnGraph (ZMod 6)).dimerWeight weightTwo Finset.univ (hexConfig false) = 1 := by
    rw [dimerWeight_univ_hexConfig]
    exact Finset.prod_eq_one fun a _ => by by_cases ha : a = 0 <;> simp [hw, ha]
  have h₁ := ofReal_mul_measure_hexConfig h
  rw [hT, hF, ENNReal.ofReal_one, one_mul, ENNReal.ofReal_ofNat] at h₁
  have h₂ := measure_hexConfig_add h
  rw [h₁] at h₂
  have hb : μ {hexConfig false} = 1 / 3 := by
    rw [← add_one_mul, show (2 : ℝ≥0∞) + 1 = 3 by norm_num] at h₂
    rw [ENNReal.div_eq_inv_mul, mul_one]
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])
  refine ⟨?_, hb⟩
  rw [h₁, hb, ← mul_div_assoc, mul_one]

/-- **Gauge on the hexagon**: a gauge transformation multiplies the weights of both matchings by
the same factor `∏_v g(v)`. -/
theorem dimerWeight_gaugeWeight_hexConfig (w : (nnGraph (ZMod 6)).edgeSet → ℝ)
    (g : ZMod 6 → ℝ) (b : Bool) :
    (nnGraph (ZMod 6)).dimerWeight ((nnGraph (ZMod 6)).gaugeWeight w g) Finset.univ
        (hexConfig b) =
      (nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig b) * ∏ v, g v := by
  have hD : (nnGraph (ZMod 6)).IsDimerConfiguration (hexConfig b) := by
    have : hexConfig b ∈ {ω | (nnGraph (ZMod 6)).IsDimerConfiguration ω} := by
      rw [setOf_isDimerConfiguration_zmod_six]
      cases b <;> simp
    exact this
  rw [dimerWeight_gaugeWeight w g Finset.univ hD]
  congr 1
  refine Finset.prod_congr (Finset.eq_univ_of_forall fun v => ?_) fun _ _ => rfl
  rw [hD.mem_dimerCoveredVertices_iff]
  refine ⟨⟨edge v, Finset.mem_univ _, ?_⟩, fun e he => absurd (Finset.mem_univ e) he⟩
  simp [coe_edge]

end TauCeti.Examples.DimerGibbs
