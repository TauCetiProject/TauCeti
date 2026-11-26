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
  (`isGibbs_dimerSpecification_int`).
* **The null clause is needed.** On the line, every measure satisfies every cylinder identity
  (`ofReal_mul_measure_cylinder_int`), in particular the point mass at the configuration with no
  edge, which leaves every vertex uncovered, so it is not dimer Gibbs
  (`not_isDimerGibbs_dirac_noEdge`).
* **The hexagon.** On the `6`-cycle, the nearest-neighbour graph of `ZMod 6`, with matchings
  `M_a = hexConfig true = {e₀, e₂, e₄}` and `M_b = hexConfig false = {e₁, e₃, e₅}`, every dimer
  Gibbs measure gives the two matchings total mass one (`measure_hexConfig_add`), and taking
  `F = E` the six edges, the cylinder identity reads `w(M_b) μ{M_a} = w(M_a) μ{M_b}`
  (`ofReal_mul_measure_hexConfig`). So for positive weights the only dimer Gibbs measure is the
  Boltzmann measure: `μ{M} = w(M)/(w(M_a) + w(M_b))` (`measure_hexConfig`), and this measure is
  dimer Gibbs (`isDimerGibbs_hexConfig`). With unit weights each matching has mass `1/2`
  (`measure_hexConfig_of_one`, `isDimerGibbs_one_hexConfig`); with `w(e₀) = 2` and `w = 1`
  elsewhere, `μ{M_a} = 2/3` and `μ{M_b} = 1/3` (`measure_hexConfig_of_weightTwo`,
  `isDimerGibbs_weightTwo_hexConfig`), so the weights in `SimpleGraph.IsDimerGibbs` enter in the
  right direction (the reversed reading would give `μ{M_a} = 1/3`).
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
    (nnGraph ℤ).dimerCompletionSet F ω = {ω} :=
  eq_singleton_iff_unique_mem.2
    ⟨mem_dimerCompletionSet_self hω, fun _ h =>
      eq_of_isDimerConfiguration_int (mem_dimerCompletionSet.1 h).1 hω
        (mem_dimerCompletionSet.1 h).2⟩

/-- On the line, the Boltzmann law of a dimer configuration at any finite set is the point mass at
it. -/
theorem dimerBoltzmann_int {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    (F : Finset (nnGraph ℤ).edgeSet) {ω : (nnGraph ℤ).edgeSet → Bool}
    (hω : (nnGraph ℤ).IsDimerConfiguration ω) :
    (nnGraph ℤ).dimerBoltzmann w F ω = Measure.dirac ω := by
  have hfin : ((nnGraph ℤ).finite_dimerCompletionSet F ω).toFinset = {ω} := by
    ext ω'
    simp [dimerCompletionSet_int F hω]
  simp [dimerBoltzmann_def, dimerPartitionFunction_def, hfin, (dimerWeight_pos hw F ω).ne']

/-- **On the line every measure is Gibbs**: for `2ℤ` acting by translations, the kernels of the
dimer specification are the point masses `γ^w_F(· | ω) = δ_ω`, so resampling changes nothing. In
particular `(δ_even + δ_odd)/2` is Gibbs. -/
theorem isGibbs_dimerSpecification_int {w : (nnGraph ℤ).edgeSet → ℝ} (hw : ∀ e, 0 < w e)
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
  rw [hk]
  exact Measure.bind_dirac

/-- **On the line every measure satisfies every cylinder identity**: for dimer configurations
`ω`, `ω'` agreeing off `F`, `w(ω' ∩ F) μ[ω]_E = w(ω ∩ F) μ[ω']_E`. -/
theorem ofReal_mul_measure_cylinder_int (w : (nnGraph ℤ).edgeSet → ℝ)
    (μ : Measure ((nnGraph ℤ).edgeSet → Bool)) (F E : Finset (nnGraph ℤ).edgeSet)
    {ω ω' : (nnGraph ℤ).edgeSet → Bool} (hω : (nnGraph ℤ).IsDimerConfiguration ω)
    (hω' : (nnGraph ℤ).IsDimerConfiguration ω') (h : ∀ e ∉ F, ω e = ω' e) :
    ENNReal.ofReal ((nnGraph ℤ).dimerWeight w F ω') * μ {η | ∀ e ∈ E, η e = ω e} =
      ENNReal.ofReal ((nnGraph ℤ).dimerWeight w F ω) * μ {η | ∀ e ∈ E, η e = ω' e} := by
  obtain rfl := eq_of_isDimerConfiguration_int hω hω' h
  rfl

/-- The configuration of the line with no edge. -/
def noEdge (_ : (nnGraph ℤ).edgeSet) : Bool :=
  false

/-- The configuration with no edge leaves every vertex uncovered: it is not a dimer
configuration. -/
theorem not_isDimerConfiguration_noEdge : ¬ (nnGraph ℤ).IsDimerConfiguration noEdge := by
  rw [isDimerConfiguration_nnGraph_iff (by decide)]
  intro h
  simpa [noEdge] using h 0

/-- **The null clause is needed**: the point mass at the configuration with no edge is not dimer
Gibbs, although it satisfies every cylinder identity (`ofReal_mul_measure_cylinder_int`). -/
theorem not_isDimerGibbs_dirac_noEdge (w : (nnGraph ℤ).edgeSet → ℝ) :
    ¬ (nnGraph ℤ).IsDimerGibbs w (Measure.dirac noEdge) := fun h => by
  have h0 := h.measure_setOf_not_isDimerConfiguration
  rw [Measure.dirac_apply_of_mem (by exact not_isDimerConfiguration_noEdge)] at h0
  exact one_ne_zero h0

/-! ### The hexagon -/

/-- `1 < 6`, so that `ZMod 6` is nontrivial. -/
local instance fact_one_lt_six : Fact (1 < 6) :=
  ⟨by decide⟩

/-- **Every dimer Gibbs measure on the hexagon is carried by its two matchings**:
`μ{M_a} + μ{M_b} = 1`. -/
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
  have := h.cylinder (F := Finset.univ) (E := Finset.univ) (isDimerConfiguration_hexConfig true)
    (isDimerConfiguration_hexConfig false) (fun e he => absurd (Finset.mem_univ e) he)
    fun _ _ e' _ => Finset.mem_univ e'
  simpa only [Finset.mem_univ, forall_const, ← funext_iff, ofPred_eq_eq_singleton] using this

/-- **Uniqueness of the dimer Gibbs measure of the hexagon**: for positive weights, every dimer
Gibbs measure gives the matching `M` the Boltzmann mass `w(M)/(w(M_a) + w(M_b))`. -/
theorem measure_hexConfig {w : (nnGraph (ZMod 6)).edgeSet → ℝ} (hw : ∀ e, 0 < w e)
    {μ : Measure ((nnGraph (ZMod 6)).edgeSet → Bool)} (h : (nnGraph (ZMod 6)).IsDimerGibbs w μ)
    (b : Bool) :
    μ {hexConfig b} =
      ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig b)) /
        (ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig true)) +
          ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig false))) := by
  have h₁ := ofReal_mul_measure_hexConfig h
  have h₂ := measure_hexConfig_add h
  have hA := ENNReal.ofReal_pos.2 (dimerWeight_pos hw Finset.univ (hexConfig true))
  rw [ENNReal.eq_div_iff (hA.trans_le le_self_add).ne'
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩), add_mul]
  cases b
  · rw [← h₁, ← mul_add, h₂, mul_one]
  · rw [h₁, ← mul_add, h₂, mul_one]

/-- **Existence of the dimer Gibbs measure of the hexagon**: for positive weights, the Boltzmann
measure giving each matching `M` the mass `w(M)/(w(M_a) + w(M_b))` is dimer Gibbs. -/
theorem isDimerGibbs_hexConfig {w : (nnGraph (ZMod 6)).edgeSet → ℝ} (hw : ∀ e, 0 < w e) :
    (nnGraph (ZMod 6)).IsDimerGibbs w
      ((ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig true)) /
          (ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig true)) +
            ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig false)))) •
        Measure.dirac (hexConfig true) +
      (ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig false)) /
          (ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig true)) +
            ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig false)))) •
        Measure.dirac (hexConfig false)) := by
  set A := ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig true))
  set B := ENNReal.ofReal ((nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig false))
  have hA : 0 < A := ENNReal.ofReal_pos.2 (dimerWeight_pos hw Finset.univ (hexConfig true))
  have hab : hexConfig true ≠ hexConfig false := hexConfig_injective.ne (by decide)
  have hD (ω : (nnGraph (ZMod 6)).edgeSet → Bool) (hω : (nnGraph (ZMod 6)).IsDimerConfiguration ω) :
      ω = hexConfig true ∨ ω = hexConfig false :=
    (Set.ext_iff.1 setOf_isDimerConfiguration_zmod_six ω).1 hω
  refine isDimerGibbs_iff.2 ⟨⟨?_⟩, ?_, fun F E ω ω' hω hω' hF hE => ?_⟩
  · simp only [add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [ENNReal.div_add_div_same, ENNReal.div_self (hA.trans_le le_self_add).ne'
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)]
  · simp [Measure.dirac_apply, isDimerConfiguration_hexConfig]
  by_cases hωω : ω = ω'
  · subst hωω
    rfl
  have hne (e : (nnGraph (ZMod 6)).edgeSet) : ω e ≠ ω' e := by
    obtain ⟨a, rfl⟩ := exists_edge_eq e
    rcases hD ω hω with rfl | rfl <;> rcases hD ω' hω' with rfl | rfl <;> simp_all
  obtain rfl : F = Finset.univ := Finset.eq_univ_of_forall fun e => by
    by_contra he
    exact hne e (hF e he)
  obtain rfl : E = Finset.univ := Finset.eq_univ_of_forall fun e' => by
    obtain ⟨a, rfl⟩ := exists_edge_eq e'
    exact hE (edge a) (Finset.mem_univ _) _ ⟨a, by simp, by simp⟩
  simp only [Finset.mem_univ, forall_const, ← funext_iff, ofPred_eq_eq_singleton]
  rcases hD ω hω with rfl | rfl <;> rcases hD ω' hω' with rfl | rfl <;>
    simp_all [A, B, div_eq_mul_inv, mul_left_comm]

/-- The dimer weight of a configuration of the hexagon on all six edges, as a product over
`ZMod 6`. -/
theorem dimerWeight_univ_hexConfig (w : (nnGraph (ZMod 6)).edgeSet → ℝ) (b : Bool) :
    (nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig b) =
      ∏ a : ZMod 6, if (b ^^ decide (a.val % 2 = 1)) = true then w (edge a) else 1 := by
  rw [dimerWeight_def, Finset.prod_filter, prod_edgeSet (by decide)]
  simp only [hexConfig_edge]

/-- **Unit weights on the hexagon**: every dimer Gibbs measure gives each matching mass `1/2`. -/
theorem measure_hexConfig_of_one {μ : Measure ((nnGraph (ZMod 6)).edgeSet → Bool)}
    (h : (nnGraph (ZMod 6)).IsDimerGibbs 1 μ) :
    μ {hexConfig true} = 2⁻¹ ∧ μ {hexConfig false} = 2⁻¹ := by
  simp [measure_hexConfig (w := 1) (fun _ => one_pos) h, one_add_one_eq_two]

/-- **Unit weights on the hexagon**: the measure giving each matching mass `1/2` is dimer Gibbs. -/
theorem isDimerGibbs_one_hexConfig :
    (nnGraph (ZMod 6)).IsDimerGibbs 1
      ((2⁻¹ : ℝ≥0∞) • Measure.dirac (hexConfig true) +
        (2⁻¹ : ℝ≥0∞) • Measure.dirac (hexConfig false)) := by
  simpa [dimerWeight_one, one_add_one_eq_two] using
    isDimerGibbs_hexConfig (w := 1) fun _ => one_pos

/-- The weight `w(e₀) = 2` and `w = 1` on the other edges of the hexagon. -/
def weightTwo (e : (nnGraph (ZMod 6)).edgeSet) : ℝ :=
  if e = DimerConfiguration.edge (0 : ZMod 6) then 2 else 1

/-- `weightTwo` is `2` on the edge `{0, 1}` and `1` on the other edges `{a, a + 1}`. -/
@[simp]
theorem weightTwo_edge (a : ZMod 6) : weightTwo (edge a) = if a = 0 then 2 else 1 := by
  simp only [weightTwo, (edge_injective (R := ZMod 6) (by decide)).eq_iff]

/-- The weight `weightTwo` is positive. -/
theorem weightTwo_pos (e : (nnGraph (ZMod 6)).edgeSet) : 0 < weightTwo e := by
  unfold weightTwo
  split_ifs <;> norm_num

/-- For `w(e₀) = 2` and `w = 1` elsewhere, the matching `M_a ∋ e₀` has weight `2` and `M_b` has
weight `1`. -/
theorem dimerWeight_weightTwo_hexConfig (b : Bool) :
    (nnGraph (ZMod 6)).dimerWeight weightTwo Finset.univ (hexConfig b) = if b then 2 else 1 := by
  rw [dimerWeight_univ_hexConfig]
  cases b
  · exact Finset.prod_eq_one fun a _ => by by_cases ha : a = 0 <;> simp [ha]
  · rw [Finset.prod_eq_single_of_mem 0 (Finset.mem_univ _) fun a _ ha => by simp [ha]]
    simp

/-- **The direction of the weights**: for `w(e₀) = 2` and `w = 1` elsewhere, every dimer Gibbs
measure gives the matching `M_a ∋ e₀` the Boltzmann mass `2/3` and `M_b` the mass `1/3`. -/
theorem measure_hexConfig_of_weightTwo {μ : Measure ((nnGraph (ZMod 6)).edgeSet → Bool)}
    (h : (nnGraph (ZMod 6)).IsDimerGibbs weightTwo μ) :
    μ {hexConfig true} = 2 / 3 ∧ μ {hexConfig false} = 1 / 3 := by
  simp only [measure_hexConfig weightTwo_pos h, dimerWeight_weightTwo_hexConfig]
  norm_num

/-- **The direction of the weights**: for `w(e₀) = 2` and `w = 1` elsewhere, the measure giving
`M_a ∋ e₀` mass `2/3` and `M_b` mass `1/3` is dimer Gibbs. -/
theorem isDimerGibbs_weightTwo_hexConfig :
    (nnGraph (ZMod 6)).IsDimerGibbs weightTwo
      ((2 / 3 : ℝ≥0∞) • Measure.dirac (hexConfig true) +
        (1 / 3 : ℝ≥0∞) • Measure.dirac (hexConfig false)) := by
  have := isDimerGibbs_hexConfig weightTwo_pos
  simp only [dimerWeight_weightTwo_hexConfig] at this
  norm_num at this
  rwa [one_div]

/-- **Gauge on the hexagon**: a gauge transformation multiplies the weights of both matchings by
the same factor `∏_v g(v)`. -/
theorem dimerWeight_gaugeWeight_hexConfig (w : (nnGraph (ZMod 6)).edgeSet → ℝ)
    (g : ZMod 6 → ℝ) (b : Bool) :
    (nnGraph (ZMod 6)).dimerWeight ((nnGraph (ZMod 6)).gaugeWeight w g) Finset.univ
        (hexConfig b) =
      (nnGraph (ZMod 6)).dimerWeight w Finset.univ (hexConfig b) * ∏ v, g v := by
  rw [dimerWeight_gaugeWeight w g Finset.univ (isDimerConfiguration_hexConfig b)]
  congr 1
  refine Finset.prod_congr (Finset.eq_univ_of_forall fun v => ?_) fun _ _ => rfl
  rw [(isDimerConfiguration_hexConfig b).mem_dimerCoveredVertices_iff]
  refine ⟨⟨edge v, Finset.mem_univ _, ?_⟩, fun e he => absurd (Finset.mem_univ e) he⟩
  simp [coe_edge]

end TauCeti.Examples.DimerGibbs
