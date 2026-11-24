/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.UniformOn
public import TauCeti.MeasureTheory.MeasurableSpace.Pi
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cylinder

/-!
# Checks: the weak topology on spaces of configurations

These examples check the weak topology on probability measures on sets of `Bool`-valued
configurations indexed by `ℤ`: the full shift, the finitely supported configurations, and the two
constant configurations. They illustrate that weak convergence can be tested on
correlation functions, that one-point functions do not determine a measure, that point masses on a
non-closed set of configurations can converge to a point mass outside it, and that the product of
trivial σ-algebras is too coarse for the weak topology:

* the point masses at the indicators of `[n, ∞)` converge to the point mass at the zero
  configuration, through convergence of all correlation functions;
* the Bernoulli product `Bern(1/2)^{⊗ℤ}` and the mixture `(δ_0 + δ_1)/2` of the two constant
  configurations have the same one-point functions `1/2` but two-point functions `1/4` and `1/2`
  at `{0, 1}`, so one-point functions do not determine the measure;
* the set of finitely supported configurations is not closed: the point masses at the indicators
  of `[0, n]` converge to the point mass at the indicator of `[0, ∞)`, and they have no limit among
  the probability measures on the finitely supported configurations;
* with the trivial σ-algebra on `Bool`, the product σ-algebra on `ℤ → Bool` is trivial, its trace
  on the two constant configurations does not contain the clopen set `{one'}` and differs from the
  Borel σ-algebra, and the two point masses there coincide; with the discrete σ-algebra the
  trace is the Borel σ-algebra and `(δ_zero' + δ_one')/2` gives `{one'}` mass `1/2`.
-/

open MeasureTheory Filter Topology Set SymbolicDynamics ProbabilityTheory
open scoped ENNReal NNReal

public noncomputable section

namespace TauCeti.Examples.WeakTopologyConfigurations

/-- A configuration as a point of the full shift `univ`. -/
def pt (x : ℤ → Bool) : (univ : Set (ℤ → Bool)) := ⟨x, mem_univ x⟩

private theorem measurable_pt : Measurable pt :=
  measurable_id.subtype_mk

-- The point masses at the indicators of `[n, ∞)` converge to the point mass at zero.
example : Tendsto (fun n : ℕ => diracProba (pt fun i => decide ((n : ℤ) ≤ i))) atTop
    (𝓝 (diracProba (pt fun _ => false))) := by
  refine tendsto_iff_forall_tendsto_correlationFunction.2 fun F => tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := F.bddAbove
  filter_upwards [eventually_gt_atTop N.toNat] with n hn
  simp only [ProbabilityMeasure.correlationFunction_diracProba, pt]
  rcases F.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp
  · have : ¬ (n : ℤ) ≤ i := by have := hN hi; omega
    have h1 : ¬ ∀ j ∈ F, (fun _ : ℤ => false) j = true := fun h => by simpa using h i hi
    have h2 : ¬ ∀ j ∈ F, decide ((n : ℤ) ≤ j) = true := fun h => this (by simpa using h i hi)
    simp only [h1, h2, ite_false]

/-- The two-sided Bernoulli product `Bern(1/2)^{⊗ℤ}`. -/
def bernoulliProduct : ProbabilityMeasure (ℤ → Bool) :=
  ⟨Measure.infinitePi fun _ : ℤ => uniformOn (univ : Set Bool), inferInstance⟩

/-- The two-sided Bernoulli product `Bern(1/2)^{⊗ℤ}`, as a measure on the full shift `univ`. -/
def bernoulliHalf : ProbabilityMeasure (univ : Set (ℤ → Bool)) :=
  bernoulliProduct.map pt

/-- The mixture `(δ_0 + δ_1)/2` of the point masses at the two constant configurations. -/
def constMix : ProbabilityMeasure (univ : Set (ℤ → Bool)) :=
  ProbabilityMeasure.convexComb ENNReal.inv_two_add_inv_two
    (diracProba (pt fun _ => false)) (diracProba (pt fun _ => true))

private theorem correlationFunction_bernoulliHalf (F : Finset ℤ) :
    bernoulliHalf.correlationFunction F = 2⁻¹ ^ F.card := by
  have : pt ⁻¹' ((↑) ⁻¹' FullShift.cylinder F fun _ => true) =
      Set.pi (F : Set ℤ) fun _ => {true} := by
    ext x
    simp [pt, FullShift.mem_cylinder]
  rw [ProbabilityMeasure.correlationFunction_def, bernoulliHalf,
    ProbabilityMeasure.map_apply _ measurable_pt.aemeasurable
      (measurableSet_preimage_fullShift_cylinder _ _), this]
  simp [bernoulliProduct, Measure.infinitePi_pi, uniformOn_univ, ENNReal.toNNReal_ofNat,
    -Bool.univ_eq]

private theorem correlationFunction_constMix (F : Finset ℤ) (hF : F.Nonempty) :
    constMix.correlationFunction F = 2⁻¹ := by
  obtain ⟨i, hi⟩ := hF
  simp [constMix, pt, show ¬ ∀ j, j ∉ F from fun h => h i hi, ENNReal.toNNReal_ofNat]

-- One-point functions agree, two-point functions at `{0, 1}` differ.
example : (∀ i : ℤ, bernoulliHalf.correlationFunction {i} = 2⁻¹ ∧
      constMix.correlationFunction {i} = 2⁻¹) ∧
    bernoulliHalf.correlationFunction {0, 1} = 4⁻¹ ∧
    constMix.correlationFunction {0, 1} = 2⁻¹ ∧ bernoulliHalf ≠ constMix := by
  have hb : bernoulliHalf.correlationFunction {0, 1} = 4⁻¹ := by
    rw [correlationFunction_bernoulliHalf]
    norm_num
  have hc : constMix.correlationFunction {0, 1} = 2⁻¹ :=
    correlationFunction_constMix _ (Finset.insert_nonempty _ _)
  refine ⟨fun i => ⟨by simp [correlationFunction_bernoulliHalf],
    correlationFunction_constMix _ (Finset.singleton_nonempty i)⟩, hb, hc, fun h => ?_⟩
  rw [h, hc] at hb
  norm_num at hb

/-- The finitely supported configurations. -/
def finSupp : Set (ℤ → Bool) := {x | {i | x i = true}.Finite}

/-- The indicator of `[0, n]`. -/
def segment (n : ℕ) : ℤ → Bool := fun i => decide (0 ≤ i ∧ i ≤ n)

/-- The indicator of `[0, ∞)`. -/
def halfLine : ℤ → Bool := fun i => decide (0 ≤ i)

private theorem segment_mem (n : ℕ) : segment n ∈ finSupp :=
  (Set.finite_Icc (0 : ℤ) n).subset fun i hi => by simpa [segment] using hi

private theorem halfLine_notMem : halfLine ∉ finSupp := fun h =>
  Set.Ici_infinite (0 : ℤ) (h.subset fun i hi => by simpa [halfLine] using hi)

private theorem tendsto_segment : Tendsto segment atTop (𝓝 halfLine) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop i.toNat] with n hn
  simp only [segment, halfLine]
  congr 1
  apply propext
  omega

private theorem tendsto_diracProba_segment :
    Tendsto (fun n => diracProba (segment n)) atTop (𝓝 (diracProba halfLine)) :=
  (continuous_diracProba.tendsto _).comp tendsto_segment

private theorem measurableSet_finSupp : MeasurableSet finSupp := by
  refine ((countable_range fun s : Finset ℤ => fun i => decide (i ∈ s)).mono ?_).measurableSet
  intro x hx
  have hx' : {i | x i = true}.Finite := hx
  refine ⟨hx'.toFinset, funext fun i => ?_⟩
  by_cases h : x i = true <;> simp [h]

-- The finitely supported configurations are not closed.
example : ¬ IsClosed finSupp := fun h =>
  halfLine_notMem (h.mem_of_tendsto tendsto_segment (Eventually.of_forall segment_mem))

-- The point masses at the indicators of `[0, n]` converge to the point mass at `[0, ∞)`.
example : Tendsto (fun n => diracProba (segment n)) atTop (𝓝 (diracProba halfLine)) :=
  tendsto_diracProba_segment

-- Among the probability measures on the finitely supported configurations, the point masses at
-- the indicators of `[0, n]` have no limit.
example : ¬ ∃ μ : ProbabilityMeasure finSupp,
    Tendsto (fun n => diracProba (⟨segment n, segment_mem n⟩ : finSupp)) atTop (𝓝 μ) := by
  rintro ⟨μ, hμ⟩
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ continuous_subtypeVal
  have hδ : ∀ n, (diracProba (⟨segment n, segment_mem n⟩ : finSupp)).map (↑) =
      diracProba (segment n) := fun n =>
    ProbabilityMeasure.map_diracProba measurable_subtypeVal _
  simp only [hδ] at hmap
  have hlim : μ.map (↑) = diracProba halfLine :=
    tendsto_nhds_unique hmap tendsto_diracProba_segment
  have h1 : (μ.map ((↑) : finSupp → ℤ → Bool)) finSupp = 1 := by
    rw [ProbabilityMeasure.map_apply _ measurable_subtypeVal.aemeasurable measurableSet_finSupp]
    simp
  simp [hlim, diracProba_apply' _ measurableSet_finSupp, halfLine_notMem] at h1

/-- The two constant configurations. -/
def constants : Set (ℤ → Bool) := {fun _ => false, fun _ => true}

/-- The zero configuration. -/
def zero' : constants := ⟨fun _ => false, by simp [constants]⟩

/-- The constant configuration `1`. -/
def one' : constants := ⟨fun _ => true, by simp [constants]⟩

/-- The trace on the constant configurations of the product of trivial σ-algebras on `Bool`. -/
abbrev trivialTrace : MeasurableSpace constants :=
  (@MeasurableSpace.pi ℤ (fun _ => Bool) fun _ => ⊥).comap (↑)

private theorem trivialTrace_eq_bot : trivialTrace = ⊥ := by
  rw [trivialTrace, MeasurableSpace.pi_bot, MeasurableSpace.comap_bot]

private theorem one'_ne_zero' : one' ≠ zero' := fun h => by
  simpa [one', zero'] using congrFun (congrArg Subtype.val h) 0

private theorem singleton_one'_eq : ({one'} : Set constants) =
    (↑) ⁻¹' FullShift.cylinder ({0} : Finset ℤ) fun _ => true := by
  ext ⟨x, hx⟩
  simp only [constants, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> simp [one', FullShift.mem_cylinder, Subtype.ext_iff, funext_iff]

private theorem isClopen_singleton_one' : IsClopen ({one'} : Set constants) := by
  rw [singleton_one'_eq]
  exact ⟨(FullShift.isClosed_cylinder _ _).preimage continuous_subtypeVal,
    (FullShift.isOpen_cylinder _ _).preimage continuous_subtypeVal⟩

-- With the trivial σ-algebra on `Bool`: the product σ-algebra is trivial, the clopen set `{one'}`
-- is not in its trace, the trace is not the Borel σ-algebra, and all point masses coincide.
example : (@MeasurableSpace.pi ℤ (fun _ => Bool) fun _ => ⊥) = ⊥ ∧
    IsClopen ({one'} : Set constants) ∧ ¬ MeasurableSet[trivialTrace] {one'} ∧
    trivialTrace ≠ borel constants ∧
    @Measure.dirac constants trivialTrace zero' = @Measure.dirac constants trivialTrace one' := by
  have hnot : ¬ MeasurableSet[trivialTrace] {one'} := by
    rw [trivialTrace_eq_bot, MeasurableSpace.measurableSet_bot_iff]
    rintro (h | h)
    · exact (singleton_nonempty _).ne_empty h
    · exact one'_ne_zero' (mem_singleton_iff.mp (h ▸ mem_univ zero')).symm
  refine ⟨MeasurableSpace.pi_bot, isClopen_singleton_one', hnot, fun h => hnot ?_, ?_⟩
  · rw [h, borel]
    exact MeasurableSpace.measurableSet_generateFrom isClopen_singleton_one'.isOpen
  · rw [trivialTrace_eq_bot]
    refine @Measure.ext constants ⊥ _ _ fun s hs => ?_
    rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl <;> simp

-- With the discrete σ-algebra on `Bool`: the trace is the Borel σ-algebra, `{one'}` is measurable,
-- and `(δ_zero' + δ_one')/2` gives it mass `1/2`.
example : (inferInstance : MeasurableSpace constants) = borel constants ∧
    MeasurableSet ({one'} : Set constants) ∧
    ProbabilityMeasure.convexComb ENNReal.inv_two_add_inv_two (diracProba zero')
      (diracProba one') {one'} = 2⁻¹ := by
  have hm : MeasurableSet ({one'} : Set constants) := by
    rw [singleton_one'_eq]
    exact measurableSet_preimage_fullShift_cylinder _ _
  refine ⟨BorelSpace.measurable_eq, hm, ?_⟩
  rw [ProbabilityMeasure.convexComb_apply]
  simp [diracProba_apply' _ hm, one'_ne_zero'.symm, ENNReal.toNNReal_ofNat]

end TauCeti.Examples.WeakTopologyConfigurations
