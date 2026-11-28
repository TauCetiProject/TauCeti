/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.OrbitCutoff.Stages

/-!
# Bounds on quotient integrals from translate averages

Let `Λ` be a discrete subgroup of a unimodular group `H` embedded in `G`. To bound a
nonnegative integral over `Λ \ G`, one can average over right translates on each fibre
`Λ \ H` before integrating transverse to `H`. A weight constant along the `H`-orbits needs
no bound on the translate averages where the weight vanishes.

The weighted estimate follows the integration-in-stages argument of
`New.Filling.lintegral_boxCutoff_le_of_average` in `New/Spanning/RemainingTerms/SchurTest.lean`
of lsernau/grh-lean at `72fead1`. It uses the cutoff and coset measures from
`Subgroup.integral_cutoffMeasure_eq_integral_cosetMeasure`.
-/

public section

open MeasureTheory Measure ProbabilityTheory Topology Function
open scoped ENNReal

namespace Subgroup

/-- A uniform upper bound for averages of a nonnegative left `Λ`-invariant function over right
translates bounds its integral over `Λ \ H` by the same constant times the covolume. The
averaging measure `κ` can be any nonzero finite measure; it need not be normalized. -/
theorem lintegral_cutoffMeasure_le_of_mul_right_average {H X : Type*} [Group H]
    [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableSpace X]
    (Λ : Subgroup H) [MeasurableSingletonClass Λ] [Countable Λ]
    [HasOrbitCutoff (count : Measure Λ) H]
    {ν : Measure H} [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    {κ : Measure X} [IsFiniteMeasure κ] (hκ : κ ≠ 0) {t : X → H} (ht : Measurable t)
    {F : H → ℝ≥0∞} (hF : Measurable F) (hinv : ∀ (γ : Λ) h, F (γ • h) = F h)
    {C : ℝ≥0∞} (hmean : ∀ h, (∫⁻ x, F (h * t x) ∂κ) ≤ C * κ Set.univ) :
    (∫⁻ h, F h ∂Λ.cutoffMeasure ν) ≤ C * Λ.cutoffMeasure ν Set.univ := by
  let : MeasurableSMul₂ Λ H := ⟨by
    simp only [Subgroup.smul_def, smul_eq_mul, Function.uncurry_def]
    exact (measurable_subtypeVal.comp measurable_fst).mul measurable_snd⟩
  have hjoint : Measurable (fun p : X × H ↦ F (p.2 * t p.1)) := by fun_prop
  have hright (x : X) :
      (∫⁻ h, F (h * t x) ∂Λ.cutoffMeasure ν) = ∫⁻ h, F h ∂Λ.cutoffMeasure ν :=
    (identDistrib_cutoffMeasure_mul_right (t x) hF hinv).lintegral_eq
  have hcompare : (∫⁻ h, F h ∂Λ.cutoffMeasure ν) * κ Set.univ ≤
      (C * Λ.cutoffMeasure ν Set.univ) * κ Set.univ := calc
    _ = ∫⁻ x, ∫⁻ h, F (h * t x) ∂Λ.cutoffMeasure ν ∂κ := by simp_rw [hright, lintegral_const]
    _ = ∫⁻ h, ∫⁻ x, F (h * t x) ∂κ ∂Λ.cutoffMeasure ν :=
      lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ∫⁻ _ : H, C * κ Set.univ ∂Λ.cutoffMeasure ν := lintegral_mono hmean
    _ = _ := by rw [lintegral_const, mul_right_comm]
  exact (ENNReal.mul_le_mul_iff_left (measure_univ_ne_zero.mpr hκ) (measure_ne_top κ _)).mp hcompare

section Stages

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

/-- For a closed subgroup embedding `i : H → G`, the nonnegative integral over `i(Λ) \ G`
is the iterated integral over `i(H) \ G` and `Λ \ H`, even when it is infinite. -/
theorem lintegral_cutoffMeasure_eq_lintegral_cosetMeasure
    (Λ : Subgroup H) [DiscreteTopology Λ] (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {i : H →* G}
    (hi : IsClosedEmbedding i) {F : G → ℝ≥0∞} (hF : Measurable F)
    (hinv : ∀ (l : Λ) g, F (i l * g) = F g) :
    (∫⁻ g, F g ∂(Λ.map i).cutoffMeasure μ) =
      ∫⁻ g, ∫⁻ h, F (i h * g) ∂Λ.cutoffMeasure ν ∂μ.cosetMeasure ν i := by
  let e : Λ ≃* Λ.map i := Λ.equivMapOfInjective i hi.injective
  have : DiscreteTopology (Λ.map i) := (hi.isEmbedding.homeomorphImage Λ).discreteTopology
  have : Countable Λ := countable_of_Lindelof_of_discrete
  let m := μ.cosetMeasure ν i
  have hUnfold : MeasurePreserving (fun p : (G × H) × Λ ↦ e p.2 • (i p.1.2 * p.1.1))
      ((m.prod (Λ.cutoffMeasure ν)).prod count) μ := by
    simpa [Function.comp_def, MeasurableEquiv.prodAssoc, Subgroup.smul_def, e, mul_assoc] using
      (μ.measurePreserving_cosetMeasure ν hi).comp
        (((MeasurePreserving.id m).prod measurePreserving_cutoffMeasure).comp
          (measurePreserving_prodAssoc m (Λ.cutoffMeasure ν) count))
  have hdist : IdentDistrib F (fun p : G × H ↦ F (i p.2 * p.1)) ((Λ.map i).cutoffMeasure μ)
      (m.prod (Λ.cutoffMeasure ν)) :=
    identDistrib_cutoffMeasure_of_measurePreserving e.toEquiv.measurePreserving_count hUnfold hF
      (μ.measurePreserving_cosetMeasure ν hi).measurable (by
        intro l g
        obtain ⟨a, rfl⟩ := e.surjective l
        exact hinv a g)
  exact hdist.lintegral_eq.trans (lintegral_prod _ hdist.aemeasurable_snd)

/-- A bound for the translate averages along a closed subgroup bounds the weighted integral
on `i(Λ) \ G` by the bound times the covolume of `Λ` in `H` times the integral of the weight
on `i(H) \ G`. The weight is constant on `H`-orbits, and the averages need only be bounded
where the weight is nonzero. -/
theorem lintegral_cutoffMeasure_mul_le_of_translate_average
    (Λ : Subgroup H) [DiscreteTopology Λ] (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {i : H →* G}
    (hi : IsClosedEmbedding i) {X : Type*} [MeasurableSpace X]
    {κ : Measure X} [IsFiniteMeasure κ] (hκ : κ ≠ 0) {t : X → H} (ht : Measurable t)
    {w F : G → ℝ≥0∞} (hw : Measurable w) (hF : Measurable F)
    (hw_inv : ∀ h g, w (i h * g) = w g) (hF_inv : ∀ (l : Λ) g, F (i l * g) = F g)
    {C : ℝ≥0∞}
    (hmean : ∀ g, w g ≠ 0 → ∀ h, (∫⁻ x, F (i (h * t x) * g) ∂κ) ≤ C * κ Set.univ) :
    (∫⁻ g, w g * F g ∂(Λ.map i).cutoffMeasure μ) ≤
      (C * Λ.cutoffMeasure ν Set.univ) * ∫⁻ g, w g ∂μ.cosetMeasure ν i := by
  have hiMeas : Measurable i := hi.continuous.measurable
  have : Countable Λ := countable_of_Lindelof_of_discrete
  have hwF : Measurable (fun g ↦ w g * F g) := hw.mul hF
  rw [Λ.lintegral_cutoffMeasure_eq_lintegral_cosetMeasure μ ν hi hwF
    (fun l g ↦ by rw [hw_inv, hF_inv]), ← lintegral_const_mul _ hw]
  refine lintegral_mono fun g ↦ ?_
  simp only [hw_inv]
  rw [lintegral_const_mul _ (by fun_prop), mul_comm _ (w g)]
  obtain hg | hg := eq_or_ne (w g) 0
  · simp [hg]
  · have h := Λ.lintegral_cutoffMeasure_le_of_mul_right_average (ν := ν) hκ ht
      (F := fun h ↦ F (i h * g)) (by fun_prop) (by
        intro l h
        simp only [Subgroup.smul_def, smul_eq_mul, map_mul, mul_assoc, hF_inv]) (hmean g hg)
    gcongr

end Stages

end Subgroup
