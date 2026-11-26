/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.HasCondDistrib
import TauCeti.MeasureTheory.Measure.Real
import TauCeti.Probability.Kernel.Composition.KernelLemmas

/-!
# Conditioning on part of the conditioning variable

Let `Z`, `X` and `Y` be almost everywhere measurable random variables on a finite measure space,
where `Y` and `Z` take values in nonempty standard Borel spaces (no condition on the codomain of
`X` beyond measurability). The conditional distribution of `Z` given `X` is obtained from the
conditional distribution of `Z` given the pair `(X, Y)` by averaging over the conditional
distribution of `Y` given `X`:
`condDistrib Z X = condDistrib Z (X, Y) ∘ₖ (Kernel.id ×ₖ condDistrib Y X)`, almost everywhere
for the law of `X`.

In Bayesian inference with missing data (Little and Rubin, *Statistical Analysis with Missing
Data*, 3rd ed., (10.8), p. 233), with `Z` the parameter, `X` the observed data and `Y` the
missing data, this says that the observed-data posterior is the complete-data posterior averaged
over the posterior predictive distribution of the missing data, the identity behind multiple
imputation.

Conditioning on a constant random variable gives the law of `Z`, normalised by the total mass.
Conditioning on a random variable with countably many values evaluates, on atoms, to a ratio of
masses.

## Main statements

* `ProbabilityTheory.condDistrib_ae_eq_comp` — the identity above.
* `ProbabilityTheory.condDistrib_const_right_apply` — the conditional distribution given a
  constant is the normalised law.
* `ProbabilityTheory.condDistrib_apply_singleton_ae_eq` — for a countable label `X`, almost
  everywhere the conditional probability of the atom of `Z` given `X = X ω` is the ratio of the
  masses of the cell and of the atom of `X`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω β γ δ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] [StandardBorelSpace γ] [Nonempty γ] [StandardBorelSpace δ] [Nonempty δ]

/-- The conditional distribution of `Z` given `X` is the conditional distribution of `Z` given
`(X, Y)` averaged over the conditional distribution of `Y` given `X`, almost everywhere for the
law of `X`. Here `μ` is a finite measure, `X`, `Y` and `Z` are almost everywhere measurable, and
the codomains of `Y` and `Z` (but not necessarily that of `X`) are nonempty standard Borel spaces.
-/
theorem condDistrib_ae_eq_comp {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → δ} {X : Ω → β}
    {Y : Ω → γ} (hZ : AEMeasurable Z μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Z X μ =ᵐ[μ.map X]
      condDistrib Z (fun ω ↦ (X ω, Y ω)) μ ∘ₖ (Kernel.id ×ₖ condDistrib Y X μ) := by
  -- Both sides disintegrate the joint law of `(X, Z)`: the conditional law of `(Y, Z)` given
  -- `X` is `condDistrib Y X μ ⊗ₖ condDistrib Z (X, Y) μ` (by `compProd_map_condDistrib` for
  -- `(X, Y)` and for `((X, Y), Z)`), and its second marginal is the right-hand side.
  have hassoc : (μ.map fun ω ↦ ((X ω, Y ω), Z ω)).map MeasurableEquiv.prodAssoc =
      μ.map fun ω ↦ (X ω, (Y ω, Z ω)) :=
    AEMeasurable.map_map_of_aemeasurable MeasurableEquiv.prodAssoc.measurable.aemeasurable
      ((hX.prodMk hY).prodMk hZ)
  have hjoint : HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X
      (condDistrib Y X μ ⊗ₖ condDistrib Z (fun ω ↦ (X ω, Y ω)) μ) μ :=
    ⟨by fun_prop, by rw [← Measure.compProd_assoc', compProd_map_condDistrib hX hY,
      compProd_map_condDistrib (hX.prodMk hY) hZ, hassoc]⟩
  have hZX := hjoint.snd
  rw [Kernel.snd_compProd_eq_comp_id_prod] at hZX
  exact condDistrib_ae_eq_of_measure_eq_compProd hX hZ hZX.map_eq

/-- The conditional distribution of `Z` given a constant random variable is the law of `Z`,
normalised by the total mass of the nonzero finite measure `μ`. -/
theorem condDistrib_const_right_apply {μ : Measure Ω} [IsFiniteMeasure μ] [NeZero μ]
    [MeasurableSingletonClass β] {Z : Ω → δ} (hZ : AEMeasurable Z μ) (b : β) :
    condDistrib Z (fun _ ↦ b) μ b = (μ Set.univ)⁻¹ • μ.map Z := by
  rw [condDistrib_congr_left hZ.ae_eq_mk, Measure.map_congr hZ.ae_eq_mk]
  have hZ' := hZ.measurable_mk
  ext s hs
  rw [condDistrib_apply_of_ne_zero measurable_const hZ' b
      (by simp [Measure.map_const, NeZero.ne μ]),
    Measure.map_apply (measurable_const.prodMk hZ') ((measurableSet_singleton b).prod hs)]
  simp [Measure.map_const, Set.mk_preimage_prod, Measure.map_apply hZ' hs]

/-- **Conditional probabilities of atoms.** For a measurable `Z` with values in a nonempty
standard Borel space and a measurable `X` with values in a countable type, almost everywhere the
conditional probability of the atom `{Z ω}` given `X = X ω` is
`μ (Z ⁻¹' {Z ω} ∩ X ⁻¹' {X ω}) / μ (X ⁻¹' {X ω})`. -/
theorem condDistrib_apply_singleton_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ] [Countable β]
    [MeasurableSingletonClass β] {Z : Ω → δ} {X : Ω → β} (hZ : Measurable Z) (hX : Measurable X) :
    ∀ᵐ ω ∂μ, condDistrib Z X μ (X ω) {Z ω} =
      (μ (X ⁻¹' {X ω}))⁻¹ * μ (Z ⁻¹' {Z ω} ∩ X ⁻¹' {X ω}) := by
  filter_upwards [TauCeti.ae_measureReal_preimage_ne_zero (μ := μ) (b := X)] with ω hω
  replace hω : μ (X ⁻¹' {X ω}) ≠ 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).not.1 hω
  have hmap : μ.map X {X ω} = μ (X ⁻¹' {X ω}) := Measure.map_apply hX (measurableSet_singleton _)
  rw [condDistrib_apply_of_ne_zero hX hZ (X ω) (hmap ▸ hω), hmap,
    Measure.map_apply (hX.prodMk hZ) ((measurableSet_singleton _).prod (measurableSet_singleton _)),
    Set.mk_preimage_prod, Set.inter_comm]

end ProbabilityTheory
