/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Disintegration.Unique
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import TauCeti.MeasureTheory.Measure.Prod

/-!
# Disintegration with a sigma-finite first marginal

A joint measure whose first marginal is sigma-finite admits a Markov disintegration when its
second space is nonempty standard Borel. This extends Mathlib's finite-measure `Measure.condKernel`:
weight the first marginal by a strictly positive integrable function, disintegrate the resulting
finite joint measure, and remove the weight. The conditional kernel is unique only almost
everywhere for the first marginal; no choice of weight or values on null sets changes it there.

This is the disintegration needed for Campbell measures and Palm kernels, whose intensity
marginals need not have finite total mass. The conditioning space has no topological or
standard-Borel assumption.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press, 2018,
  Chapter 13.

The finite disintegration and its uniqueness are Mathlib's `Measure.condKernel` and
`ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A strictly positive finite weight depending only on the first coordinate does not change
whether a kernel disintegrates a joint measure. -/
theorem withDensity_fst_compProd_eq_iff (ρ : Measure (α × β)) [SFinite ρ.fst]
    (κ : Kernel α β) [IsSFiniteKernel κ] {g : α → ℝ≥0}
    (hg : Measurable g) (hpos : ∀ x, 0 < g x) :
    (ρ.withDensity (fun p ↦ (g p.1 : ℝ≥0∞))).fst ⊗ₘ κ =
        ρ.withDensity (fun p ↦ (g p.1 : ℝ≥0∞)) ↔ ρ.fst ⊗ₘ κ = ρ := by
  rw [fst_withDensity ρ hg.coe_nnreal_ennreal, withDensity_compProd hg.coe_nnreal_ennreal]
  constructor
  · intro h
    have hinv (μ : Measure (α × β)) :
        (μ.withDensity (fun p ↦ (g p.1 : ℝ≥0∞))).withDensity
          (fun p ↦ (g p.1 : ℝ≥0∞)⁻¹) = μ :=
      withDensity_inv_same (by fun_prop)
        (ae_of_all _ fun p ↦ by exact_mod_cast (hpos p.1).ne')
        (ae_of_all _ fun _ ↦ ENNReal.coe_ne_top)
    simpa only [hinv] using congrArg
      (fun μ : Measure (α × β) ↦ μ.withDensity (fun p ↦ (g p.1 : ℝ≥0∞)⁻¹)) h
  · intro h
    rw [h]

variable [StandardBorelSpace β] [Nonempty β]

/-- Existence of a Markov disintegration for a measure with sigma-finite first marginal.
The second space must be standard Borel, but the first space is arbitrary measurable. -/
theorem exists_isMarkovKernel_compProd_eq (ρ : Measure (α × β)) [SigmaFinite ρ.fst] :
    ∃ κ : Kernel α β, IsMarkovKernel κ ∧ ρ.fst ⊗ₘ κ = ρ := by
  obtain ⟨g, hpos, hg, hint⟩ := exists_pos_lintegral_lt_of_sigmaFinite ρ.fst one_ne_zero
  let σ := ρ.withDensity (fun p ↦ (g p.1 : ℝ≥0∞))
  have : IsFiniteMeasure (ρ.fst.withDensity fun x ↦ (g x : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity (hint.trans_le le_top).ne
  have : IsFiniteMeasure σ.fst := by
    rwa [fst_withDensity ρ hg.coe_nnreal_ennreal]
  have : IsFiniteMeasure σ := ⟨by simpa only [fst_univ] using measure_lt_top σ.fst Set.univ⟩
  exact ⟨σ.condKernel, inferInstance,
    (withDensity_fst_compProd_eq_iff ρ σ.condKernel hg hpos).1 (σ.disintegrate σ.condKernel)⟩

/-- A chosen Markov disintegration of a joint measure with sigma-finite first marginal.
It is characterized up to first-marginal-almost-everywhere equality by
`compProd_fst_sigmaFiniteCondKernel` and `eq_sigmaFiniteCondKernel_of_measure_eq_compProd`. -/
def sigmaFiniteCondKernel (ρ : Measure (α × β)) [SigmaFinite ρ.fst] : Kernel α β :=
  (exists_isMarkovKernel_compProd_eq ρ).choose

instance (ρ : Measure (α × β)) [SigmaFinite ρ.fst] :
    IsMarkovKernel ρ.sigmaFiniteCondKernel :=
  (exists_isMarkovKernel_compProd_eq ρ).choose_spec.1

/-- The chosen sigma-finite conditional kernel reconstructs the original joint measure. -/
theorem compProd_fst_sigmaFiniteCondKernel (ρ : Measure (α × β)) [SigmaFinite ρ.fst] :
    ρ.fst ⊗ₘ ρ.sigmaFiniteCondKernel = ρ :=
  (exists_isMarkovKernel_compProd_eq ρ).choose_spec.2

instance (ρ : Measure (α × β)) [SigmaFinite ρ.fst] :
    ρ.IsCondKernel ρ.sigmaFiniteCondKernel :=
  ⟨compProd_fst_sigmaFiniteCondKernel ρ⟩

/-- Any finite kernel reconstructing the joint measure agrees with its chosen sigma-finite
conditional kernel almost everywhere. In particular the choice of positive weight is immaterial. -/
theorem eq_sigmaFiniteCondKernel_of_measure_eq_compProd
    (ρ : Measure (α × β)) [SigmaFinite ρ.fst] (κ : Kernel α β) [IsFiniteKernel κ]
    (hκ : ρ.fst ⊗ₘ κ = ρ) : κ =ᵐ[ρ.fst] ρ.sigmaFiniteCondKernel := by
  obtain ⟨g, hpos, hg, hint⟩ := exists_pos_lintegral_lt_of_sigmaFinite ρ.fst one_ne_zero
  let σ := ρ.withDensity (fun p ↦ (g p.1 : ℝ≥0∞))
  have : IsFiniteMeasure (ρ.fst.withDensity fun x ↦ (g x : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity (hint.trans_le le_top).ne
  have : IsFiniteMeasure σ.fst := by
    rwa [fst_withDensity ρ hg.coe_nnreal_ennreal]
  have : IsFiniteMeasure σ := ⟨by simpa only [fst_univ] using measure_lt_top σ.fst Set.univ⟩
  have h₁ := ProbabilityTheory.eq_condKernel_of_measure_eq_compProd κ
    ((withDensity_fst_compProd_eq_iff ρ κ hg hpos).2 hκ).symm
  have h₂ := ProbabilityTheory.eq_condKernel_of_measure_eq_compProd ρ.sigmaFiniteCondKernel
    ((withDensity_fst_compProd_eq_iff ρ ρ.sigmaFiniteCondKernel hg hpos).2
      (compProd_fst_sigmaFiniteCondKernel ρ)).symm
  have heq : κ =ᵐ[σ.fst] ρ.sigmaFiniteCondKernel := by
    filter_upwards [h₁, h₂] with x hx₁ hx₂ using hx₁.trans hx₂.symm
  rw [fst_withDensity ρ hg.coe_nnreal_ennreal, Filter.EventuallyEq,
    ae_withDensity_iff hg.coe_nnreal_ennreal] at heq
  filter_upwards [heq] with x hx
  exact hx (by exact_mod_cast (hpos x).ne')

/-- A finite kernel is a disintegration exactly when it is almost everywhere equal to the
chosen sigma-finite conditional kernel. -/
theorem compProd_eq_iff_ae_eq_sigmaFiniteCondKernel (ρ : Measure (α × β)) [SigmaFinite ρ.fst]
    (κ : Kernel α β) [IsFiniteKernel κ] :
    ρ.fst ⊗ₘ κ = ρ ↔ κ =ᵐ[ρ.fst] ρ.sigmaFiniteCondKernel := by
  refine ⟨eq_sigmaFiniteCondKernel_of_measure_eq_compProd ρ κ, fun h ↦ ?_⟩
  rw [compProd_congr h, compProd_fst_sigmaFiniteCondKernel]

/-- For finite joint measures the sigma-finite construction agrees almost everywhere with
Mathlib's finite conditional kernel. -/
theorem sigmaFiniteCondKernel_ae_eq_condKernel (ρ : Measure (α × β)) [IsFiniteMeasure ρ] :
    ρ.sigmaFiniteCondKernel =ᵐ[ρ.fst] ρ.condKernel :=
  (eq_sigmaFiniteCondKernel_of_measure_eq_compProd ρ ρ.condKernel
    (ρ.disintegrate ρ.condKernel)).symm

end MeasureTheory.Measure
