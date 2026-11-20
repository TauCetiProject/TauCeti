/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
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

## Main statements

* `ProbabilityTheory.condDistrib_ae_eq_comp` — the identity above.
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

The proof follows Mathlib: both sides disintegrate the joint law of `(X, Z)`, by
`compProd_map_condDistrib` applied to `(X, Y)` and to `((X, Y), Z)`, and
`condDistrib_ae_eq_of_measure_eq_compProd` gives uniqueness of the disintegration. -/
theorem condDistrib_ae_eq_comp {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → δ} {X : Ω → β}
    {Y : Ω → γ} (hZ : AEMeasurable Z μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Z X μ =ᵐ[μ.map X]
      condDistrib Z (fun ω ↦ (X ω, Y ω)) μ ∘ₖ (Kernel.id ×ₖ condDistrib Y X μ) := by
  -- the joint law of `(X, (Y, Z))`, from the two disintegrations
  have hjoint : μ.map X ⊗ₘ (condDistrib Y X μ ⊗ₖ condDistrib Z (fun ω ↦ (X ω, Y ω)) μ) =
      (μ.map fun ω ↦ ((X ω, Y ω), Z ω)).map MeasurableEquiv.prodAssoc := by
    rw [← Measure.compProd_assoc', compProd_map_condDistrib hX hY,
      compProd_map_condDistrib (hX.prodMk hY) hZ]
  refine condDistrib_ae_eq_of_measure_eq_compProd hX hZ (Eq.symm ?_)
  calc μ.map X ⊗ₘ (condDistrib Z (fun ω ↦ (X ω, Y ω)) μ ∘ₖ (Kernel.id ×ₖ condDistrib Y X μ))
      = (μ.map X ⊗ₘ (condDistrib Y X μ ⊗ₖ condDistrib Z (fun ω ↦ (X ω, Y ω)) μ)).map
          (Prod.map id Prod.snd) := by
        rw [← Kernel.snd_compProd_eq_comp_id_prod, Kernel.snd_eq,
          Measure.compProd_map measurable_snd]
    _ = μ.map fun ω ↦ (X ω, Z ω) := by
        rw [hjoint, Measure.map_map (by fun_prop) (by fun_prop),
          AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
        -- `prodAssoc` sends `((x, y), z)` to `(x, (y, z))`, so the composite map is
        -- `ω ↦ (X ω, Z ω)` by definition
        rfl

end ProbabilityTheory
