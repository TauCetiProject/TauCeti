/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Disintegration
public import TauCeti.MeasureTheory.OptimalTransport.GraphPlan
public import TauCeti.Probability.Kernel.DiracSelection

/-!
# Recovering a transport map from Dirac conditional laws

If the conditional laws of the second coordinate of a finite coupling are Dirac for
almost every source point, the coupling is the graph plan of a measurable map with the
prescribed target law. This turns almost-everywhere singleton conditional transport
fibers into a Monge map.

## References

* C. Villani, *Optimal Transport: Old and New*, Chapter 10, for the passage from
  Dirac conditional laws of a transport plan to a Monge map.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y] [Nonempty Y]
  {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}

namespace IsCoupling

/-- A finite coupling with almost everywhere Dirac conditional laws is induced by a
measurable transport map. The map is determined only up to source-almost-everywhere
equality. -/
theorem exists_graphPlan_of_ae_exists_condKernel_eq_dirac [IsFiniteMeasure π]
    (hπ : IsCoupling π μ ν)
    (hκ : ∀ᵐ x ∂μ, ∃ y : Y, π.condKernel x = Measure.dirac y) :
    ∃ T : X → Y, Measurable T ∧ HasLaw T ν μ ∧ π = graphPlan T μ := by
  obtain ⟨T, hT, hκT⟩ :=
    Probability.exists_measurable_of_ae_exists_kernel_eq_dirac π.condKernel μ hκ
  have hkernel : π.condKernel =ᵐ[μ] Kernel.deterministic T hT := by
    filter_upwards [hκT] with x hx
    simpa only [Kernel.deterministic_apply] using hx
  let _ : IsFiniteMeasure μ := by
    rw [← hπ.fst_eq]
    infer_instance
  have hgraph : π = graphPlan T μ := by
    rw [← hπ.compProd_condKernel, Measure.compProd_congr hkernel,
      Measure.compProd_deterministic hT, graphPlan_def]
  exact ⟨T, hT, (isCoupling_graphPlan_iff hT.aemeasurable).1 (hgraph ▸ hπ), hgraph⟩

end IsCoupling

end TauCeti
