/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Cluster.Interface.Basic

/-!
# Regression examples: the interfaces of a two-cell cluster

For a `2`-cluster `(Ω_1, Ω_2)`, for a `C¹` weight in dimension `n ≥ 2`, there is a single
interface: `A_12 = P_μ(Ω_1) = P_μ(Ω_2)`, the total perimeter is `P_μ(Ω) = A_12`, and the
closure of `∂*Ω_1` is the closure of `Σ_12`.
-/

public section

open MeasureTheory Module

namespace TauCeti.Examples.ClusterInterface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ}

/-- For a `2`-cluster, `A_12 = P_μ(Ω_1)`. -/
theorem interfaceArea_zero_one_eq_weightedPerimeter_cell_zero (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Cluster W 2) :
    Ω.interfaceArea 0 1 = weightedPerimeter W ⊤ (Ω.cell 0) := by
  rw [Ω.weightedPerimeter_cell_eq_sum_interfaceArea hW hn 0,
    show ({0}ᶜ : Finset (Fin 2)) = {1} by decide, Finset.sum_singleton]

/-- For a `2`-cluster, `A_12 = P_μ(Ω_2)`. -/
theorem interfaceArea_zero_one_eq_weightedPerimeter_cell_one (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Cluster W 2) :
    Ω.interfaceArea 0 1 = weightedPerimeter W ⊤ (Ω.cell 1) := by
  rw [Ω.interfaceArea_comm, Ω.weightedPerimeter_cell_eq_sum_interfaceArea hW hn 1,
    show ({1}ᶜ : Finset (Fin 2)) = {0} by decide, Finset.sum_singleton]

/-- For a `2`-cluster, the total perimeter is `A_12`. -/
theorem perimeter_eq_interfaceArea_zero_one (hW : ContDiff ℝ 1 W) (hn : 2 ≤ finrank ℝ E)
    (Ω : Cluster W 2) : Ω.perimeter = Ω.interfaceArea 0 1 := by
  rw [Ω.perimeter_eq_sum_interfaceArea hW hn, Fin.sum_univ_two,
    show Finset.Ioi (0 : Fin 2) = {1} by decide, show Finset.Ioi (1 : Fin 2) = ∅ by decide,
    Finset.sum_singleton, Finset.sum_empty, add_zero]

/-- For a `2`-cluster, the closure of `∂*Ω_1` is the closure of the single interface `Σ_12`. -/
theorem closure_reducedBoundary_cell_zero (hW : ContDiff ℝ 1 W) (hn : 2 ≤ finrank ℝ E)
    (Ω : Cluster W 2) :
    closure (reducedBoundary volume ⊤ (Ω.cell 0)) = closure (Ω.interface 0 1) := by
  rw [Ω.closure_reducedBoundary_cell hW hn 0]
  congr 1
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨fun ⟨j, hj, hx⟩ => by rwa [show j = 1 by omega] at hx, fun hx => ⟨1, by decide, hx⟩⟩

end TauCeti.Examples.ClusterInterface
