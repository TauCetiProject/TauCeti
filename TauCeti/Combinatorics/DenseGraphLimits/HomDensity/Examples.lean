/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.OfMatrix
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.SmallGraphs
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Computed homomorphism densities

This file records exact homomorphism densities for two elementary graphons. The constant
`1/2` graphon checks the general constant-graphon formula. The complete bipartite graphon on a
two-point probability space gives a nonconstant weighted example: when its two parts have masses
`1/3` and `2/3`, its edge, triangle, and four-cycle densities are respectively `4/9`, `0`, and
`8/81`.

## Main definitions

* `TauCeti.DenseGraphLimits.Graphon.completeBipartite` is the complete bipartite graphon whose
  two parts have masses `p` and `1-p`.

## Main results

* `TauCeti.DenseGraphLimits.homDensity_top_three_const_half` computes the triangle density of the
  constant `1/2` graphon;
* `TauCeti.DenseGraphLimits.homDensity_top_two_completeBipartite`,
  `TauCeti.DenseGraphLimits.homDensity_top_three_completeBipartite`, and
  `TauCeti.DenseGraphLimits.homDensity_cycleGraph_four_completeBipartite` compute the edge,
  triangle, and four-cycle densities of a complete bipartite graphon;
* the corresponding `_one_third` results specialize these formulas to part masses `1/3` and
  `2/3`.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.1.
-/

public section

noncomputable section

open MeasureTheory
open ProbabilityTheory
open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

namespace Graphon

/-- The complete bipartite graphon on a two-point probability space, with respective part masses
`p` and `1-p`. Its value is one exactly between the two distinct points. -/
def completeBipartite (p : I) : Graphon (Fin 2) (bernoulliMeasure 0 1 p) :=
  Graphon.ofMatrix (bernoulliMeasure 0 1 p)
    (fun i j ↦ if i = j then 0 else 1) (fun i j ↦ by simp only [eq_comm])

/-- The complete bipartite graphon is zero within each part and one between its parts. -/
@[simp]
theorem completeBipartite_apply (p : I) (i j : Fin 2) :
    completeBipartite p i j = if i = j then 0 else 1 := by
  rw [completeBipartite, Graphon.ofMatrix_apply]
  split <;> simp

end Graphon

/-- The triangle density of the constant `1/2` graphon is `1/8`. -/
theorem homDensity_top_three_const_half :
    homDensity (⊤ : SimpleGraph (Fin 3))
      (Graphon.const (volume : Measure I) ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩) = 1 / 8 := by
  rw [homDensity_const]
  have hcard : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by decide
  rw [hcard]
  norm_num

/-- The edge density of a complete bipartite graphon with part masses `p` and `1-p` is
`2p(1-p)`. -/
theorem homDensity_top_two_completeBipartite (p : I) :
    homDensity (⊤ : SimpleGraph (Fin 2)) (Graphon.completeBipartite p) =
      2 * p * (1 - p) := by
  rw [homDensity_top_fin_two_eq_integral_integral]
  simp only [integral_bernoulliMeasure, smul_eq_mul, Graphon.completeBipartite_apply]
  norm_num
  ring

/-- Every complete bipartite graphon has triangle density zero. -/
theorem homDensity_top_three_completeBipartite (p : I) :
    homDensity (⊤ : SimpleGraph (Fin 3)) (Graphon.completeBipartite p) = 0 := by
  rw [homDensity_top_fin_three_eq_integral_integral_integral]
  simp only [integral_bernoulliMeasure, smul_eq_mul, Graphon.completeBipartite_apply]
  norm_num

/-- The four-cycle density of a complete bipartite graphon with part masses `p` and `1-p` is
`2p²(1-p)²`. -/
theorem homDensity_cycleGraph_four_completeBipartite (p : I) :
    homDensity (SimpleGraph.cycleGraph 4) (Graphon.completeBipartite p) =
      2 * p ^ 2 * (1 - p) ^ 2 := by
  rw [homDensity_cycleGraph_four]
  rw [integral_prod _ (integrable_cycleGraph_four _)]
  simp_rw [integral_prod _ Integrable.of_finite]
  simp only [integral_bernoulliMeasure, smul_eq_mul, Graphon.completeBipartite_apply]
  norm_num
  ring

/-- The edge density of the complete bipartite graphon with part masses `1/3` and `2/3` is
`4/9`. -/
theorem homDensity_top_two_completeBipartite_one_third :
    homDensity (⊤ : SimpleGraph (Fin 2))
      (Graphon.completeBipartite ⟨1 / 3, by norm_num, by norm_num⟩) = 4 / 9 := by
  rw [homDensity_top_two_completeBipartite]
  norm_num

/-- The triangle density of the complete bipartite graphon with part masses `1/3` and `2/3`
vanishes. -/
theorem homDensity_top_three_completeBipartite_one_third :
    homDensity (⊤ : SimpleGraph (Fin 3))
      (Graphon.completeBipartite ⟨1 / 3, by norm_num, by norm_num⟩) = 0 := by
  rw [homDensity_top_three_completeBipartite]

/-- The four-cycle density of the complete bipartite graphon with part masses `1/3` and `2/3` is
`8/81`. -/
theorem homDensity_cycleGraph_four_completeBipartite_one_third :
    homDensity (SimpleGraph.cycleGraph 4)
      (Graphon.completeBipartite ⟨1 / 3, by norm_num, by norm_num⟩) = 8 / 81 := by
  rw [homDensity_cycleGraph_four_completeBipartite]
  norm_num

end DenseGraphLimits

end TauCeti
