/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1
public import TauCeti.Analysis.CStarAlgebra.Action.Hom.Lp

/-!
# Bochner `L¹` functoriality for pulled-back covariant representations

This file extends `TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap`,
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1`, and
`TauCeti.Analysis.CStarAlgebra.Action.Hom.Lp` to the Bochner `L¹` integrated form,
showing that `CovariantRepresentation.integratedOperatorBochnerL1` commutes with pullback along an
equivariant C⋆-homomorphism via `CStarAction.Hom.mapLp`.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A B H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [R1Space G] [BorelSpace G] [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {β : CStarAction G B}

/-- Pulling back a covariant pair along `φ : Hom α β` commutes with
`integratedOperatorBochnerL1`. -/
theorem integratedOperatorBochnerL1_comap (Q : CovariantRepresentation β H) (φ : Hom α β)
    (μ : Measure G) [μ.InnerRegularCompactLTTop] (u : Lp A 1 μ) :
    (Q.comap φ).integratedOperatorBochnerL1 μ u =
      Q.integratedOperatorBochnerL1 μ (φ.mapLp μ 1 u) := by
  ext v
  rw [integratedOperatorBochnerL1_apply, integratedOperatorBochnerL1_apply]
  refine integral_congr_ae ?_
  filter_upwards [φ.coeFn_mapLp u] with g hg
  simp [hg]

end TauCeti.CStarAction.CovariantRepresentation
