/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.TowerCoordinates

/-!
# The weak topology in tower coordinates

For a compact group presented by a tower of finite quotients, integral measures embed as a
closed subspace of the product of their finite coefficients. The image consists exactly of
compatible families, and the inverse of `AbstractMeasure.towerCoordinatesEquiv` is continuous
for the product topology on coefficients and the weak topology on measures.

The tower supplies the topological group structure and total disconnectedness needed for
`AbstractMeasure.compactSpace_integralMeasures_weak`. No topology instance is installed on
measures or compatible families: the weak and induced product topologies are selected explicitly.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Definition 3.5,
Remark 3.11, Proposition 3.16 and Remark 3.18.
-/

public noncomputable section

open ContinuousMap Topology TauCeti
open scoped AbstractMeasure

namespace AbstractMeasure

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
  {A : ℕ → Type*} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
  [∀ n, DiscreteTopology (A n)] [∀ n, Finite (A n)] (T : FiniteQuotientTower Γ A)

omit [CompactSpace Γ] in
/-- Tower coordinates, viewed as coefficient functions with their product topology, are weakly
continuous. -/
theorem continuous_towerCoordinates_weak {R : Type*} [NormedCommRing R] :
    @Continuous _ _ (WeakTopology (X := Γ) (R := R) (E := R)) inferInstance
      (fun μ : D(Γ, R) ↦ fun n a ↦ (towerCoordinates T μ).val n a) := by
  let : TopologicalSpace D(Γ, R) := WeakTopology
  refine continuous_pi fun n ↦ ?_
  simpa only [towerCoordinates_apply] using
    continuous_finiteProjection (R := R) (T.q n : C(Γ, A n))

variable {p : ℕ} [Fact p.Prime]

/-- Integral tower coordinates give a closed embedding for the weak topology into the product
of the coefficient functions. -/
theorem isClosedEmbedding_towerCoordinates_weak :
    @IsClosedEmbedding _ _ (WeakTopology (X := Γ) (R := ℤ_[p]) (E := ℤ_[p]))
      inferInstance (fun μ : D(Γ, ℤ_[p]) ↦ fun n a ↦
        (towerCoordinates T μ).val n a) := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  have := T.isTopologicalGroup
  have := T.totallySeparatedSpace
  let : CompactSpace D(Γ, ℤ_[p]) := compactSpace_integralMeasures_weak
  refine (continuous_towerCoordinates_weak T).isClosedEmbedding fun μ ν h ↦ ?_
  apply towerCoordinates_injective T
  exact Subtype.ext (funext fun n ↦ Finsupp.ext fun a ↦ congrArg (fun c ↦ c n a) h)

/-- A family of coefficient functions comes from an integral measure exactly when its
finite-support forms belong to the tower's compatible families. -/
theorem mem_range_towerCoordinates_iff (c : ∀ n, A n → ℤ_[p]) :
    c ∈ Set.range (fun μ : D(Γ, ℤ_[p]) ↦ fun n a ↦
      (towerCoordinates T μ).val n a) ↔
      (fun n ↦ Finsupp.equivFunOnFinite.symm (c n)) ∈ T.compatibleFamilies ℤ_[p] := by
  constructor
  · rintro ⟨μ, rfl⟩
    simpa only [Finsupp.equivFunOnFinite_symm_coe] using
      (towerCoordinates T μ).property
  · intro hc
    obtain ⟨μ, hμ⟩ := towerCoordinates_surjective T
      ⟨fun n ↦ Finsupp.equivFunOnFinite.symm (c n), hc⟩
    refine ⟨μ, funext fun n ↦ funext fun a ↦ ?_⟩
    simpa only [Finsupp.coe_equivFunOnFinite_symm] using
      congrArg (fun d ↦ d.val n a) hμ

/-- The inverse of the integral tower-coordinate equivalence is continuous from the product
topology on compatible coefficients to the weak topology on measures. -/
theorem continuous_towerCoordinatesEquiv_symm_weak :
    @Continuous _ _
      (TopologicalSpace.induced
        (fun c : T.compatibleFamilies ℤ_[p] ↦ fun n a ↦ c.val n a) inferInstance)
      (WeakTopology (X := Γ) (R := ℤ_[p]) (E := ℤ_[p]))
      (towerCoordinatesEquiv T).symm := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  let : TopologicalSpace (T.compatibleFamilies ℤ_[p]) :=
    TopologicalSpace.induced (fun c ↦ fun n a ↦ c.val n a) inferInstance
  apply (isClosedEmbedding_towerCoordinates_weak T).isEmbedding.continuous_iff.mpr
  simpa only [Function.comp_def, ← towerCoordinatesEquiv_apply,
    LinearEquiv.apply_symm_apply] using
    (continuous_induced_dom : Continuous
      (fun c : T.compatibleFamilies ℤ_[p] ↦ fun n a ↦ c.val n a))

end AbstractMeasure
