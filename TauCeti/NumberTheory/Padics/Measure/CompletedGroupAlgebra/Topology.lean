/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra.Basic
public import TauCeti.NumberTheory.Padics.Measure.Compact

/-!
# The topological comparison with the completed group algebra

The canonical algebra equivalence from integral measures on a profinite group to its
completed group algebra is a homeomorphism from the weak measure topology to the
inverse-limit topology. In particular, the comparison is a closed embedding. Weak
compactness of integral measures proves this without choosing a countable quotient tower.

The algebra equivalence and the inverse-limit topology are the existing ones. No topology
instance on the measure carrier is introduced.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
Proposition 3.16 and Remark 3.18.
-/

public section

open Topology
open _root_.AbstractMeasure

namespace TauCeti.AbstractMeasure

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {p : ℕ} [Fact p.Prime]

/-- The canonical integral-measure algebra equivalence is a homeomorphism for the weak and
inverse-limit topologies. -/
theorem isHomeomorph_completedGroupAlgebraEquiv :
    @IsHomeomorph _ _ (WeakTopology (X := Γ) (R := ℤ_[p]) (E := ℤ_[p])) _
      (completedGroupAlgebraEquiv : D(Γ, ℤ_[p]) ≃ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ) := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  let : CompactSpace D(Γ, ℤ_[p]) := compactSpace_integralMeasures_weak
  refine isHomeomorph_iff_continuous_bijective.mpr ⟨?_, AlgEquiv.bijective _⟩
  exact continuous_toCompletedGroupAlgebra.congr fun μ ↦
    (completedGroupAlgebraEquiv_apply μ).symm

/-- Integral measures embed as a closed subspace of the completed group algebra when they
carry the weak topology. The comparison is in fact surjective. -/
theorem isClosedEmbedding_toCompletedGroupAlgebra :
    @IsClosedEmbedding _ _ (WeakTopology (X := Γ) (R := ℤ_[p]) (E := ℤ_[p])) _
      (toCompletedGroupAlgebra : D(Γ, ℤ_[p]) →ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ) := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  have h : (completedGroupAlgebraEquiv : D(Γ, ℤ_[p]) → completedGroupAlgebra ℤ_[p] Γ) =
      toCompletedGroupAlgebra := funext completedGroupAlgebraEquiv_apply
  rw [← h]
  exact isHomeomorph_completedGroupAlgebraEquiv.isClosedEmbedding

end TauCeti.AbstractMeasure
