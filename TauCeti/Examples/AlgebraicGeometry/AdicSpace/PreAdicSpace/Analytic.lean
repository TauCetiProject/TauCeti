/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Analytic

/-!
# Tests for analytic points of pre-adic spaces

Every point of the adic spectrum of a Tate ring is analytic, and no point of the adic spectrum of
a discrete ring is. The open subspace of analytic points of a pre-adic space consists of analytic
points.
-/

open TopologicalSpace

namespace TauCeti.ValuationSpectrum

open Huber

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)

/-- *analyticLocus_test_tate*: over a Tate ring every point of `Spa(A, A⁺)` is analytic. -/
example [IsTateRing A] :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints = Set.univ := by
  rw [analyticPoints_presentationLimitPreAdicSpace, spaAnalytic_eq_spa_of_isTateRing]
  exact Set.eq_univ_of_forall fun x ↦ x.2

/-- *analyticLocus_test_discrete*: over a discrete ring every ideal is open, so no point of
`Spa(A, A⁺)` is analytic, although the adic spectrum itself need not be empty. -/
example [DiscreteTopology A] :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints = ∅ := by
  rw [analyticPoints_presentationLimitPreAdicSpace]
  exact Set.eq_empty_of_forall_notMem fun _ hx ↦
    (isAnalyticPoint_def _).mp ((mem_spaAnalytic_iff _ _).mp hx).2 (isOpen_discrete _)

end TauCeti.ValuationSpectrum

namespace TauCeti.PreAdicSpace

/-- The open subspace of analytic points of a pre-adic space consists of analytic points. -/
example (X : PreAdicSpace) :
    (X.restrict (Opens.isOpenEmbedding ⟨_, X.isOpen_analyticPoints⟩)).analyticPoints =
      Set.univ := by
  rw [analyticPoints_restrict]
  exact Set.eq_univ_of_forall fun x ↦ x.2

end TauCeti.PreAdicSpace
