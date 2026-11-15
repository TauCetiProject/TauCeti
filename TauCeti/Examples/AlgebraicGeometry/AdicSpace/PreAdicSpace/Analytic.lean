/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Analytic

/-!
# Tests for analytic points of pre-adic spaces

Every point of the adic spectrum of a Tate ring is analytic, so its analytic locus is all of it,
and no point of the adic spectrum of a discrete ring is, so its analytic locus is empty. The
analytic locus of a pre-adic space consists of analytic points, and the restriction of a
morphism to analytic loci is a morphism of the analytic loci.
-/

open CategoryTheory TopologicalSpace

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

/-- *analyticLocus_test_tate*: for a Tate ring the inclusion of the analytic locus of
`Spa(A, A⁺)` is an isomorphism. -/
example [IsTateRing A] :
    IsIso (PreAdicSpace.analyticLocus.ι (presentationLimitPreAdicSpace P Aplus hAplus hP)) := by
  rw [PreAdicSpace.isIso_analyticLocus_ι_iff, analyticPoints_presentationLimitPreAdicSpace,
    spaAnalytic_eq_spa_of_isTateRing]
  exact Set.eq_univ_of_forall fun x ↦ x.2

/-- *analyticLocus_test_discrete*: for a discrete ring the analytic locus of `Spa(A, A⁺)` has no
points. -/
example [DiscreteTopology A] :
    IsEmpty (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticLocus := by
  rw [← Set.range_eq_empty_iff (f := (PreAdicSpace.analyticLocus.ι _).base),
    PreAdicSpace.analyticLocus.range_ι, analyticPoints_presentationLimitPreAdicSpace]
  exact Set.eq_empty_of_forall_notMem fun _ hx ↦
    (isAnalyticPoint_def _).mp ((mem_spaAnalytic_iff _ _).mp hx).2 (isOpen_discrete _)

end TauCeti.ValuationSpectrum

namespace TauCeti.PreAdicSpace

/-- The analytic locus of a pre-adic space consists of analytic points. -/
example (X : PreAdicSpace) : X.analyticLocus.analyticPoints = Set.univ := by
  simp

/-- The identity of the analytic locus of a pre-adic space factors through the analytic locus,
by the lift of its inclusion. -/
example (X : PreAdicSpace) :
    analyticLocus.lift (analyticLocus.ι X) (analyticLocus.range_ι X).le = 𝟙 X.analyticLocus :=
  (analyticLocus.lift_uniq _ _ _ (Category.id_comp _)).symm

/-- The restriction of a morphism `f : Y ⟶ X` sending analytic points to analytic points maps a
point `y` of `Y_a` to the point of `X_a` over `f y`. -/
example {X Y : PreAdicSpace} (f : Y ⟶ X)
    (hf : Set.MapsTo f.base Y.analyticPoints X.analyticPoints) (y : Y.analyticLocus) :
    (analyticLocus.ι X).base ((analyticLocusMap f hf).base y) =
      f.base ((analyticLocus.ι Y).base y) := by
  have h := congrArg (fun φ : Y.analyticLocus ⟶ X ↦ φ.base y) (analyticLocusMap_ι f hf)
  simp only [comp_base, TopCat.comp_app] at h
  exact h

end TauCeti.PreAdicSpace
