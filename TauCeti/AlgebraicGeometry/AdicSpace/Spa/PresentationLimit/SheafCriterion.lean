/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.SheafCriterion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.PresentationLimit.Basic

/-!
# The presentation-indexed presheaf is a sheaf iff it is one on rational covers

`PairOfDefinition.HasSheafyPresentationLimit` is stated in Mathlib's shape: the
presentation-indexed presheaf is a sheaf
for the Grothendieck topology of the adic spectrum, quantifying over *all* opens and *all*
covers.
Wedhorn instead checks only covers by rational subsets. This file reconciles the two, by
applying the rational-cover criterion of `RationalSubset.SheafCriterion` — itself the basis
sheaf criterion at the basis of rational subsets — to the presentation-indexed presheaf.

## Main results

* `TauCeti.Huber.PairOfDefinition.hasSheafyPresentationLimit_iff_isSheafFor_rationalCover` : the
  reconciliation.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory _root_.TopologicalSpace TauCeti.Huber TauCeti.TopologicalSpace.Opens

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

end

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.PairOfDefinition

universe v

open CategoryTheory _root_.TopologicalSpace TauCeti.ValuationSpectrum
  TauCeti.TopologicalSpace.Opens

public section

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Rational covers decide it.** The presentation-indexed presheaf of `(P, Aplus)` is a sheaf
exactly when it satisfies the sheaf condition for every cover of an open by rational subsets. No
pair-level sheafiness is asserted: the presheaf is not known to be Wedhorn's `𝒪_X`.

This is what makes the Mathlib-shaped definition usable: `HasSheafyPresentationLimit` quantifies
over all opens and all covers, while Wedhorn checks only rational ones.

No `[IsHuberRing A]` binder: that class is `Nonempty (PairOfDefinition A)`, which the explicit
`P` already supplies, so requiring it would block a caller holding a pair of definition but no
registered instance. -/
theorem hasSheafyPresentationLimit_iff_isSheafFor_rationalCover
    (P : PairOfDefinition A) (Aplus : Subring A) :
    P.HasSheafyPresentationLimit Aplus ↔
      ∀ (E : CompleteSeparatedTopCommRingCat.{v}) ⦃U : Opens ↥(spa Aplus)⦄ (R : Presieve U),
        IsBasisCover (spaRationalOpens Aplus) R →
        Presieve.IsSheafFor (presentationLimitPresheaf P Aplus ⋙ coyoneda.obj (Opposite.op E)) R :=
  haveI : IsHuberRing A := ⟨⟨P⟩⟩
  (P.hasSheafyPresentationLimit_iff Aplus).trans (isSheaf_iff_isSheafFor_rationalCover Aplus _)

end

end TauCeti.Huber.PairOfDefinition
