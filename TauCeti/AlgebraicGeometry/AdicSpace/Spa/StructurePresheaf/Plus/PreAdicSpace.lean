/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Plus
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.PresentationLimit
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Plus.Basic

/-!
# The integral sections of the presentation-limit pre-adic space

For a Huber pair `(A, A⁺)`, the integral sections `𝒪_X⁺(V)` of the pre-adic space
`presentationLimitPreAdicSpace` on `X = Spa(A, A⁺)`, defined through its stalk valuations, are the
plus subrings `presentationLimitPlusSubring` of the presentation-limit presheaf. On a rational open
`R(T/s)` these are the plus ring `A_U⁺` of the coordinate ring `A⟨T/s⟩` (Wedhorn,
Proposition 8.16).

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpace_plusSubring`: on `Spa(A, A⁺)` the
  integral sections are `presentationLimitPlusSubring`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 8.16.
-/

public section

open TopologicalSpace

namespace TauCeti.ValuationSpectrum

universe u

/-- **The integral sections of `Spa(A, A⁺)`** are the plus subrings `presentationLimitPlusSubring`
of the presentation-limit presheaf. On a rational open `R(T/s)` these are the plus ring `A_U⁺` of
`A⟨T/s⟩`, by `map_completedPlusSubring_eq_presentationLimitPlusSubring`. -/
theorem presentationLimitPreAdicSpace_plusSubring {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : Huber.PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → Huber.IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)
    (V : Opens ↥(spa Aplus)) :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).plusSubring V =
      presentationLimitPlusSubring hAplus hP V := by
  -- the stalks and germ maps of the two presheaves agree, and so do the stalk valuations
  refine Subring.ext fun f ↦ PreAdicSpace.mem_plusSubring_iff.trans
    (Iff.trans ?_ (mem_presentationLimitPlusSubring_iff hAplus hP).symm)
  exact forall_congr' fun x ↦ forall_congr' fun hx ↦ Iff.of_eq
    (congrArg (fun w ↦ w.toValuativeRel.vle
      ((presentationLimitPresheafInCommRingCat P Aplus).germ V x hx f) 1)
        (presentationLimitPreAdicSpace_stalkValuation P Aplus hAplus hP x))

end TauCeti.ValuationSpectrum

end
