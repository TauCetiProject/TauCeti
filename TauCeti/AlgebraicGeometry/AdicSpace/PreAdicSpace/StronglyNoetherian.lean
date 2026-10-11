/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian

/-!
# Affinoid adic spaces from strongly noetherian Tate pairs

The presentation-limit pre-adic space of a strongly noetherian Tate pair is an affinoid adic
space. This packages the sheafiness theorem for strongly noetherian Tate pairs with the general
criterion that a sheafy affinoid pre-adic space is adic.

## Main result

* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian`:
  the adic spectrum of a strongly noetherian Tate pair, with its presentation-limit structure
  sheaf, is an adic space.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 8.22 and
  Theorem 8.28(b).
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

universe u

variable {A : Type u} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A) {Aplus : Subring A}

/-- **The adic spectrum of a strongly noetherian Tate pair is an affinoid adic space.** The
structure presheaf is a sheaf by the strongly noetherian form of Tate acyclicity, and the
presentation-limit pre-adic space is affinoid. The ring need not be complete or Hausdorff. -/
theorem isAdic_presentationLimitPreAdicSpace_of_isStronglyNoetherian
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P Aplus hAplus hP) :=
  isAdic_presentationLimitPreAdicSpace P Aplus hAplus hP
    (isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian P hP hAplus)

end TauCeti.ValuationSpectrum

end
