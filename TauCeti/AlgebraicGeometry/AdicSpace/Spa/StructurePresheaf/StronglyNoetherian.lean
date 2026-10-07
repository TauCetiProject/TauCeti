/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Topology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.KanExtension
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing

/-!
# Sheafiness of strongly noetherian Tate pairs

For a strongly noetherian Tate ring `A` and a ring of integral elements `A⁺`, the
presentation-limit structure presheaf of `Spa(A, A⁺)` is a sheaf of complete separated topological
rings. This is Wedhorn's Theorem 8.28(b) for the pair `(A, A⁺)`; `A` itself need not be complete
or Hausdorff.

Gluing for rational covers of rational opens, including the empty cover, holds both for sections
(`isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq`) and for continuous ring homomorphisms out of
an arbitrary topological commutative ring
(`isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_topCommRingCat`). Intersections of rational
opens are rational, so either form is the sheaf condition on the basis of rational opens
(`isSheaf_rational_comp_of_isSheafFor_ofArrows`), and it extends to all opens because the presheaf
is the limit of its values on that basis.

## Main results

* `TauCeti.ValuationSpectrum.isSheaf_underlying_presentationLimitPresheaf_of_isStronglyNoetherian` :
  the underlying presheaf of sets is a sheaf.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian` : the
  structure presheaf is a sheaf of complete separated topological rings.
* `TauCeti.Huber.isSheafyForEveryPresentation_of_isStronglyNoetherian` : every ring of integral
  elements of a strongly noetherian Tate ring satisfies
  `TauCeti.Huber.IsSheafyForEveryPresentation`.
* `TauCeti.Huber.isSheafyRing_of_isStronglyNoetherian` : a complete Hausdorff strongly noetherian
  Tate ring is sheafy.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 8.28(b), Lemma 8.34,
  and Definition 8.26.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStronglyNoetherian A] (P : PairOfDefinition A) {Aplus : Subring A}

/-- The presheaf of sets underlying the presentation-limit structure presheaf of a strongly
noetherian Tate pair is a sheaf on all opens of `Spa(A, A⁺)`. The ring need not be complete or
Hausdorff. The ring of definition of `P` lies in `A⁺`, which consists of power-bounded elements.
This is `isSheaf_underlying_presentationLimitPresheaf_of_laurentGluing` for strong noetherianness
(`laurentGluing_isStronglyNoetherian`). -/
theorem isSheaf_underlying_presentationLimitPresheaf_of_isStronglyNoetherian
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
        forget _root_.TopCommRingCat) :=
  isSheaf_underlying_presentationLimitPresheaf_of_laurentGluing P
    laurentGluing_isStronglyNoetherian (inferInstanceAs (IsStronglyNoetherian A)) hP hAplus

/-- **Wedhorn's Theorem 8.28(b) for a pair: the structure presheaf of a strongly noetherian Tate
pair is a sheaf.** Let `A` be a strongly noetherian Tate ring, `P` a pair of definition whose ring
of definition lies in `A⁺`, and `A⁺` a subring of power-bounded elements. Then the
presentation-limit structure presheaf of `Spa(A, A⁺)` is a sheaf of complete separated topological
rings on all opens.

`A` itself need not be complete or Hausdorff. -/
theorem isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) := by
  refine isSheaf_presentationLimitPresheaf_of_isSheaf_rational <|
    Presheaf.isSheaf_of_isSheaf_comp _ _ TopCommRingCat.isCompleteSeparated.ι fun E ↦ ?_
  -- a sheaf of topological rings is one whose continuous homomorphisms out of each `E` glue
  exact isSheaf_rational_comp_of_isSheafFor_ofArrows P _ fun hW hU hcov ↦
    isSheafFor_ofArrows_spaRationalOpens_of_iSup_eq_topCommRingCat P hP hAplus hW hU hcov E

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber

open TauCeti.ValuationSpectrum

/-- **Strongly noetherian Tate pairs are sheafy**: every ring of integral elements `A⁺` of a
strongly noetherian Tate ring `A` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`, so the
structure presheaf of `Spa(A, A⁺)` is a sheaf of complete separated topological rings. This is
Wedhorn's Theorem 8.28(b) for the pair `(A, A⁺)`; `A` need not be complete or Hausdorff. -/
theorem isSheafyForEveryPresentation_of_isStronglyNoetherian {A : Type v} [CommRing A]
    [UniformSpace A] [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A]
    {Aplus : Subring A} (hAplus : IsRingOfIntegralElements Aplus) :
    IsSheafyForEveryPresentation Aplus :=
  ⟨hAplus, fun P hP ↦
    isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian P hP hAplus.isPowerBounded_of_mem⟩

/-- **A complete Hausdorff strongly noetherian Tate ring is sheafy** in the sense of Wedhorn's
Definition 8.26 (`TauCeti.Huber.IsSheafyRing`). This is Wedhorn's Theorem 8.28(b) for a complete
Hausdorff ring. -/
theorem isSheafyRing_of_isStronglyNoetherian {A : Type v} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A]
    [CompleteSpace A] [T0Space A] : IsSheafyRing A :=
  isSheafyRing_iff_forall_isSheafyForEveryPresentation.mpr fun _ ↦
    isSheafyForEveryPresentation_of_isStronglyNoetherian

end TauCeti.Huber
