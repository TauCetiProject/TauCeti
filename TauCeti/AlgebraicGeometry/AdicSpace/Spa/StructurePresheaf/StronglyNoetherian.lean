/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Topology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing

import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Sheafiness of strongly noetherian Tate pairs

For a strongly noetherian Tate ring `A` and a ring of integral elements `A⁺`, the
presentation-limit structure presheaf of `Spa(A, A⁺)` is a sheaf of complete separated topological
rings. This is Wedhorn's Theorem 8.28(b) for the pair `(A, A⁺)`; `A` itself need not be complete
or Hausdorff.

Strong noetherianness satisfies `ContinuousLaurentGluing`
(`continuousLaurentGluing_isStronglyNoetherian`): it passes to completed rational localisations,
and two-piece Laurent covers of rational subsets glue, with the topology on sections induced by
restriction to the two pieces. Wedhorn's reduction of Lemma 8.34 to Laurent covers therefore gives
gluing for rational covers of rational opens, both for sections and for continuous ring
homomorphisms, and hence the sheaf property
(`isSheaf_presentationLimitPresheaf_of_continuousLaurentGluing`).

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
* `TauCeti.Huber.isSheafyRing_quotient_of_isStronglyNoetherian` : so is its quotient by a closed
  ideal.
* `TauCeti.Huber.isStablySheafyRing_of_isStronglyNoetherian` : a complete Hausdorff strongly
  noetherian Tate ring is stably sheafy.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Theorem 8.28(b), Lemma 8.34,
  Definition 8.26, and Corollary 8.35.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe u v

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

`A` itself need not be complete or Hausdorff. This is
`isSheaf_presentationLimitPresheaf_of_continuousLaurentGluing` for strong noetherianness
(`continuousLaurentGluing_isStronglyNoetherian`). -/
theorem isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian
    (hP : P.ringOfDefinition ≤ Aplus) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus) :=
  isSheaf_presentationLimitPresheaf_of_continuousLaurentGluing P
    continuousLaurentGluing_isStronglyNoetherian (inferInstanceAs (IsStronglyNoetherian A)) hP
    hAplus

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

/-- **The quotient of a complete Hausdorff strongly noetherian Tate ring by a closed ideal is
sheafy.** The quotient `A ⧸ J` carries the quotient topology and the uniformity of that additive
topological group. It is again a complete Hausdorff strongly noetherian Tate ring
(`TauCeti.Huber.IsStronglyNoetherian.quotient`), so Wedhorn's Theorem 8.28(b) applies to it. -/
theorem isSheafyRing_quotient_of_isStronglyNoetherian {A : Type v} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A]
    [CompleteSpace A] [T0Space A] (J : Ideal A) (hJ : IsClosed (J : Set A)) :
    letI := IsTopologicalAddGroup.rightUniformSpace (A ⧸ J)
    haveI : IsUniformAddGroup (A ⧸ J) := isUniformAddGroup_of_addCommGroup
    IsSheafyRing (A ⧸ J) := by
  let _ : UniformSpace (A ⧸ J) := IsTopologicalAddGroup.rightUniformSpace _
  have _ : IsUniformAddGroup (A ⧸ J) := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (A ⧸ J) := QuotientAddGroup.completeSpace_right _ J.toAddSubgroup
  have _ : T1Space (A ⧸ J) := (Ideal.Quotient.t1Space_iff J).mpr hJ
  have _ := IsStronglyNoetherian.quotient J hJ
  exact isSheafyRing_of_isStronglyNoetherian

/-- **A complete Hausdorff strongly noetherian Tate ring is stably sheafy** (Wedhorn's
Corollary 8.35): every complete Hausdorff Huber ring `B` topologically of finite type over `A`, in
the weighted sense of `TauCeti.Huber.IsTopologicallyFiniteType`, is sheafy. -/
theorem isStablySheafyRing_of_isStronglyNoetherian {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A]
    [CompleteSpace A] [T0Space A] : IsStablySheafyRing.{u, v} A := by
  have : IsStronglyNoetherian (UniformSpace.Completion A) :=
    (isStronglyNoetherian_congr (UniformSpace.Completion.completeRingEquivSelf A).symm
      (UniformSpace.Completion.uniformContinuous_completeRingEquivSelf_symm A).continuous
      (UniformSpace.Completion.uniformContinuous_completeRingEquivSelf A).continuous).mp
      inferInstance
  -- `B` is Tate, since the image of a pseudouniformiser is one, and strongly noetherian, since over
  -- a Tate ring a weighted presentation can be made strict; Theorem 8.28(b) applies to it
  refine isStablySheafyRing_iff.mpr fun B _ _ _ _ _ _ _ φ hφ ↦ ?_
  have : IsTateRing B := IsTateRing.of_continuous hφ.continuous
  have : IsStronglyNoetherian B := hφ.isStronglyNoetherian
  exact isSheafyRing_of_isStronglyNoetherian

end TauCeti.Huber
