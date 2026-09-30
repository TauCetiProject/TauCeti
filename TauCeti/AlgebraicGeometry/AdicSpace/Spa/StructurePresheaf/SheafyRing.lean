/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafForEveryPresentation
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SubsetLimit

/-!
# Sheafy Huber rings

Wedhorn calls a Huber ring `A` *sheafy* when, for every ring of integral elements `Â⁺` of its
completion `Â`, the structure presheaf of `Spa(Â, Â⁺)` is a sheaf of topological rings. Here the
sheaf condition on a pair is `TauCeti.Huber.IsSheafyForEveryPresentation`, which asks it of the
presentation-indexed limit presheaf for every compatible pair of definition.

That presheaf is isomorphic, as a presheaf, to Wedhorn's limit over rational subsets
`V ↦ lim_{U ⊆ V} Â⟨U⟩` (`TauCeti.ValuationSpectrum.rationalSubsetLimitPresheaf`), whose coordinate
rings are built from a pair of definition `P`. Since the sheaf condition does not depend on `P`,
sheafiness is the sheaf condition on that presheaf for every pair of definition of `Â`.

## Main definitions

* `TauCeti.Huber.IsSheafyRing`: sheafy Huber rings.

## Main results

* `TauCeti.Huber.isSheafyRing_iff_isSheaf_rationalSubsetLimitPresheaf`: for any pair of
  definition `P` of `Â`, `A` is sheafy exactly when the presheaf `V ↦ lim_{U ⊆ V} Â⟨U⟩` of limits
  over rational subsets built from `P` is a sheaf for every ring of integral elements of `Â`.
* `TauCeti.Huber.IsSheafyRing.isSheafyForEveryPresentation`: if `A` is sheafy, every ring of
  integral elements `A⁺` of `A` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`; the
  intermediate step `TauCeti.Huber.IsSheafyRing.isSheafyForEveryPresentation_completionPlus` gives
  the same for `Â⁺`, the closure of the image of `A⁺`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Definition 8.26.
-/

public section

open CategoryTheory UniformSpace TauCeti.ValuationSpectrum _root_.TopologicalSpace

namespace TauCeti.Huber

universe u

variable (A : Type u) [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- **Wedhorn Definition 8.26**: a Huber ring `A` is *sheafy* when every ring of integral elements
`Â⁺` of its completion `Â` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`, the sheaf
condition on the presentation-indexed limit presheaves of `Spa(Â, Â⁺)`. -/
def IsSheafyRing : Prop :=
  ∀ Aplus : Subring (Completion A), IsRingOfIntegralElements Aplus →
    IsSheafyForEveryPresentation Aplus

variable {A}

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.IsSheafyRing`. -/
theorem isSheafyRing_iff : IsSheafyRing A ↔ ∀ Aplus : Subring (Completion A),
    IsRingOfIntegralElements Aplus → IsSheafyForEveryPresentation Aplus :=
  (Iff.rfl)

/-- **Sheafiness through Wedhorn's limit over rational subsets**: for any pair of definition `P`
of `Â`, `A` is sheafy exactly when, for every ring of integral elements `Â⁺` of `Â`, the presheaf
`V ↦ lim_{U ⊆ V} Â⟨U⟩` of limits over the rational subsets of `Spa(Â, Â⁺)`, with coordinate rings
built from `P`, is a sheaf. `P` need not be contained in `Â⁺`. -/
theorem isSheafyRing_iff_isSheaf_rationalSubsetLimitPresheaf
    (P : PairOfDefinition (Completion A)) : IsSheafyRing A ↔
      ∀ (Aplus : Subring (Completion A)) (hAplus : IsRingOfIntegralElements Aplus),
        Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
          (rationalSubsetLimitPresheaf P Aplus fun _ ha ↦
            mem_powerBoundedSubring.mp (hAplus.le_powerBoundedSubring ha)) := by
  simp only [← isSheaf_presentationLimitPresheaf_iff_isSheaf_rationalSubsetLimitPresheaf]
  exact isSheafyRing_iff.trans <| forall₂_congr fun _ hAplus ↦
    (isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P).trans
      (and_iff_right hAplus)

/-- If `A` is sheafy and `A⁺` is a ring of integral elements of `A`, then `Â⁺`, the closure of the
image of `A⁺` in `Â`, satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`. For this `Â⁺`,
`TauCeti.ValuationSpectrum.spaCompletionHomeomorph` identifies `Spa(Â, Â⁺)` with `Spa(A, A⁺)`. -/
theorem IsSheafyRing.isSheafyForEveryPresentation_completionPlus (h : IsSheafyRing A)
    {Aplus : Subring A} (hAplus : IsRingOfIntegralElements Aplus) :
    IsSheafyForEveryPresentation (completionPlus Aplus) :=
  completionPlus_def Aplus ▸ isSheafyRing_iff.mp h _ hAplus.completion

/-- If `A` is sheafy, every ring of integral elements `A⁺` of `A` satisfies
`TauCeti.Huber.IsSheafyForEveryPresentation`: the sheaf condition on `Spa(Â, Â⁺)` descends to
`Spa(A, A⁺)` by completion invariance,
`TauCeti.Huber.isSheafyForEveryPresentation_completionPlus_iff`. -/
theorem IsSheafyRing.isSheafyForEveryPresentation (h : IsSheafyRing A) {Aplus : Subring A}
    (hAplus : IsRingOfIntegralElements Aplus) : IsSheafyForEveryPresentation Aplus :=
  (isSheafyForEveryPresentation_completionPlus_iff hAplus).mp
    (h.isSheafyForEveryPresentation_completionPlus hAplus)

end TauCeti.Huber

end
