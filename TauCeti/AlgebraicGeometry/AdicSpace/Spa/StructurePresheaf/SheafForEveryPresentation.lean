/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.Homeomorph
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.SheafCriterion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Transport
import TauCeti.RingTheory.Huber.RingOfDefinition

/-!
# Sheafhood across compatible presentations

`IsSheafyForEveryPresentation Aplus` requires `Aplus` to be a ring of integral elements and the
presentation-indexed limit presheaf `presentationLimitPresheaf P Aplus` to be a sheaf of complete
separated topological rings for every pair of definition `P` contained in `Aplus`. Such a pair
exists because `Aplus` is open. The universal condition is nevertheless equivalent to sheafhood
for any single pair of definition, compatible or not
(`isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf`).

On rational opens, `presentationLimitRationalIso` identifies the presheaf's values with the
completed rational localizations, and `presentationLimitRationalIso_inv_comp_map_comp_hom`
identifies its restrictions with the canonical comparison maps. On all opens, when `A⁺` consists
of power-bounded elements,
`TauCeti.ValuationSpectrum.presentationLimitPresheafIsoRationalSubsetLimitPresheaf` identifies the
presentation-indexed presheaf of `P` with Wedhorn's presheaf `V ↦ lim_{U ⊆ V} A⟨U⟩` of limits over
rational subsets, whose coordinate rings are those of presentations over the same `P`, and
`isSheaf_presentationLimitPresheaf_iff_isSheaf_rationalSubsetLimitPresheaf` transfers sheafhood
along it.

## Main results

* `TauCeti.Huber.isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf` :
  `IsSheafyForEveryPresentation A⁺` holds exactly when `A⁺` is a ring of integral elements and
  the presentation-limit presheaf of any one pair of definition of `A` is a sheaf.
* `TauCeti.Huber.isSheafyForEveryPresentation_iff_of_ringEquiv` and
  `TauCeti.Huber.IsSheafyForEveryPresentation.map` : the condition is invariant under
  isomorphisms of topological rings carrying one plus ring onto the other.
* `TauCeti.Huber.forall_isSheafyForEveryPresentation_iff_of_ringEquiv` : the same condition for
  every ring of integral elements at once is invariant under isomorphisms of topological rings.
* `TauCeti.Huber.isSheafyForEveryPresentation_completionPlus_iff` : for a ring of integral elements
  `A⁺`, the condition holds for `A⁺` exactly when it holds for the closure `Â⁺` of its image in the
  completion `Â`.

The sheaf-level comparisons behind these are in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Transport`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1, Proposition 7.48 and Theorem 8.28.
-/

open CategoryTheory _root_.TopologicalSpace TauCeti.TopologicalSpace.Opens
  TauCeti.ValuationSpectrum

namespace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- The plus ring `Aplus` is a ring of integral elements, and its presentation-indexed limit
presheaf is a sheaf for every compatible pair of definition. When `A⁺` consists of power-bounded
elements, that presheaf is isomorphic to the presheaf of limits over rational subsets built from
the same pair of definition
(`TauCeti.ValuationSpectrum.presentationLimitPresheafIsoRationalSubsetLimitPresheaf`), so this is
equivalently the sheaf condition on Wedhorn's presheaf. -/
structure IsSheafyForEveryPresentation (Aplus : Subring A) : Prop where
  /-- `Aplus` is a ring of integral elements of `A`. -/
  isRingOfIntegralElements : IsRingOfIntegralElements Aplus
  /-- The presentation-indexed limit presheaf is a sheaf for each compatible pair of definition. -/
  isSheaf (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ Aplus) :
    Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)

/-- The universal condition supplies a compatible pair of definition whose presentation-indexed
limit presheaf is a sheaf. -/
theorem IsSheafyForEveryPresentation.exists_compatible_isSheaf {Aplus : Subring A}
    (h : IsSheafyForEveryPresentation Aplus) :
    ∃ P : PairOfDefinition A, P.ringOfDefinition ≤ Aplus ∧
      Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus) := by
  obtain ⟨P, hP⟩ := exists_pairOfDefinition_ringOfDefinition_le h.isRingOfIntegralElements.isOpen
  exact ⟨P, hP, h.isSheaf P hP⟩

/-! ### Invariance under isomorphism and completion -/

/-- **`IsSheafyForEveryPresentation` is the sheaf condition for any one pair of definition**: the
presentation-limit presheaves of all pairs of definition of `A` are sheaves together, so the
universal condition reduces to a single pair, which need not be compatible with `A⁺`. -/
theorem isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf {Aplus : Subring A}
    (P : PairOfDefinition A) :
    IsSheafyForEveryPresentation Aplus ↔ IsRingOfIntegralElements Aplus ∧
      Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus) := by
  -- the identity of `A` compares the presheaves of any two pairs of definition
  have key (Q : PairOfDefinition A) :=
    isSheaf_presentationLimitPresheaf_iff_of_ringEquiv (P := Q) (P' := P) (RingEquiv.refl A)
      continuous_id continuous_id (Subring.map_id Aplus)
  refine ⟨fun h ↦ ⟨h.isRingOfIntegralElements, ?_⟩, fun h ↦ ⟨h.1, fun Q _ ↦ (key Q).mpr h.2⟩⟩
  obtain ⟨P₀, -, hP₀⟩ := h.exists_compatible_isSheaf
  exact (key P₀).mp hP₀

section RingEquiv

variable {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {Aplus : Subring A}

/-- `IsSheafyForEveryPresentation` is carried along an isomorphism of topological rings. -/
theorem IsSheafyForEveryPresentation.map (h : IsSheafyForEveryPresentation Aplus) (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) :
    IsSheafyForEveryPresentation (Aplus.map (e : A →+* B)) := by
  obtain ⟨P, -, hP⟩ := h.exists_compatible_isSheaf
  exact ⟨h.isRingOfIntegralElements.map e he he', fun _ _ ↦
    (isSheaf_presentationLimitPresheaf_iff_of_ringEquiv e he he' rfl).mp hP⟩

/-- **`IsSheafyForEveryPresentation` is invariant under isomorphism of Huber pairs**: if
`e : A ≃+* B` is an isomorphism of topological rings carrying `A⁺` onto `B⁺`, then `A⁺` satisfies
`IsSheafyForEveryPresentation` exactly when `B⁺` does. -/
theorem isSheafyForEveryPresentation_iff_of_ringEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) {Bplus : Subring B} (hplus : Aplus.map (e : A →+* B) = Bplus) :
    IsSheafyForEveryPresentation Aplus ↔ IsSheafyForEveryPresentation Bplus := by
  subst hplus
  refine ⟨fun h ↦ h.map e he he', fun h ↦ ?_⟩
  simpa only [Subring.map_map, RingEquiv.symm_comp, Subring.map_id] using h.map e.symm he' he

/-- **The sheaf condition for every plus ring is invariant under isomorphism**: along an
isomorphism of topological rings `e : A ≃+* B`, every ring of integral elements of `A` satisfies
`IsSheafyForEveryPresentation` exactly when every ring of integral elements of `B` does. -/
theorem forall_isSheafyForEveryPresentation_iff_of_ringEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) :
    (∀ Aplus : Subring A, IsRingOfIntegralElements Aplus → IsSheafyForEveryPresentation Aplus) ↔
      ∀ Bplus : Subring B, IsRingOfIntegralElements Bplus → IsSheafyForEveryPresentation Bplus :=
  -- `e` carries the rings of integral elements of `A` and of `B` onto each other
  ⟨fun h _ hB ↦ (isSheafyForEveryPresentation_iff_of_ringEquiv e.symm he' he rfl).mpr
      (h _ (hB.map _ he' he)),
    fun h _ hA ↦ (isSheafyForEveryPresentation_iff_of_ringEquiv e he he' rfl).mpr
      (h _ (hA.map _ he he'))⟩

end RingEquiv

end

public section

section Completion

open UniformSpace

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsHuberRing A] {Aplus : Subring A}

/-- **`IsSheafyForEveryPresentation` is invariant under completion**: for a ring of integral
elements `A⁺` of `A`, the closure `Â⁺` of its image in the completion `Â` satisfies
`IsSheafyForEveryPresentation` exactly when `A⁺` does. -/
theorem isSheafyForEveryPresentation_completionPlus_iff
    (hA : IsRingOfIntegralElements Aplus) :
    IsSheafyForEveryPresentation (completionPlus Aplus) ↔ IsSheafyForEveryPresentation Aplus := by
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := A)
  obtain ⟨P'⟩ := IsHuberRing.nonempty_pairOfDefinition (A := Completion A)
  have hA' : IsRingOfIntegralElements (completionPlus Aplus) :=
    completionPlus_def Aplus ▸ hA.completion
  rw [isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P',
    isSheafyForEveryPresentation_iff_isRingOfIntegralElements_and_isSheaf P,
    isSheaf_presentationLimitPresheaf_completionPlus_iff P P' hA.isPowerBounded_of_mem]
  exact ⟨fun h ↦ ⟨hA, h.2⟩, fun h ↦ ⟨hA', h.2⟩⟩

end Completion

end

end TauCeti.Huber
