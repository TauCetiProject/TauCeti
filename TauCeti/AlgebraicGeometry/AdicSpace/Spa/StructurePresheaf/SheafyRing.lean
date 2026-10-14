/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafForEveryPresentation
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SubsetLimit
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

/-!
# Sheafy and stably sheafy Huber rings

Wedhorn calls a Huber ring `A` *sheafy* when, for every ring of integral elements `Â⁺` of its
completion `Â`, the structure presheaf of `Spa(Â, Â⁺)` is a sheaf of topological rings, and
*stably sheafy* when every `Â`-algebra topologically of finite type is sheafy. Here the sheaf
condition on a pair is `TauCeti.Huber.IsSheafyForEveryPresentation`, which asks it of the
presentation-indexed limit presheaf for every compatible pair of definition.

That presheaf is isomorphic, as a presheaf, to Wedhorn's limit over rational subsets
`V ↦ lim_{U ⊆ V} Â⟨U⟩` (`TauCeti.ValuationSpectrum.rationalSubsetLimitPresheaf`), whose coordinate
rings are built from a pair of definition `P`. Since the sheaf condition does not depend on `P`,
sheafiness is the sheaf condition on that presheaf for every pair of definition of `Â`.

The stable condition quantifies over complete Hausdorff Huber rings `B`, the targets for which
Wedhorn states Proposition and Definition 6.29; `TauCeti.Huber.IsTopologicallyFiniteType` itself
does not require completeness.

## Main definitions

* `TauCeti.Huber.IsSheafyRing`: sheafy Huber rings.
* `TauCeti.Huber.IsStablySheafyRing`: stably sheafy Huber rings.

## Main results

* `TauCeti.Huber.isSheafyRing_iff_isSheaf_rationalSubsetLimitPresheaf`: for any pair of
  definition `P` of `Â`, `A` is sheafy exactly when the presheaf `V ↦ lim_{U ⊆ V} Â⟨U⟩` of limits
  over rational subsets built from `P` is a sheaf for every ring of integral elements of `Â`.
* `TauCeti.Huber.IsSheafyRing.isSheafyForEveryPresentation`: if `A` is sheafy, every ring of
  integral elements `A⁺` of `A` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`; the
  intermediate step `TauCeti.Huber.IsSheafyRing.isSheafyForEveryPresentation_completionPlus` gives
  the same for `Â⁺`, the closure of the image of `A⁺`.
* `TauCeti.Huber.isSheafyRing_iff_forall_isSheafyForEveryPresentation`: a complete Hausdorff
  Huber ring `B` is sheafy exactly when every ring of integral elements of `B` satisfies
  `TauCeti.Huber.IsSheafyForEveryPresentation`.
* `TauCeti.Huber.isSheafyRing_completion_iff`: `Â` is sheafy exactly when `A` is.
* `TauCeti.Huber.isSheafyRing_iff_of_completion_ringEquiv`: sheafiness depends only on the
  completion, up to isomorphism of topological rings.
* `TauCeti.Huber.isSheafyRing_iff_of_ringEquiv`: sheafiness is invariant under isomorphisms of
  topological rings.
* `TauCeti.Huber.isStablySheafyRing_iff_forall_isSheafyForEveryPresentation`: `A` is stably
  sheafy exactly when, for every `B` in the definition, every ring of integral elements of `B`
  satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`.
* `TauCeti.Huber.IsStablySheafyRing.isSheafyRing`: a stably sheafy Huber ring is sheafy.
* `TauCeti.Huber.isStablySheafyRing_completion_iff`: `Â` is stably sheafy exactly when `A` is.
* `TauCeti.Huber.isStablySheafyRing_iff_of_completion_ringEquiv`: stable sheafiness depends only
  on the completion, up to isomorphism of topological rings.
* `TauCeti.Huber.isStablySheafyRing_iff_of_ringEquiv`: stable sheafiness is invariant under
  isomorphisms of topological rings.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1, Definition 8.26, and
  Proposition and Definition 6.29.
-/

public section

open CategoryTheory UniformSpace TauCeti.ValuationSpectrum _root_.TopologicalSpace

namespace TauCeti.Huber

universe u v w

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

/-- **Sheafiness of a complete Hausdorff Huber ring**: a complete Hausdorff Huber ring `B` is sheafy
exactly when every ring of integral elements `B⁺` of `B` itself satisfies
`TauCeti.Huber.IsSheafyForEveryPresentation`. For an arbitrary Huber ring,
`TauCeti.Huber.IsSheafyRing.isSheafyForEveryPresentation` gives the forward direction. -/
theorem isSheafyRing_iff_forall_isSheafyForEveryPresentation {B : Type u} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B] [CompleteSpace B]
    [T0Space B] : IsSheafyRing B ↔ ∀ Bplus : Subring B, IsRingOfIntegralElements Bplus →
      IsSheafyForEveryPresentation Bplus := by
  refine ⟨fun h _ ↦ h.isSheafyForEveryPresentation, fun h ↦ isSheafyRing_iff.mpr ?_⟩
  -- carry the plus rings of `B̂` to `B` along the topological ring isomorphism `B̂ ≃ B`
  exact (forall_isSheafyForEveryPresentation_iff_of_ringEquiv _
    (Completion.uniformContinuous_completeRingEquivSelf B).continuous
    (Completion.uniformContinuous_completeRingEquivSelf_symm B).continuous).mpr h

/-- **Sheafiness is invariant under completion**: the completion `Â` of a Huber ring `A` is sheafy
exactly when `A` is. -/
@[simp]
theorem isSheafyRing_completion_iff : IsSheafyRing (Completion A) ↔ IsSheafyRing A :=
  isSheafyRing_iff_forall_isSheafyForEveryPresentation.trans isSheafyRing_iff.symm

section RingEquiv

variable {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsHuberRing B]

/-- **Sheafiness depends only on the completion**: if the completions `Â` and `B̂` of Huber rings
`A` and `B` are isomorphic as topological rings, then `A` is sheafy exactly when `B` is. -/
theorem isSheafyRing_iff_of_completion_ringEquiv (e : Completion A ≃+* Completion B)
    (he : Continuous e) (he' : Continuous e.symm) : IsSheafyRing A ↔ IsSheafyRing B :=
  isSheafyRing_iff.trans <|
    (forall_isSheafyForEveryPresentation_iff_of_ringEquiv e he he').trans isSheafyRing_iff.symm

/-- **Sheafiness is invariant under isomorphism**: if `e : A ≃+* B` is an isomorphism of
topological rings between Huber rings, then `A` is sheafy exactly when `B` is. The corresponding
statement for a plus ring `A⁺` and its image under `e` is
`TauCeti.Huber.isSheafyForEveryPresentation_iff_of_ringEquiv`. -/
theorem isSheafyRing_iff_of_ringEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    IsSheafyRing A ↔ IsSheafyRing B :=
  isSheafyRing_iff_of_completion_ringEquiv (Completion.mapRingEquiv e he he')
    (Completion.continuous_mapRingEquiv e he he') (Completion.continuous_mapRingEquiv_symm e he he')

end RingEquiv

/-! ### Stably sheafy Huber rings -/

variable (A) in
/-- **Wedhorn Definition 8.26**: a Huber ring `A` with completion `Â` is *stably sheafy* when every
complete Hausdorff Huber ring `B` topologically of finite type over `Â`, in the sense of Wedhorn's
Proposition and Definition 6.29(i) (`TauCeti.Huber.IsTopologicallyFiniteType`), is sheafy
(`TauCeti.Huber.IsSheafyRing`). The rings `B` range over an arbitrary universe `v`. -/
def IsStablySheafyRing : Prop :=
  ∀ (B : Type v) [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsHuberRing B] [CompleteSpace B] [T0Space B] (φ : Completion A →+* B),
    IsTopologicallyFiniteType φ → IsSheafyRing B

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.IsStablySheafyRing`. -/
theorem isStablySheafyRing_iff : IsStablySheafyRing.{u, v} A ↔ ∀ (B : Type v) [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B] [CompleteSpace B]
    [T0Space B] (φ : Completion A →+* B), IsTopologicallyFiniteType φ → IsSheafyRing B :=
  (Iff.rfl)

/-- **Stable sheafiness on the rings themselves**: `A` is stably sheafy exactly when, for every
complete Hausdorff Huber ring `B` topologically of finite type over `Â`, every ring of integral
elements `B⁺` of `B` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`. -/
theorem isStablySheafyRing_iff_forall_isSheafyForEveryPresentation :
    IsStablySheafyRing.{u, v} A ↔ ∀ (B : Type v) [CommRing B] [UniformSpace B]
      [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B] [CompleteSpace B] [T0Space B]
      (φ : Completion A →+* B),
      IsTopologicallyFiniteType φ → ∀ Bplus : Subring B, IsRingOfIntegralElements Bplus →
        IsSheafyForEveryPresentation Bplus := by
  rw [isStablySheafyRing_iff]
  congr!
  exact isSheafyRing_iff_forall_isSheafyForEveryPresentation

/-- **A stably sheafy Huber ring is sheafy**, since the identity of `Â` is topologically of finite
type. This uses the stable condition for rings `B` in the universe of `A`. -/
theorem IsStablySheafyRing.isSheafyRing (h : IsStablySheafyRing.{u, u} A) : IsSheafyRing A :=
  isSheafyRing_completion_iff.mp <| isStablySheafyRing_iff.mp h _ (.id _)
    isStrictlyTopologicallyFiniteType_id.isTopologicallyFiniteType

section StableRingEquiv

variable {B : Type w} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsHuberRing B]

/-- **Stable sheafiness depends only on the completion**: if the completions `Â` and `B̂` of Huber
rings `A` and `B` are isomorphic as topological rings, then `A` is stably sheafy exactly when `B`
is. `A` and `B` may lie in different universes; the rings topologically of finite type on the two
sides lie in the same universe. -/
theorem isStablySheafyRing_iff_of_completion_ringEquiv (e : Completion A ≃+* Completion B)
    (he : Continuous e) (he' : Continuous e.symm) :
    IsStablySheafyRing.{u, v} A ↔ IsStablySheafyRing.{w, v} B := by
  simp only [isStablySheafyRing_iff]
  exact ⟨fun h C _ _ _ _ _ _ _ φ hφ ↦ h C (φ.comp e) (hφ.comp_ringEquiv e he he'),
    fun h C _ _ _ _ _ _ _ φ hφ ↦ h C (φ.comp e.symm) (hφ.comp_ringEquiv e.symm he' he)⟩

/-- **Stable sheafiness is invariant under completion**: the completion `Â` of a Huber ring `A` is
stably sheafy exactly when `A` is. -/
@[simp]
theorem isStablySheafyRing_completion_iff : IsStablySheafyRing.{u, v} (Completion A) ↔
    IsStablySheafyRing.{u, v} A :=
  isStablySheafyRing_iff_of_completion_ringEquiv (Completion.completeRingEquivSelf _)
    (Completion.uniformContinuous_completeRingEquivSelf _).continuous
    (Completion.uniformContinuous_completeRingEquivSelf_symm _).continuous

/-- **Stable sheafiness is invariant under isomorphism**: if `e : A ≃+* B` is an isomorphism of
topological rings between Huber rings, then `A` is stably sheafy exactly when `B` is. -/
theorem isStablySheafyRing_iff_of_ringEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) : IsStablySheafyRing.{u, v} A ↔ IsStablySheafyRing.{w, v} B :=
  isStablySheafyRing_iff_of_completion_ringEquiv (Completion.mapRingEquiv e he he')
    (Completion.continuous_mapRingEquiv e he he') (Completion.continuous_mapRingEquiv_symm e he he')

end StableRingEquiv

end TauCeti.Huber

end
