/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic

/-!
# A cofibration which is a homotopy equivalence is a strong deformation retract

Let `A ⊆ X` have the homotopy extension property.  If the inclusion `A → X` is a homotopy
equivalence, then `A` is a strong deformation retract of `X`: there is a retraction
`r : X → A` together with a homotopy from the identity of `X` to `r` followed by the inclusion
which fixes every point of `A` throughout.  Conversely a strong deformation retract always
includes as a homotopy equivalence, so for such subsets the two notions agree.

This is the form in which cofibrations upgrade homotopy equivalences to deformations: for
instance, when `f : X → Y` is a homotopy equivalence, the inclusion of `X` into the mapping
cylinder of `f` has the homotopy extension property and is a homotopy equivalence, so `X` is a
strong deformation retract of the cylinder.

No closedness assumption on `A` is needed.

## Main declarations

* `TauCeti.HasHomotopyExtensionProperty.exists_retraction_homotopic`: a homotopy left inverse of
  the inclusion of a subset with the homotopy extension property is homotopic to a retraction.
* `TauCeti.HasHomotopyExtensionProperty.homotopicRel_of_retraction`: a retraction onto a subset
  with the homotopy extension property whose composite with the inclusion is homotopic to the
  identity is homotopic to the identity relative to the subset.
* `TauCeti.HasHomotopyExtensionProperty.exists_strong_deformation_retraction`: **if a subset with
  the homotopy extension property includes as a homotopy equivalence, it is a strong deformation
  retract.**
* `TauCeti.HasHomotopyExtensionProperty.exists_strong_deformation_retraction_iff`: the
  characterisation of strong deformation retracts among such subsets.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19; Hatcher's "deformation retraction" is stationary on the subspace,
  which is the strong notion used here.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousMap Set unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A homotopy left inverse `g : X → A` of the inclusion of a subset with the homotopy extension
property is homotopic to a retraction of `X` onto `A`. -/
theorem HasHomotopyExtensionProperty.exists_retraction_homotopic
    (hA : HasHomotopyExtensionProperty A) (g : C(X, A))
    (hg : (g.comp (subtypeVal A)).Homotopic (ContinuousMap.id A)) :
    ∃ r : C(X, A), (∀ a : A, r a = a) ∧ r.Homotopic g := by
  obtain ⟨H⟩ := hg
  obtain ⟨G, hG₀, hG₁⟩ := hA.exists_extension g H.toContinuousMap fun a => H.apply_zero a
  refine ⟨⟨fun x => G (1, x), by fun_prop⟩, fun a => ?_, ⟨Homotopy.symm ?_⟩⟩
  · simpa using hG₁ 1 a
  · exact { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun _ => rfl }

/-- A retraction `r` of `X` onto a subset `A` with the homotopy extension property whose
composite with the inclusion is homotopic to the identity of `X` is homotopic to the identity
relative to `A`. -/
theorem HasHomotopyExtensionProperty.homotopicRel_of_retraction
    (hA : HasHomotopyExtensionProperty A) {r : C(X, A)} (hr : ∀ a : A, r a = a)
    (hr' : ((subtypeVal A).comp r).Homotopic (ContinuousMap.id X)) :
    (ContinuousMap.id X).HomotopicRel ((subtypeVal A).comp r) A := by
  obtain ⟨h⟩ := hr'.symm
  -- Follow `h` from the identity to `r`, then follow `h` backwards from `r x` to `r (r x) = r x`;
  -- at the points of `A`, which `r` fixes, the second homotopy retraces the first.
  refine hA.homotopicRel_of_retracing h ((h.symm.compContinuousMap ((subtypeVal A).comp r)).cast
    (ContinuousMap.ext fun x => by simp [hr]) (ContinuousMap.id_comp _)) fun t x hx => ?_
  have hrx : (r x : X) = x := congrArg Subtype.val (hr ⟨x, hx⟩)
  simp [hrx]

/-- **A cofibration which is a homotopy equivalence is a strong deformation retract.**  If the
inclusion of a subset `A` with the homotopy extension property is a homotopy equivalence, with
homotopy inverse `g`, then there is a retraction `r : X → A` such that the identity of `X` is
homotopic, relative to `A`, to `r` followed by the inclusion. -/
theorem HasHomotopyExtensionProperty.exists_strong_deformation_retraction
    (hA : HasHomotopyExtensionProperty A) (g : C(X, A))
    (hg₁ : (g.comp (subtypeVal A)).Homotopic (ContinuousMap.id A))
    (hg₂ : ((subtypeVal A).comp g).Homotopic (ContinuousMap.id X)) :
    ∃ r : C(X, A), (∀ a : A, r a = a) ∧
      (ContinuousMap.id X).HomotopicRel ((subtypeVal A).comp r) A := by
  obtain ⟨r, hr, hrg⟩ := hA.exists_retraction_homotopic g hg₁
  exact ⟨r, hr, hA.homotopicRel_of_retraction hr (((Homotopic.refl _).comp hrg).trans hg₂)⟩

/-- A subset with the homotopy extension property is a strong deformation retract exactly when its
inclusion is a homotopy equivalence. -/
theorem HasHomotopyExtensionProperty.exists_strong_deformation_retraction_iff
    (hA : HasHomotopyExtensionProperty A) :
    (∃ r : C(X, A), (∀ a : A, r a = a) ∧
      (ContinuousMap.id X).HomotopicRel ((subtypeVal A).comp r) A) ↔
      ∃ g : C(X, A), (g.comp (subtypeVal A)).Homotopic (ContinuousMap.id A) ∧
        ((subtypeVal A).comp g).Homotopic (ContinuousMap.id X) := by
  refine ⟨fun ⟨r, hr, hrel⟩ => ⟨r, ?_, hrel.homotopic.symm⟩,
    fun ⟨g, hg₁, hg₂⟩ => hA.exists_strong_deformation_retraction g hg₁ hg₂⟩
  have hri : r.comp (subtypeVal A) = ContinuousMap.id A := ContinuousMap.ext hr
  rw [hri]

end TauCeti
