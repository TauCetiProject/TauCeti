/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Restrict

/-!
# Preimages under a map restricted to a subset or preimage

The preimage of a set `u ⊆ t` under `Set.restrictPreimage t f` has the same cardinality as the
preimage of `u` under `f`, and is finite exactly when that preimage is; in particular this holds
for the fibres over points of `t`. Dually, removing the preimage of a set from the domain does not
change the fibres over points outside that set.

For a domain restriction `u.domRestrict f`, the preimage of `{y}` lies in `{⟨x, hx⟩}` exactly when
`x` is the only point of `u` sent to `y` (`Set.preimage_domRestrict_singleton_subset_iff`), and
the preimage of `s` under the inclusion of `(s \ {x})ᶜ` lies in `{x}`
(`Set.preimage_val_compl_diff_singleton_subset`).

For `h : MapsTo f s t`, the image in `α` of the preimage of `A ⊆ t` under `h.restrict` is
`s ∩ f ⁻¹' A` (`Set.MapsTo.image_val_preimage_restrict`).
-/

public section

namespace Set

variable {α β : Type*} (t : Set β) {f : α → β}

/-- Restricting a map to the preimage of `t` does not change the cardinality of the preimage of
a subset of `t`. -/
@[simp] theorem ncard_preimage_restrictPreimage {u : Set t} :
    (t.restrictPreimage f ⁻¹' u).ncard = (f ⁻¹' (Subtype.val '' u)).ncard := by
  rw [← image_val_preimage_restrictPreimage, ncard_image_of_injective _ Subtype.val_injective]

/-- Restricting a map to the preimage of `t` does not change whether the preimage of a subset of
`t` is finite. -/
@[simp] theorem finite_preimage_restrictPreimage_iff {u : Set t} :
    (t.restrictPreimage f ⁻¹' u).Finite ↔ (f ⁻¹' (Subtype.val '' u)).Finite := by
  rw [← image_val_preimage_restrictPreimage, finite_image_iff Subtype.val_injective.injOn]

variable (f) in
/-- Removing the preimage of a set `Z` from a set `T` does not change the cardinality of the part
of `T` in a fiber over a point outside `Z`. -/
theorem natCard_fiber_sdiff_preimage {T : Set α} {Z : Set β} {y : β} (hy : y ∉ Z) :
    Nat.card {x // f x = y ∧ x ∈ T \ f ⁻¹' Z} = Nat.card {x // f x = y ∧ x ∈ T} :=
  Nat.card_congr <| Equiv.subtypeEquivRight fun x ↦ by grind

/-- The preimage of `{y}` under `u.domRestrict f` is contained in `{⟨x, hx⟩}` if and only if `x` is
the only point of `u` sent to `y`. -/
theorem preimage_domRestrict_singleton_subset_iff {u : Set α} {f : α → β} {x : α} {y : β}
    (hx : x ∈ u) :
    u.domRestrict f ⁻¹' {y} ⊆ {⟨x, hx⟩} ↔ ∀ z ∈ u, f z = y → z = x :=
  ⟨fun h z hz hfz ↦ congrArg Subtype.val (h (a := ⟨z, hz⟩) hfz),
    fun h z hz ↦ Subtype.ext (h z z.property hz)⟩

/-- The preimage of `s` under the subtype inclusion `(s \ {x})ᶜ → α` is contained in `{x}`. -/
theorem preimage_val_compl_diff_singleton_subset (s : Set α) (x : α) :
    (Subtype.val : ↥(s \ {x})ᶜ → α) ⁻¹' s ⊆ {⟨x, fun h ↦ h.2 rfl⟩} :=
  fun z hz ↦ Subtype.ext (by_contra fun h ↦ z.property ⟨hz, h⟩)

/-- For `h : MapsTo f s u`, the image in `α` of the preimage of `A ⊆ u` under `h.restrict` is the
set of points of `s` that `f` sends into `A`. -/
theorem MapsTo.image_val_preimage_restrict {s : Set α} {u : Set β} (h : MapsTo f s u)
    (A : Set u) : Subtype.val '' (h.restrict f s u ⁻¹' A) = s ∩ f ⁻¹' (Subtype.val '' A) := by
  rw [← Subtype.image_preimage_coe, ← preimage_comp, ← h.restrict_commutes, preimage_comp,
    preimage_image_eq _ Subtype.val_injective]

end Set
