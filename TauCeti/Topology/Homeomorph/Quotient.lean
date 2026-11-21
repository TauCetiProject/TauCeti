/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Homeomorphisms associated with quotient spaces

This file records how Mathlib's `Homeomorph.Quotient.congr` and
`Homeomorph.Quotient.congrRight`, homeomorphisms between quotient spaces, act on equivalence
classes, and constructs the canonical homeomorphism between an open subset of a quotient space and
the quotient of its saturated preimage.

## Main definitions

* `IsOpen.quotientComapHomeomorph`: for an open subset `V` of `Quotient r`, the canonical
  homeomorphism `Quotient (r.comap (Subtype.val : Quotient.mk r ⁻¹' V → X)) ≃ₜ V`.

## Main results

* `Homeomorph.Quotient.congr_mk`: `congr` sends the class of `x` to the class of its image.
* `Homeomorph.Quotient.congrRight_mk`: `congrRight` sends the class of `x` to the class of `x`.
* `IsOpen.quotientComapHomeomorph_mk`, `IsOpen.quotientComapHomeomorph_symm_mk`: action of
  `IsOpen.quotientComapHomeomorph` and its inverse on equivalence classes.
-/

public section

open Set Topology

namespace Homeomorph.Quotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `Homeomorph.Quotient.congr` sends the class of `x` to the class of its image. This is the
homeomorphism counterpart of Mathlib's `Quotient.congr_mk`, and holds by definition for the same
reason. The counterpart is needed because a homeomorphism and its underlying equivalence are
applied through different coercions, so `Quotient.congr_mk` does not rewrite a goal stated for
`Homeomorph.Quotient.congr`, just as `Quot.congr_mk` does not rewrite one stated for
`Quotient.congr`. -/
@[simp]
theorem congr_mk {rX : Setoid X} {rY : Setoid Y} (e : X ≃ₜ Y)
    (h : ∀ x₁ x₂, rX x₁ x₂ ↔ rY (e x₁) (e x₂)) (x : X) :
    Homeomorph.Quotient.congr e h (Quotient.mk rX x) = Quotient.mk rY (e x) :=
  rfl

/-- `Homeomorph.Quotient.congrRight` sends the class of `x` to the class of `x`. This is the
homeomorphism counterpart of Mathlib's `Quot.congr_mk`, and holds by definition for the same
reason: `Homeomorph.Quotient.congrRight` is `Quot.congr` for the identity equivalence. -/
@[simp]
theorem congrRight_mk {r r' : Setoid X} (h : ∀ x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) (x : X) :
    Homeomorph.Quotient.congrRight h (Quotient.mk r x) = Quotient.mk r' x :=
  rfl

end Homeomorph.Quotient

namespace IsOpen

variable {X : Type*} [TopologicalSpace X] {r : Setoid X}

/-- For an open subset `V` of `Quotient r`, the quotient of the saturated open preimage
`Quotient.mk r ⁻¹' V` by the induced setoid `r.comap Subtype.val` is canonically homeomorphic to
`V`. -/
noncomputable def quotientComapHomeomorph {V : Set (Quotient r)} (hV : IsOpen V) :
    Quotient (r.comap (Subtype.val : Quotient.mk r ⁻¹' V → X)) ≃ₜ V :=
  let g : C(Quotient.mk r ⁻¹' V, V) :=
    ⟨V.restrictPreimage (Quotient.mk r), continuous_quot_mk.restrictPreimage⟩
  have hg : IsQuotientMap g := (isQuotientMap_quot_mk (r := r.r)).restrictPreimage_isOpen hV
  (Homeomorph.Quotient.congrRight (r := r.comap Subtype.val) (r' := Setoid.ker g) fun _ _ ↦
    ⟨fun h ↦ Setoid.ker_def.mpr (Subtype.ext (Quotient.sound h)),
      fun h ↦ Quotient.exact (s := r) (congrArg Subtype.val (Setoid.ker_def.mp h))⟩).trans
    hg.homeomorph

/-- `IsOpen.quotientComapHomeomorph` sends the induced equivalence class of `x` in
`Quotient.mk r ⁻¹' V` to the ambient class `Quotient.mk r x.val` in `V`. -/
@[simp]
theorem quotientComapHomeomorph_mk {V : Set (Quotient r)} (hV : IsOpen V)
    (x : Quotient.mk r ⁻¹' V) :
    hV.quotientComapHomeomorph (Quotient.mk (r.comap Subtype.val) x) =
      ⟨Quotient.mk r x.val, x.property⟩ := by
  rfl

/-- The inverse of `IsOpen.quotientComapHomeomorph` sends a class `⟨Quotient.mk r x, hx⟩` in `V`
to the induced equivalence class of `⟨x, hx⟩` in `Quotient.mk r ⁻¹' V`. -/
@[simp]
theorem quotientComapHomeomorph_symm_mk {V : Set (Quotient r)} (hV : IsOpen V) (x : X)
    (hx : Quotient.mk r x ∈ V) :
    hV.quotientComapHomeomorph.symm ⟨Quotient.mk r x, hx⟩ =
      Quotient.mk (r.comap Subtype.val) ⟨x, hx⟩ :=
  hV.quotientComapHomeomorph.symm_apply_eq.mpr (quotientComapHomeomorph_mk hV ⟨x, hx⟩)

end IsOpen
