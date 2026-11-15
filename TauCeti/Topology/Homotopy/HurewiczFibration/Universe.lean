/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic

/-!
# Universe transport for Hurewicz fibrations

Lifting the source and target of a map with `ULift` preserves and reflects the
Hurewicz fibration property, without changing the universe of test spaces.
The two lifts may be chosen independently. In particular, a Hurewicz fibration
between spaces in different universes gives a native Serre fibration after
lifting both spaces into their common maximum universe.

Transport uses the native homeomorphisms `Homeomorph.ulift` and closure of
Hurewicz fibrations under composition. No size bound or separation assumption
on either space is needed.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7.
-/

public section

universe w u v u' v'

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B}

/-- Independent universe lifts of the source and target preserve and reflect the
Hurewicz fibration property, with the same test-space universe on both sides. -/
@[simp]
theorem isHurewiczFibration_ulift_iff :
    IsHurewiczFibration.{w}
      (fun e : ULift.{u'} E ↦ (ULift.up (p e.down) : ULift.{v'} B)) ↔
      IsHurewiczFibration.{w} p := by
  constructor
  · intro h
    have h' := (Homeomorph.ulift : ULift.{v'} B ≃ₜ B).isHurewiczFibration.comp
      (h.comp_homeomorph (Homeomorph.ulift : ULift.{u'} E ≃ₜ E).symm)
    convert h' using 1
    ext e
    rfl
  · intro h
    exact (Homeomorph.ulift : ULift.{v'} B ≃ₜ B).symm.isHurewiczFibration.comp
      (h.comp_homeomorph (Homeomorph.ulift : ULift.{u'} E ≃ₜ E))

/-- A Hurewicz fibration between spaces in possibly different universes is a native
Serre fibration after lifting both spaces into `Type (max u v)`. -/
theorem IsHurewiczFibration.mem_serreFibrations_ulift (h : IsHurewiczFibration.{w} p) :
    TopCat.serreFibrations
      (X := _root_.TopCat.of (ULift.{v} E)) (Y := _root_.TopCat.of (ULift.{u} B))
      (_root_.TopCat.ofHom
        ⟨fun e ↦ ULift.up (p e.down),
          continuous_uliftUp.comp (h.continuous.comp continuous_uliftDown)⟩) :=
  (isHurewiczFibration_ulift_iff.mpr h).mem_serreFibrations

end TauCeti
