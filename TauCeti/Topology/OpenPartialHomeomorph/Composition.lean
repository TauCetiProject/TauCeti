/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import TauCeti.Logic.Equiv.PartialEquiv

/-!
# Composing and restricting open partial homeomorphisms

This file supplements `Mathlib.Topology.OpenPartialHomeomorph.Composition`:

* `OpenPartialHomeomorph.image_trans_source_inter`,
  `OpenPartialHomeomorph.image_restrOpen_source_inter`,
  `OpenPartialHomeomorph.image_symm_trans_source_inter`, and
  `OpenPartialHomeomorph.image_restrOpen_symm_trans_source_inter`: equational image-transport
  formulas for compositions `e.trans e'`, open restrictions `e.restrOpen u hu`, and chart
  transitions `e.symm.trans e'`.
* `Homeomorph.refl_transOpenPartialHomeomorph`: precomposing an open partial homeomorphism with
  `Homeomorph.refl` changes nothing; together with `Homeomorph.trans_transOpenPartialHomeomorph`
  this makes `Homeomorph.transOpenPartialHomeomorph` an action of homeomorphisms.
-/

public section

namespace OpenPartialHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pushing a set forward along a composition `e.trans e'` of open partial homeomorphisms pushes its
`e`-source trace through `e` and then its `e'`-source trace through `e'`. -/
theorem image_trans_source_inter (e : OpenPartialHomeomorph X Y) (e' : OpenPartialHomeomorph Y Z)
    (s : Set X) :
    (e.trans e') '' ((e.trans e').source ∩ s) = e' '' (e'.source ∩ e '' (e.source ∩ s)) :=
  e.toPartialEquiv.image_trans_source_inter e'.toPartialEquiv s

/-- Restricting an open partial homeomorphism to an open subset `u` intersects source-restricted
images with the restricted target. -/
theorem image_restrOpen_source_inter (e : OpenPartialHomeomorph X Y) {u : Set X} (hu : IsOpen u)
    (s : Set X) :
    (e.restrOpen u hu) '' ((e.restrOpen u hu).source ∩ s) =
      (e.restrOpen u hu).target ∩ e '' (e.source ∩ s) :=
  e.toPartialEquiv.image_restr_source_inter u s

/-- A transition open partial homeomorphism `e.symm.trans e'` transports the `e`-image of `s` onto
the part of the `e'`-image of `s` lying in `(e.symm.trans e').target`. -/
theorem image_symm_trans_source_inter (e : OpenPartialHomeomorph X Y)
    (e' : OpenPartialHomeomorph X Z) (s : Set X) :
    (e.symm.trans e') '' ((e.symm.trans e').source ∩ e '' (e.source ∩ s)) =
      (e.symm.trans e').target ∩ e' '' (e'.source ∩ s) :=
  e.toPartialEquiv.image_symm_trans_source_inter e'.toPartialEquiv s

/-- Restricting a transition open partial homeomorphism `e.symm.trans e'` to an open subset `u ⊆ Y`
transports the `e`-image of `s` onto the part of the `e'`-image of `s` lying in
`((e.symm.trans e').restrOpen u hu).target`. -/
theorem image_restrOpen_symm_trans_source_inter (e : OpenPartialHomeomorph X Y)
    (e' : OpenPartialHomeomorph X Z) {u : Set Y} (hu : IsOpen u) (s : Set X) :
    ((e.symm.trans e').restrOpen u hu) ''
        (((e.symm.trans e').restrOpen u hu).source ∩ e '' (e.source ∩ s)) =
      ((e.symm.trans e').restrOpen u hu).target ∩ e' '' (e'.source ∩ s) :=
  e.toPartialEquiv.image_restr_symm_trans_source_inter e'.toPartialEquiv u s

end OpenPartialHomeomorph

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Precomposing an open partial homeomorphism with the identity homeomorphism leaves it
unchanged. -/
@[simp, mfld_simps]
theorem refl_transOpenPartialHomeomorph (c : OpenPartialHomeomorph X Y) :
    (Homeomorph.refl X).transOpenPartialHomeomorph c = c := by
  simp [transOpenPartialHomeomorph_eq_trans]

end Homeomorph
