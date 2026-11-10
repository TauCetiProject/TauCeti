/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import TauCeti.Topology.Algebra.Ring.MaximalIdeals

/-!
# Isometries on ideal quotients

An isometric ring homomorphism with dense range induces an isometry on quotients by an ideal
and its extension, provided the extended ideal is closed. Indeed, the extended ideal is then
the closure of the image of the original ideal, so distances to the two ideals agree.
This applies in particular to residue norms of presentation quotients inside completed algebras.
-/

public section

namespace RingHom

variable {A B : Type*} [SeminormedCommRing A] [SeminormedCommRing B]

/-- An isometric homomorphism with dense range induces an isometry on ideal quotients
whenever the extended ideal is closed. -/
theorem isometry_quotientMap (f : A →+* B) (hf : Isometry f) (hd : DenseRange f)
    (I : Ideal A) [IsClosed (I.map f : Set B)] :
    Isometry (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) := by
  have hclosure : closure (f '' (I : Set A)) = (I.map f : Set B) := by
    apply Set.Subset.antisymm
    · exact closure_minimal (Ideal.subset_span) inferInstance
    · exact Ideal.map_subset_closure_image_of_denseRange hd I
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotientMap_mk]
  -- Ideal quotient norms are the additive-group quotient norms used by Mathlib.
  have hA : ‖Ideal.Quotient.mk I a‖ = Metric.infDist a (I : Set A) :=
    QuotientAddGroup.norm_mk (S := I.toAddSubgroup) a
  have hB : ‖Ideal.Quotient.mk (I.map f) (f a)‖ =
      Metric.infDist (f a) (I.map f : Set B) :=
    QuotientAddGroup.norm_mk (S := (I.map f).toAddSubgroup) (f a)
  rw [hA, hB, ← hclosure, Metric.infDist_closure, Metric.infDist_image hf]

end RingHom
