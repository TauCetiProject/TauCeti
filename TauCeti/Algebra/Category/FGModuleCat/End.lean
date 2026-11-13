/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import TauCeti.Algebra.Category.FGModuleCat.Basic
import TauCeti.CategoryTheory.Functor.RingEquivEnd

/-!
# Endomorphism rings in `FGModuleCat`

The endomorphism ring of an object of `FGModuleCat A` is the ring of linear endomorphisms of its
underlying module (`FGModuleCat.endRingEquiv`), so one is local exactly when the other is
(`FGModuleCat.isLocalRing_end_iff`). In particular a local ring, as a finitely generated module
over itself, has a local endomorphism ring without any finiteness assumption, that ring being the
opposite of the ring.
-/

public section

namespace FGModuleCat

open CategoryTheory

universe v

variable {A : Type v} [Ring A]

/-- The endomorphism ring of an object of `FGModuleCat A` is isomorphic to the ring of linear
endomorphisms of its underlying module. -/
noncomputable def endRingEquiv (X : FGModuleCat A) : End X ≃+* Module.End A X :=
  ((ObjectProperty.fullyFaithfulι _).ringEquivEnd X).trans (ModuleCat.endRingEquiv X.obj)

@[simp]
theorem endRingEquiv_apply (X : FGModuleCat A) (f : End X) :
    endRingEquiv X f = f.asHom.hom.hom := by
  rw [endRingEquiv, RingEquiv.trans_apply, ModuleCat.endRingEquiv_apply,
    Functor.FullyFaithful.ringEquivEnd_apply_asHom, ObjectProperty.ι_map]

@[simp]
theorem endRingEquiv_symm_apply (X : FGModuleCat A) (f : Module.End A X) :
    (endRingEquiv X).symm f = End.of (FGModuleCat.ofHom f) := by
  rw [RingEquiv.symm_apply_eq, endRingEquiv_apply]
  simp

/-- An object of `FGModuleCat A` has a local endomorphism ring exactly when its underlying module
does. -/
theorem isLocalRing_end_iff {X : FGModuleCat A} :
    IsLocalRing (End X) ↔ IsLocalRing (Module.End A X) :=
  ⟨fun _ ↦ (endRingEquiv X).isLocalRing, fun _ ↦ (endRingEquiv X).symm.isLocalRing⟩

/-- A local ring, as a finitely generated module over itself, has a local endomorphism ring: that
ring is the opposite of the ring. -/
instance [IsLocalRing A] : IsLocalRing (End (FGModuleCat.of A A)) :=
  -- The carrier of `FGModuleCat.of A A` is `A` by definition.
  isLocalRing_end_iff.mpr (RingEquiv.moduleEndSelf A).isLocalRing

end FGModuleCat
