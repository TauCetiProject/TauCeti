/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Category.Ring.Adjunctions

/-!
# Kernel ideals of sheaf morphisms

`CategoryTheory.Sheaf.idealKernel` assembles the sectionwise ring-homomorphism kernels into a
`SheafOfModules.Submodule` of the structure module. Its locality follows from separatedness
of the target sheaf.
-/

public section

open CategoryTheory Opposite
open TauCeti.SheafOfModules

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R S : Sheaf J CommRingCat.{u}}

/-- The ideal sheaf of sections annihilated by a morphism of sheaves of commutative rings. -/
noncomputable def idealKernel (φ : R ⟶ S) :
    (SheafOfModules.unit (ringCatSheaf R)).Submodule where
  obj U := RingHom.ker (φ.hom.app U).hom
  map i s hs :=
    have hzero : φ.hom.app _ s = 0 := hs
    have h : φ.hom.app _ (R.obj.map i s) = S.obj.map i (φ.hom.app _ s) :=
      ConcreteCategory.congr_hom (φ.hom.naturality i) s
    RingHom.mem_ker.mpr (h.trans (hzero ▸ map_zero _))
  isSheaf U s hs :=
    have hsection : φ.hom.app U s = 0 := S.isSeparated _ _ hs _ _ fun _ i hi ↦
      have hzero : φ.hom.app _ (R.obj.map i.op s) = 0 := hi
      have h : S.obj.map i.op (φ.hom.app _ s) = φ.hom.app _ (R.obj.map i.op s) :=
        (ConcreteCategory.congr_hom (φ.hom.naturality i.op) s).symm
      h.trans (hzero.trans (map_zero _).symm)
    hsection

/-- The section formula for `idealKernel` identifies its ideal on each object with the
ring-homomorphism kernel there. It is the simplification rule for evaluating this construction. -/
@[simp]
theorem idealKernel_obj (φ : R ⟶ S) (U : Cᵒᵖ) :
    (idealKernel φ).toSubmodule.obj U = RingHom.ker (φ.hom.app U).hom :=
  (rfl)

end CategoryTheory.Sheaf
