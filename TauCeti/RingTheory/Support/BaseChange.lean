/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Torsion
public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import TauCeti.RingTheory.FittingIdeal.Determinant

/-!
# Annihilators of finite modules after scalar extension

A finite module vanishes after scalar extension exactly when its extended annihilator is the
unit ideal. Applied to a quotient, this detects whether a submodule spans after base change.
-/

public section

open TensorProduct

namespace TauCeti.Module

/-- A finite module vanishes after scalar extension exactly when its extended annihilator is
the unit ideal. -/
theorem annihilator_map_eq_top_iff_subsingleton_tensorProduct {A B C : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup C] [Module A C] [Module.Finite A C] :
    (Module.annihilator A C).map (algebraMap A B) = ⊤ ↔ Subsingleton (B ⊗[A] C) := by
  constructor
  · intro h
    exact TauCeti.subsingleton_tensorProduct_of_isTorsionBySet_right
      (I := Module.annihilator A C) (by rw [Ideal.smul_top_eq_map, h]; rfl)
      (Module.isTorsionBySet_annihilator A C)
  · intro h
    apply top_le_iff.mp
    rw [← (TauCeti.fittingIdeal_zero_map_eq_top_iff (R := A) (M := C) B).mpr h]
    exact Ideal.map_mono TauCeti.fittingIdeal_zero_le_annihilator

end TauCeti.Module
