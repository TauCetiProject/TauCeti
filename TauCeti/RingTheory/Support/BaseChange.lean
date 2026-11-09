/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import TauCeti.RingTheory.FittingIdeal.Determinant

/-!
# Annihilators of finite modules after scalar extension

A finite module that vanishes after scalar extension has unit extended annihilator.
This detects vanishing after base change, and hence spanning of finite-module quotients,
through an ideal in the original coefficient ring.
-/

public section

open TensorProduct

namespace TauCeti.Module

/-- If the base change of a finite `A`-module `C` to an `A`-algebra `B` vanishes, then the
annihilator of `C` generates the unit ideal of `B`. -/
theorem annihilator_map_eq_top_of_subsingleton_tensorProduct {A B C : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup C] [Module A C] [Module.Finite A C]
    [Subsingleton (B ⊗[A] C)] :
    (Module.annihilator A C).map (algebraMap A B) = ⊤ := by
  apply top_le_iff.mp
  rw [← (TauCeti.fittingIdeal_zero_map_eq_top_iff (R := A) (M := C) B).mpr inferInstance]
  exact Ideal.map_mono TauCeti.fittingIdeal_zero_le_annihilator

end TauCeti.Module
