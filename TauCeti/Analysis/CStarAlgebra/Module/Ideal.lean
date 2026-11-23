/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.RingTheory.TwoSidedIdeal.Unitization

/-!
# Unitization module action on closed ideals of C⋆-algebras

Compatibility of `TwoSidedIdeal.unitizationModuleOfSMulMem I I.smul_mem_of_isClosed` with the
complex module structure on a closed two-sided ideal `I` of a nonunital C⋆-algebra `A`.
-/

public section

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- The left `Unitization ℂ A`-module structure on a closed two-sided ideal `I` is compatible with
its `ℂ`-module structure. -/
theorem isScalarTower_unitizationModule :
    letI := I.unitizationModuleOfSMulMem I.smul_mem_of_isClosed
    IsScalarTower ℂ (Unitization ℂ A) I :=
  I.isScalarTower_unitizationModuleOfSMulMem I.smul_mem_of_isClosed I.coe_smul_complex

end TwoSidedIdeal
