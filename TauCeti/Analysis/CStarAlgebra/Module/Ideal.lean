/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Annihilator
public import TauCeti.RingTheory.TwoSidedIdeal.Unitization

/-!
# Unitization module action on closed ideals of C⋆-algebras

Compatibility of `TwoSidedIdeal.unitizationModuleOfSMulMem I I.smul_mem_of_isClosed` with the
complex module structure on a closed two-sided ideal `I` of a nonunital C⋆-algebra `A`, together
with `star`-invariance of the pullback of `(Module.annihilator (Unitization ℂ A) I).toTwoSided`
along `Unitization.inrNonUnitalAlgHom ℂ A`.
-/

public section

namespace TwoSidedIdeal

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- The left `Unitization ℂ A`-module structure on a closed two-sided ideal `I` is compatible with
its `ℂ`-module structure. -/
theorem isScalarTower_unitizationModule :
    letI := I.unitizationModuleOfSMulMem I.smul_mem_of_isClosed
    IsScalarTower ℂ (Unitization ℂ A) I :=
  I.isScalarTower_unitizationModuleOfSMulMem I.smul_mem_of_isClosed I.coe_smul_complex

/-- For a closed two-sided ideal `I` of a nonunital C⋆-algebra `A`, the preimage of
`(Module.annihilator (Unitization ℂ A) I).toTwoSided` along `Unitization.inrNonUnitalAlgHom ℂ A` is
closed under `star`. -/
theorem star_mem_comap_toTwoSided_annihilator {a : A} :
    letI := I.unitizationModuleOfSMulMem I.smul_mem_of_isClosed
    a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided →
      star a ∈ TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom ℂ A)
          (Module.annihilator (Unitization ℂ A) I).toTwoSided := by
  let _ : Module (Unitization ℂ A) I := I.unitizationModuleOfSMulMem I.smul_mem_of_isClosed
  rw [← I.annihilator_eq_comap_annihilator_unitization_of_smul_mem I.smul_mem_of_isClosed]
  exact star_mem_annihilator_of_cstar

end Unitization

end TwoSidedIdeal
