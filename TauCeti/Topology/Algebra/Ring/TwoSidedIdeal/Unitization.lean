/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TwoSidedIdeal.Unitization
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal.Annihilator

/-!
# Closedness of unitization-module annihilator pullbacks

Closedness of the preimage in `A` of `(Module.annihilator (Unitization R A) I).toTwoSided` along
`Unitization.inrNonUnitalAlgHom R A` for an `R`-invariant two-sided ideal `I` of a `T₁` nonunital
`R`-algebra `A` with separately continuous multiplication.
-/

public section

namespace TwoSidedIdeal

variable {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  [TopologicalSpace A] [SeparatelyContinuousMul A] [T1Space A]

/-- For an `R`-invariant two-sided ideal `I` of a `T₁` nonunital `R`-algebra `A` with separately
continuous multiplication, the preimage of `(Module.annihilator (Unitization R A) I).toTwoSided`
along `Unitization.inrNonUnitalAlgHom R A` is closed. -/
theorem isClosed_comap_toTwoSided_annihilator (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) :
    letI := I.unitizationModuleOfSMulMem hsmul
    IsClosed
      ((TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom R A)
          (Module.annihilator (Unitization R A) I).toTwoSided : TwoSidedIdeal A) : Set A) := by
  let _ : Module (Unitization R A) I := I.unitizationModuleOfSMulMem hsmul
  rw [← I.annihilator_eq_comap_annihilator_unitization_of_smul_mem hsmul]
  exact I.isClosed_annihilator

end TwoSidedIdeal
