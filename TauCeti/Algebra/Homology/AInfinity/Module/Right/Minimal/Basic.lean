/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Cohomology

/-!
# Minimal right A-infinity modules

A right `A∞` module is **minimal** when its unary operation `m₁` vanishes
(`TauCeti.AInfinityRightModule.IsMinimal`).  Every element of a minimal module is then a cycle and
no nonzero element is a boundary, so the module is its own cohomology.  The map induced on
cohomology by a morphism between minimal modules is therefore its linear part.  A
quasi-isomorphism between minimal modules is an isomorphism of right `A∞` modules
(`TauCeti.AInfinityRightModuleHom.IsQuasiIso.isIso`, stated for vanishing unary operations in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Iso`).  This holds over any commutative
ring.  The minimal model of a module over a field is constructed in
`TauCeti.Algebra.Homology.AInfinity.Module.Right.Minimal.Model`.

## Main definitions

* `TauCeti.AInfinityRightModule.IsMinimal`: a right `A∞` module with zero unary operation.
* `TauCeti.AInfinityRightModule.IsMinimal.cohomologyEquiv`: the identification of a minimal module
  with its cohomology.

## Main results

* `TauCeti.AInfinityRightModule.isMinimal_iff_cycles_eq_top` and
  `TauCeti.AInfinityRightModule.isMinimal_iff_boundaries_eq_bot`: minimality in terms of cycles
  and boundaries.
* `TauCeti.AInfinityRightModuleHom.cohomologyMap_cohomologyEquiv`: between minimal modules, the
  map induced on cohomology is the linear part.

The algebra counterpart is `TauCeti.AInfinityAlgebra.IsMinimal`, in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
-/

public section

namespace TauCeti

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup A]
  [Module R A] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {AA : AInfinityAlgebra R A}

namespace AInfinityRightModule

/-- A right `A∞` module is **minimal** when its unary operation `m₁` vanishes. -/
def IsMinimal (MM : AInfinityRightModule AA M) : Prop :=
  MM.differential = 0

/-- A right `A∞` module is minimal exactly when its differential vanishes. -/
theorem isMinimal_def (MM : AInfinityRightModule AA M) :
    MM.IsMinimal ↔ MM.differential = 0 :=
  Iff.rfl

/-- A right `A∞` module is minimal exactly when every element is a cycle. -/
theorem isMinimal_iff_cycles_eq_top (MM : AInfinityRightModule AA M) :
    MM.IsMinimal ↔ MM.cycles = ⊤ := by
  rw [isMinimal_def, cycles_def, LinearMap.ker_eq_top]

/-- A right `A∞` module is minimal exactly when zero is its only boundary. -/
theorem isMinimal_iff_boundaries_eq_bot (MM : AInfinityRightModule AA M) :
    MM.IsMinimal ↔ MM.boundaries = ⊥ := by
  rw [isMinimal_def, boundaries_def, LinearMap.range_eq_bot]

namespace IsMinimal

variable {MM : AInfinityRightModule AA M}

/-- Every element of a minimal module is a cycle. -/
theorem mem_cycles (h : MM.IsMinimal) (x : M) : x ∈ MM.cycles := by
  rw [(isMinimal_iff_cycles_eq_top MM).1 h]
  exact Submodule.mem_top

/-- In a minimal module, the boundaries inside the cycles are trivial. -/
theorem boundariesInCycles_eq_bot (h : MM.IsMinimal) : MM.boundariesInCycles = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [mem_boundariesInCycles, (isMinimal_iff_boundaries_eq_bot MM).1 h, Submodule.mem_bot] at hx
  exact Subtype.ext hx

/-- A minimal module is linearly equivalent to its cohomology: every element is a cycle, and no
nonzero element is a boundary. -/
noncomputable def cohomologyEquiv (h : MM.IsMinimal) : M ≃ₗ[R] MM.Cohomology :=
  (LinearEquiv.ofTop MM.cycles ((isMinimal_iff_cycles_eq_top MM).1 h)).symm ≪≫ₗ
    (Submodule.quotEquivOfEqBot _ h.boundariesInCycles_eq_bot).symm

/-- The identification of a minimal module with its cohomology sends an element to its class. -/
@[simp]
theorem cohomologyEquiv_apply (h : MM.IsMinimal) (x : M) :
    h.cohomologyEquiv x = MM.cohomologyClass (h.mem_cycles x) := by
  rw [cohomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.ofTop_symm_apply,
    Submodule.quotEquivOfEqBot_symm_apply, cohomologyClass_eq_mk]

end IsMinimal

end AInfinityRightModule

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}

/-- Between minimal modules, the map induced on cohomology is the linear part, transported along
the identifications of the modules with their cohomology. -/
theorem cohomologyMap_cohomologyEquiv (hM : MM.IsMinimal) (hN : NN.IsMinimal)
    (f : AInfinityRightModuleHom MM NN) (x : M) :
    f.cohomologyMap (hM.cohomologyEquiv x) = hN.cohomologyEquiv (f.linearPart x) := by
  simp only [AInfinityRightModule.IsMinimal.cohomologyEquiv_apply, cohomologyMap_cohomologyClass]

end AInfinityRightModuleHom

end TauCeti
