/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Reconstruction
public import TauCeti.RepresentationTheory.FDRep.BalancedUnit

/-!
# Recovering multiplicities from Clifford reconstruction

For a simple normal-subgroup representation `A`, the map sending `m` to the
intertwiner `x ↦ m ⊗ x` identifies a multiplicity module with the intertwiner
space of its reconstructed representation. The tensor is balanced over the full
endomorphism division algebra, not just the ground field. Multiplicity modules
and inertia quotients may be infinite.

The reconstructed action restricted to the normal subgroup acts only on the
representation factor. `FDRep.cliffordReconstructionUnitEquiv` specializes the
general `FDRep.balancedTensorUnitEquiv` using the existing normal-subgroup action
formula. It is the ground-field-linear unit comparison needed to invert
reconstruction.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public noncomputable section

namespace FDRep

open CategoryTheory TauCeti TauCeti.CliffordExtension

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s : (groupExtension A).Section) (hs : s 1 = 1)
  {M : Type w} [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M]
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)

local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "F" => (R) ⋙ forget₂ (Rep k N) (ModuleCat k)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "ρ" => MonoidHom.comp (cliffordReconstructionRepresentation A s hs U)
  (Subgroup.inclusion (le_inertia A))

attribute [local instance] endModule

private local instance : IsScalarTower k (End A) V := (F).endModule_isScalarTower A

variable [Simple A]

/-- The ground-field-linear tensor–Hom unit recovering the multiplicity module
from Clifford reconstruction restricted to the normal subgroup. -/
def cliffordReconstructionUnitEquiv : M ≃ₗ[k] Representation.IntertwiningMap (V).ρ ρ :=
  balancedTensorUnitEquiv A ρ (cliffordReconstructionRepresentation_inclusion_tmul A s hs U)

/-- The Clifford unit equivalence sends a multiplicity vector to its tensoring map. -/
@[simp]
theorem cliffordReconstructionUnitEquiv_apply (m : M) :
    cliffordReconstructionUnitEquiv A s hs U m =
      balancedTensorUnit A ρ (cliffordReconstructionRepresentation_inclusion_tmul A s hs U) m :=
  balancedTensorUnitEquiv_apply A ρ
    (cliffordReconstructionRepresentation_inclusion_tmul A s hs U) m

/-- The inverse Clifford unit is the inverse of the general balanced tensor–Hom unit. -/
@[simp]
theorem cliffordReconstructionUnitEquiv_symm_apply
    (f : Representation.IntertwiningMap (V).ρ ρ) :
    (cliffordReconstructionUnitEquiv A s hs U).symm f =
      (balancedTensorUnitEquiv A ρ
        (cliffordReconstructionRepresentation_inclusion_tmul A s hs U)).symm f := (rfl)

end FDRep
