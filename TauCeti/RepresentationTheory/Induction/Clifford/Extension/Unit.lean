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

This is the ground-field-linear unit comparison needed to invert reconstruction.
It specializes `FDRep.balancedTensorUnit` and its bijectivity: the reconstructed
action restricted to the normal subgroup acts only on the representation factor.

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

private theorem reconstruction_restrict_tmul (n : N) (m : M) (x : V) :
    ρ n (BalancedTensorProduct.tmul k (End A) (N := V) m x) =
      BalancedTensorProduct.tmul k (End A) (N := V) m ((V).ρ n x) := by
  -- The native tensor formula uses the FDRep carrier, rather than its Rep view.
  erw [MonoidHom.comp_apply, cliffordReconstructionRepresentation_inclusion_tmul]
  rw [FDRep.forget₂_ρ]
  rfl

/-- The canonical multiplicity map sends `m` to the normal-subgroup intertwiner
`x ↦ m ⊗ x` in the reconstructed representation. -/
def cliffordReconstructionUnit : M →ₗ[k] Representation.IntertwiningMap (V).ρ ρ :=
  balancedTensorUnit A ρ (reconstruction_restrict_tmul A s hs U)

/-- The unit comparison evaluates to the pure balanced tensor. -/
@[simp]
theorem cliffordReconstructionUnit_apply (m : M) (x : V) :
    cliffordReconstructionUnit A s hs U m x =
      BalancedTensorProduct.tmul k (End A) (N := V) m x :=
  balancedTensorUnit_apply A ρ (reconstruction_restrict_tmul A s hs U) m x

variable [Simple A]

/-- Reconstructing from a multiplicity module and then taking normal-subgroup
multiplicities recovers the original ground-field vector space, even for infinite modules. -/
theorem cliffordReconstructionUnit_bijective :
    Function.Bijective (cliffordReconstructionUnit A s hs U) :=
  balancedTensorUnit_bijective A ρ (reconstruction_restrict_tmul A s hs U)

/-- The canonical ground-field-linear unit comparison for Clifford reconstruction. -/
def cliffordReconstructionUnitEquiv :
    M ≃ₗ[k] Representation.IntertwiningMap (V).ρ ρ :=
  balancedTensorUnitEquiv A ρ (reconstruction_restrict_tmul A s hs U)

/-- The unit equivalence sends a multiplicity vector to tensoring with that vector. -/
@[simp]
theorem cliffordReconstructionUnitEquiv_apply (m : M) :
    cliffordReconstructionUnitEquiv A s hs U m =
      cliffordReconstructionUnit A s hs U m :=
  balancedTensorUnitEquiv_apply A ρ (reconstruction_restrict_tmul A s hs U) m

/-- The inverse unit equivalence recovers a vector from its tensoring intertwiner. -/
@[simp]
theorem cliffordReconstructionUnitEquiv_symm_unit (m : M) :
    (cliffordReconstructionUnitEquiv A s hs U).symm
      (cliffordReconstructionUnit A s hs U m) = m :=
  balancedTensorUnitEquiv_symm_unit A ρ (reconstruction_restrict_tmul A s hs U) m

/-- Tensoring with the recovered multiplicity vector gives the original intertwiner. -/
@[simp]
theorem cliffordReconstructionUnit_equiv_symm
    (f : Representation.IntertwiningMap (V).ρ ρ) :
    cliffordReconstructionUnit A s hs U
      ((cliffordReconstructionUnitEquiv A s hs U).symm f) = f :=
  balancedTensorUnit_equiv_symm A ρ (reconstruction_restrict_tmul A s hs U) f

end FDRep
