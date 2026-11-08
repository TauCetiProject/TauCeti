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
representation factor. The public formula
`FDRep.cliffordReconstructionRepresentation_restrict_tmul` supplies the action
hypothesis for `FDRep.balancedTensorUnitEquiv A _
(cliffordReconstructionRepresentation_restrict_tmul A s hs U)`, the
ground-field-linear unit comparison needed to invert reconstruction. Its
computation and inverse rules are the general `FDRep.balancedTensorUnit*` API.

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

/-- The reconstructed action restricted along the normal-subgroup inclusion acts
only on the representation factor, in the `Rep` carrier view used by the balanced
tensor–Hom unit. -/
theorem cliffordReconstructionRepresentation_restrict_tmul (n : N) (m : M) (x : V) :
    ρ n (BalancedTensorProduct.tmul k (End A) (N := V) m x) =
      BalancedTensorProduct.tmul k (End A) (N := V) m ((V).ρ n x) := by
  -- The native tensor formula uses the FDRep carrier, rather than its Rep view.
  erw [MonoidHom.comp_apply, cliffordReconstructionRepresentation_inclusion_tmul]
  rw [FDRep.forget₂_ρ]
  rfl

end FDRep
