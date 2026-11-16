/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Unit.Basic
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.FiniteDimensional
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Module

/-!
# The crossed-product-linear Clifford unit

Reconstructing a finite-dimensional multiplicity module and then taking its normal-subgroup
multiplicities recovers the original module over the full opposite-commutant crossed product.
The comparison sends `m` to the intertwiner `x ↦ m ⊗ x`. It respects both the commutant
coefficients and the section operators, so it preserves the algebra action rather than only
the underlying vector space. The prescribed normal-subgroup representation is simple;
no splitting-field, Maschke, or finite-inertia-quotient assumption is needed.

The linear bijection is `FDRep.cliffordReconstructionUnitEquiv`. The algebra-linearity
uses the balanced tensor relation and the conjugation formula for multiplicities.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public noncomputable section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s : (groupExtension A).Section) (hs : s 1 = 1)
  {M : Type u} [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M] [Module.Finite k M]
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)

local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "F" => (R) ⋙ forget₂ (Rep k N) (ModuleCat k)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "W" => cliffordReconstructionFDRep A s hs U
local notation "resW" => Functor.obj
  (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))) W
local notation "C" => cliffordMultiplicitySemilinearAction A s hs W

attribute [local instance] endModule

private local instance : IsScalarTower k (End A) V := (F).endModule_isScalarTower A

variable [Simple A]

private def unitLinearEquiv : M ≃ₗ[k] (A ⟶ resW) :=
  (cliffordReconstructionUnitEquiv A s hs U).trans
    ((Rep.homLinearEquiv _ _).symm.trans (forget₂HomLinearEquiv A resW))

private theorem unitLinearEquiv_apply (m : M) (x : A) :
    (unitLinearEquiv A s hs U m).hom.hom.hom x =
      BalancedTensorProduct.tmul k (End A) (N := V) m x := by
  -- The forgetful Hom equivalences repackage the same underlying linear map.
  change cliffordReconstructionUnitEquiv A s hs U m x = _
  rw [cliffordReconstructionUnitEquiv_apply]
  -- The FDRep and forgotten Rep carriers agree, but rewriting needs full transparency.
  erw [balancedTensorUnit_apply]

private theorem unitLinearEquiv_smul (d : (End A)ᵐᵒᵖ) (m : M) :
    unitLinearEquiv A s hs U (d • m) = d • unitLinearEquiv A s hs U m := by
  obtain ⟨d, rfl⟩ := op_surjective d
  ext x
  -- The opposite endomorphism action is precomposition on FDRep morphisms.
  change (unitLinearEquiv A s hs U (op d • m)).hom.hom.hom x =
    (unitLinearEquiv A s hs U m).hom.hom.hom (d.asHom.hom.hom.hom x)
  rw [unitLinearEquiv_apply, unitLinearEquiv_apply]
  erw [BalancedTensorProduct.balance]
  erw [(F).endModule_smul]
  rfl

private theorem unitLinearEquiv_clifford (c : Carrier A) (m : M) :
    unitLinearEquiv A s hs U (cliffordReconstructionMultiplicityRepresentation A s hs U c m) =
      cliffordMultiplicityRepresentation A W c (unitLinearEquiv A s hs U m) := by
  refine QuotientGroup.induction_on c fun p => ?_
  ext x
  simp only [cliffordMultiplicityRepresentation_mk_apply, unitLinearEquiv_apply]
  erw [← projection_apply A p, cliffordReconstructionRepresentation_projection_tmul]
  rw [LinearEquiv.apply_symm_apply]

private theorem unitLinearEquiv_operator (q : Quotient A) (m : M) :
    unitLinearEquiv A s hs U (U.operator q m) = (C).operator q (unitLinearEquiv A s hs U m) := by
  simpa only [cliffordMultiplicitySemilinearAction_operator,
    cliffordReconstructionMultiplicityRepresentation_section] using
      unitLinearEquiv_clifford A s hs U (s q) m

/-- Reconstructing a finite-dimensional multiplicity module and taking multiplicities
recovers it linearly over the full opposite-commutant, inverse-factor crossed product. -/
def cliffordReconstructionUnitModuleEquiv :
    letI := U.module
    letI := (C).module
    M ≃ₗ[CrossedSystem.Algebra (cliffordCrossedSystem A s hs).opInv] (A ⟶ resW) := by
  letI := U.module
  letI := (C).module
  exact LinearEquiv.ofBijective
    (CrossedSystem.SemilinearAction.linearMap U (C) (unitLinearEquiv A s hs U).toLinearMap
      (unitLinearEquiv_smul A s hs U) (unitLinearEquiv_operator A s hs U))
    (by
      constructor
      · intro m m' h
        apply (unitLinearEquiv A s hs U).injective
        simpa only [CrossedSystem.SemilinearAction.linearMap_apply,
          LinearEquiv.coe_coe] using h
      · intro f
        obtain ⟨m, hm⟩ := (unitLinearEquiv A s hs U).surjective f
        exact ⟨m, by simpa only [CrossedSystem.SemilinearAction.linearMap_apply,
          LinearEquiv.coe_coe] using hm⟩)

/-- The crossed-product unit sends a multiplicity vector to its pure-tensor intertwiner. -/
@[simp]
theorem cliffordReconstructionUnitModuleEquiv_apply (m : M) (x : A) :
    (cliffordReconstructionUnitModuleEquiv A s hs U m).hom.hom.hom x =
      BalancedTensorProduct.tmul k (End A) (N := V) m x := by
  unfold cliffordReconstructionUnitModuleEquiv
  -- The equivalence retains the algebra-linear map's forward function.
  dsimp only [LinearEquiv.ofBijective, LinearEquiv.coe_mk]
  erw [CrossedSystem.SemilinearAction.linearMap_apply]
  exact unitLinearEquiv_apply A s hs U m x

/-- Tensoring with the recovered multiplicity vector evaluates the given intertwiner. -/
@[simp]
theorem cliffordReconstructionUnitModuleEquiv_symm_apply (f : A ⟶ resW) (x : A) :
    BalancedTensorProduct.tmul k (End A) (N := V)
        ((cliffordReconstructionUnitModuleEquiv A s hs U).symm f) x = f.hom.hom.hom x := by
  rw [← cliffordReconstructionUnitModuleEquiv_apply, LinearEquiv.apply_symm_apply]

end FDRep
