/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Module
public import TauCeti.RepresentationTheory.FDRep.Balanced.Evaluation
public import TauCeti.GroupTheory.GroupExtension.Lift
public import TauCeti.Algebra.Module.Opposite

/-!
# Reconstruction from arbitrary Clifford multiplicity modules

The semilinear operators of an opposite-coefficient, inverse-factor Clifford crossed-product
module extend to an action of the canonical Clifford extension. Its kernel acts by inverse
right multiplication. Tensoring with the original normal-subgroup representation cancels
this kernel action and gives an ordinary representation of the inertia group.

The multiplicity module need not already arise as an intertwiner space. This constructs the
representation needed to recover inertia representations from crossed-product modules, over
arbitrary fields and without semisimplicity or a finite inertia quotient. Ordinary modules
supply these operators through `CrossedSystem.SemilinearAction.ofAlgHom`; conversely
`CrossedSystem.SemilinearAction.module` gives their ordinary crossed-product module structure.

The balanced descent also supplies the existing multiplicity-space specialization
`FDRep.cliffordTensorRepresentation`, so evaluation and arbitrary-module reconstruction
use the same tensor action.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s : (groupExtension A).Section) (hs : s 1 = 1)
  {M : Type w} [AddCommMonoid M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M]
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)

private theorem reconstruction_conj (q : Quotient A) (d : (End A)ˣ) :
    U.operator q * inverseRightAction k (End A) M d =
      inverseRightAction k (End A) M ((groupExtension A).conjAct (s q) d) * U.operator q := by
  ext m
  simp only [mul_apply_eq_comp, inverseRightAction_apply, U.operator_smul,
    CrossedSystem.opInv_action, cliffordCrossedSystem_action]
  congr 1
  exact congrArg (fun a : (End A)ˣ => op (a : End A))
    ((commutantAction_units (s q) d⁻¹).trans (map_inv _ _))

private theorem reconstruction_mul (q r : Quotient A) :
    U.operator q * U.operator r =
      inverseRightAction k (End A) M (GroupExtension.factorSetFun s (q, r)) *
        U.operator (q * r) := by
  ext m
  simpa only [mul_apply_eq_comp, inverseRightAction_apply, CrossedSystem.opInv_factor,
    cliffordCrossedSystem_factor] using U.operator_mul q r m

/-- The operators of an arbitrary Clifford multiplicity module extend to the canonical
Clifford extension, whose kernel acts by inverse right multiplication. -/
noncomputable def cliffordReconstructionMultiplicityRepresentation :
    Representation k (Carrier A) M :=
  s.lift hs (inverseRightAction k (End A) M) U.operator U.operator_one
    (reconstruction_conj A s hs U) (reconstruction_mul A s hs U)

/-- On the chosen section the extended representation is the given semilinear operator. -/
@[simp]
theorem cliffordReconstructionMultiplicityRepresentation_section (q : Quotient A) :
    cliffordReconstructionMultiplicityRepresentation A s hs U (s q) = U.operator q := by
  simp [cliffordReconstructionMultiplicityRepresentation]

/-- A kernel unit acts by its inverse on the right of the multiplicity module. -/
@[simp↓]
theorem cliffordReconstructionMultiplicityRepresentation_inl (d : (End A)ˣ) (m : M) :
    cliffordReconstructionMultiplicityRepresentation A s hs U (inl A d) m =
      op (↑d⁻¹ : End A) • m := by
  simpa only [cliffordReconstructionMultiplicityRepresentation, groupExtension_inl,
    inverseRightAction_apply] using congrArg (fun f : Module.End k M => f m)
      (s.lift_inl hs (inverseRightAction k (End A) M) U.operator U.operator_one
        (reconstruction_conj A s hs U) (reconstruction_mul A s hs U) d)

/-- The extension action is semilinear for its full commutant action, not merely for the
operators of the chosen section. -/
theorem cliffordReconstructionMultiplicityRepresentation_smul (c : Carrier A) (d : End A)
    (m : M) :
    cliffordReconstructionMultiplicityRepresentation A s hs U c (op d • m) =
      op (commutantAction c d) • cliffordReconstructionMultiplicityRepresentation A s hs U c m := by
  obtain ⟨a, ha⟩ := s.exists_eq_inl_mul_section c
  have hi (b : End A) : commutantAction (inl A a) b =
      (a : End A) * b * (↑a⁻¹ : End A) := by simp
  rw [ha, groupExtension_inl]
  simp only [map_mul, mul_apply_eq_comp,
    cliffordReconstructionMultiplicityRepresentation_section, U.operator_smul,
    cliffordReconstructionMultiplicityRepresentation_inl, CrossedSystem.opInv_action,
    cliffordCrossedSystem_action, AlgEquiv.mul_apply, hi]
  simp only [← mul_smul, ← op_mul]
  congr 1
  apply op_injective
  simp [mul_assoc]

end FDRep

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  {M : Type w} [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  (ρ : Representation k (Carrier A) M)
  (hsmul : ∀ (c : Carrier A) (d : End A) (m : M),
    ρ c (op d • m) = op (commutantAction c d) • ρ c m)
  (hinl : ∀ (d : (End A)ˣ) (m : M), ρ (inl A d) m = op (↑d⁻¹ : End A) • m)

local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "F" => (R) ⋙ forget₂ (Rep k N) (ModuleCat k)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "E" => BalancedTensorProduct k (End A) M V

attribute [local instance] endModule

private noncomputable def reconstructionTensorMap (p : implementers A) : E →ₗ[k] E :=
  BalancedTensorProduct.lift
    (((BalancedTensorProduct.mk k (End A)).comp (ρ (QuotientGroup.mk p : Carrier A))).compl₂
      (p.1.2.toLinearMap : V →ₗ[k] V))
    (fun (d : End A) (m : M) (x : V) => by
      -- The balanced tensor uses the forgotten representation carrier, while implementers
      -- act on the original FDRep carrier. `erw` applies the named equations across this view.
      erw [LinearMap.compl₂_apply, LinearMap.comp_apply, BalancedTensorProduct.mk_apply,
        LinearMap.compl₂_apply, LinearMap.comp_apply, BalancedTensorProduct.mk_apply,
        hsmul, commutantAction_mk, BalancedTensorProduct.balance,
        (F).endModule_smul A, (F).endModule_smul A]
      congr 1
      exact (implementerConj_apply p d (p.1.2 x)).trans
        (congrArg (fun y : A => p.1.2 (d.asHom.hom.hom.hom y))
          (p.1.2.symm_apply_apply x)))

private theorem reconstructionTensorMap_tmul (p : implementers A) (m : M) (x : V) :
    reconstructionTensorMap A ρ hsmul p (BalancedTensorProduct.tmul k (End A) (N := V) m x) =
      BalancedTensorProduct.tmul k (End A) (N := V) (ρ (QuotientGroup.mk p : Carrier A) m)
        (p.1.2 x) := by
  simp only [reconstructionTensorMap, BalancedTensorProduct.lift_tmul]
  erw [LinearMap.compl₂_apply, LinearMap.comp_apply, BalancedTensorProduct.mk_apply]
  rfl

private noncomputable def reconstructionTensorRepresentation :
    Representation k (implementers A) E where
  toFun := reconstructionTensorMap A ρ hsmul
  map_one' := by
    apply BalancedTensorProduct.hom_ext
    intro m x
    rw [reconstructionTensorMap_tmul]
    erw [QuotientGroup.mk_one, map_one]
    rfl
  map_mul' p q := by
    apply BalancedTensorProduct.hom_ext
    intro m x
    erw [mul_apply_eq_comp, reconstructionTensorMap_tmul, reconstructionTensorMap_tmul,
      reconstructionTensorMap_tmul, QuotientGroup.mk_mul, map_mul]
    rfl

include hinl in
private theorem reconstructionTensorRepresentation_kernelLift (d : (End A)ˣ) :
    reconstructionTensorRepresentation A ρ hsmul (kernelLift A d) = 1 := by
  apply BalancedTensorProduct.hom_ext
  intro m x
  erw [reconstructionTensorRepresentation, reconstructionTensorMap_tmul A ρ hsmul, ← inl_apply,
    hinl, BalancedTensorProduct.balance, (F).endModule_smul A, kernelLift_snd_apply]
  rw [one_apply_eq_self]
  exact congrArg (BalancedTensorProduct.tmul k (End A) (N := V) m)
    (congrArg (fun a : End A => a.asHom.hom.hom.hom x) d.inv_val)

include hinl in
private theorem reconstruction_projection_ker_le :
    (projection A).ker ≤ (reconstructionTensorRepresentation A ρ hsmul).toHomUnits.ker := by
  intro p hp
  obtain ⟨d, rfl⟩ := (range_kernelLift_eq_ker_projection A).symm ▸ hp
  apply Units.ext
  exact reconstructionTensorRepresentation_kernelLift A ρ hsmul hinl d

/-- Tensor a semilinear Clifford-extension representation with the original module.
Inverse right multiplication on the kernel cancels its left action on the vector factor,
so the tensor action descends to the inertia group. -/
noncomputable def cliffordBalancedTensorRepresentation : Representation k (inertia A) E :=
  (Units.coeHom _).comp ((projection A).liftOfSurjective (projection_surjective A)
    ⟨(reconstructionTensorRepresentation A ρ hsmul).toHomUnits,
      reconstruction_projection_ker_le A ρ hsmul hinl⟩)

/-- Any implementer computes the descended balanced tensor action. -/
@[simp↓]
theorem cliffordBalancedTensorRepresentation_projection_tmul (p : implementers A) (m : M) (x : V) :
    cliffordBalancedTensorRepresentation A ρ hsmul hinl (projection A p)
        (BalancedTensorProduct.tmul k (End A) (N := V) m x) =
      BalancedTensorProduct.tmul k (End A) (N := V) (ρ (QuotientGroup.mk p : Carrier A) m)
        (p.1.2 x) := by
  have h := MonoidHom.liftOfRightInverse_comp_apply (projection A)
    (Function.surjInv (projection_surjective A)) (Function.rightInverse_surjInv _)
    ⟨(reconstructionTensorRepresentation A ρ hsmul).toHomUnits,
      reconstruction_projection_ker_le A ρ hsmul hinl⟩ p
  exact (congrArg (fun a : (Module.End k E)ˣ => (a : Module.End k E)
    (BalancedTensorProduct.tmul k (End A) (N := V) m x)) h).trans
      (reconstructionTensorMap_tmul A ρ hsmul p m x)

variable [IsScalarTower k (End A)ᵐᵒᵖ M]
  (s : (groupExtension A).Section) (hs : s 1 = 1)
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)

/-- Reconstruct an inertia representation from an arbitrary opposite/inverse crossed-product
module, presented by its semilinear operators, on its balanced tensor with `A`. -/
noncomputable def cliffordReconstructionRepresentation : Representation k (inertia A) E :=
  cliffordBalancedTensorRepresentation A
    (cliffordReconstructionMultiplicityRepresentation A s hs U)
    (cliffordReconstructionMultiplicityRepresentation_smul A s hs U)
    (cliffordReconstructionMultiplicityRepresentation_inl A s hs U)

/-- The reconstructed action is the tensor of the extended multiplicity operator and the
implementing operator; it needs no realization of the multiplicity module as a Hom space. -/
@[simp↓]
theorem cliffordReconstructionRepresentation_projection_tmul
    (p : implementers A) (m : M) (x : V) :
    cliffordReconstructionRepresentation A s hs U (projection A p)
        (BalancedTensorProduct.tmul k (End A) (N := V) m x) =
      BalancedTensorProduct.tmul k (End A) (N := V)
        (cliffordReconstructionMultiplicityRepresentation A s hs U
          (QuotientGroup.mk p : Carrier A) m) (p.1.2 x) :=
  cliffordBalancedTensorRepresentation_projection_tmul A _ _ _ p m x

/-- On the normal subgroup the reconstructed action fixes the multiplicity factor and
acts by the original representation on the vector factor. -/
@[simp]
theorem cliffordReconstructionRepresentation_inclusion_tmul (n : N) (m : M) (x : V) :
    cliffordReconstructionRepresentation A s hs U (Subgroup.inclusion (le_inertia A) n)
        (BalancedTensorProduct.tmul k (End A) (N := V) m x) =
      BalancedTensorProduct.tmul k (End A) (N := V) m (A.ρ n x) := by
  have hn : (QuotientGroup.mk (diagonal A n) : Carrier A) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨n, rfl⟩
  have h := cliffordReconstructionRepresentation_projection_tmul A s hs U (diagonal A n) m x
  -- The diagonal's vector operator uses the original FDRep carrier, while the tensor
  -- uses its forgotten Rep carrier; `erw` bridges these views in the characteristic equation.
  erw [projection_apply, diagonal_fst, hn, map_one, one_apply_eq_self, diagonal_snd_apply] at h
  exact h

end FDRep
