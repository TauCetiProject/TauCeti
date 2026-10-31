/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Multiplicity
public import TauCeti.RepresentationTheory.FDRep.BalancedEvaluation

/-!
# Equivariant reconstruction from Clifford multiplicities

The inertia group acts on `Hom_N(A,W) ⊗_{End_N(A)} A` by
`f ⊗ x ↦ (W(t) f U⁻¹) ⊗ U(x)`, where `U` implements conjugation by `t`.
Both factors are semilinear for the same automorphism of the full commutant,
so their tensor map is balanced. Changing `U` by an equivariant automorphism
has no effect on the balanced tensor. This constructs the action without
choosing a section of the inertia quotient.

Evaluation `f ⊗ x ↦ f(x)` intertwines this action with `W`. If the restriction
of `W` is semisimple and isotypic of type `A`, evaluation is an equivalence of
representations. No splitting-field or scalar-Schur assumption is needed.

The multiplicity operators are `FDRep.cliffordMultiplicityRepresentation`;
the underlying reconstruction is `FDRep.isotypicBalancedEvaluationEquiv`.
The inertia action descends along `TauCeti.CliffordExtension.projection` using
Mathlib's `MonoidHom.liftOfSurjective`.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension
open scoped MonoidAlgebra

universe u v

variable {k : Type u} {G : Type v} [Group G] {N : Subgroup G} [N.Normal]

section CommRing

variable [CommRing k] (A : FDRep k N) (W : FDRep k (inertia A))

local notation "res" => Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))
local notation "resW" => (Functor.obj (res) W : FDRep k N)
local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "F" => (R) ⋙ forget₂ (Rep k N) (ModuleCat k)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "M" => (A ⟶ resW)
local notation "E" => BalancedTensorProduct k (End A) M V

attribute [local instance] endModule

private noncomputable def implementerTensorMap (p : implementers A) : E →ₗ[k] E :=
  BalancedTensorProduct.lift
    (((BalancedTensorProduct.mk k (End A)).comp
      (cliffordMultiplicityRepresentation A W (QuotientGroup.mk p : Carrier A))).compl₂
        (p.1.2.toLinearMap : V →ₗ[k] V))
    (fun (d : End A) (f : M) (x : V) => by
      -- The quotient map is typed using its exposed quotient carrier; `erw` bridges that
      -- carrier to `Carrier A` while applying the named bilinear-map equations.
      erw [LinearMap.compl₂_apply, LinearMap.comp_apply, BalancedTensorProduct.mk_apply,
        LinearMap.compl₂_apply, LinearMap.comp_apply, BalancedTensorProduct.mk_apply]
      erw [cliffordMultiplicityRepresentation_smul, commutantAction_mk]
      rw [BalancedTensorProduct.balance]
      congr 1
      erw [(F).endModule_smul A, (F).endModule_smul A]
      exact (implementerConj_apply p d (p.1.2 x)).trans
        (congrArg (fun y : A => p.1.2 (d.asHom.hom.hom.hom y))
          (p.1.2.symm_apply_apply x)))

private theorem implementerTensorMap_tmul (p : implementers A) (f : M) (x : V) :
    implementerTensorMap A W p (BalancedTensorProduct.tmul k (End A) (N := V) f x) =
      BalancedTensorProduct.tmul k (End A) (N := V)
        (cliffordMultiplicityRepresentation A W (QuotientGroup.mk p : Carrier A) f) (p.1.2 x) := by
  simp only [implementerTensorMap, BalancedTensorProduct.lift_tmul]
  erw [LinearMap.compl₂_apply, LinearMap.comp_apply, BalancedTensorProduct.mk_apply]
  rfl

private noncomputable def implementerTensorRepresentation :
    Representation k (implementers A) E where
  toFun := implementerTensorMap A W
  map_one' := by
    apply BalancedTensorProduct.hom_ext
    intro f x
    rw [implementerTensorMap_tmul]
    erw [QuotientGroup.mk_one, map_one]
    rfl
  map_mul' p q := by
    apply BalancedTensorProduct.hom_ext
    intro f x
    erw [Module.End.mul_apply, implementerTensorMap_tmul, implementerTensorMap_tmul,
      implementerTensorMap_tmul, QuotientGroup.mk_mul, map_mul]
    rfl

private theorem implementerTensorRepresentation_kernelLift (d : (End A)ˣ) :
    implementerTensorRepresentation A W (kernelLift A d) = 1 := by
  apply BalancedTensorProduct.hom_ext
  intro f x
  erw [implementerTensorRepresentation, implementerTensorMap_tmul,
    cliffordMultiplicityRepresentation_mk_kernelLift, BalancedTensorProduct.balance]
  rw [Module.End.one_apply]
  erw [(F).endModule_smul A, kernelLift_snd_apply]
  exact congrArg (BalancedTensorProduct.tmul k (End A) (N := V) f)
    (congrArg (fun a : End A => a.asHom.hom.hom.hom x) d.inv_val)

end CommRing

section Field

variable [Field k] (A : FDRep k N) (W : FDRep k (inertia A))

local notation "res" => Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))
local notation "resW" => (Functor.obj (res) W : FDRep k N)
local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "F" => (R) ⋙ forget₂ (Rep k N) (ModuleCat k)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "M" => (A ⟶ resW)
local notation "E" => BalancedTensorProduct k (End A) M V

attribute [local instance] endModule

private theorem projection_ker_le_tensor_ker :
    (projection A).ker ≤ (implementerTensorRepresentation A W).toHomUnits.ker := by
  intro p hp
  obtain ⟨d, rfl⟩ := (range_kernelLift_eq_ker_projection A).symm ▸ hp
  apply Units.ext
  exact implementerTensorRepresentation_kernelLift A W d

/-- The inertia action on the balanced multiplicity tensor. It is independent of the
implementing operator, since inverse precomposition cancels its action on the vector factor. -/
noncomputable def cliffordTensorRepresentation : Representation k (inertia A) E :=
  (Units.coeHom _).comp ((projection A).liftOfSurjective (projection_surjective A)
    ⟨(implementerTensorRepresentation A W).toHomUnits, projection_ker_le_tensor_ker A W⟩)

/-- Any implementing operator computes the inertia action on pure tensors. -/
theorem cliffordTensorRepresentation_projection_tmul (p : implementers A) (f : M) (x : V) :
    cliffordTensorRepresentation A W (projection A p)
        (BalancedTensorProduct.tmul k (End A) (N := V) f x) =
      BalancedTensorProduct.tmul k (End A) (N := V)
        (cliffordMultiplicityRepresentation A W (QuotientGroup.mk p : Carrier A) f) (p.1.2 x) := by
  have h := MonoidHom.liftOfRightInverse_comp_apply (projection A)
    (Function.surjInv (projection_surjective A)) (Function.rightInverse_surjInv _)
    ⟨(implementerTensorRepresentation A W).toHomUnits, projection_ker_le_tensor_ker A W⟩ p
  exact (congrArg (fun a : (Module.End k E)ˣ => (a : Module.End k E)
    (BalancedTensorProduct.tmul k (End A) (N := V) f x)) h).trans
      (implementerTensorMap_tmul A W p f x)

/-- Postcomposition by an inertia intertwiner acts on the multiplicity factor of the
balanced tensor and commutes with the reconstructed inertia actions. -/
noncomputable def cliffordTensorMap {W' : FDRep k (inertia A)} (g : W ⟶ W') :
    Representation.IntertwiningMap (cliffordTensorRepresentation A W)
      (cliffordTensorRepresentation A W') where
  toLinearMap := BalancedTensorProduct.map
    (Linear.rightComp k A ((Action.res (FGModuleCat k)
      (Subgroup.inclusion (le_inertia A))).map g)) LinearMap.id
    (by intro d f; simp [End.smul_left]) (fun _ _ => rfl)
  isIntertwining' t := by
    obtain ⟨p, rfl⟩ := projection_surjective A t
    apply BalancedTensorProduct.hom_ext
    intro f x
    erw [LinearMap.comp_apply, cliffordTensorRepresentation_projection_tmul,
      BalancedTensorProduct.map_tmul, LinearMap.comp_apply, BalancedTensorProduct.map_tmul,
      cliffordTensorRepresentation_projection_tmul]
    exact congrArg (fun h => BalancedTensorProduct.tmul k (End A) (N := V) h (p.1.2 x))
      (cliffordMultiplicityRepresentation_naturality A W g (QuotientGroup.mk p) f)

/-- The tensor map postcomposes the multiplicity and leaves the vector unchanged. -/
@[simp]
theorem cliffordTensorMap_tmul {W' : FDRep k (inertia A)} (g : W ⟶ W') (f : M) (x : V) :
    cliffordTensorMap A W g (BalancedTensorProduct.tmul k (End A) (N := V) f x) =
      BalancedTensorProduct.tmul k (End A) (N := V)
        (f ≫ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).map g) x := by
  exact BalancedTensorProduct.map_tmul _ _ _ _ f x

/-- Identity intertwiners induce the identity on reconstructed tensors. -/
@[simp]
theorem cliffordTensorMap_id :
    cliffordTensorMap A W (𝟙 W) =
      Representation.IntertwiningMap.id (cliffordTensorRepresentation A W) := by
  apply Representation.IntertwiningMap.ext
  apply BalancedTensorProduct.hom_ext
  intro f x
  erw [Representation.IntertwiningMap.coe_toLinearMap, cliffordTensorMap_tmul]
  simp

/-- Postcomposition on reconstructed tensors respects composition of intertwiners. -/
theorem cliffordTensorMap_comp {W' W'' : FDRep k (inertia A)} (g : W ⟶ W') (h : W' ⟶ W'') :
    cliffordTensorMap A W (g ≫ h) =
      (cliffordTensorMap A W' h).comp (cliffordTensorMap A W g) := by
  apply Representation.IntertwiningMap.ext
  apply BalancedTensorProduct.hom_ext
  intro f x
  erw [Representation.IntertwiningMap.comp_apply, cliffordTensorMap_tmul,
    cliffordTensorMap_tmul, cliffordTensorMap_tmul]
  simp only [Functor.map_comp, Category.assoc]

/-- Evaluation from the balanced multiplicity tensor to the original inertia representation
is equivariant. -/
noncomputable def cliffordBalancedEvaluation :
    Representation.IntertwiningMap (cliffordTensorRepresentation A W) W.ρ where
  toLinearMap := (F).balancedEvaluation A resW
  isIntertwining' t := by
    obtain ⟨p, rfl⟩ := projection_surjective A t
    apply BalancedTensorProduct.hom_ext
    intro f x
    have heval (g : M) (y : A) :
        ((F).balancedEvaluation A resW : E →ₗ[k] W)
          (BalancedTensorProduct.tmul k (End A) (N := V) g y) = g.hom.hom.hom y :=
      (F).balancedEvaluation_tmul A resW g y
    have h₁ := (congrArg ((F).balancedEvaluation A resW : E →ₗ[k] W)
      (cliffordTensorRepresentation_projection_tmul A W p f x)).trans (heval _ _)
    have h₂ :
        ((cliffordMultiplicityRepresentation A W (QuotientGroup.mk p : Carrier A) f).hom.hom.hom
          (p.1.2 x) : W) = W.ρ (projection A p) (f.hom.hom.hom x) := by
      rw [cliffordMultiplicityRepresentation_mk_apply, projection_apply]
      exact congrArg (fun y : A => W.ρ p.1.1 (f.hom.hom.hom y))
        (p.1.2.symm_apply_apply x)
    exact (LinearMap.comp_apply _ _ _).trans (h₁.trans (h₂.trans
      ((congrArg (W.ρ (projection A p)) (heval f x).symm).trans
        (LinearMap.comp_apply _ _ _).symm)))

/-- Balanced evaluation sends `f ⊗ x` to `f(x)`. -/
@[simp]
theorem cliffordBalancedEvaluation_tmul (f : M) (x : V) :
    cliffordBalancedEvaluation A W (BalancedTensorProduct.tmul k (End A) (N := V) f x) =
      f.hom.hom.hom x := by
  exact (F).balancedEvaluation_tmul A resW f x

/-- Evaluation is natural in the inertia representation: postcomposition of multiplicities
corresponds to the original intertwiner on vectors. -/
theorem cliffordBalancedEvaluation_naturality {W' : FDRep k (inertia A)}
    (g : W ⟶ W') (z : E) :
    cliffordBalancedEvaluation A W' (cliffordTensorMap A W g z) =
      g.hom.hom.hom (cliffordBalancedEvaluation A W z) := by
  exact (F).balancedEvaluation_naturality ((res).map g) z

/-- A semisimple isotypic restriction is reconstructed equivariantly from its multiplicities
and the given normal-subgroup representation, balanced over the full commutant. -/
noncomputable def cliffordBalancedEvaluationEquiv
    [IsSemisimpleModule k[N] (Representation.asModule (resW).ρ)]
    (h : IsIsotypicOfType k[N] (Representation.asModule (resW).ρ)
      (Representation.asModule A.ρ)) :
    Representation.Equiv (cliffordTensorRepresentation A W) W.ρ :=
  (cliffordBalancedEvaluation A W).ofBijective (A.balancedEvaluation_bijective resW h)

/-- On any balanced tensor, the reconstruction equivalence is the evaluation intertwiner. -/
theorem cliffordBalancedEvaluationEquiv_apply
    [IsSemisimpleModule k[N] (Representation.asModule (resW).ρ)]
    (h : IsIsotypicOfType k[N] (Representation.asModule (resW).ρ)
      (Representation.asModule A.ρ)) (z : E) :
    cliffordBalancedEvaluationEquiv A W h z = cliffordBalancedEvaluation A W z := by
  exact congrFun (Representation.IntertwiningMap.coe_ofBijective _ _ _ _) z

/-- The reconstruction equivalence is evaluation on pure tensors. -/
@[simp]
theorem cliffordBalancedEvaluationEquiv_tmul
    [IsSemisimpleModule k[N] (Representation.asModule (resW).ρ)]
    (h : IsIsotypicOfType k[N] (Representation.asModule (resW).ρ)
      (Representation.asModule A.ρ)) (f : M) (x : V) :
    cliffordBalancedEvaluationEquiv A W h (BalancedTensorProduct.tmul k (End A) (N := V) f x) =
      f.hom.hom.hom x := by
  rw [cliffordBalancedEvaluationEquiv_apply, cliffordBalancedEvaluation_tmul]

/-- The inverse reconstruction is the inverse of the underlying isotypic evaluation. -/
private theorem cliffordBalancedEvaluationEquiv_symm_apply_eq
    [IsSemisimpleModule k[N] (Representation.asModule (resW).ρ)]
    (h : IsIsotypicOfType k[N] (Representation.asModule (resW).ρ)
      (Representation.asModule A.ρ)) (y : W) :
    (cliffordBalancedEvaluationEquiv A W h).symm y =
      (A.isotypicBalancedEvaluationEquiv resW h).symm y := by
  apply (cliffordBalancedEvaluationEquiv A W h).injective
  simp only [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.coe_toIntertwiningMap]
  rw [Representation.Equiv.apply_symm_apply, cliffordBalancedEvaluationEquiv_apply]
  exact ((A.isotypicBalancedEvaluationEquiv_apply resW h _).symm.trans
    (LinearEquiv.apply_symm_apply _ y)).symm

/-- The inverse reconstruction takes a multiplicity's value back to its pure tensor. -/
@[simp]
theorem cliffordBalancedEvaluationEquiv_symm_apply_map
    [IsSemisimpleModule k[N] (Representation.asModule (resW).ρ)]
    (h : IsIsotypicOfType k[N] (Representation.asModule (resW).ρ)
      (Representation.asModule A.ρ)) (f : M) (x : V) :
    (cliffordBalancedEvaluationEquiv A W h).symm (f.hom.hom.hom x) =
      BalancedTensorProduct.tmul k (End A) (N := V) f x :=
  (cliffordBalancedEvaluationEquiv_symm_apply_eq A W h _).trans
    (A.isotypicBalancedEvaluationEquiv_symm_apply_map resW h f x)

/-- The inverse reconstruction is natural under inertia intertwiners. -/
theorem cliffordBalancedEvaluationEquiv_symm_naturality {W' : FDRep k (inertia A)}
    [IsSemisimpleModule k[N] (Representation.asModule (resW).ρ)]
    [IsSemisimpleModule k[N] (Representation.asModule (FDRep.ρ ((res).obj W')))]
    (h : IsIsotypicOfType k[N] (Representation.asModule (resW).ρ)
      (Representation.asModule A.ρ))
    (h' : IsIsotypicOfType k[N] (Representation.asModule (FDRep.ρ ((res).obj W')))
      (Representation.asModule A.ρ)) (g : W ⟶ W') (y : W) :
    cliffordTensorMap A W g ((cliffordBalancedEvaluationEquiv A W h).symm y) =
      (cliffordBalancedEvaluationEquiv A W' h').symm (g.hom.hom.hom y) :=
  (congrArg (cliffordTensorMap A W g) (cliffordBalancedEvaluationEquiv_symm_apply_eq A W h y)).trans
    ((A.isotypicBalancedEvaluationEquiv_symm_naturality resW ((res).obj W') h h' ((res).map g)
      y).trans (cliffordBalancedEvaluationEquiv_symm_apply_eq A W' h' _).symm)

end Field

end FDRep
