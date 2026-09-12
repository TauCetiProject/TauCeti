/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Tensor
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# The Hopf algebra descended from a Galois lattice

Let `L/k` be a finite Galois extension and let `M` be an abelian group with an action of
`Gal(L/k)`. The simultaneous action on the coefficients and exponents of `L[M]` preserves its
Hopf operations. Galois descent identifies the invariant tensors with the tensor square of the
invariant algebra, so these operations give the invariant algebra a Hopf algebra structure over
`k`.

The resulting structure is the coordinate Hopf algebra in the inverse construction from an
integral Galois lattice to a group of multiplicative type. It is defined without a finite-
generation hypothesis on `M`; finite generation is needed only when packaging it as a finite-type
affine group scheme.

## Main declarations

* `TauCeti.GaloisDescent.groupAlgebraInvariantsComulDescended`: comultiplication on the invariant
  algebra.
* `TauCeti.GaloisDescent.groupAlgebraInvariantsHopfAlgebra`: the descended Hopf algebra structure.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct TauCeti.GaloisDescent

namespace TauCeti.GaloisDescent

variable {k L M : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M]
variable [FiniteDimensional k L] [IsGalois k L]

/-- The comultiplication on the descended invariant group algebra. -/
noncomputable def groupAlgebraInvariantsComulDescended
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho →ₐ[k]
      groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho :=
  (groupAlgebraInvariantsTensorEquiv rho).symm.toAlgHom.comp
    (groupAlgebraInvariantsComul rho)

/-- Under the tensor descent equivalence, descended comultiplication is the ordinary
group-algebra comultiplication. -/
@[simp]
theorem groupAlgebraInvariantsTensorEquiv_comulDescended
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (x : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsTensorEquiv rho
        (groupAlgebraInvariantsComulDescended rho x) :
      MonoidAlgebra L (Multiplicative M) ⊗[L] MonoidAlgebra L (Multiplicative M)) =
      Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)) := by
  rw [groupAlgebraInvariantsComulDescended, AlgHom.comp_apply]
  calc
    _ = (groupAlgebraInvariantsComul rho x :
          MonoidAlgebra L (Multiplicative M) ⊗[L]
            MonoidAlgebra L (Multiplicative M)) :=
      congrArg Subtype.val ((groupAlgebraInvariantsTensorEquiv rho).apply_symm_apply
        (groupAlgebraInvariantsComul rho x))
    _ = _ := groupAlgebraInvariantsComul_apply rho x

private noncomputable def tensorMap
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho →ₐ[k]
      MonoidAlgebra L (Multiplicative M) ⊗[L] MonoidAlgebra L (Multiplicative M) :=
  (groupAlgebraTensorInvariants rho).val.comp
    (groupAlgebraInvariantsTensorEquiv rho).toAlgHom

@[simp]
private theorem tensorMap_tmul (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x y : groupAlgebraInvariants rho) :
    tensorMap rho (x ⊗ₜ[k] y) =
      (x : MonoidAlgebra L (Multiplicative M)) ⊗ₜ[L]
        (y : MonoidAlgebra L (Multiplicative M)) :=
  groupAlgebraInvariantsTensorEquiv_tmul rho x y

@[simp]
private theorem tensorMap_comulDescended
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (x : groupAlgebraInvariants rho) :
    tensorMap rho (groupAlgebraInvariantsComulDescended rho x) =
      Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)) :=
  groupAlgebraInvariantsTensorEquiv_comulDescended rho x

private noncomputable def tripleMap
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) ⊗[k]
        groupAlgebraInvariants rho →ₐ[k]
      (MonoidAlgebra L (Multiplicative M) ⊗[L]
          MonoidAlgebra L (Multiplicative M)) ⊗[L]
        MonoidAlgebra L (Multiplicative M) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft (R := L) (S := L)).restrictScalars k).comp
      (tensorMap rho))
    (((Algebra.TensorProduct.includeRight (R := L)).restrictScalars k).comp
      (groupAlgebraInvariants rho).val)
    (fun x y ↦ by
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Subalgebra.val_apply]
      exact (Commute.one_right (tensorMap rho x)).tmul
        (Commute.one_left (y : MonoidAlgebra L (Multiplicative M))))

@[simp]
private theorem tripleMap_tmul (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho)
    (x : groupAlgebraInvariants rho) :
    tripleMap rho (t ⊗ₜ[k] x) = tensorMap rho t ⊗ₜ[L]
      (x : MonoidAlgebra L (Multiplicative M)) := by
  rw [tripleMap, Algebra.TensorProduct.lift_tmul]
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

private noncomputable def tensorBaseChangeEquiv
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    L ⊗[k] (groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) ≃ₐ[L]
      MonoidAlgebra L (Multiplicative M) ⊗[L] MonoidAlgebra L (Multiplicative M) :=
  (Algebra.TensorProduct.baseChangeTensorAlgEquiv k L
      (groupAlgebraInvariants rho) (groupAlgebraInvariants rho)).trans
    (Algebra.TensorProduct.congr (groupAlgebraInvariantsBaseChangeEquiv rho)
      (groupAlgebraInvariantsBaseChangeEquiv rho))

private theorem liftEquiv_tripleMap_bijective
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Function.Bijective (AlgHom.liftEquiv k L _ _ (tripleMap rho)) := by
  let e := (Algebra.TensorProduct.baseChangeTensorAlgEquiv k L
    (groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho)
    (groupAlgebraInvariants rho)).trans
      (Algebra.TensorProduct.congr (tensorBaseChangeEquiv rho)
        (groupAlgebraInvariantsBaseChangeEquiv rho))
  have he : AlgHom.liftEquiv k L _ _ (tripleMap rho) = e.toAlgHom := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro a t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul x₁ x₂ => simp [e, tensorBaseChangeEquiv, TensorProduct.smul_tmul']
        | add x₁ x₂ hx₁ hx₂ =>
            simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx₁, hx₂]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  rw [he]
  exact e.bijective

private theorem tripleMap_injective
    (rho : Representation ℤ (L ≃ₐ[k] L) M) : Function.Injective (tripleMap rho) := by
  intro x y h
  apply Algebra.TensorProduct.includeRight_injective (A := L)
    (FaithfulSMul.algebraMap_injective k L)
  apply (liftEquiv_tripleMap_bijective rho).injective
  simpa only [Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul]
    using h

private theorem tripleMap_map_comul_left
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    tripleMap rho
        (Algebra.TensorProduct.map (groupAlgebraInvariantsComulDescended rho)
          (AlgHom.id k (groupAlgebraInvariants rho)) t) =
      Algebra.TensorProduct.map
        (Bialgebra.comulAlgHom L (MonoidAlgebra L (Multiplicative M)))
        (AlgHom.id L (MonoidAlgebra L (Multiplicative M))) (tensorMap rho t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, tripleMap_tmul, AlgHom.id_apply,
        tensorMap_tmul, tensorMap_comulDescended, Bialgebra.comulAlgHom_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem tripleMap_assoc_symm_tmul
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (x : groupAlgebraInvariants rho)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    tripleMap rho
        ((Algebra.TensorProduct.assoc k k k _ _ _).symm (x ⊗ₜ[k] t)) =
      (Algebra.TensorProduct.assoc L L L _ _ _).symm
        ((x : MonoidAlgebra L (Multiplicative M)) ⊗ₜ[L] tensorMap rho t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul y z =>
      simp only [Algebra.TensorProduct.assoc_symm_tmul, tripleMap_tmul, tensorMap_tmul]
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]

private theorem tripleMap_assoc_symm_map_comul_right
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    tripleMap rho
        ((Algebra.TensorProduct.assoc k k k _ _ _).symm
          (Algebra.TensorProduct.map (AlgHom.id k (groupAlgebraInvariants rho))
            (groupAlgebraInvariantsComulDescended rho) t)) =
      (Algebra.TensorProduct.assoc L L L _ _ _).symm
        (Algebra.TensorProduct.map (AlgHom.id L (MonoidAlgebra L (Multiplicative M)))
          (Bialgebra.comulAlgHom L (MonoidAlgebra L (Multiplicative M)))
          (tensorMap rho t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        tripleMap_assoc_symm_tmul, tensorMap_tmul, tensorMap_comulDescended,
        Bialgebra.comulAlgHom_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem groupAlgebraInvariantsComul_coassoc
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (Algebra.TensorProduct.assoc k k k _ _ _).toAlgHom.comp
        ((Algebra.TensorProduct.map (groupAlgebraInvariantsComulDescended rho)
          (AlgHom.id k (groupAlgebraInvariants rho))).comp
            (groupAlgebraInvariantsComulDescended rho)) =
      (Algebra.TensorProduct.map (AlgHom.id k (groupAlgebraInvariants rho))
        (groupAlgebraInvariantsComulDescended rho)).comp
          (groupAlgebraInvariantsComulDescended rho) := by
  ext x
  apply (Algebra.TensorProduct.assoc k k k _ _ _).symm.injective
  apply tripleMap_injective rho
  simp only [AlgHom.comp_apply]
  -- The structure axiom uses the algebra-map coercion of the associator, so state the
  -- cancellation explicitly before comparing both sides in the split triple tensor product.
  rw [show (Algebra.TensorProduct.assoc k k k _ _ _).symm
      ((Algebra.TensorProduct.assoc k k k _ _ _).toAlgHom
        (Algebra.TensorProduct.map (groupAlgebraInvariantsComulDescended rho)
          (AlgHom.id k (groupAlgebraInvariants rho))
            (groupAlgebraInvariantsComulDescended rho x))) = _ from
      (Algebra.TensorProduct.assoc k k k _ _ _).symm_apply_apply _]
  rw [tripleMap_map_comul_left,
    tripleMap_assoc_symm_map_comul_right, tensorMap_comulDescended]
  exact (Coalgebra.coassoc_symm_apply (R := L)
    (x : MonoidAlgebra L (Multiplicative M))).symm

private theorem coe_lid_map_counit
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    ((Algebra.TensorProduct.lid k (groupAlgebraInvariants rho)
        (Algebra.TensorProduct.map (groupAlgebraInvariantsCounit rho)
          (AlgHom.id k (groupAlgebraInvariants rho)) t) :
      groupAlgebraInvariants rho) : MonoidAlgebra L (Multiplicative M)) =
      Algebra.TensorProduct.lid L (MonoidAlgebra L (Multiplicative M))
        (Algebra.TensorProduct.map
          (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative M)))
          (AlgHom.id L (MonoidAlgebra L (Multiplicative M))) (tensorMap rho t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.lid_tmul, tensorMap_tmul,
        Bialgebra.counitAlgHom_apply]
      rw [← algebraMap_groupAlgebraInvariantsCounit rho x]
      simp only [IsScalarTower.algebraMap_smul]
      rfl
  | add x y hx hy =>
      simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (· + ·) hx hy

private theorem coe_rid_map_counit
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    ((Algebra.TensorProduct.rid k k (groupAlgebraInvariants rho)
        (Algebra.TensorProduct.map (AlgHom.id k (groupAlgebraInvariants rho))
          (groupAlgebraInvariantsCounit rho) t) :
      groupAlgebraInvariants rho) : MonoidAlgebra L (Multiplicative M)) =
      Algebra.TensorProduct.rid L L (MonoidAlgebra L (Multiplicative M))
        (Algebra.TensorProduct.map (AlgHom.id L (MonoidAlgebra L (Multiplicative M)))
          (Bialgebra.counitAlgHom L (MonoidAlgebra L (Multiplicative M)))
          (tensorMap rho t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.rid_tmul, tensorMap_tmul,
        Bialgebra.counitAlgHom_apply]
      rw [← algebraMap_groupAlgebraInvariantsCounit rho y]
      simp only [IsScalarTower.algebraMap_smul]
      rfl
  | add x y hx hy =>
      simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (· + ·) hx hy

private theorem groupAlgebraInvariantsComul_rTensor_counit
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (Algebra.TensorProduct.map (groupAlgebraInvariantsCounit rho)
        (AlgHom.id k (groupAlgebraInvariants rho))).comp
          (groupAlgebraInvariantsComulDescended rho) =
      (Algebra.TensorProduct.lid k (groupAlgebraInvariants rho)).symm := by
  ext x
  apply (Algebra.TensorProduct.lid k (groupAlgebraInvariants rho)).eq_symm_apply.mpr
  apply Subtype.ext
  rw [AlgHom.comp_apply, coe_lid_map_counit, tensorMap_comulDescended]
  -- `Bialgebra.ofAlgHom` is stated with algebra maps, whereas Mathlib's counit law is stated
  -- with the underlying linear tensor map.
  change Algebra.TensorProduct.lid L (MonoidAlgebra L (Multiplicative M))
      ((Coalgebra.counit (R := L)).rTensor (MonoidAlgebra L (Multiplicative M))
        (Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)))) = _
  rw [Coalgebra.rTensor_counit_comul, Algebra.TensorProduct.lid_tmul, one_smul]

private theorem groupAlgebraInvariantsComul_lTensor_counit
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (Algebra.TensorProduct.map (AlgHom.id k (groupAlgebraInvariants rho))
        (groupAlgebraInvariantsCounit rho)).comp
          (groupAlgebraInvariantsComulDescended rho) =
      (Algebra.TensorProduct.rid k k (groupAlgebraInvariants rho)).symm := by
  ext x
  apply (Algebra.TensorProduct.rid k k (groupAlgebraInvariants rho)).eq_symm_apply.mpr
  apply Subtype.ext
  rw [AlgHom.comp_apply, coe_rid_map_counit, tensorMap_comulDescended]
  -- Cross from the algebra-map tensor expression to the linear form of the counit law.
  change Algebra.TensorProduct.rid L L (MonoidAlgebra L (Multiplicative M))
      ((Coalgebra.counit (R := L)).lTensor (MonoidAlgebra L (Multiplicative M))
        (Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)))) = _
  rw [Coalgebra.lTensor_counit_comul, Algebra.TensorProduct.rid_tmul, one_smul]

@[instance_reducible]
private noncomputable def groupAlgebraInvariantsBialgebra
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Bialgebra k (groupAlgebraInvariants rho) :=
  Bialgebra.ofAlgHom (groupAlgebraInvariantsComulDescended rho)
    (groupAlgebraInvariantsCounit rho) (groupAlgebraInvariantsComul_coassoc rho)
    (groupAlgebraInvariantsComul_rTensor_counit rho)
    (groupAlgebraInvariantsComul_lTensor_counit rho)

private theorem coe_lift_antipode_left
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    ((Algebra.TensorProduct.lift (groupAlgebraInvariantsAntipode rho).toAlgHom
        (AlgHom.id k (groupAlgebraInvariants rho)) (fun _ _ ↦ Commute.all _ _) t :
      groupAlgebraInvariants rho) : MonoidAlgebra L (Multiplicative M)) =
      Algebra.TensorProduct.lift
        (HopfAlgebra.antipodeAlgHom L (MonoidAlgebra L (Multiplicative M)))
        (AlgHom.id L (MonoidAlgebra L (Multiplicative M)))
        (fun _ _ ↦ Commute.all _ _) (tensorMap rho t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgEquiv.toAlgHom_apply,
        AlgHom.id_apply, tensorMap_tmul,
        HopfAlgebra.antipodeAlgHom_apply]
      rw [Subalgebra.coe_mul, groupAlgebraInvariantsAntipode_apply]
  | add x y hx hy =>
      simp only [map_add]
      rw [← hx, ← hy]
      rfl

private theorem coe_lift_antipode_right
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    ((Algebra.TensorProduct.lift (AlgHom.id k (groupAlgebraInvariants rho))
        (groupAlgebraInvariantsAntipode rho).toAlgHom (fun _ _ ↦ Commute.all _ _) t :
      groupAlgebraInvariants rho) : MonoidAlgebra L (Multiplicative M)) =
      Algebra.TensorProduct.lift (AlgHom.id L (MonoidAlgebra L (Multiplicative M)))
        (HopfAlgebra.antipodeAlgHom L (MonoidAlgebra L (Multiplicative M)))
        (fun _ _ ↦ Commute.all _ _) (tensorMap rho t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
        AlgEquiv.toAlgHom_apply, tensorMap_tmul,
        HopfAlgebra.antipodeAlgHom_apply]
      rw [Subalgebra.coe_mul, groupAlgebraInvariantsAntipode_apply]
  | add x y hx hy =>
      simp only [map_add]
      rw [← hx, ← hy]
      rfl

private theorem groupAlgebraInvariants_mul_antipode_left
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (Algebra.TensorProduct.lift (groupAlgebraInvariantsAntipode rho).toAlgHom
        (AlgHom.id k (groupAlgebraInvariants rho)) (fun _ _ ↦ Commute.all _ _)).comp
          (groupAlgebraInvariantsComulDescended rho) =
      (Algebra.ofId k (groupAlgebraInvariants rho)).comp
        (groupAlgebraInvariantsCounit rho) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  rw [AlgHom.comp_apply, coe_lift_antipode_left, tensorMap_comulDescended,
    AlgHom.comp_apply, Algebra.ofId_apply]
  calc
    Algebra.TensorProduct.lift
        (HopfAlgebra.antipodeAlgHom L (MonoidAlgebra L (Multiplicative M)))
        (AlgHom.id L (MonoidAlgebra L (Multiplicative M)))
        (fun _ _ ↦ Commute.all _ _)
        (Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M))) =
      algebraMap L (MonoidAlgebra L (Multiplicative M))
        (Coalgebra.counit (R := L) (x : MonoidAlgebra L (Multiplicative M))) := by
          rw [← Algebra.TensorProduct.lmul'_comp_map]
          -- The Hopf axiom is stored as an equality of linear maps; the preceding rewrite
          -- identifies its multiplication with the algebra-map lift used here.
          change LinearMap.mul' L (MonoidAlgebra L (Multiplicative M))
            ((HopfAlgebra.antipode L).rTensor (MonoidAlgebra L (Multiplicative M))
              (Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)))) = _
          exact HopfAlgebra.mul_antipode_rTensor_comul_apply
            (x : MonoidAlgebra L (Multiplicative M))
    _ = algebraMap L (MonoidAlgebra L (Multiplicative M))
        (algebraMap k L (groupAlgebraInvariantsCounit rho x)) := by
      rw [algebraMap_groupAlgebraInvariantsCounit]
    _ = algebraMap k (MonoidAlgebra L (Multiplicative M))
        (groupAlgebraInvariantsCounit rho x) :=
      (IsScalarTower.algebraMap_apply k L _ _).symm
    _ = ((algebraMap k (groupAlgebraInvariants rho)
        (groupAlgebraInvariantsCounit rho x) : groupAlgebraInvariants rho) :
          MonoidAlgebra L (Multiplicative M)) := rfl

private theorem groupAlgebraInvariants_mul_antipode_right
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (Algebra.TensorProduct.lift (AlgHom.id k (groupAlgebraInvariants rho))
        (groupAlgebraInvariantsAntipode rho).toAlgHom (fun _ _ ↦ Commute.all _ _)).comp
          (groupAlgebraInvariantsComulDescended rho) =
      (Algebra.ofId k (groupAlgebraInvariants rho)).comp
        (groupAlgebraInvariantsCounit rho) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  rw [AlgHom.comp_apply, coe_lift_antipode_right, tensorMap_comulDescended,
    AlgHom.comp_apply, Algebra.ofId_apply]
  calc
    Algebra.TensorProduct.lift (AlgHom.id L (MonoidAlgebra L (Multiplicative M)))
        (HopfAlgebra.antipodeAlgHom L (MonoidAlgebra L (Multiplicative M)))
        (fun _ _ ↦ Commute.all _ _)
        (Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M))) =
      algebraMap L (MonoidAlgebra L (Multiplicative M))
        (Coalgebra.counit (R := L) (x : MonoidAlgebra L (Multiplicative M))) := by
          rw [← Algebra.TensorProduct.lmul'_comp_map]
          -- As above, expose the linear-map form of the second antipode axiom.
          change LinearMap.mul' L (MonoidAlgebra L (Multiplicative M))
            ((HopfAlgebra.antipode L).lTensor (MonoidAlgebra L (Multiplicative M))
              (Coalgebra.comul (R := L) (x : MonoidAlgebra L (Multiplicative M)))) = _
          exact HopfAlgebra.mul_antipode_lTensor_comul_apply
            (x : MonoidAlgebra L (Multiplicative M))
    _ = algebraMap L (MonoidAlgebra L (Multiplicative M))
        (algebraMap k L (groupAlgebraInvariantsCounit rho x)) := by
      rw [algebraMap_groupAlgebraInvariantsCounit]
    _ = algebraMap k (MonoidAlgebra L (Multiplicative M))
        (groupAlgebraInvariantsCounit rho x) :=
      (IsScalarTower.algebraMap_apply k L _ _).symm
    _ = ((algebraMap k (groupAlgebraInvariants rho)
        (groupAlgebraInvariantsCounit rho x) : groupAlgebraInvariants rho) :
          MonoidAlgebra L (Multiplicative M)) := rfl

/-- The Hopf algebra structure on the Galois-invariant group algebra descended from the split
group algebra over `L`.

This is a named structure rather than a global instance because it depends on the chosen Galois
action `rho`. -/
@[instance_reducible]
noncomputable def groupAlgebraInvariantsHopfAlgebra
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    HopfAlgebra k (groupAlgebraInvariants rho) := by
  letI : Bialgebra k (groupAlgebraInvariants rho) :=
    groupAlgebraInvariantsBialgebra rho
  exact HopfAlgebra.ofAlgHom (groupAlgebraInvariantsAntipode rho).toAlgHom
    (groupAlgebraInvariants_mul_antipode_left rho)
    (groupAlgebraInvariants_mul_antipode_right rho)

/-- Selecting the descended Hopf structure makes its comultiplication the explicitly descended
comultiplication. -/
theorem groupAlgebraInvariantsHopfAlgebra_comul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    HEq (letI : Module k (groupAlgebraInvariants rho) :=
          (groupAlgebraInvariantsHopfAlgebra rho).toAlgebra.toModule
        letI : Coalgebra k (groupAlgebraInvariants rho) :=
          (groupAlgebraInvariantsHopfAlgebra rho).toCoalgebra
        Coalgebra.comul (R := k) (A := groupAlgebraInvariants rho))
      (groupAlgebraInvariantsComulDescended rho).toLinearMap :=
  heq_of_eq rfl

/-- Selecting the descended Hopf structure makes its counit the invariant-algebra counit. -/
theorem groupAlgebraInvariantsHopfAlgebra_counit
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    HEq (letI : Module k (groupAlgebraInvariants rho) :=
          (groupAlgebraInvariantsHopfAlgebra rho).toAlgebra.toModule
        letI : Coalgebra k (groupAlgebraInvariants rho) :=
          (groupAlgebraInvariantsHopfAlgebra rho).toCoalgebra
        Coalgebra.counit (R := k) (A := groupAlgebraInvariants rho))
      (groupAlgebraInvariantsCounit rho).toLinearMap :=
  heq_of_eq rfl

/-- Selecting the descended Hopf structure makes its antipode the restriction of the split
group-algebra antipode. -/
theorem groupAlgebraInvariantsHopfAlgebra_antipode
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    HEq (letI : Module k (groupAlgebraInvariants rho) :=
          (groupAlgebraInvariantsHopfAlgebra rho).toAlgebra.toModule
        letI : HopfAlgebra k (groupAlgebraInvariants rho) :=
          groupAlgebraInvariantsHopfAlgebra rho
        HopfAlgebra.antipode k (A := groupAlgebraInvariants rho))
      (groupAlgebraInvariantsAntipode rho).toLinearMap :=
  heq_of_eq rfl

end TauCeti.GaloisDescent
