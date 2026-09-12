/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Tensor
import TauCeti.Algebra.TensorProduct.BaseChange
import Mathlib.RingTheory.Flat.Basic

/-!
# The Hopf algebra of Galois-invariant group-algebra elements

For a finite Galois extension `L/k`, the invariant algebra of the simultaneous action on
coefficients and exponents of `L[M]` is a Hopf algebra over `k`. Its comultiplication is
obtained from the tensor descent equivalence, its counit takes values in `k`, and its
antipode is the restriction of the split antipode. These are the coordinate Hopf algebras
used to construct groups of multiplicative type, and non-split tori when `M` is a lattice.

The coalgebra and antipode identities are checked in the split group algebra. Injectivity
of the comparison on triple tensor products allows coassociativity to descend. No finite
generation of `M` or restriction on the characteristic is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L M : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M]
variable [FiniteDimensional k L] [IsGalois k L]

variable (rho : Representation ℤ (L ≃ₐ[k] L) M)

/-- The split group algebra over the extension field. -/
local notation "A" => MonoidAlgebra L (Multiplicative M)
/-- The invariant coordinate algebra over the ground field. -/
local notation "B" => groupAlgebraInvariants rho

/-- The comultiplication of the invariant algebra, valued in its own tensor square. -/
private noncomputable def descendedComul : B →ₐ[k] B ⊗[k] B :=
  (groupAlgebraInvariantsTensorEquiv rho).symm.toAlgHom.comp
    (groupAlgebraInvariantsComul rho)

/-- The inclusion of the descended tensor square in the split tensor square. -/
private noncomputable def tensorInclusion : B ⊗[k] B →ₐ[k] A ⊗[L] A :=
  (groupAlgebraTensorInvariants rho).val.comp
    (groupAlgebraInvariantsTensorEquiv rho).toAlgHom

@[simp]
private theorem tensorInclusion_tmul (x y : B) :
    tensorInclusion rho (x ⊗ₜ[k] y) = (x : A) ⊗ₜ[L] (y : A) := by
  simp [tensorInclusion]

@[simp]
private theorem tensorInclusion_descendedComul (x : B) :
    tensorInclusion rho (descendedComul rho x) = Coalgebra.comul (R := L) (x : A) := by
  simp [tensorInclusion, descendedComul]

/-- Scalar extension identifies the tensor square with the split tensor square. -/
private noncomputable def tensorBaseChangeEquiv : L ⊗[k] (B ⊗[k] B) ≃ₐ[L] A ⊗[L] A :=
  (Algebra.TensorProduct.baseChangeTensorAlgEquiv k L B B).trans
    (Algebra.TensorProduct.congr (groupAlgebraInvariantsBaseChangeEquiv rho)
      (groupAlgebraInvariantsBaseChangeEquiv rho))

@[simp]
private theorem tensorBaseChangeEquiv_one_tmul (t : B ⊗[k] B) :
    tensorBaseChangeEquiv rho (1 ⊗ₜ[k] t) = tensorInclusion rho t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [tensorBaseChangeEquiv]
  | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]

/-- The inclusion of the right-associated tensor cube in its split counterpart. -/
private noncomputable def tripleInclusion : B ⊗[k] (B ⊗[k] B) →ₐ[k] A ⊗[L] (A ⊗[L] A) :=
  (((Algebra.TensorProduct.baseChangeTensorAlgEquiv k L B (B ⊗[k] B)).trans
    (Algebra.TensorProduct.congr (groupAlgebraInvariantsBaseChangeEquiv rho)
      (tensorBaseChangeEquiv rho))).toAlgHom.restrictScalars k).comp
        (Algebra.TensorProduct.includeRight (R := k) («A» := L) («B» := B ⊗[k] (B ⊗[k] B)))

private theorem tripleInclusion_injective : Function.Injective (tripleInclusion rho) :=
  (((Algebra.TensorProduct.baseChangeTensorAlgEquiv k L B (B ⊗[k] B)).trans
    (Algebra.TensorProduct.congr (groupAlgebraInvariantsBaseChangeEquiv rho)
      (tensorBaseChangeEquiv rho))).injective).comp
        (Algebra.TensorProduct.includeRight_injective
          (FaithfulSMul.algebraMap_injective k L))

@[simp]
private theorem tripleInclusion_tmul (x : B) (t : B ⊗[k] B) :
    tripleInclusion rho (x ⊗ₜ[k] t) = (x : A) ⊗ₜ[L] tensorInclusion rho t := by
  simp [tripleInclusion]

private theorem tripleInclusion_assoc_tmul (t : B ⊗[k] B) (z : B) :
    tripleInclusion rho (TensorProduct.assoc k B B B (t ⊗ₜ[k] z)) =
      TensorProduct.assoc L A A A (tensorInclusion rho t ⊗ₜ[L] (z : A)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]

private theorem descendedComul_coassoc :
    TensorProduct.assoc k B B B ∘ₗ (descendedComul rho).toLinearMap.rTensor B ∘ₗ
        (descendedComul rho).toLinearMap =
      (descendedComul rho).toLinearMap.lTensor B ∘ₗ (descendedComul rho).toLinearMap := by
  have hleft (t : B ⊗[k] B) :
      tripleInclusion rho (TensorProduct.assoc k B B B
        ((descendedComul rho).toLinearMap.rTensor B t)) =
      TensorProduct.assoc L A A A
        ((Coalgebra.comul (R := L)).rTensor A (tensorInclusion rho t)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [tripleInclusion_assoc_tmul]
    | add x y hx hy => simp [hx, hy]
  have hright (t : B ⊗[k] B) :
      tripleInclusion rho ((descendedComul rho).toLinearMap.lTensor B t) =
      (Coalgebra.comul (R := L)).lTensor A (tensorInclusion rho t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp [hx, hy]
  apply LinearMap.ext
  intro x
  apply tripleInclusion_injective rho
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
    hleft, hright, tensorInclusion_descendedComul]
    using Coalgebra.coassoc_apply (R := L) (x : A)

private theorem descendedComul_counit_left :
    (groupAlgebraInvariantsCounit rho).toLinearMap.rTensor B ∘ₗ
      (descendedComul rho).toLinearMap = TensorProduct.mk k k B 1 := by
  have h (t : B ⊗[k] B) :
      ((TensorProduct.lid k B)
        ((groupAlgebraInvariantsCounit rho).toLinearMap.rTensor B t) : A) =
      TensorProduct.lid L A
        ((Coalgebra.counit (R := L)).rTensor A (tensorInclusion rho t)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          TensorProduct.lid_tmul, tensorInclusion_tmul]
        rw [← algebraMap_groupAlgebraInvariantsCounit rho, IsScalarTower.algebraMap_smul]
        rfl
    | add x y hx hy => simp [hx, hy]
  apply LinearMap.ext
  intro x
  apply (TensorProduct.lid k B).injective
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, tensorInclusion_descendedComul,
    Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul,
    TensorProduct.mk_apply]

private theorem descendedComul_counit_right :
    (groupAlgebraInvariantsCounit rho).toLinearMap.lTensor B ∘ₗ
      (descendedComul rho).toLinearMap = (TensorProduct.mk k B k).flip 1 := by
  have h (t : B ⊗[k] B) :
      ((TensorProduct.rid k B)
        ((groupAlgebraInvariantsCounit rho).toLinearMap.lTensor B t) : A) =
      TensorProduct.rid L A
        ((Coalgebra.counit (R := L)).lTensor A (tensorInclusion rho t)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
          TensorProduct.rid_tmul, tensorInclusion_tmul]
        rw [← algebraMap_groupAlgebraInvariantsCounit rho, IsScalarTower.algebraMap_smul]
        rfl
    | add x y hx hy => simp [hx, hy]
  apply LinearMap.ext
  intro x
  apply (TensorProduct.rid k B).injective
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, tensorInclusion_descendedComul,
    Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul,
    LinearMap.flip_apply, TensorProduct.mk_apply]

/-- The invariant group algebra is a bialgebra over the ground field. -/
noncomputable instance groupAlgebraInvariantsBialgebra : Bialgebra k B where
  comul := ((groupAlgebraInvariantsTensorEquiv rho).symm.toAlgHom.comp
    (groupAlgebraInvariantsComul rho)).toLinearMap
  counit := (groupAlgebraInvariantsCounit rho).toLinearMap
  coassoc := by exact descendedComul_coassoc rho
  rTensor_counit_comp_comul := by exact descendedComul_counit_left rho
  lTensor_counit_comp_comul := by exact descendedComul_counit_right rho
  counit_one := map_one (groupAlgebraInvariantsCounit rho)
  mul_compr₂_counit := by ext x y; exact map_mul (groupAlgebraInvariantsCounit rho) x y
  comul_one := by exact map_one (descendedComul rho)
  mul_compr₂_comul := by ext x y; exact map_mul (descendedComul rho) x y

/-- Under tensor descent, the comultiplication is the original invariant-valued map. -/
@[simp]
theorem groupAlgebraInvariantsTensorEquiv_comul (x : B) :
    groupAlgebraInvariantsTensorEquiv rho (Coalgebra.comul (R := k) x) =
      groupAlgebraInvariantsComul rho x := by
  -- The instance's comultiplication is the composite defining `descendedComul`.
  change groupAlgebraInvariantsTensorEquiv rho (descendedComul rho x) = _
  simp [descendedComul]

/-- The counit on the invariant Hopf algebra is the descended counit. -/
@[simp]
theorem counit_groupAlgebraInvariants (x : B) :
    Coalgebra.counit (R := k) x = groupAlgebraInvariantsCounit rho x := rfl

private theorem tensorInclusion_comul (x : B) :
    tensorInclusion rho (Coalgebra.comul (R := k) x) =
      Coalgebra.comul (R := L) (x : A) := by
  simp [tensorInclusion]

private theorem descendedAntipode_left :
    LinearMap.mul' k B ∘ₗ
        (groupAlgebraInvariantsAntipode rho).toLinearMap.rTensor B ∘ₗ
          Coalgebra.comul = Algebra.linearMap k B ∘ₗ Coalgebra.counit := by
  have h (t : B ⊗[k] B) :
      (LinearMap.mul' k B
        ((groupAlgebraInvariantsAntipode rho).toLinearMap.rTensor B t) : A) =
      LinearMap.mul' L A
        ((HopfAlgebra.antipode L).rTensor A (tensorInclusion rho t)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp [hx, hy]
  apply LinearMap.ext
  intro x
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply, h, tensorInclusion_comul,
    HopfAlgebra.mul_antipode_rTensor_comul_apply, Algebra.linearMap_apply,
    counit_groupAlgebraInvariants]
  rw [← algebraMap_groupAlgebraInvariantsCounit rho]
  exact (IsScalarTower.algebraMap_apply k L A _).symm

private theorem descendedAntipode_right :
    LinearMap.mul' k B ∘ₗ
        (groupAlgebraInvariantsAntipode rho).toLinearMap.lTensor B ∘ₗ
          Coalgebra.comul = Algebra.linearMap k B ∘ₗ Coalgebra.counit := by
  have h (t : B ⊗[k] B) :
      (LinearMap.mul' k B
        ((groupAlgebraInvariantsAntipode rho).toLinearMap.lTensor B t) : A) =
      LinearMap.mul' L A
        ((HopfAlgebra.antipode L).lTensor A (tensorInclusion rho t)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp [hx, hy]
  apply LinearMap.ext
  intro x
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply, h, tensorInclusion_comul,
    HopfAlgebra.mul_antipode_lTensor_comul_apply, Algebra.linearMap_apply,
    counit_groupAlgebraInvariants]
  rw [← algebraMap_groupAlgebraInvariantsCounit rho]
  exact (IsScalarTower.algebraMap_apply k L A _).symm

/-- The coordinate Hopf algebra descended from the split group algebra along `L/k`. -/
noncomputable instance groupAlgebraInvariantsHopfAlgebra : HopfAlgebra k B where
  antipode := (groupAlgebraInvariantsAntipode rho).toLinearMap
  mul_antipode_rTensor_comul := by exact descendedAntipode_left rho
  mul_antipode_lTensor_comul := by exact descendedAntipode_right rho

/-- The antipode on the descended Hopf algebra is the restricted split antipode. -/
@[simp]
theorem antipode_groupAlgebraInvariants (x : B) :
    HopfAlgebra.antipode k x = groupAlgebraInvariantsAntipode rho x := rfl

end TauCeti.GaloisDescent
