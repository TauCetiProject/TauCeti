/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Module.Finsupp
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
public import Mathlib.LinearAlgebra.TensorProduct.Projective

/-!
# Tensor products with projective modules over a Hopf algebra

Let `H` be a Hopf algebra over a commutative semiring `R`. For an `H`-module `M`, the coproduct
tensor product `H ⊗ M`, on which `h` acts by `∑ h₁ a ⊗ h₂ m`, is isomorphic to the
tensor product `H ⊗[R] M` on which `H` acts on the left factor alone
(`TauCeti.BialgebraModule.regularTensorEquiv`). The isomorphism sends `a ⊗ m` to
`∑ a₁ ⊗ S(a₂) m`, and its inverse sends `a ⊗ m` to `a • (1 ⊗ m) = ∑ a₁ ⊗ a₂ m`. When the
antipode is bijective, the same holds with `H` on the right
(`TauCeti.BialgebraModule.tensorRegularEquiv`): `m ⊗ a ↦ ∑ a₂ ⊗ S⁻¹(a₁) m`.

So the coproduct tensor product of the regular module with a module that is projective over
`R` is a projective `H`-module. Distributing over free modules and passing to retracts gives the
main results: `P ⊗ M` is projective whenever `P` is a projective `H`-module and `M` is projective
over `R` (`TauCeti.BialgebraModule.projective_tensor_left`), and, for a bijective antipode,
so is `M ⊗ P` (`TauCeti.BialgebraModule.projective_tensor_right`). Over a field every module
is projective over `R`, so the projective modules are closed under tensoring with arbitrary
modules on the right, and, for a bijective antipode, on the left as well. This is what makes
the maps factoring through projective modules a tensor ideal of the category of all modules,
the starting point of the stable category of a finite-dimensional Hopf algebra.

## Main declarations

* `TauCeti.BialgebraModule.regularTensorEquiv`: `H ⊗ M`, with the coproduct action, is
  isomorphic to `H ⊗[R] M` with the action on the left factor.
* `TauCeti.BialgebraModule.tensorRegularEquiv`: for a bijective antipode, `M ⊗ H`, with the
  coproduct action, is isomorphic to `H ⊗[R] M` with the action on the left factor.
* `TauCeti.BialgebraModule.projective_tensor_left`,
  `TauCeti.BialgebraModule.projective_tensor_right`: tensoring a projective module with a module
  projective over `R` on either side gives a projective module.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 2.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Lemma 2.3.
-/

public noncomputable section

open scoped TensorProduct
open Coalgebra HopfAlgebra TauCeti.HopfAlgebra

namespace TauCeti.BialgebraModule

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
variable {M : Type*} [AddCommMonoid M] [Module R M] [Module H M] [IsScalarTower R H M]

section Maps

variable (R M) in
/-- The action of `H` on `M`, as an `R`-linear map out of `H ⊗[R] M`. -/
private def actMap : H ⊗[R] M →ₗ[R] M := TensorProduct.lift (Algebra.lsmul R R M).toLinearMap

@[simp] private theorem actMap_tmul (a : H) (m : M) : actMap R M (a ⊗ₜ m) = a • m := (rfl)

variable (R) in
/-- The orbit map `a ↦ a • m`, as an `R`-linear map. -/
private abbrev orbit (m : M) : H →ₗ[R] M := (LinearMap.toSpanSingleton H M m).restrictScalars R

variable (R H M) in
/-- The untwisting map `a ⊗ m ↦ ∑ a₁ ⊗ S(a₂) m` on the native tensor product. -/
private def untwist : H ⊗[R] M →ₗ[R] H ⊗[R] M :=
  (actMap R M ∘ₗ (antipode R).rTensor M).lTensor H ∘ₗ
    (TensorProduct.assoc R H H M).toLinearMap ∘ₗ (comul (R := R) (A := H)).rTensor M

private theorem untwist_tmul (a : H) (m : M) :
    untwist R H M (a ⊗ₜ m) = (orbit R m ∘ₗ antipode R).lTensor H (comul a) := by
  simp only [untwist, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
  induction comul (R := R) a using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]

variable (R H M) in
/-- The inverse untwisting map `m ⊗ a ↦ ∑ a₂ ⊗ S⁻¹(a₁) m` on the native tensor product. -/
private def untwistRight (hS : Function.Bijective (antipode R : H →ₗ[R] H)) :
    M ⊗[R] H →ₗ[R] H ⊗[R] M :=
  (actMap R M ∘ₗ (inverseAntipode hS).rTensor M).lTensor H ∘ₗ
    (TensorProduct.assoc R H H M).toLinearMap ∘ₗ
    ((TensorProduct.comm R H H).toLinearMap ∘ₗ comul (R := R) (A := H)).rTensor M ∘ₗ
    (TensorProduct.comm R M H).toLinearMap

private theorem untwistRight_tmul (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    (m : M) (a : H) :
    untwistRight R H M hS (m ⊗ₜ a) =
      (orbit R m ∘ₗ inverseAntipode hS).lTensor H
        (TensorProduct.comm R H H (comul a)) := by
  simp only [untwistRight, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    LinearMap.rTensor_tmul]
  induction comul (R := R) a using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]

variable (R H M) in
/-- The `H`-linear map `a ⊗ m ↦ a • (1 ⊗ m)` into the coproduct tensor product. -/
private def twist : H ⊗[R] M →ₗ[H] Tensor R H H M :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton H _
    ((tensorEquiv R H H M).symm.toLinearMap ∘ₗ TensorProduct.mk R H M 1))

private theorem twist_tmul (a : H) (m : M) : twist R H M (a ⊗ₜ m) = a • tmul R H 1 m := by
  simp [twist]

private theorem tensorEquiv_twist_tmul (a : H) (m : M) :
    tensorEquiv R H H M (twist R H M (a ⊗ₜ m)) = (orbit R m).lTensor H (comul a) := by
  rw [twist_tmul, tensorEquiv_smul, tensorEquiv_tmul, tensorAction_apply]
  induction comul (R := R) a using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp [map_add, hx, hy]

variable (R H M) in
/-- The `H`-linear map `a ⊗ m ↦ a • (m ⊗ 1)` into the coproduct tensor product. -/
private def twistRight : H ⊗[R] M →ₗ[H] Tensor R H M H :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton H _
    ((tensorEquiv R H M H).symm.toLinearMap ∘ₗ (TensorProduct.mk R M H).flip 1))

private theorem twistRight_tmul (a : H) (m : M) :
    twistRight R H M (a ⊗ₜ m) = a • tmul R H m 1 := by
  simp [twistRight]

private theorem tensorEquiv_twistRight_tmul (a : H) (m : M) :
    tensorEquiv R H M H (twistRight R H M (a ⊗ₜ m)) = (orbit R m).rTensor H (comul a) := by
  rw [twistRight_tmul, tensorEquiv_smul, tensorEquiv_tmul, tensorAction_apply]
  induction comul (R := R) a using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp [map_add, hx, hy]

end Maps

section Inverse

/-- The untwisting map applied to `∑ a ⊗ b m`, rewritten so that coassociativity applies. -/
private theorem untwist_lTensor_orbit (m : M) (t : H ⊗[R] H) :
    untwist R H M ((orbit R m).lTensor H t) =
      (orbit R m ∘ₗ LinearMap.mul' R H ∘ₗ (antipode R).rTensor H).lTensor H
        (TensorProduct.assoc R H H H ((comul (R := R) (A := H)).rTensor H t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, untwist_tmul]
    induction comul (R := R) a using TensorProduct.inductionOn with
    | tmul x y => simp [mul_smul]
    | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, map_add, hx, hy]
  | add x y hx hy => simp [hx, hy]

private theorem untwist_tensorEquiv_twist (x : H ⊗[R] M) :
    untwist R H M (tensorEquiv R H H M (twist R H M x)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    -- `∑ a₁ ⊗ S(a₂) a₃ m = a ⊗ m`, by coassociativity and the antipode identity.
    rw [tensorEquiv_twist_tmul, untwist_lTensor_orbit, coassoc_apply,
      ← LinearMap.lTensor_comp_apply]
    simp only [LinearMap.comp_assoc, mul_antipode_rTensor_comul]
    rw [← LinearMap.comp_assoc, LinearMap.lTensor_comp_apply, lTensor_counit_comul]
    simp
  | add x y hx hy => simp [hx, hy]

/-- The twisting map applied to `∑ a ⊗ S(b) m`, rewritten so that coassociativity applies. -/
private theorem tensorEquiv_twist_lTensor (m : M) (t : H ⊗[R] H) :
    tensorEquiv R H H M (twist R H M ((orbit R m ∘ₗ antipode R).lTensor H t)) =
      (orbit R m ∘ₗ LinearMap.mul' R H ∘ₗ (antipode R).lTensor H).lTensor H
        (TensorProduct.assoc R H H H ((comul (R := R) (A := H)).rTensor H t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
      tensorEquiv_twist_tmul]
    induction comul (R := R) a using TensorProduct.inductionOn with
    | tmul x y => simp [mul_smul]
    | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, map_add, hx, hy]
  | add x y hx hy => simp [hx, hy]

private theorem twist_untwist (x : H ⊗[R] M) :
    twist R H M (untwist R H M x) = (tensorEquiv R H H M).symm x := by
  rw [LinearEquiv.eq_symm_apply]
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    -- `∑ a₁ ⊗ a₂ S(a₃) m = a ⊗ m`, by coassociativity and the antipode identity.
    rw [untwist_tmul, tensorEquiv_twist_lTensor, coassoc_apply, ← LinearMap.lTensor_comp_apply]
    simp only [LinearMap.comp_assoc, mul_antipode_lTensor_comul]
    rw [← LinearMap.comp_assoc, LinearMap.lTensor_comp_apply, lTensor_counit_comul]
    simp
  | add x y hx hy => simp [hx, hy]

variable (hS : Function.Bijective (antipode R : H →ₗ[R] H))
include hS

/-- `∑ S⁻¹(a₂) a₁ = ε(a)`, as an identity of linear maps. -/
private theorem mul_inverseAntipode_rTensor_comm_comul :
    LinearMap.mul' R H ∘ₗ (inverseAntipode hS).rTensor H ∘ₗ
      (TensorProduct.comm R H H).toLinearMap ∘ₗ comul =
        Algebra.linearMap R H ∘ₗ counit :=
  LinearMap.ext (mul_inverseAntipode_rTensor_comm_comul_apply hS)

/-- `∑ a₂ S⁻¹(a₁) = ε(a)`, as an identity of linear maps. -/
private theorem mul_inverseAntipode_lTensor_comm_comul :
    LinearMap.mul' R H ∘ₗ (inverseAntipode hS).lTensor H ∘ₗ
      (TensorProduct.comm R H H).toLinearMap ∘ₗ comul =
        Algebra.linearMap R H ∘ₗ counit :=
  LinearMap.ext (mul_inverseAntipode_lTensor_comm_comul_apply hS)

/-- The right untwisting map applied to `∑ a m ⊗ b`, rewritten so that coassociativity
applies. -/
private theorem untwistRight_rTensor_orbit (m : M) (t : H ⊗[R] H) :
    untwistRight R H M hS ((orbit R m).rTensor H t) =
      TensorProduct.comm R M H
        ((orbit R m ∘ₗ LinearMap.mul' R H ∘ₗ (inverseAntipode hS).rTensor H ∘ₗ
          (TensorProduct.comm R H H).toLinearMap).rTensor H
          ((TensorProduct.assoc R H H H).symm ((comul (R := R) (A := H)).lTensor H t))) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, untwistRight_tmul]
    induction comul (R := R) b using TensorProduct.inductionOn with
    | tmul x y => simp [mul_smul]
    | add x y hx hy =>
      rw [map_add, map_add, TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy]
  | add x y hx hy => simp [hx, hy]

private theorem untwistRight_tensorEquiv_twistRight (x : H ⊗[R] M) :
    untwistRight R H M hS (tensorEquiv R H M H (twistRight R H M x)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    -- `∑ a₃ ⊗ S⁻¹(a₂) a₁ m = a ⊗ m`, by coassociativity and the inverse antipode identity.
    rw [tensorEquiv_twistRight_tmul, untwistRight_rTensor_orbit, coassoc_symm_apply,
      ← LinearMap.rTensor_comp_apply]
    simp only [LinearMap.comp_assoc, mul_inverseAntipode_rTensor_comm_comul hS]
    rw [← LinearMap.comp_assoc, LinearMap.rTensor_comp_apply, rTensor_counit_comul]
    simp
  | add x y hx hy => simp [hx, hy]

/-- The right twisting map applied to `∑ b ⊗ S⁻¹(a) m`, rewritten so that coassociativity
applies. -/
private theorem tensorEquiv_twistRight_lTensor (m : M) (t : H ⊗[R] H) :
    tensorEquiv R H M H (twistRight R H M
        ((orbit R m ∘ₗ inverseAntipode hS).lTensor H (TensorProduct.comm R H H t))) =
      (orbit R m ∘ₗ LinearMap.mul' R H ∘ₗ (inverseAntipode hS).lTensor H ∘ₗ
          (TensorProduct.comm R H H).toLinearMap).rTensor H
        ((TensorProduct.assoc R H H H).symm ((comul (R := R) (A := H)).lTensor H t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.comm_tmul, LinearMap.comp_apply,
      tensorEquiv_twistRight_tmul]
    induction comul (R := R) b using TensorProduct.inductionOn with
    | tmul x y => simp [mul_smul]
    | add x y hx hy =>
      rw [map_add, TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => simp [hx, hy]

private theorem twistRight_untwistRight (x : M ⊗[R] H) :
    twistRight R H M (untwistRight R H M hS x) = (tensorEquiv R H M H).symm x := by
  rw [LinearEquiv.eq_symm_apply]
  induction x using TensorProduct.inductionOn with
  | tmul m a =>
    -- `∑ a₂ S⁻¹(a₁) m ⊗ a₃ = m ⊗ a`, by coassociativity and the inverse antipode identity.
    rw [untwistRight_tmul, tensorEquiv_twistRight_lTensor, coassoc_symm_apply,
      ← LinearMap.rTensor_comp_apply]
    simp only [LinearMap.comp_assoc, mul_inverseAntipode_lTensor_comm_comul hS]
    rw [← LinearMap.comp_assoc, LinearMap.rTensor_comp_apply, rTensor_counit_comul]
    simp
  | add x y hx hy => simp [hx, hy]

end Inverse

section Equiv

variable (R H M)

/-- The coproduct tensor product `H ⊗ M` of the regular module with `M` is isomorphic to
`H ⊗[R] M` with `H` acting on the left factor alone: `a ⊗ m ↦ ∑ a₁ ⊗ S(a₂) m`. -/
def regularTensorEquiv : Tensor R H H M ≃ₗ[H] H ⊗[R] M :=
  LinearEquiv.symm
    { twist R H M with
      invFun := untwist R H M ∘ₗ (tensorEquiv R H H M).toLinearMap
      left_inv := untwist_tensorEquiv_twist
      right_inv x := by
        simpa using congrArg (tensorEquiv R H H M).symm
          (congrArg (tensorEquiv R H H M) (twist_untwist (tensorEquiv R H H M x))) }

variable {R H M}

private theorem regularTensorEquiv_apply (x : Tensor R H H M) :
    regularTensorEquiv R H M x = untwist R H M (tensorEquiv R H H M x) := (rfl)

/-- The inverse of `regularTensorEquiv` sends `a ⊗ m` to `a • (1 ⊗ m) = ∑ a₁ ⊗ a₂ m`. -/
@[simp]
theorem regularTensorEquiv_symm_tmul (a : H) (m : M) :
    (regularTensorEquiv R H M).symm (a ⊗ₜ m) = a • tmul R H 1 m :=
  twist_tmul a m

/-- `regularTensorEquiv` sends `a ⊗ m` to `∑ a₁ ⊗ S(a₂) m`, in any representation of the
coproduct of `a`. -/
theorem regularTensorEquiv_tmul (a : H) (m : M) {ι : Type*} (r : Coalgebra.Repr R a ι) :
    regularTensorEquiv R H M (tmul R H a m) =
      ∑ i ∈ r.index, r.left i ⊗ₜ (antipode R (r.right i) • m) := by
  rw [regularTensorEquiv_apply, tensorEquiv_tmul, untwist_tmul, ← r.eq]
  simp

/-- `regularTensorEquiv` sends `1 ⊗ m` to `1 ⊗ m`. -/
@[simp]
theorem regularTensorEquiv_one_tmul (m : M) :
    regularTensorEquiv R H M (tmul R H 1 m) = 1 ⊗ₜ m :=
  (LinearEquiv.eq_symm_apply _).mp (by rw [regularTensorEquiv_symm_tmul, one_smul])

variable (R H M)

/-- For a bijective antipode, the coproduct tensor product `M ⊗ H` of `M` with the regular
module is isomorphic to `H ⊗[R] M` with `H` acting on the left factor alone:
`m ⊗ a ↦ ∑ a₂ ⊗ S⁻¹(a₁) m`. -/
def tensorRegularEquiv (hS : Function.Bijective (antipode R : H →ₗ[R] H)) :
    Tensor R H M H ≃ₗ[H] H ⊗[R] M :=
  LinearEquiv.symm
    { twistRight R H M with
      invFun := untwistRight R H M hS ∘ₗ (tensorEquiv R H M H).toLinearMap
      left_inv := untwistRight_tensorEquiv_twistRight hS
      right_inv x := by
        simpa using congrArg (tensorEquiv R H M H).symm
          (congrArg (tensorEquiv R H M H) (twistRight_untwistRight hS (tensorEquiv R H M H x))) }

variable {R H M}

private theorem tensorRegularEquiv_apply (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    (x : Tensor R H M H) :
    tensorRegularEquiv R H M hS x = untwistRight R H M hS (tensorEquiv R H M H x) := (rfl)

/-- The inverse of `tensorRegularEquiv` sends `a ⊗ m` to `a • (m ⊗ 1) = ∑ a₁ m ⊗ a₂`. -/
@[simp]
theorem tensorRegularEquiv_symm_tmul (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    (a : H) (m : M) :
    (tensorRegularEquiv R H M hS).symm (a ⊗ₜ m) = a • tmul R H m 1 :=
  twistRight_tmul a m

/-- `tensorRegularEquiv` sends `m ⊗ a` to `∑ a₂ ⊗ S⁻¹(a₁) m`, in any representation of the
coproduct of `a`. -/
theorem tensorRegularEquiv_tmul (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    (m : M) (a : H) {ι : Type*} (r : Coalgebra.Repr R a ι) :
    tensorRegularEquiv R H M hS (tmul R H m a) =
      ∑ i ∈ r.index, r.right i ⊗ₜ (inverseAntipode hS (r.left i) • m) := by
  rw [tensorRegularEquiv_apply, tensorEquiv_tmul, untwistRight_tmul, ← r.eq]
  simp

/-- `tensorRegularEquiv` sends `m ⊗ 1` to `1 ⊗ m`. -/
@[simp]
theorem tensorRegularEquiv_tmul_one (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    (m : M) : tensorRegularEquiv R H M hS (tmul R H m 1) = 1 ⊗ₜ m :=
  (LinearEquiv.eq_symm_apply _).mp (by rw [tensorRegularEquiv_symm_tmul, one_smul])

end Equiv

section Projective

variable (R H M)
variable (P : Type*) [AddCommMonoid P] [Module R P] [Module H P] [IsScalarTower R H P]

/-- The coproduct tensor product `P ⊗ M` of a projective module `P` with a module `M` that is
projective over the base is projective. -/
theorem projective_tensor_left [Module.Projective H P] [Module.Projective R M] :
    Module.Projective H (Tensor R H P M) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective H P›
  -- `P ⊗ M` is a retract of `(P →₀ H) ⊗ M`, a direct sum of copies of `H ⊗ M ≅ H ⊗[R] M`.
  have : Module.Projective H (Tensor R H H M) :=
    .of_equiv (regularTensorEquiv R H M).symm
  have : Module.Projective H (Tensor R H (P →₀ H) M) :=
    .of_equiv ((finsuppLEquivDirectSum H (Tensor R H H M) P).symm ≪≫ₗ
      (finsuppLeft R H P H M).symm)
  refine .of_split (tensorMap R H s LinearMap.id)
    (tensorMap R H (Finsupp.linearCombination H id) LinearMap.id) ?_
  rw [← tensorMap_comp, hs, LinearMap.id_comp, tensorMap_id]

/-- For a bijective antipode, the coproduct tensor product `M ⊗ P` of a module `M` that is
projective over the base with a projective module `P` is projective. -/
theorem projective_tensor_right (hS : Function.Bijective (antipode R : H →ₗ[R] H))
    [Module.Projective H P] [Module.Projective R M] :
    Module.Projective H (Tensor R H M P) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective H P›
  -- `M ⊗ P` is a retract of `M ⊗ (P →₀ H)`, a direct sum of copies of `M ⊗ H ≅ H ⊗[R] M`.
  have : Module.Projective H (Tensor R H M H) :=
    .of_equiv (tensorRegularEquiv R H M hS).symm
  have : Module.Projective H (Tensor R H M (P →₀ H)) :=
    .of_equiv ((finsuppLEquivDirectSum H (Tensor R H M H) P).symm ≪≫ₗ
      (finsuppRight R H P H M).symm)
  refine .of_split (tensorMap R H LinearMap.id s)
    (tensorMap R H LinearMap.id (Finsupp.linearCombination H id)) ?_
  rw [← tensorMap_comp, hs, LinearMap.id_comp, tensorMap_id]

end Projective

end TauCeti.BialgebraModule
