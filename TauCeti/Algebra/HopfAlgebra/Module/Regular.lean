/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import TauCeti.Algebra.HopfAlgebra.Cancellation

/-!
# Untwisting coproduct tensor products with the regular module

Let `H` be a Hopf algebra over a commutative semiring `R`. For an `H`-module `M`, the coproduct
tensor product `H ⊗ M`, on which `h` acts by `∑ h₁ a ⊗ h₂ m`, is isomorphic to the
tensor product `H ⊗[R] M` on which `H` acts on the left factor alone
(`TauCeti.BialgebraModule.regularTensorEquiv`). The isomorphism sends `a ⊗ m` to
`∑ a₁ ⊗ S(a₂) m`, and its inverse sends `a ⊗ m` to `a • (1 ⊗ m) = ∑ a₁ ⊗ a₂ m`. When the
antipode is bijective, the same holds with `H` on the right
(`TauCeti.BialgebraModule.tensorRegularEquiv`): `m ⊗ a ↦ ∑ a₂ ⊗ S⁻¹(a₁) m`.

Both inverse laws are the cancellation equivalences of `H ⊗[R] H`
(`TauCeti.HopfAlgebra.comulMulRightEquiv` and `TauCeti.HopfAlgebra.comulMulLeftEquiv`), pushed
forward along the orbit map `b ↦ b • m` of each `m : M`.

## Main declarations

* `TauCeti.BialgebraModule.regularTensorEquiv`: `H ⊗ M`, with the coproduct action, is
  isomorphic to `H ⊗[R] M` with the action on the left factor.
* `TauCeti.BialgebraModule.tensorRegularEquiv`: for a bijective antipode, `M ⊗ H`, with the
  coproduct action, is isomorphic to `H ⊗[R] M` with the action on the left factor.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), proof of Proposition 2.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), proof of Lemma 2.3.
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

/-! Each map above is a cancellation equivalence of `H ⊗[R] H` followed by the orbit map
`b ↦ b • m` in the factor that becomes `M`. -/

private theorem tensorEquiv_twist_lTensor_orbit (m : M) (t : H ⊗[R] H) :
    tensorEquiv R H H M (twist R H M ((orbit R m).lTensor H t)) =
      (orbit R m).lTensor H (comulMulRightEquiv t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, tensorEquiv_twist_tmul, comulMulRightEquiv_tmul]
    induction comul (R := R) a using TensorProduct.inductionOn with
    | tmul x y => simp [mul_smul]
    | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem untwist_lTensor_orbit (m : M) (t : H ⊗[R] H) :
    untwist R H M ((orbit R m).lTensor H t) =
      (orbit R m).lTensor H (comulMulRightEquiv.symm t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, untwist_tmul, comulMulRightEquiv_symm_tmul]
    induction comul (R := R) a using TensorProduct.inductionOn with
    | tmul x y => simp [mul_smul]
    | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `a ⊗ m` is the orbit image of `a ⊗ 1`. -/
private theorem tmul_eq_lTensor_orbit (a : H) (m : M) :
    a ⊗ₜ[R] m = (orbit R m).lTensor H (a ⊗ₜ[R] (1 : H)) := by
  simp

private theorem untwist_tensorEquiv_twist (x : H ⊗[R] M) :
    untwist R H M (tensorEquiv R H H M (twist R H M x)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [tmul_eq_lTensor_orbit, tensorEquiv_twist_lTensor_orbit, untwist_lTensor_orbit,
      LinearEquiv.symm_apply_apply]
  | add x y hx hy => simp [hx, hy]

private theorem twist_untwist (x : H ⊗[R] M) :
    twist R H M (untwist R H M x) = (tensorEquiv R H H M).symm x := by
  rw [LinearEquiv.eq_symm_apply]
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [tmul_eq_lTensor_orbit, untwist_lTensor_orbit, tensorEquiv_twist_lTensor_orbit,
      LinearEquiv.apply_symm_apply]
  | add x y hx hy => simp [hx, hy]

variable (hS : Function.Bijective (antipode R : H →ₗ[R] H))
include hS

private theorem tensorEquiv_twistRight_lTensor_orbit (m : M) (t : H ⊗[R] H) :
    tensorEquiv R H M H (twistRight R H M ((orbit R m).lTensor H t)) =
      (orbit R m).rTensor H (comulMulLeftEquiv hS t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, tensorEquiv_twistRight_tmul, comulMulLeftEquiv_tmul]
    induction comul (R := R) a using TensorProduct.inductionOn with
    | tmul x y => simp [mul_smul]
    | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem untwistRight_rTensor_orbit (m : M) (t : H ⊗[R] H) :
    untwistRight R H M hS ((orbit R m).rTensor H t) =
      (orbit R m).lTensor H ((comulMulLeftEquiv hS).symm t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, untwistRight_tmul, comulMulLeftEquiv_symm_tmul]
    induction comul (R := R) b using TensorProduct.inductionOn with
    | tmul x y => simp [mul_smul]
    | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem untwistRight_tensorEquiv_twistRight (x : H ⊗[R] M) :
    untwistRight R H M hS (tensorEquiv R H M H (twistRight R H M x)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [tmul_eq_lTensor_orbit, tensorEquiv_twistRight_lTensor_orbit hS,
      untwistRight_rTensor_orbit hS, LinearEquiv.symm_apply_apply]
  | add x y hx hy => simp [hx, hy]

private theorem twistRight_untwistRight (x : M ⊗[R] H) :
    twistRight R H M (untwistRight R H M hS x) = (tensorEquiv R H M H).symm x := by
  rw [LinearEquiv.eq_symm_apply]
  induction x using TensorProduct.inductionOn with
  | tmul m a =>
    have hx : m ⊗ₜ[R] a = (orbit R m).rTensor H ((1 : H) ⊗ₜ a) := by simp
    rw [hx, untwistRight_rTensor_orbit hS, tensorEquiv_twistRight_lTensor_orbit hS,
      LinearEquiv.apply_symm_apply]
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
      right_inv x := (twist_untwist _).trans ((tensorEquiv R H H M).symm_apply_apply x) }

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
      right_inv x :=
        (twistRight_untwistRight hS _).trans ((tensorEquiv R H M H).symm_apply_apply x) }

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

end TauCeti.BialgebraModule
