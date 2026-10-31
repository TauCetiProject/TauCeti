/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Basic
import Mathlib.GroupTheory.Perm.Fin

/-!
# The universal property of the symmetric tensor power

A multilinear map `f : Mⁱ → N` that is unchanged by permuting its arguments factors uniquely
through the symmetric tensor power. This file builds that factorization,
`SymmetricPower.lift`, as the descent of `PiTensorProduct.lift f` through the quotient map
`SymmetricPower.mk`: the defining relation of the quotient identifies a pure tensor with each of
its reorderings, and `f` takes the same value on all of them.

Together with `SymmetricPower.ext`, which says that a linear map out of the symmetric power is
determined by its values on pure symmetric tensors, this says that composing with the pure
symmetric tensor `⨂ₛ` is a bijection from the linear maps `Sym[R] ι M →ₗ[R] N` onto the
permutation-invariant multilinear maps `Mⁱ → N`, for every `N`.

As a first use, prepending a fixed factor to a pure tensor is permutation-invariant in the remaining
factors, so it lifts to `SymmetricPower.consMul : M →ₗ[R] Sym[R]^k M →ₗ[R] Sym[R]^(k + 1) M`.
Since `Sym[R]^k M` is indexed by `Fin k`, this part takes the scalars in `Type`.

## Main definitions

* `SymmetricPower.lift`: the linear map on the symmetric power induced by a permutation-invariant
  multilinear map.
* `SymmetricPower.consMul`: multiplication of a symmetric tensor of degree `k` by one more
  factor, the lift of the pure tensor with that factor prepended.

## Main results

* `SymmetricPower.lift_tprod`: `lift f` agrees with `f` on pure symmetric tensors.
* `SymmetricPower.consMul_tprod` and `SymmetricPower.consMul_comm`: `consMul` prepends a factor
  to a pure tensor, and multiplications by two factors commute.
-/

public section

open scoped TensorProduct

universe u v w

variable {R ι : Type u} {M : Type v} {N : Type w}

namespace SymmetricPower

section Lift

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (f : MultilinearMap R (fun _ : ι ↦ M) N)

/-- A permutation-invariant multilinear map takes the same value on a pure tensor and on each of
its reorderings, so it is constant on the classes of the defining relation of the symmetric
power. -/
private theorem lift_rel (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) :
    addConGen (Rel R ι M) ≤ AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.lift.tprod]
      exact (congrFun (congrArg DFunLike.coe (hf e)) m).symm

/-- **The universal property of the symmetric tensor power**: a multilinear map that is unchanged
by permuting its arguments descends to a linear map on the symmetric power. -/
noncomputable def lift (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) : Sym[R] ι M →ₗ[R] N where
  toFun := (addConGen (Rel R ι M)).lift (PiTensorProduct.lift f).toAddMonoidHom (lift_rel f hf)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (PiTensorProduct.lift f).map_smul r x

/-- The descent of a multilinear map commutes with the quotient map from the tensor power. -/
@[simp]
theorem lift_mk (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (x : ⨂[R] (_ : ι), M) :
    lift f hf (mk R ι M x) = PiTensorProduct.lift f x :=
  AddCon.lift_mk' (lift_rel f hf) x

/-- The descent of a multilinear map agrees with it on pure symmetric tensors. -/
@[simp]
theorem lift_tprod (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (m : ι → M) :
    lift f hf (⨂ₛ[R] i, m i) = f m := by
  rw [tprod, LinearMap.compMultilinearMap_apply, lift_mk, PiTensorProduct.lift.tprod]

end Lift

/-! ### Multiplication by one more factor -/

section ConsMul

variable {R : Type} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Prepending a fixed factor to a pure tensor is invariant under permutations of the remaining
factors. -/
theorem tprod_cons_perm_invariant (k : ℕ) (m : M) (e : Equiv.Perm (Fin k)) :
    ((tprod R (ι := Fin (k + 1)) (M := M)).curryLeft m).domDomCongr e =
      (tprod R).curryLeft m := by
  ext v
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.curryLeft_apply]
  rw [← tprod_equiv (Equiv.Perm.decomposeFin.symm (0, e)) (Fin.cons m v)]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  | succ i => simp [Equiv.Perm.decomposeFin_symm_apply_succ]

variable (R M) in
/-- Multiplying a symmetric tensor of degree `k` by one more factor, prepended to every pure
tensor. -/
noncomputable def consMul (k : ℕ) : M →ₗ[R] Sym[R]^k M →ₗ[R] Sym[R]^(k + 1) M where
  toFun m := lift ((tprod R).curryLeft m) (tprod_cons_perm_invariant k m)
  map_add' m m' := SymmetricPower.ext fun v ↦ by
    simp [lift_tprod]
  map_smul' c m := SymmetricPower.ext fun v ↦ by
    simp [lift_tprod]

/-- Multiplying a pure symmetric tensor by one more factor prepends that factor. -/
@[simp]
theorem consMul_tprod (k : ℕ) (m : M) (v : Fin k → M) :
    consMul R M k m (⨂ₛ[R] i, v i) = ⨂ₛ[R] i, (Fin.cons m v : Fin (k + 1) → M) i := by
  simp [consMul, lift_tprod]

/-- Multiplications of a symmetric tensor by two factors commute. -/
theorem consMul_comm (k : ℕ) (m m' : M) (x : Sym[R]^k M) :
    consMul R M (k + 1) m (consMul R M k m' x) = consMul R M (k + 1) m' (consMul R M k m x) := by
  suffices h : consMul R M (k + 1) m ∘ₗ consMul R M k m' =
      consMul R M (k + 1) m' ∘ₗ consMul R M k m from LinearMap.congr_fun h x
  refine SymmetricPower.ext fun v ↦ ?_
  simp only [LinearMap.comp_apply, consMul_tprod]
  rw [← tprod_equiv (Equiv.swap 0 1) (Fin.cons m (Fin.cons m' v))]
  exact congrArg (fun f : Fin (k + 2) → M ↦ ⨂ₛ[R] i, f i)
    (Matrix.cons_cons_comp_swap_zero_one m m' v)

end ConsMul

end SymmetricPower
