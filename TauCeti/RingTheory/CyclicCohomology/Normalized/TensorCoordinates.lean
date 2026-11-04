/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Normalized.Chains
import TauCeti.LinearAlgebra.Multilinear.Quotient
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Tensor coordinates for normalized Hochschild chains

The quotient by degenerate tensors is canonically `A ⊗ (A / R1)^{⊗n}`. The equivalence
`normalizedHochschildChains.tensorEquiv` sends a chain to its zeroth entry tensored with
the quotient classes of all remaining entries. In degree zero the first factor is retained;
only the noninitial factors are divided by the span of the unit.

These are the tensor coordinates of normalized universal differential forms for a unital
algebra. The identification needs only a module with a distinguished element, not a
multiplication. It identifies the existing normalized mixed-chain model with these coordinates;
it does not construct a multiplication or differential on the coordinate space separately.

## References

* J.-L. Loday, *Cyclic Homology*, §1.1 (normalization and noncommutative forms).
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
-/

public section

noncomputable section

namespace TauCeti.normalizedHochschildChains

open PiTensorProduct
open scoped TensorProduct

variable (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] [One A]

private def coordinateTensor (n : ℕ) :
    MultilinearMap R (fun _ : Fin (n + 1) ↦ A)
      (A ⊗[R] (⨂[R] (_ : Fin n), A ⧸ Submodule.span R {(1 : A)})) :=
  LinearMap.uncurryLeft
    { toFun := fun a ↦ ((TensorProduct.mk R A _) a).compMultilinearMap
        ((tprod R).compLinearMap (fun _ ↦ (Submodule.span R {(1 : A)}).mkQ))
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

private theorem coordinateTensor_apply {n : ℕ} (a : Fin (n + 1) → A) :
    coordinateTensor R A n a = a 0 ⊗ₜ[R]
      tprod R (fun i : Fin n ↦ (Submodule.span R {(1 : A)}).mkQ (a i.succ)) := (rfl)

private theorem coordinateTensor_normalized (n : ℕ) :
    coordinateTensor R A n ∈ normalizedHochschildCochains R A _ n := by
  rw [mem_normalizedHochschildCochains_iff]
  intro a i hi ha
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  rw [coordinateTensor_apply]
  have h : (Submodule.span R {(1 : A)}).mkQ (a j.succ) = 0 := by
    rw [ha, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [(tprod R).map_coord_zero j h, TensorProduct.tmul_zero]

private theorem tensor_curryLeft_update_span {n : ℕ} (a : A)
    [DecidableEq (Fin n)] (m : Fin n → A) (i : Fin n) (x : A)
    (hx : x ∈ Submodule.span R {(1 : A)}) :
    (tensor R A n).curryLeft a (Function.update m i x) = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [MultilinearMap.map_update_smul, MultilinearMap.curryLeft_apply]
  have h : (Fin.cons a (Function.update m i 1) : Fin (n + 1) → A) i.succ = 1 := by simp
  rw [tensor_eq_zero R A _ i.succ (Fin.succ_ne_zero _) h, smul_zero]

private def quotientTensor (n : ℕ) : A →ₗ[R]
    MultilinearMap R (fun _ : Fin n ↦ A ⧸ Submodule.span R {(1 : A)})
      (normalizedHochschildChains R A n) where
  toFun a := ((tensor R A n).curryLeft a).liftQ
    (fun _ ↦ Submodule.span R {(1 : A)}) (tensor_curryLeft_update_span R A a)
  map_add' a b := by
    apply MultilinearMap.compLinearMap_injective
      (fun _ ↦ (Submodule.span R {(1 : A)}).mkQ) (fun _ ↦ Submodule.mkQ_surjective _)
    ext m
    simpa only [MultilinearMap.compLinearMap_apply, add_apply,
      Submodule.mkQ_apply, MultilinearMap.liftQ_apply] using
      congrArg (fun f ↦ f m) ((tensor R A n).curryLeft.map_add a b)
  map_smul' r a := by
    apply MultilinearMap.compLinearMap_injective
      (fun _ ↦ (Submodule.span R {(1 : A)}).mkQ) (fun _ ↦ Submodule.mkQ_surjective _)
    ext m
    simpa only [MultilinearMap.compLinearMap_apply, smul_apply,
      Submodule.mkQ_apply, MultilinearMap.liftQ_apply, RingHom.id_apply] using
      congrArg (fun f ↦ f m) ((tensor R A n).curryLeft.map_smul r a)

private theorem quotientTensor_mkQ {n : ℕ} (a : A) (m : Fin n → A) :
    quotientTensor R A n a (fun i ↦ (Submodule.span R {(1 : A)}).mkQ (m i)) =
      tensor R A n (Fin.cons a m) := by
  simp [quotientTensor, MultilinearMap.curryLeft_apply]

private def fromCoordinates (n : ℕ) :
    (A ⊗[R] (⨂[R] (_ : Fin n), A ⧸ Submodule.span R {(1 : A)})) →ₗ[R]
      normalizedHochschildChains R A n :=
  TensorProduct.lift (PiTensorProduct.lift.toLinearMap.comp (quotientTensor R A n))

private theorem fromCoordinates_tmul {n : ℕ} (a : A) (m : Fin n → A) :
    fromCoordinates R A n
      (a ⊗ₜ[R] tprod R (fun i ↦ (Submodule.span R {(1 : A)}).mkQ (m i))) =
      tensor R A n (Fin.cons a m) := by
  simp only [fromCoordinates, TensorProduct.lift.tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, PiTensorProduct.lift.tprod, quotientTensor_mkQ]

/-- Normalized Hochschild chains are tensors with the noninitial factors divided by the
span of the unit. The zeroth factor is not divided out. -/
def tensorEquiv (n : ℕ) : normalizedHochschildChains R A n ≃ₗ[R]
    A ⊗[R] (⨂[R] (_ : Fin n), A ⧸ Submodule.span R {(1 : A)}) :=
  LinearEquiv.ofLinearMap
    (lift ⟨coordinateTensor R A n, coordinateTensor_normalized R A n⟩)
    (fromCoordinates R A n)
    (by
      apply TensorProduct.ext
      apply LinearMap.ext
      intro a
      apply PiTensorProduct.ext
      ext q
      choose m hm using fun i ↦ (Submodule.span R {(1 : A)}).mkQ_surjective (q i)
      rw [← funext hm]
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂ₛₗ_apply,
        TensorProduct.mk_apply, LinearMap.comp_apply, LinearMap.id_apply]
      rw [fromCoordinates_tmul, lift_tensor, coordinateTensor_apply]
      simp)
    (by
      apply hom_ext
      intro a
      simp only [LinearMap.comp_apply, LinearMap.id_apply, lift_tensor,
        coordinateTensor_apply, fromCoordinates_tmul]
      exact congrArg (tensor R A n) (Fin.cons_self_tail a))

/-- The tensor-coordinate equivalence keeps the initial entry and quotients all other entries. -/
@[simp]
theorem tensorEquiv_tensor {n : ℕ} (a : Fin (n + 1) → A) :
    tensorEquiv R A n (tensor R A n a) = a 0 ⊗ₜ[R]
      tprod R (fun i : Fin n ↦ (Submodule.span R {(1 : A)}).mkQ (a i.succ)) := by
  simp only [tensorEquiv, LinearEquiv.coe_ofLinearMap, lift_tensor, coordinateTensor_apply]

/-- The inverse coordinate map forms the normalized chain from any representatives of the
noninitial quotient classes. -/
@[simp]
theorem tensorEquiv_symm_tmul {n : ℕ} (a : A) (m : Fin n → A) :
    (tensorEquiv R A n).symm
      (a ⊗ₜ[R] tprod R (fun i ↦ Submodule.Quotient.mk (m i))) =
        tensor R A n (Fin.cons a m) := by
  apply (tensorEquiv R A n).injective
  simp

end TauCeti.normalizedHochschildChains
