/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.RingTheory.PiTensorProduct.Equiv
public import TauCeti.RingTheory.PiTensorProduct.FiberwiseMul

/-!
# Base change of finite tensor products of commutative algebras

For a finite family of commutative `R`-algebras `A i` and a commutative `R`-algebra `T`, scalar
extension commutes with the tensor product of the family:

  `T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i)`,   `t ⊗ (⨂ₜ aᵢ) ↦ t • ⨂ₜ (1 ⊗ aᵢ)`.

Geometrically, the fibre product over `Spec R` of the `Spec (A i)` pulls back to the fibre
product over `Spec T` of their base changes. Both sides are coproducts of commutative algebras, so
the equivalence is determined by the factor inclusions
(`PiTensorProduct.baseChangeAlgEquiv_one_tmul_singleAlgHom`).

## Main definitions

* `PiTensorProduct.baseChangeAlgEquiv`: the base change equivalence.

## Main results

* `PiTensorProduct.baseChangeAlgEquiv_tmul_tprod`: its value on pure tensors.
* `PiTensorProduct.baseChangeAlgEquiv_map_permAlgEquiv`: for a tensor power, base change commutes
  with permuting the factors.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] (T : Type*) [CommSemiring T] [Algebra R T]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Type*) [∀ i, CommSemiring (A i)]
  [∀ i, Algebra R (A i)]

/-- The `R`-algebra map `⨂[R] i, A i → ⨂[T] i, (T ⊗[R] A i)` placing each factor `aᵢ` as `1 ⊗ aᵢ`
in its own slot. -/
private noncomputable def toBaseChange : (⨂[R] i, A i) →ₐ[R] ⨂[T] i, (T ⊗[R] A i) :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra R ι (⨂[T] i, (T ⊗[R] A i))).compLinearMap
      fun i ↦ (((singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i).restrictScalars R).comp
        Algebra.TensorProduct.includeRight).toLinearMap)
    (by simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, Pi.one_apply, map_one, Finset.prod_const_one])
    fun x y ↦ by simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

private theorem toBaseChange_tprod (x : ∀ i, A i) :
    toBaseChange T A (tprod R x) = ∏ i, singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i
      (1 ⊗ₜ x i) :=
  (liftAlgHom_apply _ _ _ _).trans (lift.tprod _)

private theorem toBaseChange_singleAlgHom (i : ι) (a : A i) :
    toBaseChange T A (singleAlgHom i a) = singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i
      (1 ⊗ₜ a) := by
  rw [singleAlgHom_apply, toBaseChange_tprod, Finset.prod_eq_single i (fun j _ hj ↦ ?_) (by simp),
    MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, ← Algebra.TensorProduct.one_def,
    map_one]

/-- The `T`-algebra map `⨂[T] i, (T ⊗[R] A i) → T ⊗[R] (⨂[R] i, A i)` sending `t ⊗ aᵢ` in the
slot `i` to `t ⊗ aᵢ` with `aᵢ` in the slot `i`. -/
private noncomputable def ofBaseChange : (⨂[T] i, (T ⊗[R] A i)) →ₐ[T] T ⊗[R] (⨂[R] i, A i) :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra T ι (T ⊗[R] (⨂[R] i, A i))).compLinearMap
      fun i ↦ (Algebra.TensorProduct.map (AlgHom.id T T) (singleAlgHom i)).toLinearMap)
    (by simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, Pi.one_apply, map_one, Finset.prod_const_one])
    fun x y ↦ by simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

private theorem ofBaseChange_tprod (x : ∀ i, T ⊗[R] A i) :
    ofBaseChange T A (tprod T x) =
      ∏ i, Algebra.TensorProduct.map (AlgHom.id T T) (singleAlgHom i) (x i) :=
  (liftAlgHom_apply _ _ _ _).trans (lift.tprod _)

private theorem ofBaseChange_singleAlgHom (i : ι) (x : T ⊗[R] A i) :
    ofBaseChange T A (singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i x) =
      Algebra.TensorProduct.map (AlgHom.id T T) (singleAlgHom i) x := by
  rw [singleAlgHom_apply, ofBaseChange_tprod, Finset.prod_eq_single i (fun j _ hj ↦ ?_) (by simp),
    MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, map_one]

/-- Scalar extension commutes with finite tensor products of commutative algebras:
`T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i)`, sending `t ⊗ (⨂ₜ aᵢ)` to `t • ⨂ₜ (1 ⊗ aᵢ)`. -/
noncomputable def baseChangeAlgEquiv : T ⊗[R] (⨂[R] i, A i) ≃ₐ[T] ⨂[T] i, (T ⊗[R] A i) :=
  AlgEquiv.ofAlgHom (AlgHom.liftEquiv R T _ _ (toBaseChange T A)) (ofBaseChange T A)
    (algHom_ext fun i ↦ Algebra.TensorProduct.ext_ring <| AlgHom.ext fun a ↦ by
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
      rw [ofBaseChange_singleAlgHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgHom.liftEquiv_tmul, one_smul, toBaseChange_singleAlgHom])
    (Algebra.TensorProduct.ext_ring <| algHom_ext fun i ↦ AlgHom.ext fun a ↦ by
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
      rw [AlgHom.liftEquiv_tmul, one_smul, toBaseChange_singleAlgHom, ofBaseChange_singleAlgHom,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply])

/-- `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ (⨂ₜ aᵢ)` to `t • ⨂ₜ (1 ⊗ aᵢ)`. -/
@[simp]
theorem baseChangeAlgEquiv_tmul_tprod (t : T) (x : ∀ i, A i) :
    baseChangeAlgEquiv T A (t ⊗ₜ tprod R x) = t • tprod T fun i ↦ (1 : T) ⊗ₜ[R] x i := by
  rw [baseChangeAlgEquiv, AlgEquiv.ofAlgHom_apply, AlgHom.liftEquiv_tmul, toBaseChange_tprod,
    ← tprod_eq_prod_singleAlgHom]

/-- `PiTensorProduct.baseChangeAlgEquiv` sends `1 ⊗ a`, with `a` in the slot `i`, to `1 ⊗ a` in the
slot `i`. -/
@[simp↓]
theorem baseChangeAlgEquiv_one_tmul_singleAlgHom (i : ι) (a : A i) :
    baseChangeAlgEquiv T A (1 ⊗ₜ singleAlgHom i a) =
      singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i (1 ⊗ₜ a) := by
  rw [baseChangeAlgEquiv, AlgEquiv.ofAlgHom_apply, AlgHom.liftEquiv_tmul, one_smul,
    toBaseChange_singleAlgHom]

/-- The inverse of `PiTensorProduct.baseChangeAlgEquiv` sends `t ⊗ a` in the slot `i` to `t ⊗ a`,
with `a` in the slot `i`. -/
@[simp↓]
theorem baseChangeAlgEquiv_symm_singleAlgHom (i : ι) (x : T ⊗[R] A i) :
    (baseChangeAlgEquiv T A).symm (singleAlgHom (R := T) (A := fun i ↦ T ⊗[R] A i) i x) =
      Algebra.TensorProduct.map (AlgHom.id T T) (singleAlgHom i) x :=
  ofBaseChange_singleAlgHom T A i x

/-- Base change commutes with permuting the factors of a tensor power. -/
theorem baseChangeAlgEquiv_map_permAlgEquiv {B : Type*} [CommSemiring B] [Algebra R B]
    (σ : Equiv.Perm ι) (x : T ⊗[R] (⨂[R] _ : ι, B)) :
    baseChangeAlgEquiv T (fun _ ↦ B)
        (Algebra.TensorProduct.map (AlgHom.id T T) (permAlgEquiv B σ).toAlgHom x) =
      permAlgEquiv (T ⊗[R] B) σ (baseChangeAlgEquiv T (fun _ ↦ B) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r y =>
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      generalize r • t = t
      simp [Function.comp_def]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

end PiTensorProduct
