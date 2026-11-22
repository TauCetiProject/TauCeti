/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode

/-!
# Tensor products with projective modules over a Hopf algebra

Let `H` be a Hopf algebra over a commutative semiring `R`, and let `H` act on tensor products of
modules through its coproduct (`TauCeti.BialgebraModule.Tensor`). For an `R`-module `V`, the
induced module `H ⊗[R] V`, on which `H` acts by left multiplication on the first factor, absorbs
tensor products: for every `H`-module `M` there are `H`-linear equivalences

* `TauCeti.BialgebraModule.baseChangeTensorEquiv`: `(H ⊗[R] V) ⊗ M ≃ H ⊗[R] (V ⊗[R] M)`, whose
  inverse is `h ⊗ (v ⊗ m) ↦ ∑ (h₁ ⊗ v) ⊗ h₂ • m`;
* `TauCeti.BialgebraModule.tensorBaseChangeEquiv`: `M ⊗ (H ⊗[R] V) ≃ H ⊗[R] (M ⊗[R] V)`, whose
  inverse is `h ⊗ (m ⊗ v) ↦ ∑ h₁ • m ⊗ (h₂ ⊗ v)`, when the antipode is bijective.

The inverse maps are `H`-linear for any bialgebra; the antipode, respectively its inverse, is
needed to invert them. Since every projective `H`-module is a retract of an induced module
`H ⊗[R] (ι →₀ R)`, it follows that `P ⊗ M` is projective whenever `P` is projective over `H` and
`M` is projective over `R` (`TauCeti.BialgebraModule.projective_tensor_left`), and likewise
`M ⊗ P` when the antipode is bijective (`TauCeti.BialgebraModule.projective_tensor_right`). Over a
field the condition on `M` is automatic.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 2.
* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Lemma 2.3.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS 82, AMS, 1993, Section 1.9.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti.BialgebraModule

variable (R H : Type*) [CommSemiring R]

section Bialgebra

variable [Semiring H] [Bialgebra R H]
  (V : Type*) [AddCommMonoid V] [Module R V]
  (M : Type*) [AddCommMonoid M] [Module R M] [Module H M] [IsScalarTower R H M]

/-- `(a ⊗ b) ⊗ (v ⊗ m) ↦ (a ⊗ v) ⊗ b • m`. -/
private noncomputable def shearLeftCore : (H ⊗[R] H) ⊗[R] (V ⊗[R] M) →ₗ[R] (H ⊗[R] V) ⊗[R] M :=
  TensorProduct.map LinearMap.id (TensorProduct.lift (Algebra.lsmul R R M).toLinearMap) ∘ₗ
    (TensorProduct.tensorTensorTensorComm R H H V M).toLinearMap

private theorem shearLeftCore_tmul (a b : H) (v : V) (m : M) :
    shearLeftCore R H V M ((a ⊗ₜ b) ⊗ₜ (v ⊗ₜ m)) = (a ⊗ₜ v) ⊗ₜ (b • m) := by
  simp [shearLeftCore]

private theorem shearLeftCore_mul (t s : H ⊗[R] H) (w : V ⊗[R] M) :
    shearLeftCore R H V M ((t * s) ⊗ₜ w) =
      tensorPairAction R (H ⊗[R] V) M t (shearLeftCore R H V M (s ⊗ₜ w)) := by
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
  | tmul v m =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [add_mul, TensorProduct.add_tmul, map_add, ht, ht',
        LinearMap.add_apply]
    | tmul a b =>
      induction s using TensorProduct.inductionOn with
      | add s s' hs hs' => simp only [mul_add, TensorProduct.add_tmul, map_add, hs, hs']
      | tmul c d =>
        simp [shearLeftCore_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_smul,
          TensorProduct.smul_tmul']

/-- `h ⊗ (v ⊗ m) ↦ ∑ (h₁ ⊗ v) ⊗ h₂ • m`. -/
private noncomputable def shearLeft : H ⊗[R] (V ⊗[R] M) →ₗ[R] (H ⊗[R] V) ⊗[R] M :=
  shearLeftCore R H V M ∘ₗ comul.rTensor (V ⊗[R] M)

private theorem shearLeft_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (v : V) (m : M) :
    shearLeft R H V M (h ⊗ₜ (v ⊗ₜ m)) =
      ∑ i ∈ r.index, (r.left i ⊗ₜ v) ⊗ₜ (r.right i • m) := by
  simp [shearLeft, ← r.eq, TensorProduct.sum_tmul, map_sum, shearLeftCore_tmul]

private theorem shearLeft_smul (g : H) (x : H ⊗[R] (V ⊗[R] M)) :
    shearLeft R H V M (g • x) =
      tensorPairAction R (H ⊗[R] V) M (comul g) (shearLeft R H V M x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul h w =>
    simp [shearLeft, TensorProduct.smul_tmul', Bialgebra.comul_mul, shearLeftCore_mul]

/-- `(a ⊗ b) ⊗ (m ⊗ v) ↦ a • m ⊗ (b ⊗ v)`. -/
private noncomputable def shearRightCore :
    (H ⊗[R] H) ⊗[R] (M ⊗[R] V) →ₗ[R] M ⊗[R] (H ⊗[R] V) :=
  TensorProduct.map (TensorProduct.lift (Algebra.lsmul R R M).toLinearMap) LinearMap.id ∘ₗ
    (TensorProduct.tensorTensorTensorComm R H H M V).toLinearMap

private theorem shearRightCore_tmul (a b : H) (m : M) (v : V) :
    shearRightCore R H V M ((a ⊗ₜ b) ⊗ₜ (m ⊗ₜ v)) = (a • m) ⊗ₜ (b ⊗ₜ v) := by
  simp [shearRightCore]

private theorem shearRightCore_mul (t s : H ⊗[R] H) (w : M ⊗[R] V) :
    shearRightCore R H V M ((t * s) ⊗ₜ w) =
      tensorPairAction R M (H ⊗[R] V) t (shearRightCore R H V M (s ⊗ₜ w)) := by
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
  | tmul m v =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [add_mul, TensorProduct.add_tmul, map_add, ht, ht',
        LinearMap.add_apply]
    | tmul a b =>
      induction s using TensorProduct.inductionOn with
      | add s s' hs hs' => simp only [mul_add, TensorProduct.add_tmul, map_add, hs, hs']
      | tmul c d =>
        simp [shearRightCore_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_smul,
          TensorProduct.smul_tmul']

/-- `h ⊗ (m ⊗ v) ↦ ∑ h₁ • m ⊗ (h₂ ⊗ v)`. -/
private noncomputable def shearRight : H ⊗[R] (M ⊗[R] V) →ₗ[R] M ⊗[R] (H ⊗[R] V) :=
  shearRightCore R H V M ∘ₗ comul.rTensor (M ⊗[R] V)

private theorem shearRight_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (m : M) (v : V) :
    shearRight R H V M (h ⊗ₜ (m ⊗ₜ v)) =
      ∑ i ∈ r.index, (r.left i • m) ⊗ₜ (r.right i ⊗ₜ v) := by
  simp [shearRight, ← r.eq, TensorProduct.sum_tmul, map_sum, shearRightCore_tmul]

private theorem shearRight_smul (g : H) (x : H ⊗[R] (M ⊗[R] V)) :
    shearRight R H V M (g • x) =
      tensorPairAction R M (H ⊗[R] V) (comul g) (shearRight R H V M x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul h w =>
    simp [shearRight, TensorProduct.smul_tmul', Bialgebra.comul_mul, shearRightCore_mul]

end Bialgebra

section HopfAlgebra

variable [Semiring H] [HopfAlgebra R H]
  (V : Type*) [AddCommMonoid V] [Module R V]
  (M : Type*) [AddCommMonoid M] [Module R M] [Module H M] [IsScalarTower R H M]

/-- `(h ⊗ v) ⊗ m ↦ ∑ h₁ ⊗ (v ⊗ S(h₂) • m)`. -/
private noncomputable def unshearLeft : (H ⊗[R] V) ⊗[R] M →ₗ[R] H ⊗[R] (V ⊗[R] M) :=
  (TensorProduct.assoc R H V M).toLinearMap ∘ₗ shearLeftCore R H V M ∘ₗ
    (TensorProduct.map LinearMap.id (HopfAlgebra.antipode R)).rTensor (V ⊗[R] M) ∘ₗ
    comul.rTensor (V ⊗[R] M) ∘ₗ (TensorProduct.assoc R H V M).toLinearMap

private theorem unshearLeft_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (v : V) (m : M) :
    unshearLeft R H V M ((h ⊗ₜ v) ⊗ₜ m) =
      ∑ i ∈ r.index, r.left i ⊗ₜ (v ⊗ₜ (HopfAlgebra.antipode R (r.right i) • m)) := by
  simp [unshearLeft, ← r.eq, TensorProduct.sum_tmul, map_sum, shearLeftCore_tmul]

private theorem unshearLeft_shearLeft (x : H ⊗[R] (V ⊗[R] M)) :
    unshearLeft R H V M (shearLeft R H V M x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul h w =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | tmul v m =>
      let r := ℛ R h
      -- Coassociativity, pushed through `x ⊗ (y ⊗ z) ↦ x ⊗ (v ⊗ (S(y) * z) • m)`; then
      -- `∑ S(h₁) * h₂ = ε(h)` and the counit law.
      have key := congrArg (LinearMap.lTensor H ((TensorProduct.mk R V M v) ∘ₗ
        (LinearMap.toSpanSingleton H M m).restrictScalars R ∘ₗ LinearMap.mul' R H ∘ₗ
          (HopfAlgebra.antipode R).rTensor H))
        (sum_tmul_tmul_eq r (fun i => ℛ R (r.left i)) (fun i => ℛ R (r.right i)))
      have hc := congrArg (LinearMap.lTensor H ((TensorProduct.mk R V M v) ∘ₗ
        LinearMap.toSpanSingleton R M m)) (sum_tmul_counit_eq r)
      simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.rTensor_tmul, LinearMap.mul'_apply, LinearMap.coe_restrictScalars,
        LinearMap.toSpanSingleton_apply, TensorProduct.mk_apply, one_smul] at key hc
      simp only [shearLeft_tmul R H V M r, unshearLeft_tmul R H V M (ℛ R _), map_sum, ← mul_smul]
      rw [key]
      simp only [← TensorProduct.tmul_sum, ← Finset.sum_smul, HopfAlgebra.sum_antipode_mul_eq_smul,
        smul_one_smul, hc]

private theorem shearLeft_unshearLeft (x : (H ⊗[R] V) ⊗[R] M) :
    shearLeft R H V M (unshearLeft R H V M x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul y m =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [TensorProduct.add_tmul, map_add, hy, hy']
    | tmul h v =>
      let r := ℛ R h
      -- Coassociativity, pushed through `x ⊗ (y ⊗ z) ↦ (x ⊗ v) ⊗ (y * S(z)) • m`; then
      -- `∑ h₁ * S(h₂) = ε(h)` and the counit law.
      have key := congrArg (TensorProduct.map ((TensorProduct.mk R H V).flip v)
        ((LinearMap.toSpanSingleton H M m).restrictScalars R ∘ₗ LinearMap.mul' R H ∘ₗ
          (HopfAlgebra.antipode R).lTensor H))
        (sum_tmul_tmul_eq r (fun i => ℛ R (r.left i)) (fun i => ℛ R (r.right i)))
      have hc := congrArg (TensorProduct.map ((TensorProduct.mk R H V).flip v)
        (LinearMap.toSpanSingleton R M m)) (sum_tmul_counit_eq r)
      simp only [map_sum, TensorProduct.map_tmul, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.lTensor_tmul, LinearMap.mul'_apply, LinearMap.coe_restrictScalars,
        LinearMap.toSpanSingleton_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        one_smul] at key hc
      simp only [unshearLeft_tmul R H V M r, map_sum, shearLeft_tmul R H V M (ℛ R _), ← mul_smul]
      rw [key]
      simp only [← TensorProduct.tmul_sum, ← Finset.sum_smul, HopfAlgebra.sum_mul_antipode_eq_smul,
        smul_one_smul, hc]

/-- For an `R`-module `V`, the tensor product of the induced module `H ⊗[R] V` with any module
`M` is the induced module `H ⊗[R] (V ⊗[R] M)`. The inverse sends `h ⊗ (v ⊗ m)` to
`∑ (h₁ ⊗ v) ⊗ h₂ • m` (`baseChangeTensorEquiv_symm_tmul`), and this equivalence sends
`(h ⊗ v) ⊗ m` to `∑ h₁ ⊗ (v ⊗ S(h₂) • m)` (`baseChangeTensorEquiv_tmul`). -/
noncomputable def baseChangeTensorEquiv :
    Tensor R H (H ⊗[R] V) M ≃ₗ[H] H ⊗[R] (V ⊗[R] M) :=
  LinearEquiv.symm
    { toFun x := (tensorEquiv R H (H ⊗[R] V) M).symm (shearLeft R H V M x)
      map_add' x y := by simp
      map_smul' g x := (tensorEquiv R H (H ⊗[R] V) M).injective <| by
        simp [shearLeft_smul, tensorAction_apply]
      invFun y := unshearLeft R H V M (tensorEquiv R H (H ⊗[R] V) M y)
      left_inv x := by simp [unshearLeft_shearLeft]
      right_inv y := by simp [shearLeft_unshearLeft] }

/-- `baseChangeTensorEquiv` on a pure tensor, through any representation of the coproduct. -/
theorem baseChangeTensorEquiv_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (v : V)
    (m : M) :
    baseChangeTensorEquiv R H V M (tmul R H (h ⊗ₜ v) m) =
      ∑ i ∈ r.index, r.left i ⊗ₜ (v ⊗ₜ (HopfAlgebra.antipode R (r.right i) • m)) := by
  simp [baseChangeTensorEquiv, unshearLeft_tmul R H V M r]

/-- The inverse of `baseChangeTensorEquiv` on a pure tensor, through any representation of the
coproduct. -/
theorem baseChangeTensorEquiv_symm_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (v : V)
    (m : M) :
    (baseChangeTensorEquiv R H V M).symm (h ⊗ₜ (v ⊗ₜ m)) =
      ∑ i ∈ r.index, tmul R H (r.left i ⊗ₜ v) (r.right i • m) := by
  simp [baseChangeTensorEquiv, shearLeft_tmul R H V M r, map_sum]

section InverseAntipode

variable (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))

/-- `m ⊗ (h ⊗ v) ↦ ∑ h₂ ⊗ (S⁻¹(h₁) • m ⊗ v)`. -/
private noncomputable def unshearRight : M ⊗[R] (H ⊗[R] V) →ₗ[R] H ⊗[R] (M ⊗[R] V) :=
  (TensorProduct.leftComm R M H V).toLinearMap ∘ₗ shearRightCore R H V M ∘ₗ
    (TensorProduct.map (TauCeti.HopfAlgebra.inverseAntipode hS) LinearMap.id).rTensor
      (M ⊗[R] V) ∘ₗ
    comul.rTensor (M ⊗[R] V) ∘ₗ (TensorProduct.leftComm R M H V).toLinearMap

private theorem unshearRight_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (m : M) (v : V) :
    unshearRight R H V M hS (m ⊗ₜ (h ⊗ₜ v)) =
      ∑ i ∈ r.index,
        r.right i ⊗ₜ ((TauCeti.HopfAlgebra.inverseAntipode hS (r.left i) • m) ⊗ₜ v) := by
  simp [unshearRight, ← r.eq, TensorProduct.sum_tmul, map_sum, shearRightCore_tmul]

private theorem unshearRight_shearRight (x : H ⊗[R] (M ⊗[R] V)) :
    unshearRight R H V M hS (shearRight R H V M x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul h w =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | tmul m v =>
      let r := ℛ R h
      -- Coassociativity, pushed through `x ⊗ (y ⊗ z) ↦ z ⊗ ((S⁻¹(y) * x) • m ⊗ v)`; then
      -- `∑ S⁻¹(h₂) * h₁ = ε(h)` and the counit law.
      have key := congrArg ((TensorProduct.comm R (M ⊗[R] V) H).toLinearMap ∘ₗ
        (((TensorProduct.mk R M V).flip v ∘ₗ (LinearMap.toSpanSingleton H M m).restrictScalars R ∘ₗ
          LinearMap.mul' R H ∘ₗ (TauCeti.HopfAlgebra.inverseAntipode hS).rTensor H ∘ₗ
            (TensorProduct.comm R H H).toLinearMap).rTensor H) ∘ₗ
        (TensorProduct.assoc R H H H).symm.toLinearMap)
        (sum_tmul_tmul_eq r (fun i => ℛ R (r.left i)) (fun i => ℛ R (r.right i)))
      have hc := congrArg ((TensorProduct.comm R (M ⊗[R] V) H).toLinearMap ∘ₗ
        TensorProduct.map ((TensorProduct.mk R M V).flip v ∘ₗ LinearMap.toSpanSingleton R M m)
          LinearMap.id) (sum_counit_tmul_eq r)
      simp only [map_sum, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.comm_tmul,
        TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.coe_restrictScalars,
        LinearMap.toSpanSingleton_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        LinearMap.id_apply, one_smul] at key hc
      simp only [shearRight_tmul R H V M r, map_sum, unshearRight_tmul R H V M hS (ℛ R _),
        ← mul_smul]
      rw [← key]
      simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ← Finset.sum_smul,
        TauCeti.HopfAlgebra.sum_inverseAntipode_mul_eq_smul hS, smul_one_smul, hc]

private theorem shearRight_unshearRight (x : M ⊗[R] (H ⊗[R] V)) :
    shearRight R H V M (unshearRight R H V M hS x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m y =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | tmul h v =>
      let r := ℛ R h
      -- Coassociativity, pushed through `x ⊗ (y ⊗ z) ↦ (y * S⁻¹(x)) • m ⊗ (z ⊗ v)`; then
      -- `∑ h₂ * S⁻¹(h₁) = ε(h)` and the counit law.
      have key := congrArg
        (TensorProduct.map ((LinearMap.toSpanSingleton H M m).restrictScalars R ∘ₗ
            LinearMap.mul' R H ∘ₗ (TensorProduct.comm R H H).toLinearMap ∘ₗ
              (TauCeti.HopfAlgebra.inverseAntipode hS).rTensor H)
          ((TensorProduct.mk R H V).flip v) ∘ₗ
        (TensorProduct.assoc R H H H).symm.toLinearMap)
        (sum_tmul_tmul_eq r (fun i => ℛ R (r.left i)) (fun i => ℛ R (r.right i)))
      have hc := congrArg (TensorProduct.map (LinearMap.toSpanSingleton R M m)
        ((TensorProduct.mk R H V).flip v)) (sum_counit_tmul_eq r)
      simp only [map_sum, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.comm_tmul,
        TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.coe_restrictScalars,
        LinearMap.toSpanSingleton_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        one_smul] at key hc
      simp only [unshearRight_tmul R H V M hS r, map_sum, shearRight_tmul R H V M (ℛ R _),
        ← mul_smul]
      rw [← key]
      simp only [← TensorProduct.sum_tmul, ← Finset.sum_smul,
        TauCeti.HopfAlgebra.sum_mul_inverseAntipode_eq_smul hS, smul_one_smul, hc]

/-- For an `R`-module `V` and a Hopf algebra with bijective antipode, the tensor product of any
module `M` with the induced module `H ⊗[R] V` is the induced module `H ⊗[R] (M ⊗[R] V)`. The
inverse sends `h ⊗ (m ⊗ v)` to `∑ h₁ • m ⊗ (h₂ ⊗ v)` (`tensorBaseChangeEquiv_symm_tmul`), and this
equivalence sends `m ⊗ (h ⊗ v)` to `∑ h₂ ⊗ (S⁻¹(h₁) • m ⊗ v)` (`tensorBaseChangeEquiv_tmul`). -/
noncomputable def tensorBaseChangeEquiv :
    Tensor R H M (H ⊗[R] V) ≃ₗ[H] H ⊗[R] (M ⊗[R] V) :=
  LinearEquiv.symm
    { toFun x := (tensorEquiv R H M (H ⊗[R] V)).symm (shearRight R H V M x)
      map_add' x y := by simp
      map_smul' g x := (tensorEquiv R H M (H ⊗[R] V)).injective <| by
        simp [shearRight_smul, tensorAction_apply]
      invFun y := unshearRight R H V M hS (tensorEquiv R H M (H ⊗[R] V) y)
      left_inv x := by simp [unshearRight_shearRight]
      right_inv y := by simp [shearRight_unshearRight] }

/-- `tensorBaseChangeEquiv` on a pure tensor, through any representation of the coproduct. -/
theorem tensorBaseChangeEquiv_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (m : M)
    (v : V) :
    tensorBaseChangeEquiv R H V M hS (tmul R H m (h ⊗ₜ v)) =
      ∑ i ∈ r.index,
        r.right i ⊗ₜ ((TauCeti.HopfAlgebra.inverseAntipode hS (r.left i) • m) ⊗ₜ v) := by
  simp [tensorBaseChangeEquiv, unshearRight_tmul R H V M hS r]

/-- The inverse of `tensorBaseChangeEquiv` on a pure tensor, through any representation of the
coproduct. -/
theorem tensorBaseChangeEquiv_symm_tmul {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (m : M)
    (v : V) :
    (tensorBaseChangeEquiv R H V M hS).symm (h ⊗ₜ (m ⊗ₜ v)) =
      ∑ i ∈ r.index, tmul R H (r.left i • m) (r.right i ⊗ₜ v) := by
  simp [tensorBaseChangeEquiv, shearRight_tmul R H V M r, map_sum]

end InverseAntipode

end HopfAlgebra

section Projective

variable {R H} [Semiring H] [HopfAlgebra R H]
  {P M : Type*} [AddCommMonoid P] [Module R P] [Module H P] [IsScalarTower R H P]
  [AddCommMonoid M] [Module R M] [Module H M] [IsScalarTower R H M]

/-- Over a Hopf algebra, the tensor product `P ⊗ M` of a projective module `P` with a module `M`
that is projective over the base ring is projective. -/
instance projective_tensor_left [Module.Projective H P] [Module.Projective R M] :
    Module.Projective H (Tensor R H P M) := by
  classical
  -- `P` is a retract of `P →₀ H ≃ H ⊗[R] (P →₀ R)`, and `baseChangeTensorEquiv` makes
  -- `(H ⊗[R] (P →₀ R)) ⊗ M` an induced module.
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective H P›
  let e := TensorProduct.finsuppScalarRight R H H P
  refine Module.Projective.of_split
    ((baseChangeTensorEquiv R H (P →₀ R) M).toLinearMap ∘ₗ
      tensorMap R H (e.symm.toLinearMap ∘ₗ s) LinearMap.id)
    (tensorMap R H (Finsupp.linearCombination H id ∘ₗ e.toLinearMap) LinearMap.id ∘ₗ
      (baseChangeTensorEquiv R H (P →₀ R) M).symm.toLinearMap) ?_
  ext p m
  simpa using congrArg (tmul R H · m) (LinearMap.congr_fun hs p)

/-- Over a Hopf algebra with bijective antipode, the tensor product `M ⊗ P` of a module `M` that
is projective over the base ring with a projective module `P` is projective. -/
theorem projective_tensor_right (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    [Module.Projective H P] [Module.Projective R M] :
    Module.Projective H (Tensor R H M P) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective H P›
  let e := TensorProduct.finsuppScalarRight R H H P
  refine Module.Projective.of_split
    ((tensorBaseChangeEquiv R H (P →₀ R) M hS).toLinearMap ∘ₗ
      tensorMap R H LinearMap.id (e.symm.toLinearMap ∘ₗ s))
    (tensorMap R H LinearMap.id (Finsupp.linearCombination H id ∘ₗ e.toLinearMap) ∘ₗ
      (tensorBaseChangeEquiv R H (P →₀ R) M hS).symm.toLinearMap) ?_
  ext m p
  simpa using congrArg (tmul R H m ·) (LinearMap.congr_fun hs p)

end Projective

end TauCeti.BialgebraModule
