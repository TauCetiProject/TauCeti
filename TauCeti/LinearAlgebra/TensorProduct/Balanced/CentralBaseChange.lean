/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import TauCeti.RingTheory.TensorProduct.CentralBaseChange

/-!
# Balanced extension and central base change

For a commutative `A`-algebra `S` and a possibly noncommutative `A`-algebra `Λ`, the central
base change `S ⊗[A] M` of a left `Λ`-module is extension of scalars along
`Λ → S ⊗[A] Λ`. This comparison lets extension along morphisms of orders be compared with
completion at primes of their central base ring.

The construction uses the universal properties of `BalancedExtension` and `TensorProduct`.
No flatness hypothesis is needed.
-/

public section

open scoped TensorProduct

namespace TauCeti.BalancedExtension

variable (A : Type*) [CommRing A] (S : Type*) [CommRing S] [Algebra A S]
  (Λ : Type*) [Ring Λ] [Algebra A Λ]
  (M : Type*) [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]

attribute [local instance low] TauCeti.CentralBaseChange.module moduleBase

/-- The `A`-linear map `m ↦ 1 ⊗ m` into the extension along `Λ → S ⊗[A] Λ`. -/
private noncomputable def includeRightBase :
    M →ₗ[A] BalancedExtension
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : Λ →ₐ[A] S ⊗[A] Λ)) M where
  toFun m := tmul _ 1 m
  map_add' := tmul_add 1
  map_smul' a m := by
    simp only [RingHom.id_apply]
    rw [smul_tmul', ← algebraMap_smul Λ a m, tmul_smul]
    simp only [one_mul, RingHom.coe_coe, AlgHom.commutes]
    rw [Algebra.algebraMap_eq_smul_one]

private theorem includeRightBase_apply (m : M) :
    includeRightBase A S Λ M m = tmul _ 1 m := rfl

private instance : IsScalarTower A S (BalancedExtension
    (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : Λ →ₐ[A] S ⊗[A] Λ)) M) :=
  IsScalarTower.to₁₂₄ A S (S ⊗[A] Λ) _

/-- The map `s ⊗ m ↦ (s ⊗ 1) ⊗ m` into the balanced extension, inverse to `includeRightEquiv`. -/
private noncomputable def centralInverse :
    S ⊗[A] M →ₗ[S]
      BalancedExtension
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : Λ →ₐ[A] S ⊗[A] Λ)) M :=
  (includeRightBase A S Λ M).liftBaseChange S

private theorem centralInverse_tmul (s : S) (m : M) :
    centralInverse A S Λ M (s ⊗ₜ[A] m) = tmul _ (s ⊗ₜ[A] 1) m := by
  simp only [centralInverse, LinearMap.liftBaseChange_tmul, includeRightBase_apply,
    smul_tmul', ← Algebra.algebraMap_eq_smul_one,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

private theorem lift_includeRight_tmul (s : S) (l : Λ) (m : M) :
    lift (CentralBaseChange.includeRight A S Λ M) (tmul _ (s ⊗ₜ[A] l) m) = s ⊗ₜ[A] (l • m) := by
  rw [lift_tmul, CentralBaseChange.includeRight_apply, CentralBaseChange.tmul_smul_tmul, mul_one]

private theorem rightInverse_centralInverse :
    Function.RightInverse (centralInverse A S Λ M)
      (lift (CentralBaseChange.includeRight A S Λ M)) := by
  have h := TensorProduct.AlgebraTensorModule.ext (A := S) (R := A)
    (g := ((lift (CentralBaseChange.includeRight A S Λ M)).restrictScalars S).comp
      (centralInverse A S Λ M)) (h := LinearMap.id) (fun s m ↦ by
        simp [centralInverse_tmul])
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.id_apply] using
    LinearMap.congr_fun h x

private theorem leftInverse_centralInverse :
    Function.LeftInverse (centralInverse A S Λ M)
      (lift (CentralBaseChange.includeRight A S Λ M)) := by
  intro x
  induction x using induction_on with
  | tmul t m =>
    have ht := TensorProduct.AlgebraTensorModule.ext (A := S) (R := A)
      (g := (centralInverse A S Λ M).comp
        (((lift (CentralBaseChange.includeRight A S Λ M)).restrictScalars S).comp
          ((LinearMap.toSpanSingleton (S ⊗[A] Λ) _ (tmul _ 1 m)).restrictScalars S)))
      (h := (LinearMap.toSpanSingleton (S ⊗[A] Λ) _ (tmul _ 1 m)).restrictScalars S)
      (fun s l ↦ by
        simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
          LinearMap.toSpanSingleton_apply, ← tmul_eq_smul_one_tmul]
        rw [lift_includeRight_tmul, centralInverse_tmul, tmul_smul]
        simp)
    simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      LinearMap.toSpanSingleton_apply, ← tmul_eq_smul_one_tmul] using
        LinearMap.congr_fun ht t
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]

/-- Central base change `S ⊗[A] M` is balanced extension along `Λ → S ⊗[A] Λ`, `l ↦ 1 ⊗ l`. -/
noncomputable def includeRightEquiv :
    BalancedExtension
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : Λ →ₐ[A] S ⊗[A] Λ)) M
      ≃ₗ[S ⊗[A] Λ] S ⊗[A] M :=
  { lift (CentralBaseChange.includeRight A S Λ M) with
    invFun := centralInverse A S Λ M
    left_inv := leftInverse_centralInverse A S Λ M
    right_inv := rightInverse_centralInverse A S Λ M }

/-- `includeRightEquiv` sends `(s ⊗ l) ⊗ m` to `s ⊗ (l • m)`. -/
@[simp]
theorem includeRightEquiv_tmul (s : S) (l : Λ) (m : M) :
    includeRightEquiv A S Λ M (tmul _ (s ⊗ₜ[A] l) m) = s ⊗ₜ[A] (l • m) := by
  exact lift_includeRight_tmul A S Λ M s l m

/-- The inverse of `includeRightEquiv` sends `s ⊗ m` to `(s ⊗ 1) ⊗ m`, inserting the unit
of `Λ`. -/
@[simp]
theorem includeRightEquiv_symm_tmul (s : S) (m : M) :
    (includeRightEquiv A S Λ M).symm (s ⊗ₜ[A] m) = tmul _ (s ⊗ₜ[A] 1) m := by
  exact centralInverse_tmul A S Λ M s m

/-- The comparison sends the balanced unit map to the central unit map. -/
@[simp]
theorem includeRightEquiv_one_tmul (m : M) :
    includeRightEquiv A S Λ M (tmul _ 1 m) = (1 : S) ⊗ₜ[A] m := by
  simpa only [Algebra.TensorProduct.one_def, one_smul] using
    includeRightEquiv_tmul A S Λ M 1 1 m

variable {Λ' : Type*} [Ring Λ'] [Algebra A Λ']
  (f : Λ →ₐ[A] Λ') [Module A (BalancedExtension (RingHomClass.toRingHom f) M)]
  [IsScalarTower A Λ' (BalancedExtension (RingHomClass.toRingHom f) M)]

/-- Balanced extension along an `A`-algebra homomorphism `f : Λ → Λ'` commutes with central
base change: extending `S ⊗[A] M` along the base-changed map `id_S ⊗ f` is the central base
change of `Λ' ⊗_Λ M`. Completion of an order at a prime is the case where `S` is the completion
of `A`. The extended module must have an `A`-action compatible with its `Λ'`-action;
activate `BalancedExtension.moduleBase` locally when no suitable action is already available. -/
noncomputable def baseChangeEquiv :
    BalancedExtension
      (RingHomClass.toRingHom (Algebra.TensorProduct.map (AlgHom.id A S) f)) (S ⊗[A] M)
      ≃ₗ[S ⊗[A] Λ'] S ⊗[A] BalancedExtension (RingHomClass.toRingHom f) M := by
  let i : Λ →ₐ[A] S ⊗[A] Λ := Algebra.TensorProduct.includeRight
  let j : Λ' →ₐ[A] S ⊗[A] Λ' := Algebra.TensorProduct.includeRight
  let g := Algebra.TensorProduct.map (AlgHom.id A S) f
  have h : (RingHomClass.toRingHom g).comp (RingHomClass.toRingHom i) =
      (RingHomClass.toRingHom j).comp (RingHomClass.toRingHom f) := by
    rw [← AlgHom.comp_toRingHom, ← AlgHom.comp_toRingHom]
    exact congrArg _ (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id A S) f)
  exact (congr (RingHomClass.toRingHom g) (includeRightEquiv A S Λ M).symm).trans <|
    (cancelBaseChange (RingHomClass.toRingHom i) (RingHomClass.toRingHom g)).trans <|
      (congrRingHom h).trans <|
      (cancelBaseChange (RingHomClass.toRingHom f) (RingHomClass.toRingHom j)).symm.trans
        (includeRightEquiv A S Λ' (BalancedExtension (RingHomClass.toRingHom f) M))

/-- After central base change, a pure balanced tensor has the expected coefficient product. -/
@[simp]
theorem baseChangeEquiv_tmul (s t : S) (l : Λ') (m : M) :
    baseChangeEquiv A S Λ M f
      (tmul _ (s ⊗ₜ[A] l) (t ⊗ₜ[A] m)) =
        (s * t) ⊗ₜ[A] tmul (RingHomClass.toRingHom f) l m := by
  simp only [baseChangeEquiv, LinearEquiv.trans_apply, congr_tmul,
    includeRightEquiv_symm_tmul, cancelBaseChange_tmul, congrRingHom_tmul,
    cancelBaseChange_symm_tmul]
  have hmap : (RingHomClass.toRingHom (Algebra.TensorProduct.map (AlgHom.id A S) f))
      (t ⊗ₜ[A] (1 : Λ)) = t ⊗ₜ[A] (1 : Λ') := by
    simp
  rw [hmap, Algebra.TensorProduct.tmul_mul_tmul, mul_one, includeRightEquiv_tmul,
    smul_tmul, mul_one]

/-- The base-change comparison commutes with the balanced unit map. -/
@[simp]
theorem baseChangeEquiv_one_tmul (s : S) (m : M) :
    baseChangeEquiv A S Λ M f (tmul _ 1 (s ⊗ₜ[A] m)) =
      s ⊗ₜ[A] tmul (RingHomClass.toRingHom f) 1 m := by
  simpa only [Algebra.TensorProduct.one_def, one_mul] using
    baseChangeEquiv_tmul A S Λ M f 1 s 1 m

/-- The inverse of `baseChangeEquiv` sends `s ⊗ (l ⊗ m)` to `(s ⊗ l) ⊗ (1 ⊗ m)`, inserting the
unit of `S`. -/
@[simp]
theorem baseChangeEquiv_symm_tmul (s : S) (l : Λ') (m : M) :
    (baseChangeEquiv A S Λ M f).symm (s ⊗ₜ[A] tmul (RingHomClass.toRingHom f) l m) =
      tmul _ (s ⊗ₜ[A] l) ((1 : S) ⊗ₜ[A] m) := by
  apply (baseChangeEquiv A S Λ M f).injective
  rw [LinearEquiv.apply_symm_apply, baseChangeEquiv_tmul, mul_one]

end TauCeti.BalancedExtension
