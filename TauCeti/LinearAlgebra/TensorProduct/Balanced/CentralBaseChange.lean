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

attribute [local instance low] TauCeti.CentralBaseChange.module

/-- The map `m ↦ 1 ⊗ m`, semilinear for `Λ → S ⊗[A] Λ`. -/
private noncomputable def centralInclude :
    M →ₛₗ[RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight : Λ →ₐ[A] S ⊗[A] Λ)] S ⊗[A] M where
  toFun m := 1 ⊗ₜ[A] m
  map_add' := TensorProduct.tmul_add _
  map_smul' l m := by simp

private theorem centralInclude_apply (m : M) :
    centralInclude A S Λ M m = (1 : S) ⊗ₜ[A] m := (rfl)

/-- The `A`-action on a balanced extension induced from the destination algebra.
As with `CentralBaseChange.module`, activate this locally when the action is needed. -/
noncomputable abbrev moduleBase {R T : Type*} [Ring R] [Ring T] [Algebra A T]
    (f : R →+* T) (P : Type*) [AddCommGroup P] [Module R P] :
    Module A (BalancedExtension f P) :=
  Module.restrictScalars A T _

attribute [local instance low] moduleBase

/-- Restricting the destination action to its central base ring forms a scalar tower. -/
instance {R T : Type*} [Ring R] [Ring T] [Algebra A T]
    (f : R →+* T) (P : Type*) [AddCommGroup P] [Module R P] :
    IsScalarTower A T (BalancedExtension f P) :=
  IsScalarTower.restrictScalars A T _

/-- Central scalars act on the first factor of a balanced extension. -/
theorem base_smul_tmul {R T : Type*} [Ring R] [Ring T] [Algebra A T]
    (f : R →+* T) {P : Type*} [AddCommGroup P] [Module R P] (a : A) (t : T) (p : P) :
    a • tmul f t p = tmul f (a • t) p := by
  rw [← IsScalarTower.algebraMap_smul T a (tmul f t p), smul_tmul, Algebra.smul_def]

/-- The map `s ⊗ m ↦ (s ⊗ 1) ⊗ m` into the balanced extension. -/
private noncomputable def centralInverse :
    S ⊗[A] M →ₗ[A]
      BalancedExtension
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : Λ →ₐ[A] S ⊗[A] Λ)) M :=
  TensorProduct.lift <| LinearMap.mk₂ A
    (fun s m ↦ tmul _ (s ⊗ₜ[A] 1) m)
    (fun _ _ _ ↦ by rw [TensorProduct.add_tmul, add_tmul])
    (fun a s m ↦ by
      rw [base_smul_tmul, TensorProduct.smul_tmul'])
    (fun _ _ _ ↦ tmul_add _ _ _)
    (fun a s m ↦ by
      rw [← IsScalarTower.algebraMap_smul Λ a m, tmul_smul]
      rw [base_smul_tmul]
      dsimp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.algebraMap_eq_smul_one,
        one_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul'])

private theorem centralInverse_tmul (s : S) (m : M) :
    centralInverse A S Λ M (s ⊗ₜ[A] m) = tmul _ (s ⊗ₜ[A] 1) m :=
  TensorProduct.lift.tmul _ _

/-- Central base change is balanced extension along `Λ → S ⊗[A] Λ`. -/
noncomputable def centralBaseChangeEquiv :
    BalancedExtension
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : Λ →ₐ[A] S ⊗[A] Λ)) M
      ≃ₗ[S ⊗[A] Λ] S ⊗[A] M := by
  let f := lift (centralInclude A S Λ M)
  let g := centralInverse A S Λ M
  have hfg : Function.RightInverse g f := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s m => simp only [g, centralInverse_tmul, f, lift_tmul, centralInclude_apply,
        CentralBaseChange.tmul_smul_tmul, mul_one, one_smul]
    | add x y hx hy => simp only [_root_.map_add, hx, hy]
  have hgf : Function.LeftInverse g f := by
    intro x
    induction x using induction_on with
    | tmul t m =>
      induction t using TensorProduct.inductionOn with
      | tmul s l =>
        dsimp only [f, g]
        rw [lift_tmul, centralInclude_apply, CentralBaseChange.tmul_smul_tmul,
          mul_one, centralInverse_tmul, tmul_smul]
        congr 1
        exact Algebra.TensorProduct.tmul_mul_tmul s 1 (1 : Λ) l |>.trans (by simp)
      | add t t' ht ht' => simp only [add_tmul, _root_.map_add, ht, ht']
    | add x y hx hy => simp only [_root_.map_add, hx, hy]
  exact LinearEquiv.ofBijective f ⟨hgf.injective, hfg.surjective⟩

@[simp]
theorem centralBaseChangeEquiv_tmul (s : S) (l : Λ) (m : M) :
    centralBaseChangeEquiv A S Λ M (tmul _ (s ⊗ₜ[A] l) m) = s ⊗ₜ[A] (l • m) := by
  exact (lift_tmul (centralInclude A S Λ M) (s ⊗ₜ[A] l) m).trans (by
    rw [centralInclude_apply, CentralBaseChange.tmul_smul_tmul, mul_one])

@[simp]
theorem centralBaseChangeEquiv_symm_tmul (s : S) (m : M) :
    (centralBaseChangeEquiv A S Λ M).symm (s ⊗ₜ[A] m) = tmul _ (s ⊗ₜ[A] 1) m := by
  apply (centralBaseChangeEquiv A S Λ M).injective
  rw [LinearEquiv.apply_symm_apply, centralBaseChangeEquiv_tmul, one_smul]

variable {Λ' : Type*} [Ring Λ'] [Algebra A Λ']
  (f : Λ →ₐ[A] Λ') [Module A (BalancedExtension (RingHomClass.toRingHom f) M)]
  [IsScalarTower A Λ' (BalancedExtension (RingHomClass.toRingHom f) M)]

/-- Balanced extension along an `A`-algebra homomorphism commutes with central base change.
The completed scalar homomorphism is `S ⊗ f`. -/
noncomputable def baseChangeEquiv :
    BalancedExtension
      (RingHomClass.toRingHom (Algebra.TensorProduct.map (AlgHom.id A S) f)) (S ⊗[A] M)
      ≃ₗ[S ⊗[A] Λ'] S ⊗[A] BalancedExtension (RingHomClass.toRingHom f) M := by
  let i : Λ →ₐ[A] S ⊗[A] Λ := Algebra.TensorProduct.includeRight
  let j : Λ' →ₐ[A] S ⊗[A] Λ' := Algebra.TensorProduct.includeRight
  let g := Algebra.TensorProduct.map (AlgHom.id A S) f
  have h : (RingHomClass.toRingHom g).comp (RingHomClass.toRingHom i) =
      (RingHomClass.toRingHom j).comp (RingHomClass.toRingHom f) := by
    ext l
    simp [g, i, j]
  exact (congr (RingHomClass.toRingHom g) (centralBaseChangeEquiv A S Λ M).symm).trans <|
    (cancelBaseChange (RingHomClass.toRingHom i) (RingHomClass.toRingHom g)).trans <|
      (congrRingHom h).trans <|
      (cancelBaseChange (RingHomClass.toRingHom f) (RingHomClass.toRingHom j)).symm.trans
        (centralBaseChangeEquiv A S Λ' (BalancedExtension (RingHomClass.toRingHom f) M))

/-- After central base change, a pure balanced tensor has the expected coefficient product. -/
@[simp]
theorem baseChangeEquiv_tmul (s t : S) (l : Λ') (m : M) :
    baseChangeEquiv A S Λ M f
      (tmul _ (s ⊗ₜ[A] l) (t ⊗ₜ[A] m)) =
        (s * t) ⊗ₜ[A] tmul (RingHomClass.toRingHom f) l m := by
  simp only [baseChangeEquiv, LinearEquiv.trans_apply, congr_tmul,
    centralBaseChangeEquiv_symm_tmul, cancelBaseChange_tmul, congrRingHom_tmul,
    cancelBaseChange_symm_tmul]
  have hmap : (RingHomClass.toRingHom (Algebra.TensorProduct.map (AlgHom.id A S) f))
      (t ⊗ₜ[A] (1 : Λ)) = t ⊗ₜ[A] (1 : Λ') := by
    simp
  rw [hmap, Algebra.TensorProduct.tmul_mul_tmul, mul_one, centralBaseChangeEquiv_tmul,
    smul_tmul, mul_one]

@[simp]
theorem baseChangeEquiv_symm_tmul (s : S) (l : Λ') (m : M) :
    (baseChangeEquiv A S Λ M f).symm (s ⊗ₜ[A] tmul (RingHomClass.toRingHom f) l m) =
      tmul _ (s ⊗ₜ[A] l) ((1 : S) ⊗ₜ[A] m) := by
  apply (baseChangeEquiv A S Λ M f).injective
  rw [LinearEquiv.apply_symm_apply, baseChangeEquiv_tmul, mul_one]

end TauCeti.BalancedExtension
