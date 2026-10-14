/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Bilinear
public import TauCeti.Algebra.TensorProduct.Module
public import TauCeti.RingTheory.Derivation.Bimodule
public import Mathlib.Algebra.Algebra.Unitization

/-!
# Noncommutative universal one-forms

For a possibly nonunital associative algebra `A` over a commutative ring `k`, this file constructs
its universal one-forms from the forced unitization `Unitization k A`.  The module of one-forms is
the kernel of multiplication

`Unitization k A ⊗[k] Unitization k A → Unitization k A`.

It carries the outer bimodule actions.  The universal differential sends `a : A` to
`1 ⊗ a - a ⊗ 1`, satisfies the nonunital Leibniz rule, and represents derivations from `A`
into every bimodule over its forced unitization.

This is the degree-one input for the tensor algebra of universal differential forms and for the
cycle description of cyclic cocycles.
-/

public section

open MulOpposite TensorProduct
open scoped TensorProduct

namespace TauCeti

universe u v w

section OneForms

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Universal one-forms of a nonunital algebra, defined using its forced unitization. -/
def UniversalOneForms : Submodule k (Unitization k A ⊗[k] Unitization k A) :=
  (LinearMap.mul' k (Unitization k A)).ker

/-- Universal one-forms are the kernel of multiplication on the forced unitization. -/
theorem universalOneForms_def :
    UniversalOneForms k A = (LinearMap.mul' k (Unitization k A)).ker := by
  rw [UniversalOneForms]

/-- A tensor is a universal one-form exactly when its product vanishes. -/
@[simp]
theorem mem_universalOneForms {t : Unitization k A ⊗[k] Unitization k A} :
    t ∈ UniversalOneForms k A ↔ LinearMap.mul' k (Unitization k A) t = 0 := by
  rw [universalOneForms_def, LinearMap.mem_ker]

namespace UniversalOneForms

/-- Left multiplication on the first factor of the tensor model for universal one-forms. -/
def leftAction (a : Unitization k A) :
    Unitization k A ⊗[k] Unitization k A →ₗ[k] Unitization k A ⊗[k] Unitization k A :=
  (LinearMap.mulLeft k a).rTensor (Unitization k A)

/-- Right multiplication on the second factor of the tensor model for universal one-forms. -/
def rightAction (a : Unitization k A) :
    Unitization k A ⊗[k] Unitization k A →ₗ[k] Unitization k A ⊗[k] Unitization k A :=
  (LinearMap.mulRight k a).lTensor (Unitization k A)

/-- The left outer action multiplies the first factor of a pure tensor. -/
@[simp]
theorem leftAction_tmul (a x y : Unitization k A) :
    leftAction k A a (x ⊗ₜ[k] y) = (a * x) ⊗ₜ[k] y := by
  simp [leftAction]

/-- The right outer action multiplies the second factor of a pure tensor. -/
@[simp]
theorem rightAction_tmul (a x y : Unitization k A) :
    rightAction k A a (x ⊗ₜ[k] y) = x ⊗ₜ[k] (y * a) := by
  simp [rightAction]

instance instSMulLeft : SMul (Unitization k A) (UniversalOneForms k A) where
  smul a ω := ⟨leftAction k A a ω.1, by
    rw [mem_universalOneForms, leftAction, LinearMap.mul'_rTensor_mulLeft,
      (mem_universalOneForms k A).1 ω.2, mul_zero]⟩

instance instSMulRight : SMul (Unitization k A)ᵐᵒᵖ (UniversalOneForms k A) where
  smul a ω := ⟨rightAction k A a.unop ω.1, by
    rw [mem_universalOneForms, rightAction, LinearMap.mul'_lTensor_mulRight,
      (mem_universalOneForms k A).1 ω.2, zero_mul]⟩

/-- The coercion of the left action to the tensor model. -/
@[simp]
theorem coe_smul_left (a : Unitization k A) (ω : UniversalOneForms k A) :
    ((a • ω : UniversalOneForms k A) : Unitization k A ⊗[k] Unitization k A) =
      leftAction k A a ω.1 := by
  rfl

/-- The coercion of the right action to the tensor model. -/
@[simp]
theorem coe_smul_right (a : (Unitization k A)ᵐᵒᵖ) (ω : UniversalOneForms k A) :
    ((a • ω : UniversalOneForms k A) : Unitization k A ⊗[k] Unitization k A) =
      rightAction k A a.unop ω.1 := by
  rfl

instance instModuleLeft : Module (Unitization k A) (UniversalOneForms k A) where
  one_smul ω := Subtype.ext <| by
    rw [coe_smul_left]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy]
  mul_smul a b ω := Subtype.ext <| by
    rw [coe_smul_left, coe_smul_left, coe_smul_left]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [mul_assoc]
    · simp only [map_add, hx, hy]
  smul_zero a := Subtype.ext <| by
    rw [coe_smul_left, Submodule.coe_zero, map_zero]
  smul_add a ω η := Subtype.ext <| by
    rw [coe_smul_left, Submodule.coe_add, Submodule.coe_add, map_add, coe_smul_left,
      coe_smul_left]
  add_smul a b ω := Subtype.ext <| by
    rw [coe_smul_left, Submodule.coe_add, coe_smul_left, coe_smul_left]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [add_mul, add_tmul]
    · simp only [map_add, hx, hy]
      abel
  zero_smul ω := Subtype.ext <| by
    rw [coe_smul_left, Submodule.coe_zero]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy, add_zero]

instance instModuleRight : Module (Unitization k A)ᵐᵒᵖ (UniversalOneForms k A) where
  one_smul ω := Subtype.ext <| by
    rw [coe_smul_right]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy]
  mul_smul a b ω := Subtype.ext <| by
    rw [coe_smul_right, coe_smul_right, coe_smul_right, unop_mul]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [mul_assoc]
    · simp only [map_add, hx, hy]
  smul_zero a := Subtype.ext <| by
    rw [coe_smul_right, Submodule.coe_zero, map_zero]
  smul_add a ω η := Subtype.ext <| by
    rw [coe_smul_right, Submodule.coe_add, Submodule.coe_add, map_add, coe_smul_right,
      coe_smul_right]
  add_smul a b ω := Subtype.ext <| by
    rw [coe_smul_right, Submodule.coe_add, coe_smul_right, coe_smul_right, unop_add]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [mul_add, tmul_add]
    · simp only [map_add, hx, hy]
      abel
  zero_smul ω := Subtype.ext <| by
    rw [coe_smul_right, Submodule.coe_zero, unop_zero]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy, add_zero]

instance instSMulCommClass :
    SMulCommClass (Unitization k A) (Unitization k A)ᵐᵒᵖ (UniversalOneForms k A) :=
  ⟨fun a b ω ↦ Subtype.ext <| by
    simp only [coe_smul_left, coe_smul_right]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy]⟩

instance instIsScalarTowerLeft :
    IsScalarTower k (Unitization k A) (UniversalOneForms k A) :=
  ⟨fun r a ω ↦ Subtype.ext <| by
    simp only [coe_smul_left, Submodule.coe_smul_of_tower]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp only [leftAction_tmul]
      exact congrArg (· ⊗ₜ[k] y) (smul_mul_assoc r a x)
    · simp only [map_add, smul_add, hx, hy]⟩

instance instIsScalarTowerRight :
    IsScalarTower k (Unitization k A)ᵐᵒᵖ (UniversalOneForms k A) :=
  ⟨fun r a ω ↦ Subtype.ext <| by
    simp only [coe_smul_right, Submodule.coe_smul_of_tower]
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp only [rightAction_tmul, unop_smul]
      rw [← TensorProduct.tmul_smul]
      exact congrArg (TensorProduct.tmul k x) (mul_smul_comm r y a.unop)
    · simp only [map_add, smul_add, hx, hy]⟩

/-- The universal derivation on the forced unitization. -/
def derivation : BimoduleDerivation k (Unitization k A) (UniversalOneForms k A) where
  toLinearMap :=
    { toFun := fun a ↦ ⟨1 ⊗ₜ[k] a - a ⊗ₜ[k] 1, by simp⟩
      map_add' := fun a b ↦ Subtype.ext <| by
        simp only [tmul_add, add_tmul, Submodule.coe_add]
        abel
      map_smul' := fun r a ↦ Subtype.ext <| by
        simp only [Submodule.coe_smul_of_tower, smul_sub]
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul]
        simp }
  map_one_eq_zero' := Subtype.ext <| sub_self _
  leibniz' := fun a b ↦ Subtype.ext <| by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, coe_smul_left,
      coe_smul_right, unop_op, map_sub, leftAction_tmul, rightAction_tmul, mul_one, one_mul]
    abel

/-- The tensor formula for the universal derivation on the forced unitization. -/
@[simp]
theorem coe_derivation (a : Unitization k A) :
    (((derivation k A) a : UniversalOneForms k A) :
      Unitization k A ⊗[k] Unitization k A) = 1 ⊗ₜ[k] a - a ⊗ₜ[k] 1 := by
  unfold derivation
  rfl

/-- The universal differential of an element of the original nonunital algebra. -/
def d : A →ₗ[k] UniversalOneForms k A :=
  (derivation k A).toLinearMap.comp (Unitization.inrHom k k A)

/-- The differential on the original algebra is the restriction of the unitization derivation. -/
@[simp]
theorem d_apply (a : A) : d k A a = (derivation k A) (a : Unitization k A) := by
  rfl

/-- The universal differential is `1 ⊗ a - a ⊗ 1` inside the forced unitization. -/
theorem coe_d (a : A) :
    ((d k A a : UniversalOneForms k A) : Unitization k A ⊗[k] Unitization k A) =
      1 ⊗ₜ[k] (a : Unitization k A) - (a : Unitization k A) ⊗ₜ[k] 1 := by
  rw [d_apply, coe_derivation]

/-- The universal differential satisfies the Leibniz rule on the original nonunital algebra. -/
theorem d_mul (a b : A) :
    d k A (a * b) = (a : Unitization k A) • d k A b +
      op (b : Unitization k A) • d k A a := by
  rw [d_apply, d_apply, d_apply, Unitization.inr_mul]
  exact (derivation k A).leibniz (a : Unitization k A) (b : Unitization k A)

section UniversalProperty

variable {M : Type w} [AddCommGroup M] [Module k M]
  [Module (Unitization k A) M] [Module (Unitization k A)ᵐᵒᵖ M]
  [IsScalarTower k (Unitization k A) M]
  [IsScalarTower k (Unitization k A)ᵐᵒᵖ M]
  [SMulCommClass (Unitization k A) (Unitization k A)ᵐᵒᵖ M]

attribute [local instance] TensorProduct.Algebra.module

private def tensorLift (D : BimoduleDerivation k (Unitization k A) M) :
    Unitization k A ⊗[k] Unitization k A →ₗ[k] M :=
  TensorProduct.lift ((Algebra.lsmul k k M).toLinearMap.compl₂ D.toLinearMap)

omit [IsScalarTower k (Unitization k A)ᵐᵒᵖ M]
    [SMulCommClass (Unitization k A) (Unitization k A)ᵐᵒᵖ M] in
@[simp]
private theorem tensorLift_tmul (D : BimoduleDerivation k (Unitization k A) M)
    (x y : Unitization k A) : tensorLift k A D (x ⊗ₜ[k] y) = x • D y := rfl

omit [IsScalarTower k (Unitization k A)ᵐᵒᵖ M]
    [SMulCommClass (Unitization k A) (Unitization k A)ᵐᵒᵖ M] in
private theorem tensorLift_leftAction (D : BimoduleDerivation k (Unitization k A) M)
    (a : Unitization k A) (t : Unitization k A ⊗[k] Unitization k A) :
    tensorLift k A D (leftAction k A a t) = a • tensorLift k A D t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

omit [IsScalarTower k (Unitization k A)ᵐᵒᵖ M] in
private theorem tensorLift_rightAction (D : BimoduleDerivation k (Unitization k A) M)
    (b : Unitization k A) (t : Unitization k A ⊗[k] Unitization k A) :
    tensorLift k A D (rightAction k A b t) =
      op b • tensorLift k A D t + LinearMap.mul' k (Unitization k A) t • D b := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      simp only [rightAction_tmul, tensorLift_tmul, LinearMap.mul'_apply, D.leibniz,
        smul_add, mul_smul]
      rw [smul_comm x (op b)]
      abel
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      simp only [map_add, add_smul, smul_add]
      abel

private def liftLinear (D : BimoduleDerivation k (Unitization k A) M) :
    UniversalOneForms k A →ₗ[k] M :=
  (tensorLift k A D).comp (UniversalOneForms k A).subtype

/-- The bimodule map induced by a derivation from the forced unitization. -/
def lift (D : BimoduleDerivation k (Unitization k A) M) :
    UniversalOneForms k A →ₗ[Unitization k A ⊗[k] (Unitization k A)ᵐᵒᵖ] M :=
  TauCeti.Algebra.TensorProduct.linearMapOfFactors (UniversalOneForms k A) (liftLinear k A D)
    (fun a ω ↦ by
      simp only [TensorProduct.Algebra.smul_def, one_smul]
      exact tensorLift_leftAction k A D a ω.1)
    (fun b ω ↦ by
      simp only [TensorProduct.Algebra.smul_def, one_smul, liftLinear, LinearMap.comp_apply,
        Submodule.subtype_apply, coe_smul_right]
      rw [tensorLift_rightAction, (mem_universalOneForms k A).1 ω.2, zero_smul, add_zero,
        op_unop])

private theorem lift_apply (D : BimoduleDerivation k (Unitization k A) M)
    (ω : UniversalOneForms k A) : lift k A D ω = tensorLift k A D ω.1 := by
  simp [lift, liftLinear, TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply]

/-- The induced bimodule map factors the derivation through the universal derivation. -/
@[simp]
theorem lift_derivation (D : BimoduleDerivation k (Unitization k A) M)
    (a : Unitization k A) : lift k A D ((derivation k A) a) = D a := by
  simp only [lift_apply, coe_derivation, map_sub, tensorLift_tmul, one_smul]
  rw [D.map_one_eq_zero, smul_zero, sub_zero]

private theorem coe_tensorLift_derivation (t : Unitization k A ⊗[k] Unitization k A) :
    ((tensorLift k A (derivation k A) t : UniversalOneForms k A) :
      Unitization k A ⊗[k] Unitization k A) =
      t - LinearMap.mul' k (Unitization k A) t ⊗ₜ[k] 1 := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      simp only [tensorLift_tmul, coe_smul_left, coe_derivation, map_sub, leftAction_tmul,
        LinearMap.mul'_apply, mul_one]
  | add x y hx hy =>
      simp only [map_add, Submodule.coe_add, hx, hy, add_tmul]
      abel

private theorem tensorLift_derivation_coe (ω : UniversalOneForms k A) :
    tensorLift k A (derivation k A) ω.1 = ω := by
  apply Subtype.ext
  rw [coe_tensorLift_derivation, (mem_universalOneForms k A).1 ω.2, zero_tmul, sub_zero]

/-- A bimodule map out of universal one-forms is determined by its values on differentials. -/
theorem lift_unique (D : BimoduleDerivation k (Unitization k A) M)
    (f : UniversalOneForms k A →ₗ[Unitization k A ⊗[k] (Unitization k A)ᵐᵒᵖ] M)
    (hf : ∀ a, f ((derivation k A) a) = D a) : f = lift k A D := by
  apply LinearMap.ext
  intro ω
  calc
    f ω = f (tensorLift k A (derivation k A) ω.1) :=
      congrArg f (tensorLift_derivation_coe k A ω).symm
    _ = tensorLift k A D ω.1 := by
      induction ω.1 using TensorProduct.inductionOn with
      | tmul x y =>
          simp only [tensorLift_tmul]
          rw [← hf y]
          have h :=
            f.map_smul (x ⊗ₜ[k] (1 : (Unitization k A)ᵐᵒᵖ)) ((derivation k A) y)
          simpa only [TensorProduct.Algebra.smul_def, one_smul] using h
      | add x y hx hy => simp only [map_add, hx, hy]
    _ = lift k A D ω := (lift_apply k A D ω).symm

/-- Universal one-forms represent derivations into any bimodule over the forced unitization. -/
theorem existsUnique_lift (D : BimoduleDerivation k (Unitization k A) M) :
    ∃! f : UniversalOneForms k A →ₗ[Unitization k A ⊗[k] (Unitization k A)ᵐᵒᵖ] M,
      ∀ a, f ((derivation k A) a) = D a := by
  exact ⟨lift k A D, lift_derivation k A D, fun f hf ↦ lift_unique k A D f hf⟩

/-- Universal one-forms represent derivations of the original nonunital algebra into a bimodule
over its forced unitization. -/
theorem existsUnique_lift_d (D : A →ₗ[k] M)
    (hD : ∀ a b, D (a * b) = (a : Unitization k A) • D b +
      op (b : Unitization k A) • D a) :
    ∃! f : UniversalOneForms k A →ₗ[Unitization k A ⊗[k] (Unitization k A)ᵐᵒᵖ] M,
      ∀ a, f (d k A a) = D a := by
  let Dext := BimoduleDerivation.ofUnitization D hD
  refine ⟨lift k A Dext, fun a ↦ ?_, fun f hf ↦ ?_⟩
  · rw [d_apply, lift_derivation, BimoduleDerivation.ofUnitization_inr]
  · apply lift_unique k A Dext f
    intro x
    induction x with
    | inl_add_inr r a =>
      rw [map_add, map_add, map_add, ← Unitization.algebraMap_eq_inl,
        BimoduleDerivation.map_algebraMap, BimoduleDerivation.map_algebraMap, map_zero, zero_add,
        zero_add, ← d_apply, hf, BimoduleDerivation.ofUnitization_inr]

end UniversalProperty

end UniversalOneForms

end OneForms

end TauCeti
