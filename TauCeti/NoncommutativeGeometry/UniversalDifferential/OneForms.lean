/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

private theorem multiplication_leftAction (a : Unitization k A)
    (t : Unitization k A ⊗[k] Unitization k A) :
    LinearMap.mul' k (Unitization k A) (leftAction k A a t) =
      a * LinearMap.mul' k (Unitization k A) t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

private theorem multiplication_rightAction (a : Unitization k A)
    (t : Unitization k A ⊗[k] Unitization k A) :
    LinearMap.mul' k (Unitization k A) (rightAction k A a t) =
      LinearMap.mul' k (Unitization k A) t * a := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]

instance instModuleLeft : Module (Unitization k A) (UniversalOneForms k A) where
  smul a ω := ⟨leftAction k A a ω.1, by
    change LinearMap.mul' k (Unitization k A) (leftAction k A a ω.1) = 0
    rw [multiplication_leftAction, ω.property, mul_zero]⟩
  one_smul ω := Subtype.ext <| by
    change leftAction k A 1 ω.1 = ω.1
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy]
  mul_smul a b ω := Subtype.ext <| by
    change leftAction k A (a * b) ω.1 = leftAction k A a (leftAction k A b ω.1)
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [mul_assoc]
    · simp only [map_add, hx, hy]
  smul_zero a := Subtype.ext <| by
    change leftAction k A a 0 = 0
    exact map_zero _
  smul_add a ω η := Subtype.ext <| by
    change leftAction k A a (ω.1 + η.1) = leftAction k A a ω.1 + leftAction k A a η.1
    exact map_add _ _ _
  add_smul a b ω := Subtype.ext <| by
    change leftAction k A (a + b) ω.1 = leftAction k A a ω.1 + leftAction k A b ω.1
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [add_mul, add_tmul]
    · simp only [map_add, hx, hy]
      abel
  zero_smul ω := Subtype.ext <| by
    change leftAction k A 0 ω.1 = 0
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy, add_zero]

instance instModuleRight : Module (Unitization k A)ᵐᵒᵖ (UniversalOneForms k A) where
  smul a ω := ⟨rightAction k A a.unop ω.1, by
    change LinearMap.mul' k (Unitization k A) (rightAction k A a.unop ω.1) = 0
    rw [multiplication_rightAction, ω.property, zero_mul]⟩
  one_smul ω := Subtype.ext <| by
    change rightAction k A 1 ω.1 = ω.1
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy]
  mul_smul a b ω := Subtype.ext <| by
    change rightAction k A (b.unop * a.unop) ω.1 =
      rightAction k A a.unop (rightAction k A b.unop ω.1)
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [mul_assoc]
    · simp only [map_add, hx, hy]
  smul_zero a := Subtype.ext <| by
    change rightAction k A a.unop 0 = 0
    exact map_zero _
  smul_add a ω η := Subtype.ext <| by
    change rightAction k A a.unop (ω.1 + η.1) =
      rightAction k A a.unop ω.1 + rightAction k A a.unop η.1
    exact map_add _ _ _
  add_smul a b ω := Subtype.ext <| by
    change rightAction k A (a.unop + b.unop) ω.1 =
      rightAction k A a.unop ω.1 + rightAction k A b.unop ω.1
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [mul_add, tmul_add]
    · simp only [map_add, hx, hy]
      abel
  zero_smul ω := Subtype.ext <| by
    change rightAction k A 0 ω.1 = 0
    refine TensorProduct.inductionOn ω.1 (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp
    · simp only [map_add, hx, hy, add_zero]

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
    { toFun := fun a ↦ ⟨1 ⊗ₜ[k] a - a ⊗ₜ[k] 1, by
        change LinearMap.mul' k (Unitization k A) (1 ⊗ₜ[k] a - a ⊗ₜ[k] 1) = 0
        simp⟩
      map_add' := fun a b ↦ Subtype.ext <| by
        simp only [tmul_add, add_tmul, Submodule.coe_add]
        abel
      map_smul' := fun r a ↦ Subtype.ext <| by
        simp only [Submodule.coe_smul_of_tower, smul_sub]
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul]
        simp }
  map_one_eq_zero' := Subtype.ext <| sub_self _
  leibniz' := fun a b ↦ Subtype.ext <| by
    exact show
      1 ⊗ₜ[k] (a * b) - (a * b) ⊗ₜ[k] 1 =
        leftAction k A a (1 ⊗ₜ[k] b - b ⊗ₜ[k] 1) +
          rightAction k A b (1 ⊗ₜ[k] a - a ⊗ₜ[k] 1) by
      simp only [map_sub, leftAction_tmul, rightAction_tmul, mul_one, one_mul]
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
  TensorProduct.lift <| LinearMap.mk₂ k (fun x y ↦ x • D y)
    (fun x y z ↦ by simp only [add_smul])
    (fun r x y ↦ smul_assoc r x (D y))
    (fun x y z ↦ by simp only [map_add, smul_add])
    (fun r x y ↦ by rw [D.map_smul, smul_comm])

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
      simp only [TensorProduct.Algebra.smul_def, one_smul]
      change tensorLift k A D (rightAction k A b.unop ω.1) = b • tensorLift k A D ω.1
      rw [tensorLift_rightAction, ω.property, zero_smul, add_zero]
      simp only [op_unop])

@[simp]
private theorem lift_apply (D : BimoduleDerivation k (Unitization k A) M)
    (ω : UniversalOneForms k A) : lift k A D ω = tensorLift k A D ω.1 := by
  simp [lift, liftLinear, TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply]

/-- The induced bimodule map factors the derivation through the universal derivation. -/
theorem lift_derivation (D : BimoduleDerivation k (Unitization k A) M)
    (a : Unitization k A) : lift k A D ((derivation k A) a) = D a := by
  simp only [lift_apply, coe_derivation, map_sub, tensorLift_tmul, one_smul]
  rw [D.map_one_eq_zero, smul_zero, sub_zero]

private def generate :
    Unitization k A ⊗[k] Unitization k A →ₗ[k] UniversalOneForms k A :=
  TensorProduct.lift <| LinearMap.mk₂ k (fun x y ↦ x • (derivation k A) y)
    (fun x y z ↦ by simp only [add_smul])
    (fun r x y ↦ smul_assoc r x ((derivation k A) y))
    (fun x y z ↦ by simp only [map_add, smul_add])
    (fun r x y ↦ by rw [BimoduleDerivation.map_smul, smul_comm])

private theorem coe_generate (t : Unitization k A ⊗[k] Unitization k A) :
    ((generate k A t : UniversalOneForms k A) : Unitization k A ⊗[k] Unitization k A) =
      t - LinearMap.mul' k (Unitization k A) t ⊗ₜ[k] 1 := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      simp only [generate, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
        coe_smul_left, coe_derivation, map_sub, leftAction_tmul,
        LinearMap.mul'_apply, mul_one]
  | add x y hx hy =>
      simp only [map_add, Submodule.coe_add, hx, hy, add_tmul]
      abel

private theorem generate_coe (ω : UniversalOneForms k A) : generate k A ω.1 = ω := by
  apply Subtype.ext
  rw [coe_generate, ω.property, zero_tmul, sub_zero]

/-- Extend a derivation on a nonunital algebra by zero on the scalar summand of its forced
unitization. -/
def BimoduleDerivation.ofUnitization (D : A →ₗ[k] M)
    (hD : ∀ a b, D (a * b) = (a : Unitization k A) • D b +
      op (b : Unitization k A) • D a) :
    BimoduleDerivation k (Unitization k A) M where
  toLinearMap := D.comp (Unitization.sndHom k k A)
  map_one_eq_zero' := by simp
  leibniz' := fun x y ↦ by
    change D (x * y).snd = x • D y.snd + op y • D x.snd
    have left_decomp (z : Unitization k A) (m : M) :
        z • m = z.fst • m + (z.snd : Unitization k A) • m := by
      conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq z]
      rw [add_smul]
      congr 1
      change algebraMap k (Unitization k A) z.fst • m = z.fst • m
      rw [IsScalarTower.algebraMap_smul]
    have right_decomp (z : Unitization k A) (m : M) :
        op z • m = z.fst • m + op (z.snd : Unitization k A) • m := by
      conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq z]
      rw [op_add, add_smul]
      congr 1
      change algebraMap k (Unitization k A)ᵐᵒᵖ z.fst • m = z.fst • m
      rw [IsScalarTower.algebraMap_smul]
    rw [Unitization.snd_mul, map_add, map_add, map_smul, map_smul, hD]
    calc
      x.fst • D y.snd + y.fst • D x.snd +
          ((x.snd : Unitization k A) • D y.snd +
            op (y.snd : Unitization k A) • D x.snd) =
        (x.fst • D y.snd + (x.snd : Unitization k A) • D y.snd) +
          (y.fst • D x.snd + op (y.snd : Unitization k A) • D x.snd) := by abel
      _ = x • D y.snd + op y • D x.snd := by
        rw [← left_decomp, ← right_decomp]

omit [SMulCommClass (Unitization k A) (Unitization k A)ᵐᵒᵖ M] in
/-- Extending by zero and then evaluating on the original algebra recovers the derivation. -/
@[simp]
theorem BimoduleDerivation.ofUnitization_inr (D : A →ₗ[k] M)
    (hD : ∀ a b, D (a * b) = (a : Unitization k A) • D b +
      op (b : Unitization k A) • D a) (a : A) :
    BimoduleDerivation.ofUnitization (k := k) (A := A) D hD (a : Unitization k A) = D a := by
  unfold BimoduleDerivation.ofUnitization
  rfl

/-- A bimodule map out of universal one-forms is determined by its values on differentials. -/
theorem lift_unique (D : BimoduleDerivation k (Unitization k A) M)
    (f : UniversalOneForms k A →ₗ[Unitization k A ⊗[k] (Unitization k A)ᵐᵒᵖ] M)
    (hf : ∀ a, f ((derivation k A) a) = D a) : f = lift k A D := by
  apply LinearMap.ext
  intro ω
  calc
    f ω = f (generate k A ω.1) := congrArg f (generate_coe k A ω).symm
    _ = tensorLift k A D ω.1 := by
      induction ω.1 using TensorProduct.inductionOn with
      | tmul x y =>
          simp only [generate, TensorProduct.lift.tmul, LinearMap.mk₂_apply, tensorLift_tmul]
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
  let Dext := BimoduleDerivation.ofUnitization (k := k) (A := A) D hD
  refine ⟨lift k A Dext, fun a ↦ ?_, fun f hf ↦ ?_⟩
  · rw [d_apply, lift_derivation, BimoduleDerivation.ofUnitization_inr]
  · apply lift_unique k A Dext f
    intro x
    induction x with
    | inl_add_inr r a =>
      have hdScalar : (derivation k A) (Unitization.inl r) = 0 := by
        have hinl : Unitization.inl r = r • (1 : Unitization k A) := by ext <;> simp
        rw [hinl]
        rw [BimoduleDerivation.map_smul, BimoduleDerivation.map_one_eq_zero, smul_zero]
      have hextScalar : Dext (Unitization.inl r) = 0 := by
        have hinl : Unitization.inl r = r • (1 : Unitization k A) := by ext <;> simp
        rw [hinl]
        rw [BimoduleDerivation.map_smul, BimoduleDerivation.map_one_eq_zero, smul_zero]
      rw [map_add, map_add, map_add, hdScalar, hextScalar, map_zero, zero_add, zero_add,
        ← d_apply, hf, BimoduleDerivation.ofUnitization_inr]

end UniversalProperty

end UniversalOneForms

end OneForms

end TauCeti
