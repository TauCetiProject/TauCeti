/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Multiplicative families on tensor powers

A morphism `f : X ⟶ M` into a monoid object extends uniquely to morphisms
`tensorPow X n ⟶ M` that preserve the empty tensor and the concatenation of two blocks.
`tensorPowLift` constructs this extension by iterated multiplication; `tensorPowLiftEquiv`
expresses its universal property as an equivalence with multiplicative families.

This is the degreewise universal property of the tensor algebra. It applies in particular to
DG bimodules with their balanced tensor product, without imposing commutativity on the middle
algebra. When the coproduct of tensor powers exists and tensoring preserves it, these families
are the restrictions of monoid morphisms out of the tensor algebra to its length summands.
No coproduct or derived replacement is constructed here.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 4, for tensor algebras of DG bimodules.
-/

public section

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y M N : C} [MonObj M] [MonObj N]

/-- Extend a morphism into a monoid object to all tensor powers by iterated multiplication.
The empty tensor is sent to the unit. -/
def tensorPowLift (f : X ⟶ M) : (n : ℕ) → tensorPow X n ⟶ M
  | 0 => η[M]
  | n + 1 => (f ⊗ₘ tensorPowLift f n) ≫ μ[M]

@[simp]
theorem tensorPowLift_zero (f : X ⟶ M) : tensorPowLift f 0 = η[M] := (rfl)

/-- On a nonempty tensor, multiply the image of the first factor by the image of the rest. -/
theorem tensorPowLift_succ (f : X ⟶ M) (n : ℕ) :
    tensorPowLift f (n + 1) = (f ⊗ₘ tensorPowLift f n) ≫ μ[M] := (rfl)

@[simp]
theorem tensorPowLift_one (f : X ⟶ M) :
    tensorPowLift f 1 = (ρ_ X).hom ≫ f := by
  simp [tensorPowLift_succ]

/-- Iterated multiplication sends concatenation of blocks to multiplication. -/
@[reassoc]
theorem tensorPowAddIso_hom_tensorPowLift (f : X ⟶ M) (m n : ℕ) :
    (tensorPowAddIso X m n).hom ≫ tensorPowLift f (n + m) =
      (tensorPowLift f m ⊗ₘ tensorPowLift f n) ≫ μ[M] := by
  induction m with
  | zero => simp [tensorPowAddIso_zero]
  | succ m ih =>
    -- Match the recursive index without rewriting the dependent target object.
    rw [tensorPowAddIso_succ_hom,
      show tensorPowLift f (n + (m + 1)) = _ from tensorPowLift_succ f (n + m),
      tensorPowLift_succ f m]
    simp only [Category.assoc]
    rw [tensorHom_def'_assoc, ← whiskerLeft_comp_assoc, ih]
    simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc,
      comp_whiskerRight, MonObj.mul_assoc]
    simp only [associator_naturality_left_assoc]
    simp [whisker_exchange_assoc]

/-- Iterated multiplication commutes with a morphism of monoid objects. -/
@[simp, reassoc]
theorem tensorPowLift_comp (f : X ⟶ M) (g : M ⟶ N) [IsMonHom g] (n : ℕ) :
    tensorPowLift f n ≫ g = tensorPowLift (f ≫ g) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [tensorPowLift_succ, ih]

/-- Iterated multiplication is natural in the generators. -/
@[simp, reassoc]
theorem tensorPowMap_tensorPowLift (g : X ⟶ Y) (f : Y ⟶ M) (n : ℕ) :
    tensorPowMap g n ≫ tensorPowLift f n = tensorPowLift (g ≫ f) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [tensorPowMap_succ, tensorPowLift_succ, ih]

/-- A unit-preserving multiplicative family of maps from tensor powers into a monoid object.
All components are constrained by the unit and concatenation laws. -/
structure TensorPowHom (X M : C) [MonObj M] where
  /-- The map on tensors of length `n`. -/
  app (n : ℕ) : tensorPow X n ⟶ M
  /-- The empty tensor maps to the unit. -/
  app_zero : app 0 = η[M]
  /-- Concatenation of blocks maps to multiplication. -/
  app_add (m n : ℕ) :
    (tensorPowAddIso X m n).hom ≫ app (n + m) = (app m ⊗ₘ app n) ≫ μ[M]

attribute [simp] TensorPowHom.app_zero

namespace TensorPowHom

/-- Multiplicative families are equal if their components are equal. -/
@[ext]
theorem ext {F G : TensorPowHom X M} (h : ∀ n, F.app n = G.app n) : F = G := by
  have hh := funext h
  cases F
  cases G
  cases hh
  rfl

/-- Recover the map on generators by removing the trailing tensor unit. -/
def generator (F : TensorPowHom X M) : X ⟶ M := (ρ_ X).inv ≫ F.app 1

@[simp]
theorem rightUnitor_hom_generator (F : TensorPowHom X M) :
    (ρ_ X).hom ≫ F.generator = F.app 1 := by
  simp [generator]

/-- Multiplicativity with a length-one block gives the recursion on components. -/
theorem app_succ (F : TensorPowHom X M) (n : ℕ) :
    F.app (n + 1) = (F.generator ⊗ₘ F.app n) ≫ μ[M] := by
  have he := congrArg (((ρ_ X).inv ▷ tensorPow X n) ≫ ·) (F.app_add 1 n)
  rw [tensorPowAddIso_one_hom, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp] at he
  rw [tensorHom_def, generator, comp_whiskerRight_assoc]
  simpa only [tensorHom_def, Category.assoc] using he

/-- Iterating the generator map recovers the original multiplicative family. -/
@[simp]
theorem tensorPowLift_generator (F : TensorPowHom X M) (n : ℕ) :
    tensorPowLift F.generator n = F.app n := by
  induction n with
  | zero => exact F.app_zero.symm
  | succ n ih => rw [F.app_succ, tensorPowLift_succ, ih]

/-- The component on generators determines a multiplicative family. -/
theorem ext_generator {F G : TensorPowHom X M} (h : F.generator = G.generator) : F = G := by
  ext n
  rw [← F.tensorPowLift_generator, ← G.tensorPowLift_generator, h]

end TensorPowHom

/-- The degreewise universal property of the tensor algebra: maps from the generators to a
monoid object correspond to unit-preserving multiplicative families on the tensor powers. -/
def tensorPowLiftEquiv : (X ⟶ M) ≃ TensorPowHom X M where
  toFun f :=
    { app := tensorPowLift f
      app_zero := tensorPowLift_zero f
      app_add := tensorPowAddIso_hom_tensorPowLift f }
  invFun := TensorPowHom.generator
  left_inv f := by simp [TensorPowHom.generator]
  right_inv F := by
    ext n
    exact F.tensorPowLift_generator n

@[simp]
theorem tensorPowLiftEquiv_app (f : X ⟶ M) (n : ℕ) :
    (tensorPowLiftEquiv f).app n = tensorPowLift f n := (rfl)

@[simp]
theorem tensorPowLiftEquiv_generator (f : X ⟶ M) :
    (tensorPowLiftEquiv f).generator = f :=
  tensorPowLiftEquiv.symm_apply_apply f

@[simp]
theorem tensorPowLiftEquiv_symm_apply (F : TensorPowHom X M) :
    tensorPowLiftEquiv.symm F = F.generator := (rfl)

end TauCeti
