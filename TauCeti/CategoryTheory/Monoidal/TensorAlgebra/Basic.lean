/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic
public import TauCeti.CategoryTheory.GradedObject.Total

/-!
# The coproduct tensor algebra in a monoidal category

If a monoidal category has small coproducts and tensoring on either side preserves countable
coproducts, the coproduct of the tensor powers of an object is a monoid object. Its unit includes
tensor length zero, and its multiplication concatenates blocks of tensor factors. The
computation rule `TauCeti.ιTotal_tensorAlgebraMul` retains tensor length explicitly. Morphisms of
generators induce monoid morphisms, giving `TauCeti.tensorAlgebraFunctor`. The coproduct descent
`TauCeti.tensorAlgebraDesc` extends any unit-preserving multiplicative family on tensor powers
uniquely to a monoid morphism.

This is an ordinary, not a derived or completed, construction. In a category of DG bimodules it
provides the underlying tensor algebra once preservation of coproducts is established; replacing
the generating bimodule by a suitable cofibrant one is a separate homological step.

The construction uses the coproduct tensor descent of `CategoryTheory.GradedObject.totalTensorDesc`
and the block comparisons of `TauCeti.tensorPowAddIso`. No braiding or additive structure is needed.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 4, for tensor algebras of bimodules.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory GradedObject

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoproducts.{0} C]
  [∀ A : C, PreservesColimitsOfShape (Discrete ℕ) (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape (Discrete ℕ) (tensorRight A)]

/-- The coproduct of all tensor powers of `X`, including the tensor unit in length zero. -/
abbrev tensorAlgebraObj (X : C) : C := (total ℕ C).obj (tensorPow X)

/-- Multiplication by concatenation of tensor blocks in the coproduct tensor algebra. -/
def tensorAlgebraMul (X : C) : tensorAlgebraObj X ⊗ tensorAlgebraObj X ⟶ tensorAlgebraObj X :=
  totalTensorDesc fun m n ↦ (tensorPowAddIso X m n).hom ≫ ιTotal (tensorPow X) (n + m)

/-- Multiplying summands of lengths `m` and `n` concatenates their tensor factors and lands in
length `n + m`. The order of addition follows the right-nested tensor-power convention. -/
@[reassoc (attr := simp)]
theorem ιTotal_tensorAlgebraMul (X : C) (m n : ℕ) :
    (ιTotal (tensorPow X) m ⊗ₘ ιTotal (tensorPow X) n) ≫ tensorAlgebraMul X =
      (tensorPowAddIso X m n).hom ≫ ιTotal (tensorPow X) (n + m) :=
  ιTotal_tensorHom_ιTotal_totalTensorDesc _ m n

private theorem tensorAlgebra_one_mul (X : C) :
    ιTotal (tensorPow X) 0 ▷ tensorAlgebraObj X ≫ tensorAlgebraMul X =
      (λ_ (tensorAlgebraObj X)).hom := by
  refine whiskerLeft_total_hom_ext fun n ↦ ?_
  rw [← tensorHom_def'_assoc, ιTotal_tensorAlgebraMul]
  simp

private theorem tensorAlgebra_mul_one (X : C) :
    tensorAlgebraObj X ◁ ιTotal (tensorPow X) 0 ≫ tensorAlgebraMul X =
      (ρ_ (tensorAlgebraObj X)).hom := by
  refine whiskerRight_total_hom_ext fun n ↦ ?_
  rw [← tensorHom_def_assoc, ιTotal_tensorAlgebraMul, tensorPowAddIso_zero_right_hom,
    Category.assoc]
  rw [rightUnitor_naturality]
  rw [← eqToHom_naturality (ιTotal (tensorPow X)) (Nat.zero_add n).symm]
  simp

@[reassoc]
private theorem tensorAlgebra_mul_component (X : C) (m n : ℕ) {A B : C}
    (f : A ⟶ tensorPow X m) (g : B ⟶ tensorPow X n) :
    ((f ≫ ιTotal (tensorPow X) m) ⊗ₘ (g ≫ ιTotal (tensorPow X) n)) ≫ tensorAlgebraMul X =
      (f ⊗ₘ g) ≫ (tensorPowAddIso X m n).hom ≫ ιTotal (tensorPow X) (n + m) := by
  rw [← tensorHom_comp_tensorHom_assoc, ιTotal_tensorAlgebraMul]

private theorem tensorAlgebra_mul_component_left (X : C) (m n : ℕ) {A : C}
    (f : A ⟶ tensorPow X m) :
    ((f ≫ ιTotal (tensorPow X) m) ⊗ₘ ιTotal (tensorPow X) n) ≫ tensorAlgebraMul X =
      f ▷ tensorPow X n ≫ (tensorPowAddIso X m n).hom ≫
        ιTotal (tensorPow X) (n + m) := by
  rw [← whiskerRight_comp_tensorHom_assoc, ιTotal_tensorAlgebraMul]

private theorem tensorAlgebra_mul_component_right (X : C) (m n : ℕ) {B : C}
    (g : B ⟶ tensorPow X n) :
    (ιTotal (tensorPow X) m ⊗ₘ (g ≫ ιTotal (tensorPow X) n)) ≫ tensorAlgebraMul X =
      tensorPow X m ◁ g ≫ (tensorPowAddIso X m n).hom ≫
        ιTotal (tensorPow X) (n + m) := by
  rw [← whiskerLeft_comp_tensorHom_assoc, ιTotal_tensorAlgebraMul]

private theorem tensorAlgebra_mul_assoc (X : C) :
    tensorAlgebraMul X ▷ tensorAlgebraObj X ≫ tensorAlgebraMul X =
      (α_ (tensorAlgebraObj X) (tensorAlgebraObj X) (tensorAlgebraObj X)).hom ≫
        tensorAlgebraObj X ◁ tensorAlgebraMul X ≫ tensorAlgebraMul X := by
  refine total_tensor_tensor_hom_ext fun a b c ↦ ?_
  rw [tensorHom_comp_whiskerRight_assoc, ιTotal_tensorAlgebraMul,
    associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc, ιTotal_tensorAlgebraMul]
  rw [tensorAlgebra_mul_component_left, tensorAlgebra_mul_component_right]
  rw [reassoc_of% (tensorPowAddIso_assoc X a b c)]
  rw [← eqToHom_naturality (ιTotal (tensorPow X)) (Nat.add_assoc c b a)]
  simp

/-- The monoid structure on the coproduct tensor algebra, with its tensor-length-zero unit. -/
@[instance_reducible, instance]
def tensorAlgebraMonObj (X : C) : MonObj (tensorAlgebraObj X) where
  one := ιTotal (tensorPow X) 0
  mul := tensorAlgebraMul X
  one_mul := tensorAlgebra_one_mul X
  mul_one := tensorAlgebra_mul_one X
  mul_assoc := tensorAlgebra_mul_assoc X

/-- The tensor algebra unit is the inclusion of the length-zero summand. -/
@[simp]
theorem tensorAlgebra_one (X : C) :
    MonObj.one (X := tensorAlgebraObj X) = ιTotal (tensorPow X) 0 := (rfl)

/-- The tensor algebra monoid multiplication is concatenation. -/
@[simp]
theorem tensorAlgebra_mul (X : C) :
    MonObj.mul (X := tensorAlgebraObj X) = tensorAlgebraMul X := (rfl)

/-- The coproduct of the tensor powers of a morphism preserves the tensor algebra unit and
multiplication. -/
instance isMonHom_total_map_tensorPowMap {X Y : C} (f : X ⟶ Y) :
    IsMonHom ((total ℕ C).map (tensorPowMap f)) where
  one_hom := by simp
  mul_hom := by
    refine total_tensor_hom_ext fun m n ↦ ?_
    simp only [tensorAlgebra_mul, ιTotal_tensorAlgebraMul_assoc, ιTotal_total_map,
      tensorHom_comp_tensorHom_assoc]
    rw [tensorAlgebra_mul_component, tensorPowAddIso_hom_naturality_assoc]

/-- The coproduct tensor algebra, functorial in its generating object, valued in monoid objects.
The unit and multiplication are given by `tensorAlgebra_one` and `tensorAlgebra_mul`; on tensor
length `n` the induced morphism is `tensorPowMap f n`. -/
-- The object projection must reduce to state formulas for the underlying monoid morphisms.
@[expose]
def tensorAlgebraFunctor : C ⥤ Mon C where
  obj X := Mon.mk (tensorAlgebraObj X)
  map f := { hom := (total ℕ C).map (tensorPowMap f)
             isMonHom_hom := isMonHom_total_map_tensorPowMap f }
  map_id X := Mon.Hom.ext (total_hom_ext fun n ↦ by
    simp [ιTotal_total_map, tensorPowMap_id])
  map_comp f g := Mon.Hom.ext (total_hom_ext fun n ↦ by
    simp [ιTotal_total_map, tensorPowMap_comp])

/-- The underlying object of the tensor algebra functor is the coproduct of tensor powers. -/
@[simp]
theorem tensorAlgebraFunctor_obj_X (X : C) :
    ((tensorAlgebraFunctor (C := C)).obj X).X = tensorAlgebraObj X := (rfl)

/-- On underlying morphisms, the tensor algebra functor is the coproduct of tensor powers. -/
theorem tensorAlgebraFunctor_map_hom {X Y : C} (f : X ⟶ Y) :
    ((tensorAlgebraFunctor (C := C)).map f).hom =
      (total ℕ C).map (tensorPowMap f) := (rfl)

/-- On the tensor-length-`n` summand, the induced monoid morphism is the `n`-fold tensor power
of the morphism on generators. -/
@[simp, reassoc]
theorem ιTotal_tensorAlgebraFunctor_map_hom {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ιTotal (tensorPow X) n ≫ ((tensorAlgebraFunctor (C := C)).map f).hom =
      tensorPowMap f n ≫ ιTotal (tensorPow Y) n := by
  rw [tensorAlgebraFunctor_map_hom]
  exact ιTotal_total_map (tensorPowMap f) n

/-- Monoid morphisms out of the tensor algebra agree if they agree on every tensor-length
summand. For underlying morphisms in `C`, use `GradedObject.total_hom_ext`. -/
@[ext]
theorem tensorAlgebra_hom_ext {X : C} {A : Mon C}
    {f g : Mon.mk (tensorAlgebraObj X) ⟶ A}
    (h : ∀ n, ιTotal (tensorPow X) n ≫ f.hom = ιTotal (tensorPow X) n ≫ g.hom) :
    f = g :=
  Mon.Hom.ext (total_hom_ext h)

/-- A unit-preserving multiplicative family on tensor powers descends to a morphism of monoid
objects out of the coproduct tensor algebra. This is coproduct descent; constructing the family
from a map on generators is separate. -/
def tensorAlgebraDesc (X : C) (A : Mon C) (φ : ∀ n, tensorPow X n ⟶ A.X)
    (h0 : φ 0 = MonObj.one)
    (hmul : ∀ m n, (tensorPowAddIso X m n).hom ≫ φ (n + m) =
      (φ m ⊗ₘ φ n) ≫ MonObj.mul) : Mon.mk (tensorAlgebraObj X) ⟶ A where
  hom := descTotal φ
  isMonHom_hom := {
    one_hom := by
      rw [tensorAlgebra_one, ιTotal_descTotal]
      exact h0
    mul_hom := by
      rw [tensorAlgebra_mul]
      refine total_tensor_hom_ext fun m n ↦ ?_
      rw [ιTotal_tensorAlgebraMul_assoc, tensorHom_comp_tensorHom_assoc,
        ιTotal_descTotal, ιTotal_descTotal, ιTotal_descTotal]
      exact hmul m n }

/-- The descended monoid morphism restricts to the prescribed map on every tensor-length
summand. -/
@[reassoc (attr := simp)]
theorem ιTotal_tensorAlgebraDesc_hom (X : C) (A : Mon C)
    (φ : ∀ n, tensorPow X n ⟶ A.X) (h0 : φ 0 = MonObj.one)
    (hmul : ∀ m n, (tensorPowAddIso X m n).hom ≫ φ (n + m) =
      (φ m ⊗ₘ φ n) ≫ MonObj.mul) (n : ℕ) :
    ιTotal (tensorPow X) n ≫ (tensorAlgebraDesc X A φ h0 hmul).hom = φ n :=
  ιTotal_descTotal φ n

/-- A morphism out of the coproduct tensor algebra is the descent of its restrictions to all
tensor-length summands. -/
theorem tensorAlgebraDesc_unique (X : C) (A : Mon C)
    (φ : ∀ n, tensorPow X n ⟶ A.X) (h0 : φ 0 = MonObj.one)
    (hmul : ∀ m n, (tensorPowAddIso X m n).hom ≫ φ (n + m) =
      (φ m ⊗ₘ φ n) ≫ MonObj.mul) (f : Mon.mk (tensorAlgebraObj X) ⟶ A)
    (hf : ∀ n, ιTotal (tensorPow X) n ≫ f.hom = φ n) :
    f = tensorAlgebraDesc X A φ h0 hmul := by
  apply tensorAlgebra_hom_ext
  intro n
  rw [hf n, ιTotal_tensorAlgebraDesc_hom]

end TauCeti
