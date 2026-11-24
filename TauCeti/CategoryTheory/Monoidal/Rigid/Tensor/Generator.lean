/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Tensor generators

An object `X` with a right dual `Xᘁ` in a monoidal category with finite biproducts
*tensor-generates* the category if every object is a quotient of a subobject of a finite
direct sum of tensor words

```text
X^{⊗ a} ⊗ (Xᘁ)^{⊗ b},
```

where a tensor power with exponent zero is the tensor unit (`TauCeti.tensorPow`). Equivalently,
every object is a subquotient of `P(X, Xᘁ)` for a polynomial `P` with natural coefficients in
two variables. For the representations of an affine group scheme over a field, this is the
categorical form of the coordinate algebra being finitely generated (Deligne–Milne,
Proposition 2.20(b)).

Tensor generation is weaker than generation under finite sums and subquotients alone: the
degree-one character of `𝔾ₘ` tensor-generates its representations, but its finite sums and
subquotients only contain representations of weight one.

## Main declaration

* `TauCeti.IsTensorGenerator`: the object `X` tensor-generates with its right dual, unfolded by
  `TauCeti.isTensorGenerator_iff`.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Proposition 2.20.
-/

public section

open CategoryTheory MonoidalCategory Limits

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]
  [HasFiniteBiproducts C]

/-- An object `X` with a right dual `Xᘁ` *tensor-generates* `C` if every object of `C` is a
quotient of a subobject of a finite direct sum of tensor words `X^{⊗ a} ⊗ (Xᘁ)^{⊗ b}`; a tensor
power with exponent zero is the tensor unit. -/
def IsTensorGenerator (X : C) [HasRightDual X] : Prop :=
  ∀ Y : C, ∃ (ι : Type) (_ : Finite ι) (a b : ι → ℕ) (Z : C)
    (i : Z ⟶ ⨁ fun j ↦ tensorPow X (a j) ⊗ tensorPow Xᘁ (b j)) (p : Z ⟶ Y), Mono i ∧ Epi p

/-- Unfolding `IsTensorGenerator`: every object is a quotient of a subobject of a finite direct
sum of tensor words in `X` and `Xᘁ`. -/
theorem isTensorGenerator_iff (X : C) [HasRightDual X] :
    IsTensorGenerator X ↔ ∀ Y : C, ∃ (ι : Type) (_ : Finite ι) (a b : ι → ℕ) (Z : C)
      (i : Z ⟶ ⨁ fun j ↦ tensorPow X (a j) ⊗ tensorPow Xᘁ (b j)) (p : Z ⟶ Y), Mono i ∧ Epi p :=
  Iff.rfl

end TauCeti
