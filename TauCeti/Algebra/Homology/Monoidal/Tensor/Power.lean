/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy

/-!
# Tensor powers of homotopy equivalences

This file defines a right-associated tensor power of a homological complex in a monoidal
preadditive category and proves that tensor powers preserve homotopy equivalences.  The latter
statement does not require any flatness hypothesis: it is obtained by repeatedly applying the
fact that the total tensor product is functorial on homotopy equivalences.

The construction is intended for tensor resolutions.  In particular, a contraction of one
resolution can be tensored once for every coset before the permutation action on the factors is
introduced.

## Main definitions

* `HomologicalComplex.tensorPower`: the right-associated tensor power of a complex.
* `HomotopyEquiv.tensorPower`: the tensor power of a homotopy equivalence.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C I : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [AddMonoid I]
  {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]
  [∀ K L : HomologicalComplex C c, HasTensor K L]

/-- The right-associated `n`-fold tensor power of a homological complex.  The zeroth tensor power
is the tensor unit. -/
@[expose] noncomputable def tensorPower (K : HomologicalComplex C c) :
    ℕ → HomologicalComplex C c
  | 0 => tensorUnit C c
  | n + 1 => tensorObj K (tensorPower K n)

/-- The zeroth tensor power is the tensor unit. -/
@[simp] theorem tensorPower_zero (K : HomologicalComplex C c) :
    tensorPower K 0 = tensorUnit C c :=
  rfl

/-- A successor tensor power is obtained by tensoring another copy on the left. -/
@[simp] theorem tensorPower_succ (K : HomologicalComplex C c) (n : ℕ) :
    tensorPower K (n + 1) = tensorObj K (tensorPower K n) :=
  rfl

end HomologicalComplex

namespace HomotopyEquiv

open HomologicalComplex

variable {C I : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [AddMonoid I]
  {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]
  [∀ K L : HomologicalComplex C c, HasTensor K L]
  {K L : HomologicalComplex C c}

/-- Tensoring a homotopy equivalence with itself `n` times gives a homotopy equivalence of
tensor powers. -/
noncomputable def tensorPower (e : HomotopyEquiv K L) :
    (n : ℕ) → HomotopyEquiv (K.tensorPower n) (L.tensorPower n)
  | 0 => HomotopyEquiv.refl _
  | n + 1 => mapBifunctor (MonoidalCategory.curriedTensor C) c e (tensorPower e n)

/-- The forward map on the zeroth tensor power is the identity of the tensor unit. -/
@[simp] theorem tensorPower_hom_zero (e : HomotopyEquiv K L) :
    (e.tensorPower 0).hom = 𝟙 _ :=
  (rfl)

/-- The inverse map on the zeroth tensor power is the identity of the tensor unit. -/
@[simp] theorem tensorPower_inv_zero (e : HomotopyEquiv K L) :
    (e.tensorPower 0).inv = 𝟙 _ :=
  (rfl)

/-- The forward map on a successor tensor power is the tensor product of the forward maps. -/
@[simp] theorem tensorPower_hom_succ (e : HomotopyEquiv K L) (n : ℕ) :
    (e.tensorPower (n + 1)).hom = tensorHom e.hom (e.tensorPower n).hom :=
  mapBifunctor_hom e (e.tensorPower n)

/-- The inverse map on a successor tensor power is the tensor product of the inverse maps. -/
@[simp] theorem tensorPower_inv_succ (e : HomotopyEquiv K L) (n : ℕ) :
    (e.tensorPower (n + 1)).inv = tensorHom e.inv (e.tensorPower n).inv :=
  mapBifunctor_inv e (e.tensorPower n)

end HomotopyEquiv
