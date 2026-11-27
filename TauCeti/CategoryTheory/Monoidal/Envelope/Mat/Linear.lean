/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Mat
public import TauCeti.CategoryTheory.Monoidal.Envelope.Mat.Basic
public import TauCeti.CategoryTheory.Monoidal.Linear

/-!
# Monoidal linearity of the matrix category

If tensoring in `C` is linear in each variable, so is the Kronecker product of morphism
matrices in its additive envelope `Mat_ C`. In particular, the additive envelope of
the linear tensor product of two monoidal linear categories is again monoidal linear.
-/

public section

namespace CategoryTheory.Mat_

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C]

/-- The additive envelope of a monoidal linear category is monoidal linear. -/
instance instMonoidalLinear : MonoidalLinear R (Mat_ C) where
  whiskerLeft_smul _ {_ _} r f := by ext i j; simp
  smul_whiskerRight r {_ _} f _ := by ext i j; simp

end CategoryTheory.Mat_
