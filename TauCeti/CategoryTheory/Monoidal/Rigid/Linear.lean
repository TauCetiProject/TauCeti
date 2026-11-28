/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive

/-!
# Linearity of rigid dual functors

The instance `TauCeti.instLinearDoubleRightDualFunctor` makes the double right dual functor linear
over the ground semiring of a linear monoidal category. Rescaling a double-dual structure map
by `r` therefore rescales its composite with its double dual by `r ^ 2`. This turns normalization
into a square-root problem and allows the two signed lifts to be classified for objects with scalar
endomorphisms over an algebraically closed field of characteristic different from two.
The instance uses
`TauCeti.doubleRightDualFunctor_map` and `TauCeti.rightAdjointMate_smul`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

variable {C : Type*} [Category* C] [MonoidalCategory C] [RightRigidCategory C]

/-- The double right dual functor is linear in a linear monoidal category. -/
instance instLinearDoubleRightDualFunctor {R : Type*} [Semiring R] [Preadditive C]
    [Linear R C] [MonoidalPreadditive C] [MonoidalLinear R C] :
    (doubleRightDualFunctor C).Linear R where
  map_smul {X Y} f r := by
    have h : (r • f)ᘁᘁ = r • fᘁᘁ := by simp only [rightAdjointMate_smul]
    have hmap : r • (doubleRightDualFunctor C).map f = r • fᘁᘁ :=
      congrArg (fun g : (Xᘁ : C)ᘁ ⟶ (Yᘁ : C)ᘁ ↦ r • g) (doubleRightDualFunctor_map f)
    exact (doubleRightDualFunctor_map (r • f)).trans (h.trans hmap.symm)

end TauCeti
