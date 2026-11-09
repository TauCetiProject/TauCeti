/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# The left-factor action on a base change is semilinear

Let `G` act on a commutative `A`-algebra `B` by ring automorphisms commuting with `A`. Mathlib
lets `G` act on the left factor of `B ⊗[A] M` (`TensorProduct.leftDistribMulAction`). This action
is `B`-semilinear: `g • (b • z) = (g • b) • (g • z)`. Mathlib has no such `SMulDistribClass`
instance.

## Main results

* `TauCeti.MulSemiringAction.smulDistribClass_tensorProduct`: the action of `G` on the left factor
  of `B ⊗[A] M` is `B`-semilinear.
-/

public section

open TensorProduct

namespace TauCeti.MulSemiringAction

variable (A B G : Type*) [CommSemiring A] [CommSemiring B] [Algebra A B] [Monoid G]
  [MulSemiringAction G B] [SMulCommClass A G B] (M : Type*) [AddCommMonoid M] [Module A M]

/-- The action of `G` on the left factor of `B ⊗[A] M` is `B`-semilinear. -/
instance smulDistribClass_tensorProduct : SMulDistribClass G B (B ⊗[A] M) where
  smul_distrib_smul g b z := by
    induction z using TensorProduct.inductionOn with
    | tmul x m => simp [smul_tmul', smul_mul']
    | add x y hx hy => simp only [smul_add, hx, hy]

end TauCeti.MulSemiringAction
