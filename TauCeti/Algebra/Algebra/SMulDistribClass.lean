/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic

/-!
# Semilinear actions are linear over the fixed scalars

Let `G` act on an `A`-algebra `B` by `A`-algebra automorphisms. A *semilinear* action of `G` on a
`B`-module `N` is a distributive action with `g • (b • n) = (g • b) • (g • n)` (Mathlib's
`SMulDistribClass G B N`). Since `G` fixes the image of `A` in `B`, such an action commutes with
the action of `A`, so the invariants of `N` form an `A`-submodule.

## Main results

* `TauCeti.MulSemiringAction.smulCommClass_of_smulDistribClass`: a `B`-semilinear action is
  `A`-linear.
-/

public section

namespace TauCeti.MulSemiringAction

variable (A B G : Type*) [CommSemiring A] [Semiring B] [Algebra A B] [Monoid G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- A `B`-semilinear action of `G` on `N` is `A`-linear, since `G` fixes the image of `A`. Thus
the invariants of `N` form an `A`-submodule. -/
theorem smulCommClass_of_smulDistribClass (N : Type*) [AddCommMonoid N] [Module A N] [Module B N]
    [IsScalarTower A B N] [DistribMulAction G N] [SMulDistribClass G B N] :
    SMulCommClass G A N where
  smul_comm g a n := by
    rw [← algebraMap_smul B a n, smul_distrib_smul, smul_algebraMap, algebraMap_smul]

end TauCeti.MulSemiringAction
