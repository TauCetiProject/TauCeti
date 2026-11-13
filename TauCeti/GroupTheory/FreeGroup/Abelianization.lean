/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import TauCeti.Algebra.FreeAbelianGroup.Basic

/-!
# The abelianization of a free group has unique roots

The free abelian group `FreeAbelianGroup α` has unique division
(`FreeAbelianGroup.instHasUniqueDiv`), and it is by definition the additive version of the
abelianization of the free group `FreeGroup α`. Hence the abelianization of every free group has
unique roots, and in particular is torsion-free: if `g ^ n` lies in the commutator subgroup of a
free group for some `n ≠ 0`, then so does `g`.

## Main results

* `IsFreeGroup.instHasUniqueRootsAbelianization`: the abelianization of a free group has unique
  roots.
-/

public section

namespace IsFreeGroup

/-- The abelianization of a free group has unique roots: `a ^ n = b ^ n` with `n ≠ 0` forces
`a = b`. In particular it is torsion-free. -/
instance instHasUniqueRootsAbelianization {G : Type*} [Group G] [IsFreeGroup G] :
    HasUniqueRoots (Group.Abelianization G) :=
  -- `FreeAbelianGroup α` is defined as `Additive (Group.Abelianization (FreeGroup α))`.
  have : HasUniqueRoots (Group.Abelianization (FreeGroup (Generators G))) :=
    inferInstanceAs (HasUniqueRoots (Multiplicative (FreeAbelianGroup _)))
  (toFreeGroup G).abelianizationCongr.injective.hasUniqueRoots
    (toFreeGroup G).abelianizationCongr.toMonoidHom

end IsFreeGroup
