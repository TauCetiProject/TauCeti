/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import TauCeti.Algebra.FreeAbelianGroup.Basic

/-!
# The abelianization of a free group is torsion-free

The free abelian group `FreeAbelianGroup α` is torsion-free
(`FreeAbelianGroup.instIsAddTorsionFree`), and it is by definition the additive version of the
abelianization of the free group `FreeGroup α`. Hence the abelianization of every free group is
torsion-free: if `g ^ n` lies in the commutator subgroup of a free group for some `n ≠ 0`, then
so does `g`.

## Main results

* `IsFreeGroup.instIsMulTorsionFreeAbelianization`: the abelianization of a free group is
  torsion-free.
-/

public section

namespace IsFreeGroup

/-- The abelianization of a free group is torsion-free. -/
instance instIsMulTorsionFreeAbelianization {G : Type*} [Group G] [IsFreeGroup G] :
    IsMulTorsionFree (Abelianization G) :=
  -- `FreeAbelianGroup α` is defined as `Additive (Abelianization (FreeGroup α))`.
  have : IsMulTorsionFree (Abelianization (FreeGroup (Generators G))) :=
    inferInstanceAs (IsMulTorsionFree (Multiplicative (FreeAbelianGroup _)))
  (toFreeGroup G).abelianizationCongr.injective.isMulTorsionFree
    (toFreeGroup G).abelianizationCongr.toMonoidHom

end IsFreeGroup
