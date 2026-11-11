/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# Free abelian groups are torsion-free

The free abelian group `FreeAbelianGroup α` is isomorphic to the group `α →₀ ℤ` of finitely
supported integer-valued functions (`FreeAbelianGroup.equivFinsupp`), so it is torsion-free.

## Main results

* `FreeAbelianGroup.instIsAddTorsionFree`: a free abelian group is torsion-free.
-/

public section

/-- A free abelian group is torsion-free. -/
instance FreeAbelianGroup.instIsAddTorsionFree {α : Type*} :
    IsAddTorsionFree (FreeAbelianGroup α) :=
  (FreeAbelianGroup.equivFinsupp α).injective.isAddTorsionFree
    (FreeAbelianGroup.equivFinsupp α).toAddMonoidHom
