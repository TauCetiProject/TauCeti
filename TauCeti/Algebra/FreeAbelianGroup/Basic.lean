/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# Free abelian groups have unique division

The free abelian group `FreeAddCommGroup α` is isomorphic to the group `α →₀ ℤ` of finitely
supported integer-valued functions (`FreeAddCommGroup.equivFinsupp`), so it has unique division:
`n • a = n • b` with `n ≠ 0` forces `a = b`. In particular it is torsion-free.

## Main results

* `FreeAddCommGroup.instHasUniqueDiv`: a free abelian group has unique division.
-/

public section

/-- A free abelian group has unique division: `n • a = n • b` with `n ≠ 0` forces `a = b`. -/
instance FreeAddCommGroup.instHasUniqueDiv {α : Type*} : HasUniqueDiv (FreeAddCommGroup α) :=
  (FreeAddCommGroup.equivFinsupp α).injective.hasUniqueDiv
    (FreeAddCommGroup.equivFinsupp α).toAddMonoidHom
