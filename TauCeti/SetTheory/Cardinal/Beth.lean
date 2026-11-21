/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Cofinality of beth numbers

The beth function `o ↦ ℶ_ o` is normal (`Cardinal.isNormal_beth`), and so is its composite with
`Cardinal.ord`. A normal function preserves the cofinality of limit ordinals, so at a limit
ordinal `o` the cofinality of `ℶ_ o` is that of `o`. In particular, indexing by the initial
ordinal of a regular cardinal `c` produces a strong limit cardinal `ℶ_ c.ord` of cofinality
exactly `c`; this is the standard way of producing strong limit cardinals of prescribed
cofinality, which is what size-bounding arguments with cutoff cardinals need.

## Main results

* `Cardinal.isNormal_ord_beth`: `o ↦ (ℶ_ o).ord` is a normal function.
* `Cardinal.cof_ord_beth`: at a limit ordinal `o`, `(ℶ_ o).ord.cof = o.cof`.
* `Cardinal.IsRegular.cof_ord_beth_ord`: for a regular cardinal `c`, `(ℶ_ c.ord).ord.cof = c`.
* `Cardinal.IsRegular.isStrongLimit_beth_ord`: for a regular cardinal `c`, `ℶ_ c.ord` is a strong
  limit.
-/

public section

universe u

open Ordinal Order

namespace Cardinal

/-- The ordinal-valued beth function `o ↦ (ℶ_ o).ord` is normal. -/
theorem isNormal_ord_beth : IsNormal fun o : Ordinal.{u} ↦ (ℶ_ o).ord :=
  isNormal_ord.comp isNormal_beth

/-- At a limit ordinal `o`, the beth number `ℶ_ o` has the same cofinality as `o`. -/
theorem cof_ord_beth {o : Ordinal.{u}} (ho : IsSuccLimit o) : (ℶ_ o).ord.cof = o.cof :=
  cof_map_of_isNormal isNormal_ord_beth ho

/-- For a regular cardinal `c`, the beth number indexed by the initial ordinal of `c` has
cofinality exactly `c`. -/
theorem IsRegular.cof_ord_beth_ord {c : Cardinal.{u}} (hc : c.IsRegular) :
    (ℶ_ c.ord).ord.cof = c := by
  rw [cof_ord_beth (isSuccLimit_ord hc.aleph0_le), hc.cof_ord]

/-- For a regular cardinal `c`, the beth number indexed by the initial ordinal of `c` is a strong
limit cardinal. -/
theorem IsRegular.isStrongLimit_beth_ord {c : Cardinal.{u}} (hc : c.IsRegular) :
    IsStrongLimit (ℶ_ c.ord) :=
  isStrongLimit_beth.2 (isSuccLimit_ord hc.aleph0_le).isSuccPrelimit

end Cardinal
