/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commensurable
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Commensurable subgroups and the commensurator

Every subgroup is contained in its own commensurator, since conjugation by an element of `H`
fixes `H` and commensurability is reflexive.

## Main statements

* `Subgroup.Commensurable.le_commensurator`: `H ≤ Subgroup.Commensurable.commensurator H`.
-/

public section

namespace Subgroup.Commensurable

/-- Every subgroup is contained in its own commensurator. -/
theorem le_commensurator {G : Type*} [Group G] (H : Subgroup G) : H ≤ commensurator H :=
  fun _ hu ↦ by simpa [Subgroup.conj_smul_eq_self_of_mem hu] using Commensurable.refl H

end Subgroup.Commensurable
