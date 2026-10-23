/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Zero objects in `TopModuleCat`

A topological module whose carrier is a subsingleton is a zero object of `TopModuleCat R`
(`TopModuleCat.isZero_of_subsingleton`), the counterpart for `TopModuleCat R` of
`ModuleCat.isZero_of_subsingleton`. It turns the vanishing of a cohomology module of
`TopModuleCat R`, recorded as a `Subsingleton` instance on its carrier, into the categorical
statement `IsZero` used by bundled interfaces.
-/

public section

open CategoryTheory Limits

namespace TopModuleCat

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- A topological module whose carrier is a subsingleton is a zero object, as in
`ModuleCat.isZero_of_subsingleton`. -/
theorem isZero_of_subsingleton (M : TopModuleCat R) [Subsingleton M] : IsZero M :=
  (IsZero.iff_id_eq_zero M).2 (by ext x; exact Subsingleton.elim _ _)

end TopModuleCat
