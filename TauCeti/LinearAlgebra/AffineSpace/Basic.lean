/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Algebra.Module.Basic

/-!
# Scalars of an affine space with two distinct points

If an affine space over a module `V` over a ring `R` has two distinct points, then `R` is
nontrivial (`AddTorsor.nontrivial_of_ne`): over the zero ring every module, hence every torsor
under it, has at most one point.

## Main results

* `AddTorsor.nontrivial_of_ne`: a ring acting on a space with two distinct points is nontrivial.
-/

public section

namespace AddTorsor

variable (R V : Type*) {P : Type*} [Semiring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

include V in
/-- A ring acting on a space with two distinct points is nontrivial. -/
theorem nontrivial_of_ne {a b : P} (hab : a ≠ b) : Nontrivial R := by
  by_contra hR
  have : Subsingleton R := not_nontrivial_iff_subsingleton.1 hR
  exact hab (((AddTorsor.subsingleton_iff V P).1 (Module.subsingleton R V)).elim a b)

end AddTorsor
