/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The dimension of a Lie submodule

A Lie submodule and its carrier submodule have the same underlying type, so they have the same
dimension; the same holds for a Lie subalgebra and the Lie submodule it becomes over itself. This
file states those definitional equalities once, as the bridges that dimension counts over Lie
submodules pass through: the linear-algebra lemmas about dimensions of direct sums are stated for
`Submodule`, while the Lie-theoretic dimension lemmas are stated for `LieSubmodule`.

## Main results

* `LieSubmodule.finrank_toSubmodule`: a Lie submodule has the dimension of its carrier submodule.
* `LieSubalgebra.finrank_toLieSubmodule`: a Lie subalgebra has the dimension of the Lie submodule
  it determines over itself.
* `LieSubmodule.finrank_bot`: the trivial Lie submodule has dimension zero.
* `LieSubmodule.finrank_eq_zero_of_eq_bot`: the hypothesis form of the same fact.
-/

public section

open Module

namespace LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- The type underlying a Lie submodule is the type underlying its carrier submodule, so the two
have the same dimension. -/
@[simp]
theorem finrank_toSubmodule (N : LieSubmodule R L M) :
    finrank R N.toSubmodule = finrank R N :=
  rfl

variable [Nontrivial R]

/-- **The trivial Lie submodule has dimension zero.** This is the `LieSubmodule` normal form:
`simp` rewrites dimensions of carrier submodules into dimensions of Lie submodules, so it does not
reach `_root_.finrank_bot` for a trivial Lie submodule. -/
@[simp]
theorem finrank_bot : finrank R (⊥ : LieSubmodule R L M) = 0 := by
  rw [← finrank_toSubmodule, bot_toSubmodule, _root_.finrank_bot]

/-- **A trivial Lie submodule has dimension zero.** Unlike `Submodule.finrank_eq_zero`, which is
an equivalence, this needs no finiteness or rank condition. -/
theorem finrank_eq_zero_of_eq_bot {N : LieSubmodule R L M} (h : N = ⊥) : finrank R N = 0 :=
  h ▸ finrank_bot

end LieSubmodule

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The type underlying a Lie subalgebra is the type underlying the Lie submodule it determines
over itself, so the two have the same dimension. -/
@[simp]
theorem finrank_toLieSubmodule (K : LieSubalgebra R L) :
    finrank R K.toLieSubmodule = finrank R K :=
  rfl

end LieSubalgebra
