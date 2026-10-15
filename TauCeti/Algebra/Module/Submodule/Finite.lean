/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.Order.CompactlyGenerated

/-!
# Finite generation of submodules

An independent family of submodules whose supremum is finitely generated has only finitely
many nonzero members. This specializes `iSupIndep.finite_ne_bot_of_isCompactElement` using the
equivalence between finite generation and compactness in the lattice of submodules.

`Submodule.toAddSubgroup` is reducible and keeps the carrier set, so `p` and `p.toAddSubgroup`
have the same elements and the same `ℤ`-module structure. Instance search is nevertheless keyed
on the head symbol, so a `Module.Finite ℤ p` instance is never tried against the goal
`Module.Finite ℤ p.toAddSubgroup`. This file records that transfer once, for every `ℤ`-submodule,
rather than at each lattice presented to an API that reads additive subgroups.

## Main declarations

* `iSupIndep.finite_ne_bot_of_fg`: an independent family of submodules with finitely generated
  supremum has finite support.
* `TauCeti.instModuleFiniteToAddSubgroup`: a finitely generated `ℤ`-submodule stays finitely
  generated when read as an additive subgroup.
-/

public section

/-- An independent family of submodules spanning a finitely generated submodule has only finitely
many nonzero members. -/
theorem iSupIndep.finite_ne_bot_of_fg {R ι M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {A : ι → Submodule R M} (hAi : iSupIndep A) (hAf : (⨆ i, A i).FG) :
    {i | A i ≠ ⊥}.Finite :=
  hAi.finite_ne_bot_of_isCompactElement ((Submodule.fg_iff_compact _).mp hAf)

namespace TauCeti

/-- A finitely generated `ℤ`-submodule is still finitely generated when read as an additive
subgroup, the two being the same type. -/
instance instModuleFiniteToAddSubgroup {M : Type*} [AddCommGroup M] (p : Submodule ℤ M)
    [Module.Finite ℤ p] : Module.Finite ℤ p.toAddSubgroup :=
  inferInstanceAs (Module.Finite ℤ p)

end TauCeti
