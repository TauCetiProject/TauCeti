/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic

/-!
# Scalar towers on the quotient of a presentation

The module `relations.Quotient` presented by `relations : Module.Relations A` is the quotient of
the free module `relations.G →₀ A` by the span of the relations. Mathlib equips it with its
`A`-module structure only. When `A` is itself an algebra over a ring `S` — a group ring `R[G]`
over `R`, say — the free module is an `S`-module compatibly with its `A`-module structure, and so
is the quotient. This file records that `S`-module structure and the scalar tower, which is what
lets a presented `A`-module be tensored over `S`, as in the base change of a module over an
integral group ring `ℤ_p[G]` to `ℚ_p`.

## Main results

* `Module.Relations.Quotient.module'`: the `S`-module structure on `relations.Quotient` for a
  ring `S` acting on `A` compatibly with multiplication.
* `Module.Relations.Quotient.isScalarTower`: `S`, `A` and `relations.Quotient` form a scalar
  tower.
-/

public section

namespace Module.Relations

variable {A : Type*} [Ring A] (relations : Relations A) (S : Type*) [Semiring S] [Module S A]
  [IsScalarTower S A A]

/-- The quotient of a presentation of an `A`-module is a module over any ring `S` acting on `A`
compatibly with multiplication, by the `S`-module structure of the quotient of the free
`A`-module `relations.G →₀ A`. -/
noncomputable instance Quotient.module' : Module S relations.Quotient :=
  inferInstanceAs (Module S ((relations.G →₀ A) ⧸ Submodule.span A (Set.range relations.relation)))

/-- The `S`- and `A`-module structures on the quotient of a presentation form a scalar tower. -/
noncomputable instance Quotient.isScalarTower : IsScalarTower S A relations.Quotient :=
  inferInstanceAs
    (IsScalarTower S A ((relations.G →₀ A) ⧸ Submodule.span A (Set.range relations.relation)))

end Module.Relations
