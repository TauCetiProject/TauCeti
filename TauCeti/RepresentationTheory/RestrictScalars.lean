/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Forgetting the scalars of a representation

A representation of a monoid `G` on a `k`-module `V` is in particular a representation on the
underlying abelian group, that is on `V` as a `ℤ`-module for its canonical `ℤ`-module structure,
because every operator is additive. `Representation.restrictScalarsInt` packages this
observation. It is the discrete counterpart of `ContRepresentation.restrictScalarsInt`.

It is what lets a representation that is naturally linear over a larger ring, such as a quotient
`M ⧸ r • M` of a module over the valuation ring of a local field, be compared with integral
representations that carry no such structure, such as the unit group of a local field. Tate
cohomology and the Herbrand quotient of such a comparison are taken in `Rep ℤ G`.

Only the canonical `ℤ`-module structure exists on every abelian group without a choice, which is
why the target ring is `ℤ` rather than an arbitrary subring of `k`.

## Main definitions

* `Representation.restrictScalarsInt`: a representation over `k`, read as a representation over
  `ℤ` with the same operators.
-/

public section

namespace Representation

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A representation on a `k`-module, read as a representation on the underlying abelian group:
each operator is restricted to a `ℤ`-linear map. Its operators are those of `ρ`
(`Representation.restrictScalarsInt_apply`). -/
def restrictScalarsInt (ρ : Representation k G V) : Representation ℤ G V where
  toFun g := (ρ g).restrictScalars ℤ
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- The operators of `ρ.restrictScalarsInt` are those of `ρ`. -/
@[simp]
theorem restrictScalarsInt_apply (ρ : Representation k G V) (g : G) (v : V) :
    ρ.restrictScalarsInt g v = ρ g v :=
  (rfl)

end Representation
