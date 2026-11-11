/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Restricting the scalars of a representation

A representation of a monoid `G` on a `k`-module `V` is also a representation over any semiring
`R` acting on `V` compatibly with `k`, in the sense of `LinearMap.CompatibleSMul V V R k`: every
`k`-linear operator is then `R`-linear. `Representation.restrictScalars` packages this
observation.

The main instance is `R = ℤ` for an additive group `V`, through
`LinearMap.CompatibleSMul.intModule`: `ρ.restrictScalars ℤ` reads `ρ` as a representation on the
underlying abelian group. It is the discrete counterpart of
`ContRepresentation.restrictScalarsInt`. It is what lets a representation that is naturally
linear over a larger ring, such as a quotient `M ⧸ r • M` of a module over the valuation ring of a
local field, be compared with integral representations that carry no such structure, such as the
unit group of a local field. Tate cohomology and the Herbrand quotient of such a comparison are
taken in `Rep ℤ G`.

## Main definitions

* `Representation.restrictScalars`: a representation over `k`, read as a representation over a
  compatible semiring `R` with the same operators.
-/

public section

namespace Representation

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]
variable (R : Type*) [Semiring R] [Module R V] [LinearMap.CompatibleSMul V V R k]

/-- A representation on a `k`-module, read as a representation over a semiring `R` whose action
is compatible with that of `k`: each operator is restricted to an `R`-linear map. For `R = ℤ`
this reads `ρ` as a representation on the underlying abelian group. Its operators are those of
`ρ` (`Representation.restrictScalars_apply`). -/
def restrictScalars (ρ : Representation k G V) : Representation R G V where
  toFun g := (ρ g).restrictScalars R
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- The operators of `ρ.restrictScalars R` are those of `ρ`. -/
@[simp]
theorem restrictScalars_apply (ρ : Representation k G V) (g : G) (v : V) :
    ρ.restrictScalars R g v = ρ g v :=
  (rfl)

end Representation
