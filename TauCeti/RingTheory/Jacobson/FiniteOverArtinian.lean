/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Ring

/-!
# The Jacobson radical of a ring finite over an Artinian ring

This file packages the standard Artinian-ring API for a ring `A` that is a finitely generated
module over an Artinian ring `K` acting compatibly with its multiplication
(`IsScalarTower K A A`). The motivating case is a finite-dimensional algebra over a field, or more
generally a ring finite-dimensional over a division ring. For such an `A`, its Jacobson radical is
nilpotent, the quotient by the radical is semisimple, and `A` itself is semisimple exactly when the
radical vanishes.

Mathlib proves all three statements for an arbitrary left Artinian ring. The only bridge supplied
here is the standard implication from finiteness over an Artinian ring to the Artinian condition,
via `IsArtinianRing.of_finite`. The mathematical inputs are:

* `IsArtinianRing.isSemisimpleRing_iff_jacobson`, the semisimplicity criterion; and
* the `IsSemiprimaryRing` instance on an Artinian ring, which provides nilpotence of the radical
  (`IsSemiprimaryRing.isNilpotent`) and semisimplicity of the quotient by it
  (`IsSemiprimaryRing.isSemisimpleRing`).

## Main results

* `TauCeti.isSemisimpleRing_iff_jacobson_eq_bot`: such a ring is semisimple if and only if its
  Jacobson radical is zero.
* `TauCeti.isNilpotent_jacobson`: the Jacobson radical of such a ring is nilpotent.
* `TauCeti.isSemisimpleRing_quotient_jacobson`: the quotient of such a ring by its Jacobson radical
  is semisimple.
-/

public section

namespace TauCeti

universe u v

variable {K : Type u} {A : Type v} [Ring K] [IsArtinianRing K] [Ring A] [Module K A]
  [IsScalarTower K A A] [Module.Finite K A]

include K

/-- A ring finite over an Artinian ring is semisimple if and only if its Jacobson radical
vanishes. -/
theorem isSemisimpleRing_iff_jacobson_eq_bot :
    IsSemisimpleRing A ↔ Ring.jacobson A = ⊥ :=
  have := IsArtinianRing.of_finite K A
  IsArtinianRing.isSemisimpleRing_iff_jacobson

/-- The Jacobson radical of a ring finite over an Artinian ring is nilpotent. -/
theorem isNilpotent_jacobson : IsNilpotent (Ring.jacobson A) :=
  have := IsArtinianRing.of_finite K A
  IsSemiprimaryRing.isNilpotent

/-- The quotient of a ring finite over an Artinian ring by its Jacobson radical is semisimple. -/
theorem isSemisimpleRing_quotient_jacobson : IsSemisimpleRing (A ⧸ Ring.jacobson A) :=
  have := IsArtinianRing.of_finite K A
  IsSemiprimaryRing.isSemisimpleRing

end TauCeti
