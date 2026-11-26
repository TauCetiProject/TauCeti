/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite-dimensionality of submodules over a larger ring

Let `M` be a module over a ring `A` whose action extends that of a division ring `K`
(`IsScalarTower K A M`). If `M` is finite-dimensional over `K`, then so is every `A`-submodule of
`M` (`Submodule.finiteDimensional_of_isScalarTower`). This is the submodule counterpart of
Mathlib's instance `Module.Finite.quotient` for quotients by `A`-submodules, and for `A = K` it is
Mathlib's `FiniteDimensional.finiteDimensional_submodule`.
-/

public section

namespace Submodule

variable {K A M : Type*} [DivisionRing K] [Ring A] [SMul K A] [AddCommGroup M] [Module A M]
  [Module K M] [IsScalarTower K A M] [FiniteDimensional K M]

/-- An `A`-submodule of a module that is finite-dimensional over `K` is finite-dimensional over
`K`, when the `A`-action extends the `K`-action. -/
instance finiteDimensional_of_isScalarTower (N : Submodule A M) : FiniteDimensional K N :=
  .of_injective (N.subtype.restrictScalars K) N.injective_subtype

end Submodule
