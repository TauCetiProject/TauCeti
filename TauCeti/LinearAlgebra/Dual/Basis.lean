/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Rank of the dual of a finite free module

The linear dual of a finite free module over a commutative ring has the same rank as the module,
since a finite basis identifies the module with its dual (`Module.Basis.toDualEquiv`). Over a
field this is Mathlib's `Subspace.dual_finrank_eq`.

## Main results

* `TauCeti.Module.dual_finrank_eq`: `finrank R (Dual R M) = finrank R M` for a finite free
  module `M`.
-/

public section

namespace TauCeti.Module

/-- A finite free module and its linear dual have the same rank. Over a field this is
`Subspace.dual_finrank_eq`. -/
@[simp]
theorem dual_finrank_eq (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (Module.Dual R M) = Module.finrank R M := by
  classical
  exact (Module.Free.chooseBasis R M).toDualEquiv.finrank_eq.symm

end TauCeti.Module
