/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group
public import Mathlib.Algebra.Module.SpanRank

/-!
# The number of generators of a discriminant group

For a nondegenerate integral lattice `L`, the discriminant group `Lᵛ / L` needs at most
`rank L` generators. We use Mathlib's `Submodule.spanFinrank` for the least number of generators
of a finite abelian group, viewed as a `ℤ`-module.

The quotient map carries a generating set of the free dual lattice to a generating set of the
discriminant group. The dual lattice has the same rank as `L`, so no choice of Gram matrix or
Smith normal form is needed.

## Main declarations

* `TauCeti.IntegralLattice.spanFinrank_discriminantGroup_le_finrank`: the bound `l(A_L) ≤ rank L`.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The discriminant group of a nondegenerate integral lattice needs at most its rank many
generators. The least number of generators is Mathlib's `Submodule.spanFinrank` over `ℤ`. -/
theorem spanFinrank_discriminantGroup_le_finrank (L : IntegralLattice V) [L.IsNondegenerate] :
    (⊤ : Submodule ℤ L.DiscriminantGroup).spanFinrank ≤ Module.finrank ℤ L := by
  have h := Submodule.spanFinrank_map_le_of_fg L.carrierInDual.mkQ
    (Module.Finite.fg_top (R := ℤ) (M := L.dualCarrier))
  rwa [Submodule.map_top, LinearMap.range_eq_top.mpr L.carrierInDual.mkQ_surjective,
    ← Module.finrank_eq_spanFinrank_of_free (R := ℤ) (M := L.dualCarrier),
    L.finrank_dualCarrier, ← L.finrank_carrier] at h

end TauCeti.IntegralLattice
