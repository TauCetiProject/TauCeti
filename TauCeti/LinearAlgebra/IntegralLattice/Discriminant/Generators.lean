/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Primary.Generators
public import TauCeti.GroupTheory.Rank
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group

/-!
# The number of generators of a discriminant group

For a nondegenerate integral lattice `L`, the discriminant group `Lᵛ / L` and each of its
`n`-primary components need at most `rank L` generators.

The quotient map carries a generating set of the free dual lattice to a generating set of the
discriminant group. The dual lattice has the same rank as `L`, so no choice of Gram matrix or
Smith normal form is needed.

## Main declarations

* `TauCeti.IntegralLattice.spanFinrank_discriminantGroup_le_finrank`: the bound `l(A_L) ≤ rank L`.
* `TauCeti.IntegralLattice.rank_primaryComponent_discriminantGroup_le_finrank`: the bound
  `AddGroup.rank (A_L)_n ≤ rank L` for every `n : ℕ`.
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

/-- Every `n`-primary component of the discriminant group of a nondegenerate integral lattice has
`AddGroup.rank` at most `rank L`. -/
theorem rank_primaryComponent_discriminantGroup_le_finrank (L : IntegralLattice V)
    [L.IsNondegenerate] (n : ℕ) :
    AddGroup.rank (AddCommGroup.primaryComponent L.DiscriminantGroup n) ≤ Module.finrank ℤ L := by
  refine (AddCommGroup.rank_primaryComponent_le L.DiscriminantGroup n).trans ?_
  rw [AddGroup.rank_eq_spanFinrank_top]
  exact L.spanFinrank_discriminantGroup_le_finrank

end TauCeti.IntegralLattice
