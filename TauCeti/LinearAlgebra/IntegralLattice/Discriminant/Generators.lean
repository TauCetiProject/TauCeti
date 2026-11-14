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
`n`-primary components need at most `rank L` generators. We provide the bounds both for Mathlib's
`Submodule.spanFinrank` over `ℤ` and for `AddGroup.rank`.

The quotient map carries a generating set of the free dual lattice to a generating set of the
discriminant group. The dual lattice has the same rank as `L`, so no choice of Gram matrix or
Smith normal form is needed.

## Main declarations

* `TauCeti.IntegralLattice.spanFinrank_discriminantGroup_le_finrank` and
  `TauCeti.IntegralLattice.rank_discriminantGroup_le_finrank`: the bound `l(A_L) ≤ rank L`.
* `TauCeti.IntegralLattice.spanFinrank_primaryComponent_discriminantGroup_le_finrank` and
  `TauCeti.IntegralLattice.rank_primaryComponent_discriminantGroup_le_finrank`: the bound
  `l((A_L)_n) ≤ rank L` for every `n : ℕ`.
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

/-- The discriminant group of a nondegenerate integral lattice has `AddGroup.rank` at most the
lattice rank. -/
theorem rank_discriminantGroup_le_finrank (L : IntegralLattice V) [L.IsNondegenerate] :
    AddGroup.rank L.DiscriminantGroup ≤ Module.finrank ℤ L := by
  rw [AddGroup.rank_eq_spanFinrank_top]
  exact L.spanFinrank_discriminantGroup_le_finrank

/-- Every `n`-primary component of the discriminant group of a nondegenerate integral lattice needs
at most `rank L` generators (measured by `Submodule.spanFinrank` over `ℤ`). -/
theorem spanFinrank_primaryComponent_discriminantGroup_le_finrank (L : IntegralLattice V)
    [L.IsNondegenerate] (n : ℕ) :
    (⊤ : Submodule ℤ (AddCommGroup.primaryComponent L.DiscriminantGroup n)).spanFinrank ≤
      Module.finrank ℤ L :=
  (AddCommGroup.spanFinrank_primaryComponent_le L.DiscriminantGroup n).trans
    L.spanFinrank_discriminantGroup_le_finrank

/-- Every `n`-primary component of the discriminant group of a nondegenerate integral lattice has
`AddGroup.rank` at most `rank L`. -/
theorem rank_primaryComponent_discriminantGroup_le_finrank (L : IntegralLattice V)
    [L.IsNondegenerate] (n : ℕ) :
    AddGroup.rank (AddCommGroup.primaryComponent L.DiscriminantGroup n) ≤ Module.finrank ℤ L := by
  rw [AddGroup.rank_eq_spanFinrank_top]
  exact L.spanFinrank_primaryComponent_discriminantGroup_le_finrank n

end TauCeti.IntegralLattice
