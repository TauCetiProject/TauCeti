/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.PowerSeries
public import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Constants are integrally closed in Laurent series

For a field `K`, the Laurent series algebraic over `K` are the constants: `K` is integrally closed
in `K⸨X⸩`. A Laurent series integral over `K` is integral over `K⟦X⟧`, so it is a power series,
because `K⟦X⟧` is integrally closed in its fraction field `K⸨X⸩`; and the power series integral
over `K` are the constants (`PowerSeries.isIntegrallyClosedIn`).

For instance a root of unity of `K⸨X⸩` is a constant root of unity. This is what identifies the
automorphisms of a ramified extension `K⸨X⸩ ⊆ K⸨u⸩`, `u ^ d = X`, with rescalings `u ↦ η u` by
roots of unity `η ∈ K`, for every field `K`.

## Main results

* `TauCeti.LaurentSeries.isIntegrallyClosedIn`: `K` is integrally closed in `K⸨X⸩`.
-/

public section

open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

variable (K : Type*) [Field K]

/-- A field `K` is integrally closed in `K⸨X⸩`: the Laurent series algebraic over `K` are the
constants. -/
instance isIntegrallyClosedIn : IsIntegrallyClosedIn K K⸨X⸩ := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap K K⸨X⸩).injective, fun {f} hf ↦ ?_⟩
  -- `f` is integral over `K⟦X⟧`, hence a power series `p`, which is again integral over `K`.
  obtain ⟨p, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hf.tower_top (A := K⟦X⟧))
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    ((isIntegral_algHom_iff (IsScalarTower.toAlgHom K K⟦X⟧ K⸨X⸩)
      (IsFractionRing.injective K⟦X⟧ K⸨X⸩)).mp hf)
  exact ⟨c, (IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩ c).symm⟩

end TauCeti.LaurentSeries
