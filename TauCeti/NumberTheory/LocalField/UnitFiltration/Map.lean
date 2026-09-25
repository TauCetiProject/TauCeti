/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic

/-!
# The unit filtration under extension maps

For a compatible extension `L/K` of nonarchimedean local fields, the algebra map multiplies
normalized valuations by the ramification index `e(L/K)`. Consequently it carries the depth-`i`
unit subgroup of `K` into the depth-`e(L/K) i` unit subgroup of `L`.

This file records that compatibility both elementwise and as an inclusion between subgroups. It
is the covariant functoriality of the unit filtration; norm maps in the opposite direction require
the Herbrand function and obey a different formula.

## Main results

* `TauCeti.unitsMap_algebraMap_mem_unitFiltration`: the elementwise compatibility statement.
* `TauCeti.map_unitFiltration_le`: the image of `U(K,i)` is contained in `U(L,e(L/K)i)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- The algebra map from `K` to `L` carries a depth-`i` unit into a depth-`e(L/K) i` unit.
Here `e(L/K)` is the ramification index. -/
theorem unitsMap_algebraMap_mem_unitFiltration {i : ℕ} {x : Kˣ}
    (hx : x ∈ unitFiltration K i) :
    Units.map (algebraMap K L : K →* L) x ∈
      unitFiltration L (ramificationIndex K L * i) := by
  obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.mp hx
  refine mem_unitFiltration_iff_exists.mpr
    ⟨Units.map (algebraMap 𝒪[K] 𝒪[L] : 𝒪[K] →* 𝒪[L]) u, ?_, ?_⟩
  · have hu' : algebraMap 𝒪[K] 𝒪[L] ((u : 𝒪[K]) - 1) ∈
        (𝓂[K] ^ i).map (algebraMap 𝒪[K] 𝒪[L]) :=
      Ideal.mem_map_of_mem (algebraMap 𝒪[K] 𝒪[L]) hu
    rw [map_sub, map_one, Ideal.map_pow, map_maximalIdeal_eq_maximalIdeal_pow K L] at hu'
    simpa only [Units.coe_map, MonoidHom.coe_ofClass, pow_mul] using hu'
  · simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rw [coe_algebraMap_integerRing]
    exact congrArg (algebraMap K L) hux

variable (K L) in
/-- The image of the depth-`i` unit subgroup of `K` under the algebra map is contained in the
depth-`e(L/K) i` unit subgroup of `L`. -/
theorem map_unitFiltration_le (i : ℕ) :
    (unitFiltration K i).map (Units.map (algebraMap K L : K →* L)) ≤
      unitFiltration L (ramificationIndex K L * i) := by
  rintro y ⟨x, hx, rfl⟩
  exact unitsMap_algebraMap_mem_unitFiltration hx

end TauCeti
