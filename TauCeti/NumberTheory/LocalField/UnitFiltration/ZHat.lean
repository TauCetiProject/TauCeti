/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
public import TauCeti.Topology.Algebra.Group.Units

/-!
# Lifting `ℤ̂` into the depth-zero unit filtration of a local field

In a nonarchimedean local field `L`, the depth-zero unit filtration `U(L, 0) = 𝒪[L]ˣ` is compact
(`isCompact_unitFiltration 0`) and totally disconnected (as a subgroup of `Lˣ`, since `L` is
totally disconnected). Hence every unit `u : Lˣ` with `valuation L (u : L) = 1` determines a
continuous homomorphism `ℤ̂ →ₜ* Lˣ` sending `zHat.gen` to `u`
(`TauCeti.zHatLiftUnitFiltration`).

## Main definitions

* `TauCeti.compactSpace_unitFiltration`: compactness of each step `unitFiltration L i`.
* `TauCeti.zHatLiftUnitFiltration`: the continuous homomorphism `ℤ̂ →ₜ* Lˣ` sending `zHat.gen` to
  a unit of valuation `1`.

## Main results

* `TauCeti.zHatLiftUnitFiltration_gen`: `zHatLiftUnitFiltration u hu` sends `zHat.gen` to `u`.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

universe u

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Each step `unitFiltration L i` of the unit filtration of a nonarchimedean local field is a
compact space. -/
instance compactSpace_unitFiltration (i : ℕ) : CompactSpace (unitFiltration L i) :=
  isCompact_iff_compactSpace.mp (isCompact_unitFiltration i)

/-- Lift a unit of valuation `1` in a nonarchimedean local field `L` to a continuous homomorphism
`ℤ̂ →ₜ* Lˣ` via the profinite unit group `U(L, 0)`. -/
def zHatLiftUnitFiltration (u : Lˣ) (hu : valuation L (u : L) = 1) : zHat.{u} →ₜ* Lˣ :=
  let incl : unitFiltration L 0 →ₜ* Lˣ := ⟨(unitFiltration L 0).subtype, continuous_subtypeVal⟩
  incl.comp (zHat.lift ⟨u, (mem_unitFiltration_zero _).mpr hu⟩)

/-- The lift `zHatLiftUnitFiltration u hu` sends `zHat.gen` to `u`. -/
@[simp]
theorem zHatLiftUnitFiltration_gen (u : Lˣ) (hu : valuation L (u : L) = 1) :
    zHatLiftUnitFiltration.{u} u hu zHat.gen = u := by
  simp only [zHatLiftUnitFiltration, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    zHat.lift_gen]
  rfl

end TauCeti
