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
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Lifting `ℤ̂` into the depth-zero unit filtration of a local field

In a nonarchimedean local field `L`, the depth-zero unit filtration `U(L, 0) = 𝒪[L]ˣ` is compact
(`compactSpace_unitFiltration 0`) and totally disconnected (as a subgroup of `Lˣ`, since `L` is
totally disconnected). Hence every unit `u : Lˣ` with `valuation L (u : L) = 1` determines a
continuous homomorphism `ℤ̂ →ₜ* Lˣ` sending `zHat.gen` to `u`
(`TauCeti.zHatLiftUnitFiltration`).

## Main definitions

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

/-- Lift a unit of valuation `1` in a nonarchimedean local field `L` to a continuous homomorphism
`ℤ̂ →ₜ* Lˣ` via the profinite unit group `U(L, 0)`. -/
def zHatLiftUnitFiltration (u : Lˣ) (hu : valuation L (u : L) = 1) : zHat.{u} →ₜ* Lˣ :=
  (TauCeti.ContinuousMonoidHom.subgroupSubtype (unitFiltration L 0)).comp
    (zHat.lift ⟨u, (mem_unitFiltration_zero _).mpr hu⟩)

/-- The lift `zHatLiftUnitFiltration u hu` sends `zHat.gen` to `u`. -/
@[simp]
theorem zHatLiftUnitFiltration_gen (u : Lˣ) (hu : valuation L (u : L) = 1) :
    zHatLiftUnitFiltration.{u} u hu zHat.gen = u := by
  simp only [zHatLiftUnitFiltration, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    zHat.lift_gen, TauCeti.ContinuousMonoidHom.subgroupSubtype_apply]

end TauCeti
