/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# The period map of a period pair

A period pair `L = (ω₁, ω₂)` determines the `ℤ`-linear map `ℤ × ℤ → ℂ`,
`(m, n) ↦ m ω₁ + n ω₂` (`PeriodPair.periodMap`). It is injective, and its range is the lattice
`L.lattice`, so the range is a discrete subgroup of full rank. Unlike `L.lattice` itself, the
domain `ℤ × ℤ` does not depend on `L`: a period pair `ω y` varying with a parameter `y` gives a
family of period maps `y ↦ (ω y).periodMap` with one fixed lattice of marks, which is the input of
the family of one-dimensional complex tori `ℂ / (ℤ ω₁(y) + ℤ ω₂(y))`. If the periods `ω₁(y)` and
`ω₂(y)` are `C^n` in `y`, then so is every period `(ω y).periodMap l`
(`TauCeti.contMDiff_periodMap_apply`).
-/

public section

open scoped Manifold

namespace PeriodPair

variable (L : PeriodPair)

/-- The **period map** `(m, n) ↦ m ω₁ + n ω₂` of a period pair, an isomorphism of `ℤ × ℤ` onto the
lattice `L.lattice` followed by the inclusion into `ℂ`. -/
noncomputable def periodMap : ℤ × ℤ →ₗ[ℤ] ℂ :=
  L.lattice.subtype ∘ₗ L.latticeEquivProd.symm.toLinearMap

@[simp] theorem periodMap_apply (x : ℤ × ℤ) : L.periodMap x = x.1 * L.ω₁ + x.2 * L.ω₂ :=
  L.latticeEquiv_symm_apply x

/-- The period map sends `(1, 0)` to the first period. -/
theorem periodMap_one_zero : L.periodMap (1, 0) = L.ω₁ := by
  simp

/-- The period map sends `(0, 1)` to the second period. -/
theorem periodMap_zero_one : L.periodMap (0, 1) = L.ω₂ := by
  simp

/-- The range of the period map is the lattice of the period pair. -/
theorem range_periodMap : LinearMap.range L.periodMap = L.lattice := by
  rw [periodMap, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]

/-- The period map is injective: the two periods are linearly independent. -/
theorem injective_periodMap : Function.Injective L.periodMap :=
  L.lattice.injective_subtype.comp L.latticeEquivProd.symm.injective

instance : DiscreteTopology (LinearMap.range L.periodMap) :=
  L.range_periodMap ▸ inferInstance

instance : IsZLattice ℝ (LinearMap.range L.periodMap) where
  span_top := by
    rw [range_periodMap]
    exact IsZLattice.span_top

end PeriodPair

namespace TauCeti

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℂ EY] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ EY H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  {n : WithTop ℕ∞}

/-- The periods of a period pair varying `C^n` with a parameter are `C^n`. -/
theorem contMDiff_periodMap_apply {ω : Y → PeriodPair} (hω₁ : ContMDiff I 𝓘(ℂ) n fun y ↦ (ω y).ω₁)
    (hω₂ : ContMDiff I 𝓘(ℂ) n fun y ↦ (ω y).ω₂) (l : ℤ × ℤ) :
    ContMDiff I 𝓘(ℂ) n fun y ↦ (ω y).periodMap l := by
  simp only [PeriodPair.periodMap_apply]
  exact (contMDiff_const.mul hω₁).add (contMDiff_const.mul hω₂)

end TauCeti
