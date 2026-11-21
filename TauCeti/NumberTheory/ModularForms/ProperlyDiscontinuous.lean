/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
public import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# `SL(2, ℤ)` acts properly discontinuously on the upper half-plane

Mathlib's `properlyDiscontinuousSL2ZRange` makes the image `𝒮ℒ` of `SL(2, ℤ)` in `GL(2, ℝ)` act
properly discontinuously on `ℍ`, but `SL(2, ℤ)` itself, acting through
`UpperHalfPlane.SLAction`, is a type rather than a subgroup of `GL(2, ℝ)`, so that instance does
not apply to it. This file transports it along the injective `Matrix.SpecialLinearGroup.mapGL`.

The module also re-exports `Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup`, whose instance
passes proper discontinuity from a group to each of its subgroups, and
`TauCeti.Topology.Algebra.ConstMulAction`, whose
`TauCeti.finite_stabilizer_of_properlyDiscontinuousSMul` turns proper discontinuity into a
`Finite` instance on point stabilisers. Importing this file therefore gives
`ProperlyDiscontinuousSMul Γ ℍ` and `Finite (MulAction.stabilizer Γ z)` for `SL(2, ℤ)` and for
every `Γ : Subgroup SL(2, ℤ)` by typeclass search.

## Main declarations

* `TauCeti.ModularGroup.properlyDiscontinuousSMul`: `SL(2, ℤ)` acts properly discontinuously on
  `ℍ`.
-/

public section

open scoped MatrixGroups UpperHalfPlane

namespace TauCeti.ModularGroup

/-- **`SL(2, ℤ)` acts properly discontinuously on `ℍ`**, and hence, through Mathlib's subgroup
instance, so does each of its subgroups. In particular every point stabiliser is finite, through
`TauCeti.finite_stabilizer_of_properlyDiscontinuousSMul`, so the elliptic order `e_P` is defined
at every point of `ℍ` and not only inside the fundamental domain. -/
instance properlyDiscontinuousSMul : ProperlyDiscontinuousSMul SL(2, ℤ) ℍ :=
  -- `SL(2, ℤ)` acts through the injective `mapGL ℝ`, onto Mathlib's image group `𝒮ℒ`
  (MonoidHom.rangeRestrict_injective_iff.2
    (Matrix.SpecialLinearGroup.mapGL_injective (R := ℤ) (S := ℝ))).properlyDiscontinuousSMul
    fun _ _ ↦ by
      simp only [Subgroup.smul_def, MonoidHom.coe_rangeRestrict, MulAction.compHom_smul_def]

end TauCeti.ModularGroup

end
