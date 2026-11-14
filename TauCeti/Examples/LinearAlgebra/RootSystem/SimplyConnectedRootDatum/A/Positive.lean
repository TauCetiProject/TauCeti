/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A.Positive

/-!
# The greatest roots of types `A₁`, `A₂` and `A₇`

The pinned datum of type `A₇` has `28` positive roots, and its highest root `e₀ - e₇` has
simple-root coefficients `(1, 1, 1, 1, 1, 1, 1)` and height `7`. In type `A₂` the highest root is
`e₀ - e₂`, the root `e₁ - e₂` is positive while `e₂ - e₁` is not, and the negative root `e₂ - e₀`
has column `(-1, -1)`. In type `A₁` the greatest column is `(1)`.
-/

public section

namespace TauCeti.Examples

open DynkinType

/-- Type `A₇` has `28` positive roots. -/
example : (posRoots (typeASimplyConnectedRootDatum 7) (typeASimplyConnectedBase 7)).ncard = 28 := by
  rw [ncard_posRoots_typeASimplyConnectedRootDatum]
  rfl

/-- Every simple-root coefficient of the highest root of type `A₇` is `1`. -/
example (k : Fin 7) :
    (typeASimplyConnectedBase 7).rootCoefficients (typeASimplyConnectedBase 7).highestRoot
      ⟨typeASimpleIndex 7 k, by
        rw [mem_typeASimplyConnectedBase_support, typeASimpleIndex_val]; exact k.isLt⟩ = 1 :=
  rootCoefficients_highestRoot_typeA k

/-- The highest root of type `A₇` has height `7`. -/
example : (typeASimplyConnectedBase 7).height (typeASimplyConnectedBase 7).highestRoot = 7 := by
  rw [height_highestRoot_typeASimplyConnectedBase]
  rfl

/-- The highest root of type `A₂` is `e₀ - e₂`. -/
example : (typeASimplyConnectedBase 2).highestRoot =
    typeAIndexEquiv 2 ⟨(0, 2), by decide⟩ :=
  highestRoot_typeASimplyConnectedBase

/-- In type `A₂` the negative root `e₂ - e₀` has column `(-1, -1)`. -/
example (k : Fin 2) :
    (typeASimplyConnectedBase 2).rootCoefficients (typeAIndexEquiv 2 ⟨(2, 0), by decide⟩)
      ⟨typeASimpleIndex 2 k, by
        rw [mem_typeASimplyConnectedBase_support, typeASimpleIndex_val]; exact k.isLt⟩ = -1 := by
  rw [rootCoefficients_typeASimplyConnectedBase, coroot_typeAIndexEquiv]
  fin_cases k <;> decide

/-- In type `A₂` the root `e₁ - e₂` is positive and `e₂ - e₁` is not. -/
example : (typeASimplyConnectedBase 2).IsPos (typeAIndexEquiv 2 ⟨(1, 2), by decide⟩) ∧
    ¬ (typeASimplyConnectedBase 2).IsPos (typeAIndexEquiv 2 ⟨(2, 1), by decide⟩) := by
  rw [isPos_typeAIndexEquiv_iff, isPos_typeAIndexEquiv_iff]
  decide

/-- The greatest column of type `A₁` is `(1)`. -/
example : (typeASimplyConnectedBase 1).rootCoefficients (typeASimplyConnectedBase 1).highestRoot
    ⟨typeASimpleIndex 1 0, by
      rw [mem_typeASimplyConnectedBase_support, typeASimpleIndex_val]; exact Fin.isLt 0⟩ = 1 :=
  rootCoefficients_highestRoot_typeA 0

end TauCeti.Examples
