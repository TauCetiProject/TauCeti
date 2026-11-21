/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic

/-!
# Continuous automorphisms of a discrete group

For a discrete topology every map is continuous, so every abstract automorphism of `G` is a
continuous automorphism and forgetting continuity is an isomorphism
`ContinuousAut G ≃* MulAut G`. It carries the continuous inner automorphisms onto the inner
automorphisms, so for a discrete group the continuous outer automorphism group
`TauCeti.ContinuousOut G` is the outer automorphism group `TauCeti.OuterAut G` of the underlying
abstract group. For a nondiscrete topology the two groups differ in general: for the additive
reals with their usual topology the continuous automorphisms are the dilations, while a
`ℚ`-linear exchange of two elements of a Hamel basis is an abstract automorphism that is not
continuous.

## Main definitions

* `TauCeti.ContinuousAut.mulEquivMulAutOfDiscrete`: for discrete `G`, the forgetful map
  `ContinuousAut G →* MulAut G` as an isomorphism.
* `TauCeti.ContinuousOut.mulEquivOuterAutOfDiscrete`: for a discrete group `G`,
  `ContinuousOut G ≃* OuterAut G`.

## Main results

* `TauCeti.ContinuousAut.map_mulEquivMulAutOfDiscrete_range_conj`: the forgetful isomorphism
  carries the continuous inner automorphisms onto the inner automorphisms.
-/

public section

namespace TauCeti

namespace ContinuousAut

section Mul

variable {G : Type*} [Mul G] [TopologicalSpace G] [DiscreteTopology G]

/-- For a discrete topology every automorphism is continuous, so forgetting continuity is an
isomorphism from the continuous automorphisms onto all automorphisms. -/
def mulEquivMulAutOfDiscrete : ContinuousAut G ≃* MulAut G where
  toFun := toMulAut
  invFun φ :=
    { φ with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  left_inv φ := ContinuousMulEquiv.ext fun x ↦ by simp
  right_inv φ := MulEquiv.ext fun x ↦ by simp
  map_mul' := map_mul toMulAut

@[simp]
theorem mulEquivMulAutOfDiscrete_apply (φ : ContinuousAut G) :
    mulEquivMulAutOfDiscrete φ = toMulAut φ :=
  (rfl)

@[simp]
theorem coe_mulEquivMulAutOfDiscrete_symm (φ : MulAut G) :
    ⇑(mulEquivMulAutOfDiscrete.symm φ) = φ :=
  (rfl)

end Mul

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- The forgetful isomorphism of a discrete group carries the continuous inner automorphisms onto
the inner automorphisms. -/
theorem map_mulEquivMulAutOfDiscrete_range_conj :
    (conj : G →* ContinuousAut G).range.map
        ((mulEquivMulAutOfDiscrete : ContinuousAut G ≃* MulAut G) : ContinuousAut G →* MulAut G) =
      (MulAut.conj : G →* MulAut G).range := by
  rw [MonoidHom.map_range]
  exact congrArg MonoidHom.range (MonoidHom.ext toMulAut_conj)

end Group

end ContinuousAut

namespace ContinuousOut

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- For a discrete group the continuous outer automorphism group is the outer automorphism group
of the underlying abstract group. -/
def mulEquivOuterAutOfDiscrete : ContinuousOut G ≃* OuterAut G :=
  QuotientGroup.congr _ _ ContinuousAut.mulEquivMulAutOfDiscrete
    ContinuousAut.map_mulEquivMulAutOfDiscrete_range_conj

@[simp]
theorem mulEquivOuterAutOfDiscrete_mk (φ : ContinuousAut G) :
    mulEquivOuterAutOfDiscrete (φ : ContinuousOut G) =
      (ContinuousAut.toMulAut φ : OuterAut G) :=
  (rfl)

@[simp]
theorem mulEquivOuterAutOfDiscrete_symm_mk (φ : MulAut G) :
    mulEquivOuterAutOfDiscrete.symm (φ : OuterAut G) =
      (ContinuousAut.mulEquivMulAutOfDiscrete.symm φ : ContinuousOut G) :=
  (rfl)

end ContinuousOut

end TauCeti
