/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.Analysis.Semigroups.Group.Basic

/-!
# Strongly continuous representations of the real line as C₀-groups

A continuous representation `π` of `Multiplicative ℝ` on a real or complex normed space whose
orbits `g ↦ π g v` are continuous is a strongly continuous one-parameter group `t ↦ π (ofAdd t)`
of real operators in the sense of the semigroup development,
`ContRepresentation.toStronglyContinuousGroup`. This makes the generator theory of C₀-groups
available for representations of `ℝ`.
-/

public section

noncomputable section

open TauCeti.Semigroups

namespace ContRepresentation

/-- A continuous representation of `ℝ` with continuous orbits, regarded as a strongly continuous
one-parameter group of real operators. -/
def toStronglyContinuousGroup {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] (π : ContRepresentation 𝕜 (Multiplicative ℝ) V)
    (hπ : ∀ v, Continuous fun g => π g v) :
    StronglyContinuousGroup V where
  toFun t := (π (Multiplicative.ofAdd t)).restrictScalars ℝ
  map_zero' := by
    ext v
    simp
  map_add' s t := by
    ext v
    simp [ofAdd_add, map_mul]
  continuousAt_zero' v := ((hπ v).comp continuous_ofAdd).continuousAt

@[simp]
theorem toStronglyContinuousGroup_apply {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
    (π : ContRepresentation 𝕜 (Multiplicative ℝ) V) (hπ : ∀ v, Continuous fun g => π g v)
    (t : ℝ) (v : V) : π.toStronglyContinuousGroup hπ t v = π (Multiplicative.ofAdd t) v :=
  (rfl)

end ContRepresentation
