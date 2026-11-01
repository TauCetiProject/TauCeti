/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.Analysis.Semigroups.Group.Unitary
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Strongly continuous representations of the real line as C₀-groups

A continuous representation `π` of the real line, written multiplicatively as
`Multiplicative ℝ`, on a complex normed space whose orbits `g ↦ π g v` are continuous is a
strongly continuous one-parameter group `t ↦ π (ofAdd t)` of real operators,
`ContRepresentation.toStronglyContinuousGroup`. When `π` is unitary on a complex inner product
space, so is this group, `ContRepresentation.isUnitary_toStronglyContinuousGroup`; its
self-adjoint Stone generator `H` then satisfies `π (ofAdd t) = exp (i t H)`.
-/

public section

noncomputable section

open TauCeti.Semigroups

namespace ContRepresentation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A representation of the real line with continuous orbits, as the strongly continuous
one-parameter group `t ↦ π (ofAdd t)` of real operators. -/
def toStronglyContinuousGroup (π : ContRepresentation ℂ (Multiplicative ℝ) V)
    (hπ : ∀ v, Continuous fun g => π g v) : StronglyContinuousGroup V where
  toFun t := (π (Multiplicative.ofAdd t)).restrictScalars ℝ
  map_zero' := by
    ext v
    simp
  map_add' s t := by
    ext v
    simp [ofAdd_add, map_mul]
  continuousAt_zero' v := ((hπ v).comp continuous_ofAdd).continuousAt

@[simp]
theorem toStronglyContinuousGroup_apply (π : ContRepresentation ℂ (Multiplicative ℝ) V)
    (hπ : ∀ v, Continuous fun g => π g v) (t : ℝ) (v : V) :
    π.toStronglyContinuousGroup hπ t v = π (Multiplicative.ofAdd t) v :=
  (rfl)

/-- The C₀-group of a unitary representation of the real line is unitary. -/
theorem isUnitary_toStronglyContinuousGroup {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : ContRepresentation ℂ (Multiplicative ℝ) H} (hU : π.IsUnitary)
    (hπ : ∀ v, Continuous fun g => π g v) : (π.toStronglyContinuousGroup hπ).IsUnitary :=
  .intro fun t v w => by simpa using hU.inner_map_map (Multiplicative.ofAdd t) v w

end ContRepresentation
