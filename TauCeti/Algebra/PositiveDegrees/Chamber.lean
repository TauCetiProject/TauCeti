/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Basic
public import TauCeti.Geometry.Convex.Cone.Chamber
public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Distinguished points of positive-degree chambers

An integral lattice identifies an integral degree functional with a point of its real
dual. Strict positivity of the degree puts this point in the positive chamber and its
negative in the negative chamber. Thus both chambers are nonempty and, for a finitely generated
monoid, are open neighborhoods of these distinguished points
(`AddSubmonoid.isOpen_positiveChamber`).

The distinguished point is the continuous form of
`TauCeti.Toric.IsIntegralLattice.realCharacter`. Finite dimensionality is supplied by the
lattice itself.

## Provenance

Adapted from `Mei/Algebra/PositiveDegrees/Chamber.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace TauCeti.PositiveDegrees

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)

/-- The real dual point determined by the integral degree functional. -/
noncomputable def degreePoint : V →L[ℝ] ℝ :=
  haveI := h.finiteDimensional
  (h.realCharacter d.degree).toContinuousLinearMap

/-- The degree point evaluates on lattice vectors as the original degree. -/
@[simp]
theorem degreePoint_apply (n : N) : d.degreePoint h (i n) = (d.degree n : ℝ) := by
  simp [degreePoint]

/-- The positive degree functional lies in the positive chamber. -/
theorem degreePoint_mem_positiveChamber : d.degreePoint h ∈ d.monoid.positiveChamber i := by
  rw [AddSubmonoid.mem_positiveChamber]
  intro n hn hn0
  simpa using (Int.cast_pos.mpr (d.degree_pos hn hn0) : (0 : ℝ) < d.degree n)

/-- The negative degree functional lies in the negative chamber. -/
theorem neg_degreePoint_mem_negativeChamber :
    -d.degreePoint h ∈ d.monoid.negativeChamber i := by
  simpa using d.degreePoint_mem_positiveChamber h

end TauCeti.PositiveDegrees
