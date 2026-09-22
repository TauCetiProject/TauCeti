/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
public import Mathlib.Topology.Homotopy.Path

/-!
# The path traced by a diffeotopy

A diffeotopy of `M` is a `C^n` motion through self-diffeomorphisms, so its time slices are a
jointly `C^n` family of diffeomorphisms; `Diffeomorph.ofSmoothFamily` therefore makes them a
continuous curve in `TauCeti.Diff` for the weak Whitney topology. Since a diffeotopy starts at
the identity, that curve is a path from `1` to the final diffeomorphism: a self-diffeomorphism
diffeotopic to the identity lies in the path component of `1`.

This is the first consumer of the weak Whitney topology on diffeomorphisms; it is kept apart
from `TauCeti.Geometry.Diffeomorphism.Topology` so that the topology itself does not drag in
diffeotopy theory and the real-manifold structure of the unit interval.

## Main definitions

* `TauCeti.Diffeotopy.toPath`: the path traced in `TauCeti.Diff` by a diffeotopy.

## Main results

* `TauCeti.Diffeotopy.continuous_timeSlice`: the time slices of a diffeotopy move continuously.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for smooth
  isotopies and diffeotopies.
-/

public section

namespace TauCeti.Diffeotopy

open unitInterval
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (Φ : Diffeotopy J n M)

variable [IsManifold J n M]

/-- The time slices of a diffeotopy move continuously in the weak Whitney topology. -/
theorem continuous_timeSlice : Continuous Φ.timeSlice :=
  Φ.contMDiff_timeSlice.continuous_diffeomorphWeakWhitney

/-- A diffeotopy is a path in `TauCeti.Diff` from the identity to its final diffeomorphism; in
particular a self-diffeomorphism diffeotopic to the identity lies in the path component of
`1`. -/
noncomputable def toPath : Path (1 : Diff J M n) Φ.final where
  toFun := Φ.timeSlice
  continuous_toFun := Φ.continuous_timeSlice
  source' := (Φ.timeSlice_zero).trans _root_.Diffeomorph.one_def.symm
  target' := Φ.final_def.symm

/-- The path traced by a diffeotopy is its family of time slices. -/
@[simp]
theorem toPath_apply (t : I) : Φ.toPath t = Φ.timeSlice t := (rfl)

end TauCeti.Diffeotopy
