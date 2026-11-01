/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Orientation.Family
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Diffeotopies preserve orientation

Every time slice of a diffeotopy preserves every orientation of its ambient manifold.
In particular the final diffeomorphism does. This lets a diffeotopy move the centre of an
oriented embedded disc while retaining its orientation, before applying the disc theorem
at a common centre. The manifold may have boundary or corners and need not be connected.

The result uses local constancy of orientation behavior in a `C¹` family with invertible
slice derivatives, and the identity slice at time zero.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 4, §6 (the disc theorem).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.Diffeotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} [IsManifold I n M]
  {ι : Type*} [Fintype ι]

/-- Every time slice of a positive-order diffeotopy preserves every ambient orientation,
including on a disconnected manifold or a manifold with corners. -/
@[simp]
theorem isOrientationPreservingAt_timeSlice (Φ : Diffeotopy I n M) (hn : 1 ≤ n)
    (o : Manifold.Orientation I M ι) (t : unitInterval) (x : M) :
    let : IsManifold I 1 M := .of_le hn
    o.IsOrientationPreservingAt o (Φ.timeSlice t) x := by
  let : IsManifold I 1 M := .of_le hn
  have hs (s : unitInterval) : (fun y => Φ (s, y)) = Φ.timeSlice s :=
    funext fun y => (Φ.timeSlice_apply s y).symm
  have h := Manifold.Orientation.isOrientationPreservingAt_family_iff o o
    (Φ.contMDiff.of_le hn) x
    (fun s => by
      rw [hs s]
      exact (Φ.timeSlice s).isInvertible_mfderiv (ne_of_gt (lt_of_lt_of_le (by simp) hn))) t 0
  rw [hs t] at h
  apply h.mpr
  have hzero : (fun y => Φ (0, y)) = id := funext Φ.apply_zero
  rw [hzero]
  exact Manifold.Orientation.isOrientationPreservingAt_id o x

/-- The final diffeomorphism of a positive-order diffeotopy preserves every ambient
orientation. -/
@[simp]
theorem isOrientationPreservingAt_final (Φ : Diffeotopy I n M) (hn : 1 ≤ n)
    (o : Manifold.Orientation I M ι) (x : M) :
    let : IsManifold I 1 M := .of_le hn
    o.IsOrientationPreservingAt o Φ.final x := by
  let : IsManifold I 1 M := .of_le hn
  rw [Φ.final_def]
  exact Φ.isOrientationPreservingAt_timeSlice hn o 1 x

end TauCeti.Diffeotopy
