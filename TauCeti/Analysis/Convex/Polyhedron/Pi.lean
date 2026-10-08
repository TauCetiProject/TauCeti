/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Basic.Finite.Sum

/-!
# Polyhedral boxes in finite coordinate spaces

Coordinate boxes are convex polyhedra. Consequently the closed balls for the
supremum metric on a finite real coordinate space are convex polyhedra. These
balls give polyhedral neighbourhoods when restricting local PL decompositions.
-/

public section

open Set

namespace TauCeti

variable {ι : Type*}

/-- A box cut out by finitely many lower and upper coordinate bounds is a convex polyhedron,
including boxes with empty intervals or no coordinates. -/
theorem isConvexPolyhedron_pi_Icc [Finite ι] (a b : ι → ℝ) :
    IsConvexPolyhedron (Set.pi univ fun i => Icc (a i) (b i)) := by
  let coord (i : ι) : (ι → ℝ) →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).toContinuousAffineMap
  let inequalities : ι ⊕ ι → (ι → ℝ) →ᴬ[ℝ] ℝ :=
    Sum.elim (fun i => ContinuousAffineMap.const ℝ (ι → ℝ) (a i) - coord i)
      (fun i => coord i - ContinuousAffineMap.const ℝ (ι → ℝ) (b i))
  convert isConvexPolyhedron_setOf_forall inequalities using 1
  ext x
  simp [inequalities, coord, Sum.forall, Pi.le_def]

/-- Nonnegative-radius closed balls in a finite real coordinate space are convex polyhedra
for the supremum metric. -/
theorem isConvexPolyhedron_closedBall_pi [Fintype ι] (x : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    IsConvexPolyhedron (Metric.closedBall x r) := by
  rw [closedBall_pi x hr]
  simpa only [Real.closedBall_eq_Icc] using
    isConvexPolyhedron_pi_Icc (fun i => x i - r) (fun i => x i + r)

end TauCeti
