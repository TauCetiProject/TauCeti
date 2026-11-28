/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Activation
public import TauCeti.Topology.PL.Map

/-!
# Piecewise affineness of the coordinatewise rectifier

On a finite coordinate space the rectifier agrees with a linear projection on each
closed orthant.
-/

public section

namespace TauCeti

open Set Neuromanifold

/-- On a finite coordinate space the ReLU layer is piecewise affine. Its cells are the
closed orthants, with one choice of sign for each coordinate. -/
theorem isPiecewiseAffineOn_reluActivation {ι : Type*} [Finite ι] (p : PUnit)
    (s : Set (ι → ℝ)) : IsPiecewiseAffineOn (reluActivation p) s := by
  classical
  let coord (i : ι) : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let test (J : Set ι) (i : ι) : (ι → ℝ) →ᴬ[ℝ] ℝ :=
    if i ∈ J then -(coord i).toContinuousAffineMap else (coord i).toContinuousAffineMap
  let piece (J : Set ι) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i => if i ∈ J then coord i else 0
  refine isPiecewiseAffineOn_of_finite (A := fun J => (piece J).toContinuousAffineMap)
    (fun J => isConvexPolyhedron_setOf_forall (test J)) ?_ ?_
  · intro x _
    refine mem_iUnion.mpr ⟨{i | 0 ≤ x i}, ?_⟩
    intro i
    by_cases hi : 0 ≤ x i <;> simp [test, coord, hi, le_of_not_ge]
  · intro J x hx
    funext i
    have hi := hx.2 i
    by_cases hJ : i ∈ J
    · simp [test, coord, hJ] at hi
      simp [piece, coord, hJ, max_eq_right hi]
    · simp [test, coord, hJ] at hi
      simp [piece, hJ, max_eq_left hi]

end TauCeti
