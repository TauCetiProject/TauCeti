/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Splitting off the first Euclidean coordinate

`EuclideanSpace.cons` adjoins a first coordinate by a continuous linear equivalence. The
squared distance splits into the sum of the contributions of the first coordinate and the tail.
-/

public section

noncomputable section

namespace EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Adjoin a first coordinate to a Euclidean vector, as a continuous linear equivalence. -/
def cons : (𝕜 × EuclideanSpace 𝕜 (Fin n)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
  ((ContinuousLinearEquiv.refl 𝕜 𝕜).prodCongr (PiLp.continuousLinearEquiv 2 𝕜 _)).trans
    ((Fin.consEquivL 𝕜 (fun _ ↦ 𝕜)).trans (PiLp.continuousLinearEquiv 2 𝕜 _).symm)

/-- The coordinate formula for adjoining a first coordinate. -/
theorem cons_apply (z : 𝕜 × EuclideanSpace 𝕜 (Fin n)) :
    cons z = WithLp.toLp 2 (Fin.cons z.1 (WithLp.ofLp z.2)) := (rfl)

/-- The first coordinate of `cons (t, x)` is `t`. -/
@[simp] theorem cons_zero (t : 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) : cons (t, x) 0 = t := by
  simp [cons_apply]

/-- The successor coordinates of `cons (t, x)` are the original coordinates of `x`. -/
@[simp] theorem cons_succ (t : 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) (i : Fin n) :
    cons (t, x) i.succ = x i := by
  simp [cons_apply]

/-- Drop the first coordinate of a Euclidean vector. -/
def tail : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
  LinearMap.snd 𝕜 𝕜 _ ∘ₗ cons.symm.toLinearEquiv.toLinearMap

/-- After dropping the first coordinate, the coordinate at `i` is the old coordinate at `i.succ`. -/
@[simp] theorem tail_apply (x : EuclideanSpace 𝕜 (Fin (n + 1))) (i : Fin n) :
    tail x i = x i.succ := (rfl)

/-- Dropping an adjoined coordinate recovers the original vector. -/
@[simp] theorem tail_cons (t : 𝕜) (x : EuclideanSpace 𝕜 (Fin n)) : tail (cons (t, x)) = x := by
  ext i
  simp

/-- Adjoining the first coordinate to the tail recovers the original vector. -/
@[simp] theorem cons_tail (x : EuclideanSpace 𝕜 (Fin (n + 1))) : cons (x 0, tail x) = x := by
  ext i
  cases i using Fin.cases <;> simp

/-- Squared Euclidean distance splits into the first coordinate and the tail. -/
theorem dist_cons_sq (t s : 𝕜) (x y : EuclideanSpace 𝕜 (Fin n)) :
    dist (cons (t, x)) (cons (s, y)) ^ 2 = dist t s ^ 2 + dist x y ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq x y, Fin.sum_univ_succ]
  simp only [cons_zero, cons_succ]

end EuclideanSpace
