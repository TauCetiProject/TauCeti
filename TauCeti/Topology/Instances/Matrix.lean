/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic

/-!
# Topological properties of matrices

Mathlib gives `Matrix m n α` the product topology of `m → n → α`, so for finite index types it is
pseudo-metrizable whenever `α` is. This makes metrizable-codomain results, such as measurability
of pointwise limits of measurable maps, available for matrix-valued functions without choosing a
matrix norm.

The same product topology gives entrywise control of a real matrix-valued map near a point of
continuity, again without a matrix norm
(`ContinuousAt.exists_ball_subset_forall_abs_sub_le`).

Over a topological field, the inverse of a matrix-valued function that is continuous at a point
with invertible value is continuous there (`ContinuousAt.matrix_inv`), and so are its entries
(`ContinuousAt.matrix_inv_apply`).

The Kronecker product of two continuously varying matrices is continuous in the product topology.
-/

public section

namespace TauCeti

/-- A space of matrices with finitely many rows and columns over a pseudo-metrizable space is
pseudo-metrizable. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α]
    [TopologicalSpace.PseudoMetrizableSpace α] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n α) :=
  -- The topology of `Matrix m n α` is by definition the product topology on `m → n → α`.
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → α))

end TauCeti

namespace ContinuousAt

open Filter Metric
open scoped Topology

/-- If a real matrix-valued map `a` on a pseudo-metric space is continuous at `x`, then for every
neighbourhood `s` of `x` and every `ε > 0` there is a ball `B(x, r) ⊆ s` on which every entry of
`a` differs from its value at `x` by at most `ε`. -/
theorem exists_ball_subset_forall_abs_sub_le {X m n : Type*} [PseudoMetricSpace X] [Finite m]
    [Finite n] {a : X → Matrix m n ℝ} {x : X} (hcont : ContinuousAt a x) {s : Set X}
    (hs : s ∈ 𝓝 x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ s ∧ ∀ y ∈ ball x r, ∀ i j, |a y i j - a x i j| ≤ ε := by
  have hev : ∀ᶠ y in 𝓝 x, y ∈ s ∧ ∀ i j, |a y i j - a x i j| ≤ ε := by
    refine Eventually.and hs (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
    have hij : ContinuousAt (fun y => a y i j) x :=
      (continuous_id.matrix_elem i j).continuousAt.comp hcont
    filter_upwards [Metric.tendsto_nhds.1 hij ε hε] with y hy
    exact (Real.dist_eq _ _ ▸ hy).le
  obtain ⟨r, hr, hrx⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨r, hr, fun y hy => (hrx y hy).1, fun y hy => (hrx y hy).2⟩

end ContinuousAt

section Inverse

variable {X n K : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n] [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] {A : X → Matrix n n K} {x : X}

/-- The inverse of a matrix-valued function is continuous at every point where the function is
continuous and its value is invertible. -/
theorem ContinuousAt.matrix_inv (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) :
    ContinuousAt (fun y ↦ (A y)⁻¹) x :=
  (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)).comp hA

/-- The entries of the inverse of a matrix-valued function are continuous at every point where the
function is continuous and its value is invertible. -/
theorem ContinuousAt.matrix_inv_apply (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) (k l : n) :
    ContinuousAt (fun y ↦ (A y)⁻¹ k l) x :=
  (continuous_apply_apply k l).continuousAt.comp (hA.matrix_inv hdet)

end Inverse

open scoped Kronecker

/-- The Kronecker product of two continuous matrix-valued functions is continuous. -/
@[continuity, fun_prop]
theorem Continuous.matrix_kronecker {X R l m n p : Type*} [TopologicalSpace X]
    [TopologicalSpace R] [Mul R] [ContinuousMul R]
    {A : X → Matrix l m R} {B : X → Matrix n p R}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x ↦ A x ⊗ₖ B x) := by
  apply continuous_matrix
  intro i j
  simp only [Matrix.kroneckerMap_apply]
  exact (hA.matrix_elem i.1 j.1).mul (hB.matrix_elem i.2 j.2)
