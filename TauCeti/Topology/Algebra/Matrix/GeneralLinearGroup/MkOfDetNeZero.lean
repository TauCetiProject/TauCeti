/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of packaging nonsingular matrices in the general linear group

Over a topological field, a continuous family of matrices with nonzero determinant stays
continuous after packaging each matrix as an element of `GL` by
`Matrix.GeneralLinearGroup.mkOfDetNeZero`: the inverse is `det⁻¹ • adjugate`.

## Main results

* `Matrix.GeneralLinearGroup.continuous_mkOfDetNeZero`: a continuous family of nonsingular
  matrices is continuous into `GL`.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {X n K : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n] [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]

/-- A continuous family of matrices with nonzero determinant is continuous into `GL`. -/
theorem continuous_mkOfDetNeZero {f : X → Matrix n n K} (hf : Continuous f)
    (h : ∀ x, (f x).det ≠ 0) : Continuous fun x ↦ mkOfDetNeZero (f x) (h x) := by
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  refine ((hf.matrix_det.inv₀ h).smul hf.matrix_adjugate).congr fun x ↦ ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

end Matrix.GeneralLinearGroup
