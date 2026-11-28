/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix

/-!
# Matrices over a product as a product of matrices, topologically

Mathlib's `Matrix.prodEquiv` identifies the matrices `Matrix m n (α × β)` over a product with the
pairs of matrices `Matrix m n α × Matrix m n β`, taking the two components entrywise. For the
entrywise product topologies both directions are continuous, so this is a homeomorphism.

## Main definitions

* `Matrix.prodHomeomorph`: `Matrix.prodEquiv` as a homeomorphism.
-/

public section

namespace Matrix

variable (m n α β : Type*) [TopologicalSpace α] [TopologicalSpace β]

/-- `Matrix.prodEquiv` as a homeomorphism: the matrices over `α × β` are homeomorphic to the
pairs of matrices over `α` and over `β`, for the entrywise product topologies. -/
def prodHomeomorph : Matrix m n (α × β) ≃ₜ Matrix m n α × Matrix m n β where
  toEquiv := prodEquiv m n α β
  continuous_toFun :=
    (continuous_id.matrix_map continuous_fst).prodMk (continuous_id.matrix_map continuous_snd)
  continuous_invFun := continuous_matrix fun i j ↦
    ((continuous_fst.matrix_elem i j).prodMk (continuous_snd.matrix_elem i j))

/-- The underlying equivalence of `Matrix.prodHomeomorph` is `Matrix.prodEquiv`. -/
@[simp]
theorem prodHomeomorph_toEquiv : (prodHomeomorph m n α β).toEquiv = prodEquiv m n α β :=
  (rfl)

variable {m n α β}

/-- `Matrix.prodHomeomorph` takes the two components of a matrix over `α × β` entrywise. -/
@[simp]
theorem prodHomeomorph_apply (A : Matrix m n (α × β)) :
    prodHomeomorph m n α β A = (A.map Prod.fst, A.map Prod.snd) :=
  (rfl)

/-- The inverse of `Matrix.prodHomeomorph` pairs the entries of two matrices. -/
@[simp]
theorem prodHomeomorph_symm_apply (A : Matrix m n α × Matrix m n β) :
    (prodHomeomorph m n α β).symm A = of fun i j ↦ (A.1 i j, A.2 i j) :=
  (rfl)

end Matrix
