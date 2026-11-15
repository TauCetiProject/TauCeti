/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Continuity of ordered Hermitian eigenvalues

The decreasing eigenvalue list of a Hermitian matrix is `1`-Lipschitz from the Euclidean
operator norm to the sup norm on the list. In particular it is continuous, including at
repeated eigenvalues, and measurable for the entrywise Borel structure on matrices.
These results allow eigenvalues of a measurable random Hermitian matrix to be treated as
random variables, without choosing measurable eigenvectors.

We use both the subtype `{A : Matrix n n 𝕜 // A.IsHermitian}` and the self-adjoint submodule
`selfAdjoint (Matrix n n 𝕜)`, with their inherited topologies and measurable structures.
Continuity uses the usual entrywise topology: Mathlib's Euclidean operator norm induces this
same topology. Consequently, the locus where a given sorted eigenvalue is simple and the open
simple-spectrum locus `{X | StrictAnti X.2.isHermitian.eigenvalues₀}` are open in
`selfAdjoint (Matrix n n 𝕜)`. Empty index types are allowed.

## References

* R. Bhatia, *Matrix Analysis*, Springer (1997), Chapter III, for Weyl's perturbation bound
  and continuity of ordered eigenvalues.
-/

public section

noncomputable section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator

/-- The decreasing eigenvalue list is `1`-Lipschitz for the Euclidean operator norm on
Hermitian matrices and the sup norm on the eigenvalue list. -/
theorem lipschitzWith_eigenvalues₀ :
    LipschitzWith 1 (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.2.eigenvalues₀) := by
  refine LipschitzWith.of_dist_le_mul fun A B => ?_
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    A.2.abs_eigenvalues₀_sub_le_norm B.2 i

/-- Ordered Hermitian eigenvalues depend continuously on the matrix, even at repeated
eigenvalues. -/
@[fun_prop]
theorem continuous_eigenvalues₀ :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.2.eigenvalues₀) :=
  lipschitzWith_eigenvalues₀.continuous

/-- Mathlib's matrix-indexed eigenvalue list is continuous on Hermitian matrices. -/
@[fun_prop]
theorem continuous_eigenvalues :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.2.eigenvalues) := by
  apply continuous_pi
  intro i
  -- The matrix-indexed list is the sorted list reindexed by a fixed finite equivalence.
  simpa only [IsHermitian.eigenvalues, Function.comp_def] using
    (continuous_apply _).comp (continuous_eigenvalues₀ (n := n) (𝕜 := 𝕜))

/-- The sorted eigenvalue map is continuous on `selfAdjoint (Matrix n n 𝕜)`. -/
@[fun_prop]
theorem continuous_eigenvalues₀_selfAdjoint :
    Continuous (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues₀) :=
  continuous_eigenvalues₀.comp (continuous_subtype_val.subtype_mk fun X ↦ X.2.isHermitian)

/-- Mathlib's matrix-indexed eigenvalue list is continuous on `selfAdjoint (Matrix n n 𝕜)`. -/
@[fun_prop]
theorem continuous_eigenvalues_selfAdjoint :
    Continuous (fun X : selfAdjoint (Matrix n n 𝕜) ↦ X.2.isHermitian.eigenvalues) :=
  continuous_eigenvalues.comp (continuous_subtype_val.subtype_mk fun X ↦ X.2.isHermitian)

/-- Self-adjoint matrices whose `k`-th sorted eigenvalue is simple form an open set. -/
theorem isOpen_setOf_forall_eigenvalues₀_ne (k : Fin (Fintype.card n)) :
    IsOpen {X : selfAdjoint (Matrix n n 𝕜) |
      ∀ j ≠ k, X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} := by
  have heq : {X : selfAdjoint (Matrix n n 𝕜) |
      ∀ j ≠ k, X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} =
      ⋂ j ∈ Finset.univ.erase k, {X : selfAdjoint (Matrix n n 𝕜) |
        X.2.isHermitian.eigenvalues₀ j ≠ X.2.isHermitian.eigenvalues₀ k} := by
    ext X; simp [Finset.mem_erase]
  rw [heq]
  exact isOpen_biInter_finset fun j _ ↦ isOpen_ne_fun
    ((continuous_apply j).comp continuous_eigenvalues₀_selfAdjoint)
    ((continuous_apply k).comp continuous_eigenvalues₀_selfAdjoint)

/-- The simple-spectrum locus `{X | StrictAnti X.2.isHermitian.eigenvalues₀}` is open in
`selfAdjoint (Matrix n n 𝕜)`. -/
theorem isOpen_setOf_strictAnti_eigenvalues₀ :
    IsOpen {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} := by
  have heq : {X : selfAdjoint (Matrix n n 𝕜) | StrictAnti X.2.isHermitian.eigenvalues₀} =
      ⋂ i : Fin (Fintype.card n), ⋂ j : {j : Fin (Fintype.card n) // i < j},
        {X : selfAdjoint (Matrix n n 𝕜) |
          X.2.isHermitian.eigenvalues₀ j.1 < X.2.isHermitian.eigenvalues₀ i} := by
    ext X; simp [StrictAnti, Subtype.forall]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ isOpen_lt
    ((continuous_apply j.1).comp continuous_eigenvalues₀_selfAdjoint)
    ((continuous_apply i).comp continuous_eigenvalues₀_selfAdjoint)

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The ordered eigenvalue list of a Hermitian matrix is measurable for the entrywise
Borel structure. -/
@[fun_prop]
theorem measurable_eigenvalues₀ :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.2.eigenvalues₀) :=
  continuous_eigenvalues₀.measurable

/-- Mathlib's matrix-indexed eigenvalue list is measurable on Hermitian matrices. -/
@[fun_prop]
theorem measurable_eigenvalues :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.2.eigenvalues) :=
  continuous_eigenvalues.measurable

end Matrix
