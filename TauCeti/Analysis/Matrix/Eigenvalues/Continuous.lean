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

We use the subtype of Hermitian matrices, with its inherited topology and measurable
structure. For a family of Hermitian matrices, continuity of the entries at a point gives
continuity of the ordered eigenvalues there (`Matrix.continuousAt_eigenvalues₀`). Continuity
uses the usual entrywise topology: Mathlib's Euclidean operator norm induces this same topology.
Empty index types are allowed.

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
    LipschitzWith 1 (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) := by
  refine LipschitzWith.of_dist_le_mul fun A B => ?_
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    A.property.abs_eigenvalues₀_sub_le_norm B.property i

/-- Ordered Hermitian eigenvalues depend continuously on the matrix, even at repeated
eigenvalues. -/
@[fun_prop]
theorem continuous_eigenvalues₀ :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) :=
  lipschitzWith_eigenvalues₀.continuous

/-- Mathlib's matrix-indexed eigenvalue list is continuous on Hermitian matrices. -/
@[fun_prop]
theorem continuous_eigenvalues :
    Continuous (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues) := by
  apply continuous_pi
  intro i
  -- The matrix-indexed list is the sorted list reindexed by a fixed finite equivalence.
  simpa only [IsHermitian.eigenvalues, Function.comp_def] using
    (continuous_apply _).comp (continuous_eigenvalues₀ (n := n) (𝕜 := 𝕜))

/-- The ordered eigenvalues of a family of Hermitian matrices are continuous at every point at
which its entries are, including at repeated eigenvalues. -/
theorem continuousAt_eigenvalues₀ {X : Type*} [TopologicalSpace X] {M : X → Matrix n n 𝕜}
    (hM : ∀ x, (M x).IsHermitian) {x₀ : X} (h : ∀ a b, ContinuousAt (fun x ↦ M x a b) x₀)
    (i : Fin (Fintype.card n)) : ContinuousAt (fun x ↦ (hM x).eigenvalues₀ i) x₀ :=
  ((continuous_apply i).comp continuous_eigenvalues₀).continuousAt.comp
    (f := fun x ↦ (⟨M x, hM x⟩ : {A : Matrix n n 𝕜 // A.IsHermitian}))
    (tendsto_subtype_rng.2 (continuousAt_pi.2 fun a ↦ continuousAt_pi.2 fun b ↦ h a b))

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The ordered eigenvalue list of a Hermitian matrix is measurable for the entrywise
Borel structure. -/
@[fun_prop]
theorem measurable_eigenvalues₀ :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues₀) :=
  continuous_eigenvalues₀.measurable

/-- Mathlib's matrix-indexed eigenvalue list is measurable on Hermitian matrices. -/
@[fun_prop]
theorem measurable_eigenvalues :
    Measurable (fun A : {A : Matrix n n 𝕜 // A.IsHermitian} => A.property.eigenvalues) :=
  continuous_eigenvalues.measurable

end Matrix
