/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import TauCeti.LinearAlgebra.Projectivization.Projector
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Real projective space as a compact real algebraic set of matrices

The projector map `Projectivization.projector : ℙ K (ι → K) → Matrix ι ι K` sends a line spanned
by `x` to the matrix `x xᵀ / (xᵀ x)`, and is a bijection onto the *projector locus*
`TauCeti.projectorLocus ι K` of symmetric idempotent matrices of trace one
(`Projectivization.range_projector`). Here we add its topological and semialgebraic properties.

The projector map is continuous for the quotient topology on projective space. Over `ℝ`,
projective space is compact and matrices form a Hausdorff space, so the projector map is a closed
embedding: it is a homeomorphism from real projective space onto the projector locus, which is
compact. The locus is cut out by polynomial equations in the matrix entries, hence is
semialgebraic. Together these exhibit real projective space as a compact real algebraic subset of
an affine space, which is the reduction used to transport triangulations of compact semialgebraic
sets to real projective spaces.

## Main results

* `Projectivization.continuous_projector`: the projector map is continuous.
* `Projectivization.isClosedEmbedding_projector`: over `ℝ` the projector map is a closed
  embedding.
* `TauCeti.isClosed_projectorLocus` and `TauCeti.isCompact_projectorLocus`: the projector locus
  is closed, and compact over `ℝ`.
* `TauCeti.isSemialgebraic_projectorLocus`: the projector locus is semialgebraic in the matrix
  entries.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §3, p. 464.
-/

public section

open Matrix MvPolynomial Topology
open scoped LinearAlgebra.Projectivization

namespace Projectivization

open TauCeti

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]

/-- The projector map is continuous for the quotient topology on projective space. -/
theorem continuous_projector : Continuous (projector : ℙ K (ι → K) → Matrix ι ι K) := by
  rw [continuous_iff]
  have hcomp : projector ∘ mk' K = fun x : {x : ι → K // x ≠ 0} ↦ rankOneProjector x.1 :=
    funext fun x ↦ by simp
  simp only [hcomp, rankOneProjector_def]
  exact ((continuous_subtype_val.dotProduct continuous_subtype_val).inv₀ fun x ↦
    dotProduct_self_eq_zero.not.mpr x.2).smul
    (continuous_subtype_val.matrix_vecMulVec continuous_subtype_val)

/-- Over `ℝ` the projector map is a closed embedding, hence a homeomorphism from real projective
space onto the projector locus `TauCeti.projectorLocus ι ℝ`. -/
theorem isClosedEmbedding_projector :
    IsClosedEmbedding (projector : ℙ ℝ (ι → ℝ) → Matrix ι ι ℝ) :=
  continuous_projector.isClosedEmbedding projector_injective

end Projectivization

namespace TauCeti

variable {ι K : Type*} [Fintype ι] [Field K]

/-- The projector locus is closed. -/
theorem isClosed_projectorLocus [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] :
    IsClosed (projectorLocus ι K) := by
  have h : projectorLocus ι K = {A | Aᵀ = A} ∩ {A | A * A = A} ∩ {A | A.trace = 1} := by
    ext A
    simp [IsSymm, IsIdempotentElem, and_assoc]
  rw [h]
  exact ((isClosed_eq continuous_id.matrix_transpose continuous_id).inter
    (isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id)).inter
    (isClosed_eq continuous_id.matrix_trace continuous_const)

/-- The real projector locus is compact, being the image of compact real projective space. -/
theorem isCompact_projectorLocus : IsCompact (projectorLocus ι ℝ) :=
  Projectivization.range_projector (ι := ι) (K := ℝ) ▸
    isCompact_range Projectivization.continuous_projector

/-- The projector locus is semialgebraic: in the matrix entries `a (i, j)` it is cut out by the
polynomial equations expressing symmetry, idempotence and trace one. -/
theorem isSemialgebraic_projectorLocus [LinearOrder K] :
    IsSemialgebraic {a : ι × ι → K | Matrix.of (Function.curry a) ∈ projectorLocus ι K} := by
  have h : {a : ι × ι → K | Matrix.of (Function.curry a) ∈ projectorLocus ι K} =
      ((⋂ p : ι × ι, {a | eval a (X p.swap) = eval a (X p)}) ∩
        ⋂ p : ι × ι, {a | eval a (∑ k, X (p.1, k) * X (k, p.2)) = eval a (X p)}) ∩
        {a | eval a (∑ i, X (i, i)) = eval a 1} := by
    ext a
    simp [IsSymm, IsIdempotentElem, ← Matrix.ext_iff, mul_apply, trace, Prod.forall, and_assoc]
  rw [h]
  exact ((IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_eq _ _).inter
    (IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_eq _ _)).inter
    (isSemialgebraic_eval_eq _ _)

end TauCeti
