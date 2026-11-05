/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
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

Over an ordered field the standard affine charts of projective space are semialgebraic in this
model. The inverse chart at `i` followed by the projector map is a semialgebraic map from `Kⁿ`,
the image of the affine open `{x_i ≠ 0}` is a semialgebraic set, and the chart at `i` read in the
model, `A ↦ (A (i.succAbove k) i / A i i)_k`, is semialgebraic on it. Consequently, over `ℝ` and
any other ordered field with semialgebraic projections, a subset of projective space has
semialgebraic image in the model exactly when it is semialgebraic in every standard affine
chart. The analyticity of the same maps is in
`TauCeti.Geometry.Manifold.Projectivization.Projector`.

## Main results

* `Projectivization.continuous_projector`: the projector map is continuous.
* `Projectivization.isClosedEmbedding_projector`: over `ℝ` the projector map is a closed
  embedding.
* `TauCeti.isClosed_projectorLocus` and `TauCeti.isCompact_projectorLocus`: the projector locus
  is closed, and compact over `ℝ`.
* `TauCeti.isSemialgebraic_projectorLocus`: the projector locus is semialgebraic in the matrix
  entries.
* `TauCeti.isSemialgebraicMap_projector_affineChart_symm`,
  `TauCeti.isSemialgebraic_image_projector_affineOpen` and
  `TauCeti.isSemialgebraicOn_projector_affineChart`: the standard affine charts and their inverses,
  read in the projector model, are semialgebraic.
* `TauCeti.isSemialgebraic_image_projector_iff`: a subset of projective space has semialgebraic
  image in the projector model if and only if it is semialgebraic in every standard affine chart.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §3, p. 464.
-/

public section

open Matrix MvPolynomial Set Topology
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
    simp [IsSymm, IsIdempotentElem, ← Matrix.ext_iff, Matrix.mul_apply, trace, Prod.forall,
      and_assoc]
  rw [h]
  exact ((IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_eq _ _).inter
    (IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_eq _ _)).inter
    (isSemialgebraic_eval_eq _ _)

/-! ### The standard affine charts in the projector model -/

section AffineChart

open Projectivization

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- The inverse of the standard affine chart at `i` followed by the projector map is a
semialgebraic map into the matrix entries: it sends `z ∈ Kⁿ` to the projector `v vᵀ / (vᵀ v)` of
`v = Fin.insertNth i 1 z`, whose graph is cut out by the polynomial equations `(vᵀ v) A = v vᵀ`. -/
theorem isSemialgebraicMap_projector_affineChart_symm (i : Fin (n + 1)) :
    IsSemialgebraicMap fun z : Fin n → K ↦
      fun q : Fin (n + 1) × Fin (n + 1) ↦ projector ((affineChart i).symm z) q.1 q.2 := by
  rw [← isSemialgebraicOn_univ]
  -- The homogeneous coordinates `Fin.insertNth i 1 z`, as polynomials in the input coordinates.
  let V : Fin (n + 1) → MvPolynomial (Fin n ⊕ (Fin (n + 1) × Fin (n + 1))) K :=
    Fin.insertNth i 1 fun k ↦ X (.inl k)
  refine isSemialgebraicOn_of_forall_eq_iff isSemialgebraic_univ
    (fun q ↦ (∑ r, V r * V r) * X (.inr q) - V q.1 * V q.2) fun z _ A ↦ ?_
  set v : Fin (n + 1) → K := Fin.insertNth i 1 z
  have hs : v ⬝ᵥ v ≠ 0 := dotProduct_self_eq_zero.not.mpr (Fin.insertNth_one_ne_zero i z)
  have hV (r) : eval (Sum.elim z A) (V r) = v r := by
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i r <;> simp [V, v]
  simp only [map_sub, map_mul, map_sum, hV, eval_X, Sum.elim_inr, funext_iff]
  refine forall_congr' fun q ↦ ?_
  rw [affineChart_symm_apply, projector_mk, rankOneProjector_apply, div_eq_iff hs, sub_eq_zero,
    eq_comm]
  simp [v, dotProduct, mul_comm]

/-- The image of the standard affine open `{x_i ≠ 0}` under the projector map is semialgebraic in
the matrix entries: it is the part of the projector locus with nonzero `i`-th diagonal entry. -/
theorem isSemialgebraic_image_projector_affineOpen {ι : Type*} [Fintype ι] (i : ι) :
    IsSemialgebraic {a : ι × ι → K | Matrix.of (Function.curry a) ∈ projector '' affineOpen i} := by
  rw [image_projector_affineOpen]
  convert isSemialgebraic_projectorLocus.inter
    (isSemialgebraic_eval_eq_zero (X (i, i) : MvPolynomial (ι × ι) K)).compl using 1
  ext a
  simp

/-- The standard affine chart at `i` read in the projector model is semialgebraic on the image of
its domain: it sends a matrix `A` of the image of `{x_i ≠ 0}` to the ratios
`A (i.succAbove k) i / A i i` (`Projectivization.affineChart_eq_projector_div`). -/
theorem isSemialgebraicOn_projector_affineChart (i : Fin (n + 1)) :
    IsSemialgebraicOn (fun a : Fin (n + 1) × Fin (n + 1) → K ↦
        fun k ↦ a (i.succAbove k, i) / a (i, i))
      {a | Matrix.of (Function.curry a) ∈ projector '' affineOpen i} := by
  -- The graph is cut out by the equations `A i i * z k = A (i.succAbove k) i` over the domain.
  refine isSemialgebraicOn_of_forall_eq_iff (isSemialgebraic_image_projector_affineOpen i)
    (fun k ↦ X (.inl (i, i)) * X (.inr k) - X (.inl (i.succAbove k, i))) fun a ha w ↦ ?_
  rw [mem_ofPred_eq, image_projector_affineOpen] at ha
  have hii : a (i, i) ≠ 0 := ha.2
  simp only [funext_iff]
  refine forall_congr' fun k ↦ ?_
  rw [div_eq_iff hii, eq_comm, ← sub_eq_zero]
  simp [mul_comm]

/-- **Semialgebraic subsets of projective space.** Over an ordered field with semialgebraic
projections, such as `ℝ`, a subset `S` of projective space has semialgebraic image in the
projector model exactly when it is semialgebraic in every standard affine chart, that is, when
each image `affineChart i '' (S ∩ affineOpen i)` is semialgebraic. -/
theorem isSemialgebraic_image_projector_iff [HasSemialgebraicProjections K]
    {S : Set (ℙ K (Fin (n + 1) → K))} :
    IsSemialgebraic {a : Fin (n + 1) × Fin (n + 1) → K |
        Matrix.of (Function.curry a) ∈ projector '' S} ↔
      ∀ i, IsSemialgebraic (affineChart i '' (S ∩ affineOpen i)) := by
  constructor
  · -- The chart at `i` is the chart read in the projector model, applied to the image of `S`
    -- inside the image of `{x_i ≠ 0}`.
    intro hS i
    convert ((isSemialgebraicOn_projector_affineChart i).mono
      (hS.inter (isSemialgebraic_image_projector_affineOpen i)) inter_subset_right
      ).isSemialgebraic_image using 1
    ext z
    constructor
    · rintro ⟨p, ⟨hpS, hpi⟩, rfl⟩
      exact ⟨fun q ↦ projector p q.1 q.2, ⟨⟨p, hpS, rfl⟩, ⟨p, hpi, rfl⟩⟩,
        (affineChart_eq_projector_div i p).symm⟩
    · rintro ⟨a, ⟨⟨p, hpS, hp⟩, ⟨p', hpi, hp'⟩⟩, rfl⟩
      obtain rfl := projector_injective (hp.trans hp'.symm)
      refine ⟨p, ⟨hpS, hpi⟩, ?_⟩
      rw [affineChart_eq_projector_div, hp]
      rfl
  · -- The image of `S` is the union over `i` of the images of the chart images under the inverse
    -- charts followed by the projector map.
    intro hS
    convert IsSemialgebraic.iUnion fun i ↦
      (isSemialgebraicMap_projector_affineChart_symm i).isSemialgebraic_image (hS i) using 1
    ext a
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨p, hpS, hp⟩
      obtain ⟨i, hi⟩ := exists_mem_affineOpen p
      refine ⟨i, affineChart i p, ⟨p, ⟨hpS, hi⟩, rfl⟩, ?_⟩
      rw [(affineChart i).left_inv (by simpa using hi), hp]
      rfl
    · rintro ⟨i, _, ⟨p, ⟨hpS, hi⟩, rfl⟩, rfl⟩
      refine ⟨p, hpS, ?_⟩
      rw [(affineChart i).left_inv (by simpa using hi)]
      rfl

end AffineChart

end TauCeti
