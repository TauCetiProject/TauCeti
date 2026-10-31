/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex
public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Complex projective space as a compact real algebraic set of matrices

The Hermitian projector map `Projectivization.hermitianProjector : ℙ 𝕜 (ι → 𝕜) → Matrix ι ι 𝕜`
sends the line spanned by `x` to the matrix `x x* / (x* x)`, and over `ℝ` or `ℂ` it is a bijection
onto the *Hermitian projector locus* `TauCeti.hermitianProjectorLocus ι 𝕜` of star projections of
trace one (`Projectivization.range_hermitianProjector`). Here we add its topological and
semialgebraic properties.

The Hermitian projector map is continuous for the quotient topology on projective space, which is
compact, so it is a closed embedding: a homeomorphism from `ℙ 𝕜 (ι → 𝕜)` onto the locus, which is
compact. In the real and imaginary parts of the matrix entries, the complex locus is cut out by
real polynomial equations, hence is semialgebraic. The same holds for the image of every
projective zero locus of homogeneous polynomials: a line lies on the zero locus exactly when every
column of its Hermitian projector, a multiple of a spanning vector, is a common zero. This exhibits
complex projective space, and each of its projective algebraic subsets, as compact semialgebraic
subsets of a real affine space, the form in which triangulation theorems for compact
semialgebraic sets apply to them.

The real coordinates of a complex `ι × ι` matrix are indexed by `(ι × ι) ⊕ (ι × ι)`: the matrix
with entries `a (Sum.inl (i, j)) + a (Sum.inr (i, j)) * I`, as in
`TauCeti.isSemialgebraic_setOf_eval_sumElim_star_eq_zero`.

## Main results

* `Projectivization.continuous_hermitianProjector`: the Hermitian projector map is continuous.
* `Projectivization.isClosedEmbedding_hermitianProjector`: over `ℝ` or `ℂ` the Hermitian projector
  map is a closed embedding.
* `TauCeti.isClosed_hermitianProjectorLocus` and `TauCeti.isCompact_hermitianProjectorLocus`: the
  Hermitian projector locus is closed, and compact over `ℝ` or `ℂ`.
* `TauCeti.isSemialgebraic_hermitianProjectorLocus`: the complex Hermitian projector locus is
  semialgebraic in the real and imaginary parts of the matrix entries.
* `TauCeti.image_hermitianProjector_complexProjectiveZeroLocus` and
  `TauCeti.isSemialgebraic_image_hermitianProjector_complexProjectiveZeroLocus`: the image of a
  projective zero locus of homogeneous polynomials is the part of the locus whose columns are
  common zeros, and is semialgebraic.

## References

J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und
ihrer Grenzgebiete (3) 36, Springer, 1998, §3.4, for projective spaces as affine real algebraic
sets of projection matrices.
-/

public section

open Matrix MvPolynomial Topology Complex
open scoped LinearAlgebra.Projectivization ComplexOrder

namespace Projectivization

open TauCeti

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]

/-- The Hermitian projector map is continuous for the quotient topology on projective space. -/
theorem continuous_hermitianProjector :
    Continuous (hermitianProjector : ℙ 𝕜 (ι → 𝕜) → Matrix ι ι 𝕜) := by
  rw [continuous_iff]
  have hcomp : hermitianProjector ∘ mk' 𝕜 =
      fun x : {x : ι → 𝕜 // x ≠ 0} ↦ rankOneHermitianProjector x.1 :=
    funext fun x ↦ by simp
  simp only [hcomp, rankOneHermitianProjector_def]
  exact ((continuous_subtype_val.star.dotProduct continuous_subtype_val).inv₀ fun x ↦
    dotProduct_star_self_eq_zero.not.mpr x.2).smul
    (continuous_subtype_val.matrix_vecMulVec continuous_subtype_val.star)

/-- Over `ℝ` or `ℂ` the Hermitian projector map is a closed embedding, hence a homeomorphism from
projective space onto the Hermitian projector locus `TauCeti.hermitianProjectorLocus ι 𝕜`. -/
theorem isClosedEmbedding_hermitianProjector :
    IsClosedEmbedding (hermitianProjector : ℙ 𝕜 (ι → 𝕜) → Matrix ι ι 𝕜) :=
  continuous_hermitianProjector.isClosedEmbedding hermitianProjector_injective

end Projectivization

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The Hermitian projector locus is closed. -/
theorem isClosed_hermitianProjectorLocus {K : Type*} [Field K] [StarRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [ContinuousStar K] [T2Space K] :
    IsClosed (hermitianProjectorLocus ι K) := by
  have h : hermitianProjectorLocus ι K =
      {A | A * A = A} ∩ {A | star A = A} ∩ {A | A.trace = 1} := by
    ext A
    simp [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, and_assoc]
  rw [h]
  exact ((isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id).inter
    (isClosed_eq continuous_star continuous_id)).inter
    (isClosed_eq continuous_id.matrix_trace continuous_const)

/-- Over `ℝ` or `ℂ` the Hermitian projector locus is compact, being the image of compact projective
space. -/
theorem isCompact_hermitianProjectorLocus {𝕜 : Type*} [RCLike 𝕜] :
    IsCompact (hermitianProjectorLocus ι 𝕜) :=
  Projectivization.range_hermitianProjector (ι := ι) (𝕜 := 𝕜) ▸
    isCompact_range Projectivization.continuous_hermitianProjector

/-- The complex Hermitian projector locus is semialgebraic in the real and imaginary parts
`a (Sum.inl (i, j))` and `a (Sum.inr (i, j))` of the matrix entries: it is cut out by the
polynomial equations, in the entries and their conjugates, expressing self-adjointness,
idempotence and trace one. -/
theorem isSemialgebraic_hermitianProjectorLocus :
    IsSemialgebraic {a : (ι × ι) ⊕ (ι × ι) → ℝ |
      Matrix.of (fun i j ↦ (a (.inl (i, j)) : ℂ) + a (.inr (i, j)) * I) ∈
        hermitianProjectorLocus ι ℂ} := by
  let z (a : (ι × ι) ⊕ (ι × ι) → ℝ) : (ι × ι) ⊕ (ι × ι) → ℂ :=
    Sum.elim (fun k ↦ (a (.inl k) : ℂ) + a (.inr k) * I)
      (fun k ↦ star ((a (.inl k) : ℂ) + a (.inr k) * I))
  have h : {a : (ι × ι) ⊕ (ι × ι) → ℝ |
      Matrix.of (fun i j ↦ (a (.inl (i, j)) : ℂ) + a (.inr (i, j)) * I) ∈
        hermitianProjectorLocus ι ℂ} =
      ((⋂ p : ι × ι, {a | eval (z a) (∑ k, X (.inl (p.1, k)) * X (.inl (k, p.2)) -
          X (.inl p)) = 0}) ∩
        ⋂ p : ι × ι, {a | eval (z a) (X (.inr p.swap) - X (.inl p)) = 0}) ∩
        {a | eval (z a) (∑ i, X (.inl (i, i)) - 1) = 0} := by
    ext a
    simp [z, isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, ← Matrix.ext_iff, mul_apply,
      trace, sub_eq_zero, Prod.forall, and_assoc]
  rw [h]
  exact ((IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_setOf_eval_sumElim_star_eq_zero _).inter
    (IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_setOf_eval_sumElim_star_eq_zero _)).inter
    (isSemialgebraic_setOf_eval_sumElim_star_eq_zero _)

variable {N : ℕ} {κ : Type*} {p : κ → MvPolynomial (Fin N) ℂ} {d : κ → ℕ}

/-- The Hermitian projectors of the lines on a projective zero locus of homogeneous polynomials
are the points of the Hermitian projector locus whose columns are common zeros of the
polynomials. -/
theorem image_hermitianProjector_complexProjectiveZeroLocus
    (hp : ∀ k, (p k).IsHomogeneous (d k)) :
    Projectivization.hermitianProjector '' complexProjectiveZeroLocus p =
      hermitianProjectorLocus (Fin N) ℂ ∩ {A | ∀ k i, eval (fun j ↦ A j i) (p k) = 0} := by
  ext A
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨Projectivization.hermitianProjector_mem_hermitianProjectorLocus L, fun k i ↦ ?_⟩
    induction L using Projectivization.ind with | h x hx =>
    -- Each column of the Hermitian projector of `x` is a multiple of `x`.
    have hcol : (fun j ↦ Projectivization.hermitianProjector (.mk ℂ x hx) j i) =
        (star (x i) / (star x ⬝ᵥ x)) • x := by
      funext j
      simp [rankOneHermitianProjector_apply, div_eq_mul_inv, mul_comm, mul_assoc]
    rw [hcol]
    exact (complexProjectiveZeroLocus_mk_iff_forall_smul x hx).mp hL k _
  · rintro ⟨hA, hpA⟩
    have htr : A.trace ≠ 0 := (mem_hermitianProjectorLocus.mp hA).2 ▸ one_ne_zero
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero htr
    have hv : (fun j ↦ A j i) ≠ 0 := fun h ↦ hi (congr_fun h i)
    refine ⟨.mk ℂ _ hv, (complexProjectiveZeroLocus_mk_iff hp _ hv).mpr fun k ↦ hpA k i, ?_⟩
    rw [Projectivization.hermitianProjector_mk, rankOneHermitianProjector_col_eq_self hA hi]

/-- The image of a projective zero locus of finitely many homogeneous polynomials under the
Hermitian projector map is semialgebraic in the real and imaginary parts of the matrix
entries. -/
theorem isSemialgebraic_image_hermitianProjector_complexProjectiveZeroLocus [Finite κ]
    (hp : ∀ k, (p k).IsHomogeneous (d k)) :
    IsSemialgebraic {a : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℝ |
      Matrix.of (fun i j ↦ (a (.inl (i, j)) : ℂ) + a (.inr (i, j)) * I) ∈
        Projectivization.hermitianProjector '' complexProjectiveZeroLocus p} := by
  let z (a : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℝ) : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℂ :=
    Sum.elim (fun k ↦ (a (.inl k) : ℂ) + a (.inr k) * I)
      (fun k ↦ star ((a (.inl k) : ℂ) + a (.inr k) * I))
  have h : {a : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℝ |
      Matrix.of (fun i j ↦ (a (.inl (i, j)) : ℂ) + a (.inr (i, j)) * I) ∈
        Projectivization.hermitianProjector '' complexProjectiveZeroLocus p} =
      {a | Matrix.of (fun i j ↦ (a (.inl (i, j)) : ℂ) + a (.inr (i, j)) * I) ∈
        hermitianProjectorLocus (Fin N) ℂ} ∩
        ⋂ k, ⋂ i, {a | eval (z a) (rename (fun j ↦ .inl (j, i)) (p k)) = 0} := by
    ext a
    simp only [image_hermitianProjector_complexProjectiveZeroLocus hp, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iInter, eval_rename]
    rfl
  rw [h]
  exact isSemialgebraic_hermitianProjectorLocus.inter
    (IsSemialgebraic.iInter fun _ ↦ IsSemialgebraic.iInter fun _ ↦
      isSemialgebraic_setOf_eval_sumElim_star_eq_zero _)

end TauCeti
