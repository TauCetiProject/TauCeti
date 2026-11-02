/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
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
with entries `(TauCeti.complexToRealPi (ι × ι)).symm a (i, j)`, that is
`a (Sum.inl (i, j)) + a (Sum.inr (i, j)) * I`.

The standard affine charts of complex projective space are compatible with this model. In these
real coordinates, the inverse chart at `i` followed by the Hermitian projector map is a
semialgebraic map from `ℝ²ⁿ`, the image of the affine open `{x_i ≠ 0}` is a semialgebraic set, and
the chart at `i` read in the model, `A ↦ (A (i.succAbove k) i / A i i)_k`, is semialgebraic on
it. Composing the two, every transition map between standard affine charts
is semialgebraic on its domain. These comparisons transfer semialgebraic statements between the
compact matrix model, where compact semialgebraic triangulation applies, and the affine charts,
where projective algebraic sets are affine algebraic sets.

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
* `TauCeti.isSemialgebraicMap_hermitianProjector_affineChart_symm`,
  `TauCeti.isSemialgebraic_image_hermitianProjector_affineOpen` and
  `TauCeti.isSemialgebraicOn_hermitianProjector_affineChart`: the standard affine charts and their
  inverses, read in the Hermitian projector model, are semialgebraic.
* `TauCeti.isSemialgebraicOn_affineChart_symm_trans`: the transition maps between the standard
  affine charts are semialgebraic.

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
`a (Sum.inl (i, j))` and `a (Sum.inr (i, j))` of the matrix entries, recombined by
`TauCeti.complexToRealPi`: it is cut out by the polynomial equations, in the entries and their
conjugates, expressing self-adjointness, idempotence and trace one. -/
theorem isSemialgebraic_hermitianProjectorLocus :
    IsSemialgebraic {a : (ι × ι) ⊕ (ι × ι) → ℝ |
      Matrix.of (fun i j ↦ (complexToRealPi (ι × ι)).symm a (i, j)) ∈
        hermitianProjectorLocus ι ℂ} := by
  let z (a : (ι × ι) ⊕ (ι × ι) → ℝ) : (ι × ι) ⊕ (ι × ι) → ℂ :=
    Sum.elim (fun k ↦ (a (.inl k) : ℂ) + a (.inr k) * I)
      (fun k ↦ star ((a (.inl k) : ℂ) + a (.inr k) * I))
  have h : {a : (ι × ι) ⊕ (ι × ι) → ℝ |
      Matrix.of (fun i j ↦ (complexToRealPi (ι × ι)).symm a (i, j)) ∈
        hermitianProjectorLocus ι ℂ} =
      ((⋂ p : ι × ι, {a | eval (z a) (∑ k, X (.inl (p.1, k)) * X (.inl (k, p.2)) -
          X (.inl p)) = 0}) ∩
        ⋂ p : ι × ι, {a | eval (z a) (X (.inr p.swap) - X (.inl p)) = 0}) ∩
        {a | eval (z a) (∑ i, X (.inl (i, i)) - 1) = 0} := by
    ext a
    simp [z, isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint,
      ← Matrix.ext_iff, Matrix.mul_apply, trace, sub_eq_zero, Prod.forall, and_assoc]
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
      Matrix.of (fun i j ↦ (complexToRealPi (Fin N × Fin N)).symm a (i, j)) ∈
        Projectivization.hermitianProjector '' complexProjectiveZeroLocus p} := by
  let z (a : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℝ) : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℂ :=
    Sum.elim (fun k ↦ (a (.inl k) : ℂ) + a (.inr k) * I)
      (fun k ↦ star ((a (.inl k) : ℂ) + a (.inr k) * I))
  have h : {a : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℝ |
      Matrix.of (fun i j ↦ (complexToRealPi (Fin N × Fin N)).symm a (i, j)) ∈
        Projectivization.hermitianProjector '' complexProjectiveZeroLocus p} =
      {a | Matrix.of (fun i j ↦ (complexToRealPi (Fin N × Fin N)).symm a (i, j)) ∈
        hermitianProjectorLocus (Fin N) ℂ} ∩
        ⋂ k, ⋂ i, {a | eval (z a) (rename (fun j ↦ .inl (j, i)) (p k)) = 0} := by
    ext a
    simp only [image_hermitianProjector_complexProjectiveZeroLocus hp, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iInter, eval_rename, Matrix.of_apply, complexToRealPi_symm_apply]
    rfl
  rw [h]
  exact isSemialgebraic_hermitianProjectorLocus.inter
    (IsSemialgebraic.iInter fun _ ↦ IsSemialgebraic.iInter fun _ ↦
      isSemialgebraic_setOf_eval_sumElim_star_eq_zero _)

/-! ### The standard affine charts in real coordinates -/

section AffineChart

open Projectivization

variable {n : ℕ}

/-- In real coordinates, the inverse of the standard affine chart at `i` followed by the Hermitian
projector map is a semialgebraic map: it sends `z ∈ ℂⁿ` to the Hermitian projector
`v v* / (v* v)` of `v = Fin.insertNth i 1 z`, whose graph is cut out by the polynomial equations
`(v* v) A = v v*`. -/
theorem isSemialgebraicMap_hermitianProjector_affineChart_symm (i : Fin (n + 1)) :
    IsSemialgebraicMap fun a : Fin n ⊕ Fin n → ℝ ↦
      complexToRealPi (Fin (n + 1) × Fin (n + 1)) fun q ↦
        hermitianProjector ((affineChart i).symm ((complexToRealPi (Fin n)).symm a)) q.1 q.2 := by
  rw [← isSemialgebraicOn_univ, ← Set.preimage_univ (f := (complexToRealPi (Fin n)).symm)]
  -- Complex coordinates `z` of `ℂⁿ` and `A` of the matrices, together with their conjugates.
  let V : Fin (n + 1) → MvPolynomial
      ((Fin n ⊕ (Fin (n + 1) × Fin (n + 1))) ⊕ (Fin n ⊕ (Fin (n + 1) × Fin (n + 1)))) ℂ :=
    Fin.insertNth i 1 fun k ↦ X (.inl (.inl k))
  let Vc : Fin (n + 1) → MvPolynomial
      ((Fin n ⊕ (Fin (n + 1) × Fin (n + 1))) ⊕ (Fin n ⊕ (Fin (n + 1) × Fin (n + 1)))) ℂ :=
    Fin.insertNth i 1 fun k ↦ X (.inr (.inl k))
  refine isSemialgebraicOn_complexToRealPi_of_forall_eq_iff
    (g := fun z q ↦ hermitianProjector ((affineChart i).symm z) q.1 q.2)
    (Set.preimage_univ (f := (complexToRealPi (Fin n)).symm) ▸ isSemialgebraic_univ)
    (fun q ↦ (∑ r, Vc r * V r) * X (.inl (.inr q)) - V q.1 * Vc q.2) fun z _ A ↦ ?_
  set v : Fin (n + 1) → ℂ := Fin.insertNth i 1 z
  have hs : star v ⬝ᵥ v ≠ 0 := dotProduct_star_self_eq_zero.not.mpr (Fin.insertNth_one_ne_zero i z)
  have hV (r) : eval (Sum.elim (Sum.elim z A) fun t ↦ star (Sum.elim z A t)) (V r) = v r := by
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i r <;> simp [V, v]
  have hVc (r) : eval (Sum.elim (Sum.elim z A) fun t ↦ star (Sum.elim z A t)) (Vc r) =
      star (v r) := by
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i r <;> simp [Vc, v]
  simp only [map_sub, map_mul, map_sum, hV, hVc, funext_iff]
  refine forall_congr' fun q ↦ ?_
  rw [affineChart_symm_apply, hermitianProjector_mk, rankOneHermitianProjector_apply, div_eq_iff hs,
    sub_eq_zero, eq_comm]
  simp [v, dotProduct, mul_comm]

/-- In real coordinates, the image of the standard affine open `{x_i ≠ 0}` under the Hermitian
projector map is semialgebraic: it is the part of the Hermitian projector locus with nonzero
`i`-th diagonal entry. -/
theorem isSemialgebraic_image_hermitianProjector_affineOpen {ι : Type*} [Fintype ι] (i : ι) :
    IsSemialgebraic {b : (ι × ι) ⊕ (ι × ι) → ℝ |
      Matrix.of (fun r s ↦ (complexToRealPi (ι × ι)).symm b (r, s)) ∈
        hermitianProjector '' affineOpen i} := by
  rw [image_hermitianProjector_affineOpen]
  convert isSemialgebraic_hermitianProjectorLocus.inter
    (isSemialgebraic_setOf_eval_sumElim_star_eq_zero
      (X (.inl (i, i)) : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℂ)).compl using 1
  ext b
  simp

/-- In real coordinates, the standard affine chart at `i` read in the Hermitian projector model is
semialgebraic on the image of its domain: it sends a matrix `A` of the image of `{x_i ≠ 0}` to the
ratios `A (i.succAbove k) i / A i i` (`Projectivization.affineChart_eq_hermitianProjector_div`). -/
theorem isSemialgebraicOn_hermitianProjector_affineChart (i : Fin (n + 1)) :
    IsSemialgebraicOn (fun b ↦ complexToRealPi (Fin n) fun k ↦
        (complexToRealPi _).symm b (i.succAbove k, i) / (complexToRealPi _).symm b (i, i))
      {b | Matrix.of (fun r s ↦ (complexToRealPi (Fin (n + 1) × Fin (n + 1))).symm b (r, s)) ∈
        hermitianProjector '' affineOpen i} := by
  -- The graph is cut out by the equations `A i i * z k = A (i.succAbove k) i` over the domain.
  refine isSemialgebraicOn_complexToRealPi_of_forall_eq_iff
    (g := fun A k ↦ A (i.succAbove k, i) / A (i, i))
    (s := {A | Matrix.of (fun r s ↦ A (r, s)) ∈ hermitianProjector '' affineOpen i})
    (isSemialgebraic_image_hermitianProjector_affineOpen i)
    (fun k ↦ X (.inl (.inl (i, i))) * X (.inl (.inr k)) - X (.inl (.inl (i.succAbove k, i))))
    fun A hA w ↦ ?_
  rw [image_hermitianProjector_affineOpen] at hA
  have hii : A (i, i) ≠ 0 := by simpa only [Set.mem_ofPred_eq, Matrix.of_apply] using hA.2
  simp only [funext_iff]
  refine forall_congr' fun k ↦ ?_
  rw [div_eq_iff hii, eq_comm, ← sub_eq_zero]
  simp [mul_comm]

/-- **Semialgebraicity of the chart changes.** In real coordinates, the transition map from the
standard affine chart of complex projective space at `i` to the one at `j` is semialgebraic on its
domain. It factors through the Hermitian projector model, as the inverse chart at `i` followed by
the chart at `j` read in that model. -/
theorem isSemialgebraicOn_affineChart_symm_trans (i j : Fin (n + 1)) :
    IsSemialgebraicOn (fun a ↦ complexToRealPi (Fin n)
        ((affineChart i).symm.trans (affineChart j) ((complexToRealPi (Fin n)).symm a)))
      ((complexToRealPi (Fin n)).symm ⁻¹'
        ((affineChart (K := ℂ) i).symm.trans (affineChart j)).source) := by
  -- Read in the projector model, the domain is the inverse image of the image of `{x_j ≠ 0}`.
  have hdom : (complexToRealPi (Fin n)).symm ⁻¹'
      ((affineChart (K := ℂ) i).symm.trans (affineChart j)).source =
      (fun a ↦ complexToRealPi (Fin (n + 1) × Fin (n + 1)) fun q ↦
        hermitianProjector ((affineChart i).symm ((complexToRealPi (Fin n)).symm a)) q.1 q.2) ⁻¹'
      {b | Matrix.of (fun r s ↦ (complexToRealPi (Fin (n + 1) × Fin (n + 1))).symm b (r, s)) ∈
        hermitianProjector '' affineOpen j} := by
    have hp (p : ℙ ℂ (Fin (n + 1) → ℂ)) : Matrix.of (fun r s ↦
        (complexToRealPi (Fin (n + 1) × Fin (n + 1))).symm
          (complexToRealPi _ fun q ↦ hermitianProjector p q.1 q.2) (r, s)) =
        hermitianProjector p := by
      ext r s
      simp only [Matrix.of_apply, ContinuousLinearEquiv.symm_apply_apply]
    ext a
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, PartialEquiv.trans_source,
      PartialEquiv.symm_source, affineChart_target, affineChart_source, Set.univ_inter]
    rw [hp, hermitianProjector_injective.mem_set_image]
  have hs := hdom ▸
    (isSemialgebraicMap_hermitianProjector_affineChart_symm i).isSemialgebraic_preimage
      (isSemialgebraic_image_hermitianProjector_affineOpen j)
  refine ((isSemialgebraicOn_hermitianProjector_affineChart j).comp
    ((isSemialgebraicMap_hermitianProjector_affineChart_symm i).isSemialgebraicOn hs)
    (fun a ha ↦ ?_)).congr fun a _ ↦ ?_
  · rw [hdom] at ha
    exact ha
  · simp [affineChart_eq_hermitianProjector_div]

end AffineChart

end TauCeti
