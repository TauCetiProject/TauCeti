/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import TauCeti.LinearAlgebra.Projectivization.Projector

/-!
# The Hermitian projector of a line

For a vector `x : ι → K` over a field with an involution `star`,
`TauCeti.rankOneHermitianProjector x` is the matrix `x x* / (x* x)`, with entries
`x i * star (x j) / ∑ k, star (x k) * x k`. When `x* x ≠ 0` it is the orthogonal projector onto the
line spanned by `x` for the Hermitian form `star v ⬝ᵥ w`. It is unchanged when `x` is rescaled, so
it descends to a map `Projectivization.hermitianProjector : ℙ K (ι → K) → Matrix ι ι K`.

The *Hermitian projector locus* `TauCeti.hermitianProjectorLocus ι K` consists of the star
projections (self-adjoint idempotents, `IsStarProjection`) of trace one. In characteristic zero a
matrix of the locus is the Hermitian projector of each of its columns with nonzero diagonal entry
(`TauCeti.rankOneHermitianProjector_col_eq_self`). Over `ℝ` or `ℂ` the map
`Projectivization.hermitianProjector` is a bijection from `ℙ 𝕜 (ι → 𝕜)` onto the locus.

For a field with trivial involution, such as `ℝ`, this is the rank-one projector
`TauCeti.rankOneProjector` and its locus is `TauCeti.projectorLocus`
(`TauCeti.rankOneHermitianProjector_eq_rankOneProjector`). Over `ℂ` the transpose-based projector
is not the right object: `xᵀ x` vanishes on the nonzero vectors with `∑ k, x k ^ 2 = 0`, and the
matrices `x xᵀ / (xᵀ x)` are not self-adjoint. The Hermitian projector instead realizes complex
projective space as a set of Hermitian matrices, which is a real algebraic set in the real and
imaginary parts of the entries. Its topological and semialgebraic properties are in
`TauCeti.Geometry.RealAlgebraic.HermitianProjectorEmbedding`.

## Main declarations

* `TauCeti.rankOneHermitianProjector x`: the matrix `x x* / (x* x)`.
* `TauCeti.hermitianProjectorLocus ι K`: the star projections of trace one.
* `Projectivization.hermitianProjector`: the Hermitian projector of a line of `ι → K`.

## Main results

* `TauCeti.rankOneHermitianProjector_mem_hermitianProjectorLocus`: the Hermitian projector of a
  vector with `x* x ≠ 0` lies in the locus.
* `TauCeti.rankOneHermitianProjector_col_eq_self`: a matrix in the locus is the Hermitian
  projector of each of its columns with nonzero diagonal entry.
* `Projectivization.hermitianProjector_injective` and `Projectivization.range_hermitianProjector`:
  over `ℝ` or `ℂ` the Hermitian projector map is a bijection from `ℙ 𝕜 (ι → 𝕜)` onto the locus.

## References

J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und
ihrer Grenzgebiete (3) 36, Springer, 1998, §3.4, for real projective space as the algebraic set of
symmetric idempotent matrices of trace one. The Hermitian projector is the same construction for
the standard Hermitian form.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace TauCeti

variable {ι K : Type*} [Fintype ι] [Field K] [StarRing K]

/-- The Hermitian projector `x x* / (x* x)` of a vector `x : ι → K`. When `x* x ≠ 0` it is the
orthogonal projector onto the line spanned by `x` for the Hermitian form `star v ⬝ᵥ w`; when
`x* x = 0`, for instance for `x = 0`, it is the zero matrix. -/
def rankOneHermitianProjector (x : ι → K) : Matrix ι ι K :=
  (star x ⬝ᵥ x)⁻¹ • vecMulVec x (star x)

theorem rankOneHermitianProjector_def (x : ι → K) :
    rankOneHermitianProjector x = (star x ⬝ᵥ x)⁻¹ • vecMulVec x (star x) :=
  (rfl)

theorem rankOneHermitianProjector_apply (x : ι → K) (i j : ι) :
    rankOneHermitianProjector x i j = x i * star (x j) / (star x ⬝ᵥ x) := by
  simp [rankOneHermitianProjector, vecMulVec_apply, div_eq_inv_mul]

@[simp]
theorem rankOneHermitianProjector_zero : rankOneHermitianProjector (0 : ι → K) = 0 := by
  simp [rankOneHermitianProjector]

/-- The Hermitian projector only depends on the line spanned by the vector. -/
@[simp]
theorem rankOneHermitianProjector_smul {c : K} (hc : c ≠ 0) (x : ι → K) :
    rankOneHermitianProjector (c • x) = rankOneHermitianProjector x := by
  have hc' : star c ≠ 0 := star_ne_zero.mpr hc
  ext i j
  simp only [rankOneHermitianProjector_apply, Pi.smul_apply, smul_eq_mul, star_smul,
    dotProduct_smul, smul_dotProduct, star_mul']
  rcases eq_or_ne (star x ⬝ᵥ x) 0 with hx | hx
  · simp [hx]
  field_simp

/-- For a field with trivial involution, such as `ℝ`, the Hermitian projector is the rank-one
projector `x xᵀ / (xᵀ x)`. -/
theorem rankOneHermitianProjector_eq_rankOneProjector [TrivialStar K] (x : ι → K) :
    rankOneHermitianProjector x = rankOneProjector x := by
  simp [rankOneHermitianProjector, rankOneProjector_def, star_trivial]

theorem rankOneHermitianProjector_mulVec (x y : ι → K) :
    rankOneHermitianProjector x *ᵥ y = ((star x ⬝ᵥ y) / (star x ⬝ᵥ x)) • x := by
  rw [rankOneHermitianProjector, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    div_eq_inv_mul]

/-- The Hermitian projector of a vector `x` with `x* x ≠ 0` fixes `x`. -/
theorem rankOneHermitianProjector_mulVec_self {x : ι → K} (hx : star x ⬝ᵥ x ≠ 0) :
    rankOneHermitianProjector x *ᵥ x = x := by
  rw [rankOneHermitianProjector_mulVec, div_self hx, one_smul]

theorem isSelfAdjoint_rankOneHermitianProjector (x : ι → K) :
    IsSelfAdjoint (rankOneHermitianProjector x) := by
  have h : star (star x ⬝ᵥ x) = star x ⬝ᵥ x := (star_dotProduct x x).symm
  rw [IsSelfAdjoint, rankOneHermitianProjector, star_smul, star_inv₀, h, star_eq_conjTranspose,
    conjTranspose_vecMulVec, star_star]

theorem isIdempotentElem_rankOneHermitianProjector (x : ι → K) :
    IsIdempotentElem (rankOneHermitianProjector x) := by
  rcases eq_or_ne (star x ⬝ᵥ x) 0 with hx | hx
  · simp [IsIdempotentElem, rankOneHermitianProjector, hx]
  simp [IsIdempotentElem, rankOneHermitianProjector, smul_mul_smul_comm, vecMulVec_mul_vecMulVec,
    smul_smul, hx]

theorem isStarProjection_rankOneHermitianProjector (x : ι → K) :
    IsStarProjection (rankOneHermitianProjector x) :=
  ⟨isIdempotentElem_rankOneHermitianProjector x, isSelfAdjoint_rankOneHermitianProjector x⟩

theorem trace_rankOneHermitianProjector {x : ι → K} (hx : star x ⬝ᵥ x ≠ 0) :
    (rankOneHermitianProjector x).trace = 1 := by
  rw [rankOneHermitianProjector, trace_smul, trace_vecMulVec, dotProduct_comm x, smul_eq_mul,
    inv_mul_cancel₀ hx]

/-- A vector `x` with `x* x ≠ 0` has the same Hermitian projector as `y` if and only if `x` and
`y` span the same line. -/
theorem rankOneHermitianProjector_eq_rankOneHermitianProjector_iff {x y : ι → K}
    (hx : star x ⬝ᵥ x ≠ 0) :
    rankOneHermitianProjector x = rankOneHermitianProjector y ↔ ∃ c : K, c • y = x := by
  refine ⟨fun h ↦ ⟨(star y ⬝ᵥ x) / (star y ⬝ᵥ y), ?_⟩, ?_⟩
  · rw [← rankOneHermitianProjector_mulVec, ← h, rankOneHermitianProjector_mulVec_self hx]
  · rintro ⟨c, rfl⟩
    exact rankOneHermitianProjector_smul (by rintro rfl; simp at hx) y

variable (ι K) in
/-- The *Hermitian projector locus*: the star projections (self-adjoint idempotents) of trace
one. Over `ℝ` or `ℂ` these are exactly the Hermitian projectors of nonzero vectors
(`Projectivization.range_hermitianProjector`). -/
def hermitianProjectorLocus : Set (Matrix ι ι K) :=
  {A | IsStarProjection A ∧ A.trace = 1}

@[simp]
theorem mem_hermitianProjectorLocus {A : Matrix ι ι K} :
    A ∈ hermitianProjectorLocus ι K ↔ IsStarProjection A ∧ A.trace = 1 :=
  Iff.rfl

/-- For a field with trivial involution, such as `ℝ`, the Hermitian projector locus is the
projector locus of symmetric idempotents of trace one. -/
theorem hermitianProjectorLocus_eq_projectorLocus [TrivialStar K] :
    hermitianProjectorLocus ι K = projectorLocus ι K := by
  ext A
  simp [isStarProjection_iff, IsSelfAdjoint, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, IsSymm]
  tauto

/-- The Hermitian projector of a vector with `x* x ≠ 0` lies in the Hermitian projector locus. -/
theorem rankOneHermitianProjector_mem_hermitianProjectorLocus {x : ι → K} (hx : star x ⬝ᵥ x ≠ 0) :
    rankOneHermitianProjector x ∈ hermitianProjectorLocus ι K :=
  ⟨isStarProjection_rankOneHermitianProjector x, trace_rankOneHermitianProjector hx⟩

variable [CharZero K]

/-- A matrix in the Hermitian projector locus is the Hermitian projector of each of its columns
whose diagonal entry is nonzero. This recovers the line of a point of the locus, and gives the
inverse of the Hermitian projector map on the standard affine charts. -/
theorem rankOneHermitianProjector_col_eq_self {A : Matrix ι ι K}
    (hA : A ∈ hermitianProjectorLocus ι K) {i : ι} (hi : A i i ≠ 0) :
    rankOneHermitianProjector (fun k ↦ A k i) = A := by
  obtain ⟨⟨hI, hS⟩, htr⟩ := hA
  set v : ι → K := fun k ↦ A k i
  -- The idempotent `A` fixes its column `v`, and since `A` is self-adjoint, `v* v = A i i ≠ 0`.
  have hAv : A *ᵥ v = v := funext fun j ↦ by
    simp only [mulVec, dotProduct, v]
    simpa only [mul_apply] using congr_fun₂ hI.eq j i
  have hv : star v ⬝ᵥ v ≠ 0 := by
    have hS' : ∀ k, star (A k i) = A i k := fun k ↦ by
      simpa [star_eq_conjTranspose, conjTranspose_apply] using congr_fun₂ hS.star_eq i k
    have : star v ⬝ᵥ v = (A * A) i i := by simp [v, dotProduct, mul_apply, hS']
    rwa [this, hI.eq]
  -- So `A` fixes the line of `P = rankOneHermitianProjector v`: `A * P = P`, and taking adjoints
  -- gives `P * A = P`.
  have hAP : A * rankOneHermitianProjector v = rankOneHermitianProjector v := by
    rw [rankOneHermitianProjector, Matrix.mul_smul, mul_vecMulVec, hAv]
  have hPA : rankOneHermitianProjector v * A = rankOneHermitianProjector v := by
    simpa only [star_mul, (isSelfAdjoint_rankOneHermitianProjector v).star_eq, hS.star_eq] using
      congr_arg star hAP
  -- Hence `A - P` is an idempotent of trace zero, so it is zero.
  have hB : IsIdempotentElem (A - rankOneHermitianProjector v) := by
    rw [IsIdempotentElem, sub_mul, mul_sub, mul_sub, hI.eq, hAP, hPA,
      (isIdempotentElem_rankOneHermitianProjector v).eq]
    abel
  exact (sub_eq_zero.mp (Matrix.IsIdempotentElem.eq_zero_of_trace_eq_zero hB
    (by rw [trace_sub, htr, trace_rankOneHermitianProjector hv, sub_self]))).symm

/-- Every matrix in the Hermitian projector locus is the Hermitian projector of a nonzero
vector. -/
theorem exists_rankOneHermitianProjector_eq_of_mem_hermitianProjectorLocus {A : Matrix ι ι K}
    (hA : A ∈ hermitianProjectorLocus ι K) :
    ∃ x : ι → K, x ≠ 0 ∧ rankOneHermitianProjector x = A := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hA.2 ▸ one_ne_zero : A.trace ≠ 0)
  exact ⟨fun k ↦ A k i, fun h ↦ hi (congr_fun h i), rankOneHermitianProjector_col_eq_self hA hi⟩

end TauCeti

namespace Projectivization

open TauCeti

section Field

variable {ι K : Type*} [Fintype ι] [Field K] [StarRing K]

/-- The Hermitian projector of a line of `ι → K`: the matrix `x x* / (x* x)` for any nonzero
vector `x` spanning the line. -/
def hermitianProjector (p : ℙ K (ι → K)) : Matrix ι ι K :=
  p.lift (fun x ↦ rankOneHermitianProjector x.1) fun x y c h ↦ by
    rw [h, rankOneHermitianProjector_smul]
    rintro rfl
    exact x.2 (by simp [h])

@[simp]
theorem hermitianProjector_mk (x : ι → K) (hx : x ≠ 0) :
    hermitianProjector (mk K x hx) = rankOneHermitianProjector x :=
  Projectivization.lift_mk _ _ x hx

/-- For a field with trivial involution, such as `ℝ`, the Hermitian projector of a line is its
rank-one projector. -/
theorem hermitianProjector_eq_projector [TrivialStar K] :
    (hermitianProjector : ℙ K (ι → K) → Matrix ι ι K) = projector := by
  funext p
  induction p using ind with
  | h x hx => simp [rankOneHermitianProjector_eq_rankOneProjector]

end Field

section RCLike

open scoped ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]

/-- Over `ℝ` or `ℂ` the Hermitian projector of every line lies in the Hermitian projector
locus. -/
theorem hermitianProjector_mem_hermitianProjectorLocus (p : ℙ 𝕜 (ι → 𝕜)) :
    hermitianProjector p ∈ hermitianProjectorLocus ι 𝕜 := by
  induction p using ind with
  | h x hx =>
    exact rankOneHermitianProjector_mem_hermitianProjectorLocus
      (dotProduct_star_self_eq_zero.not.mpr hx)

/-- Over `ℝ` or `ℂ` the Hermitian projector map is injective: distinct lines of `ι → 𝕜` have
distinct Hermitian projectors. -/
theorem hermitianProjector_injective :
    Function.Injective (hermitianProjector : ℙ 𝕜 (ι → 𝕜) → Matrix ι ι 𝕜) := by
  intro p q h
  induction p using ind with | h x hx =>
  induction q using ind with | h y hy =>
  rw [mk_eq_mk_iff']
  exact (rankOneHermitianProjector_eq_rankOneHermitianProjector_iff
    (dotProduct_star_self_eq_zero.not.mpr hx)).mp h

/-- Over `ℝ` or `ℂ` the image of the Hermitian projector map is exactly the Hermitian projector
locus. -/
theorem range_hermitianProjector :
    Set.range (hermitianProjector : ℙ 𝕜 (ι → 𝕜) → Matrix ι ι 𝕜) =
      hermitianProjectorLocus ι 𝕜 := by
  refine Set.Subset.antisymm
    (Set.range_subset_iff.mpr hermitianProjector_mem_hermitianProjectorLocus) fun A hA ↦ ?_
  obtain ⟨x, hx, rfl⟩ := exists_rankOneHermitianProjector_eq_of_mem_hermitianProjectorLocus hA
  exact ⟨mk 𝕜 x hx, hermitianProjector_mk x hx⟩

end RCLike

end Projectivization
