/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# The rank-one projector of a line

For a vector `x : ι → K` over a field `K`, `TauCeti.rankOneProjector x` is the matrix
`x xᵀ / (xᵀ x)`, with entries `x i * x j / ∑ k, x k ^ 2`. When `xᵀ x ≠ 0` it is the orthogonal
projector onto the line spanned by `x`. It is unchanged when `x` is rescaled, so it descends to a
map `Projectivization.projector : ℙ K (ι → K) → Matrix ι ι K`.

The *projector locus* `TauCeti.projectorLocus ι K` consists of the symmetric idempotent matrices of
trace one. In characteristic zero, a matrix of the locus is the rank-one projector of each of its
rows with nonzero diagonal entry (`TauCeti.rankOneProjector_row_eq_self`): these rows recover the
line, and give the inverse of the projector map on the standard affine charts. Over an ordered
field `xᵀ x ≠ 0` for every nonzero `x`, and the projector map is a bijection from `ℙ K (ι → K)`
onto the projector locus. Since the locus is cut out by polynomial equations in the entries, this
realizes projective space as an algebraic set of matrices. Over `ℝ` this is the standard embedding
of real projective space as a compact real algebraic set; its topological and semialgebraic
properties are in `TauCeti.Geometry.RealAlgebraic.ProjectorEmbedding`.

## Main declarations

* `TauCeti.rankOneProjector x`: the matrix `x xᵀ / (xᵀ x)`.
* `TauCeti.projectorLocus ι K`: the symmetric idempotent matrices of trace one.
* `Projectivization.projector`: the rank-one projector of a line of `ι → K`.

## Main results

* `TauCeti.rankOneProjector_mem_projectorLocus`: the projector of a vector with `xᵀ x ≠ 0` lies
  in the locus.
* `TauCeti.rankOneProjector_row_eq_self`: a matrix in the locus is the projector of each of its
  rows with nonzero diagonal entry. Its proof uses two matrix facts proved here:
  `Matrix.IsSymm.mulVec_row_of_isIdempotentElem` (a symmetric idempotent fixes its rows) and
  `Matrix.IsIdempotentElem.eq_zero_of_trace_eq_zero` (in characteristic zero an idempotent of
  trace zero vanishes).
* `Projectivization.projector_injective` and `Projectivization.range_projector`: the projector
  map is a bijection from `ℙ K (ι → K)` onto the projector locus.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §3, p. 464, for the use of this embedding to reduce triangulation of
real projective spaces to the affine case. The formula here uses all homogeneous coordinates; the
printed formula omits one of them.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace Matrix

variable {ι K : Type*} [Fintype ι]

/-- A symmetric idempotent matrix fixes each of its rows, since the row `A i` is also the column
`A *ᵥ Pi.single i 1`. -/
theorem IsSymm.mulVec_row_of_isIdempotentElem [Semiring K] {A : Matrix ι ι K} (hS : A.IsSymm)
    (hI : IsIdempotentElem A) (i : ι) : A *ᵥ A i = A i := by
  classical
  rw [← row_apply' A i, ← col_transpose, hS.eq, ← mulVec_single_one, mulVec_mulVec, hI.eq]

/-- Over a field of characteristic zero, an idempotent matrix of trace zero is zero: the trace of
an idempotent is the dimension of its range. This is the matrix form of
`LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero`. -/
theorem IsIdempotentElem.eq_zero_of_trace_eq_zero [Field K] [CharZero K] {A : Matrix ι ι K}
    (hA : IsIdempotentElem A) (htr : A.trace = 0) : A = 0 := by
  classical
  refine toLinAlgEquiv'.injective ?_
  rw [map_zero]
  exact LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (hA.map toLinAlgEquiv')
    ((trace_toLin'_eq A).trans htr)

end Matrix

namespace TauCeti

variable {ι K : Type*} [Fintype ι] [Field K]

/-- The rank-one projector `x xᵀ / (xᵀ x)` of a vector `x : ι → K`. When `xᵀ x ≠ 0` it is the
orthogonal projector onto the line spanned by `x`; when `xᵀ x = 0`, for instance for `x = 0`, it
is the zero matrix. -/
def rankOneProjector (x : ι → K) : Matrix ι ι K :=
  (x ⬝ᵥ x)⁻¹ • vecMulVec x x

theorem rankOneProjector_def (x : ι → K) :
    rankOneProjector x = (x ⬝ᵥ x)⁻¹ • vecMulVec x x :=
  (rfl)

theorem rankOneProjector_apply (x : ι → K) (i j : ι) :
    rankOneProjector x i j = x i * x j / (x ⬝ᵥ x) := by
  simp [rankOneProjector, vecMulVec_apply, div_eq_inv_mul]

@[simp]
theorem rankOneProjector_zero : rankOneProjector (0 : ι → K) = 0 := by
  simp [rankOneProjector]

/-- The rank-one projector only depends on the line spanned by the vector. -/
@[simp]
theorem rankOneProjector_smul {c : K} (hc : c ≠ 0) (x : ι → K) :
    rankOneProjector (c • x) = rankOneProjector x := by
  ext i j
  simp only [rankOneProjector_apply, Pi.smul_apply, smul_eq_mul, dotProduct_smul,
    smul_dotProduct]
  field_simp

theorem rankOneProjector_mulVec (x y : ι → K) :
    rankOneProjector x *ᵥ y = ((x ⬝ᵥ y) / (x ⬝ᵥ x)) • x := by
  rw [rankOneProjector, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    div_eq_inv_mul]

theorem isSymm_rankOneProjector (x : ι → K) : (rankOneProjector x).IsSymm := by
  simp [IsSymm, rankOneProjector, transpose_smul, transpose_vecMulVec]

variable (ι K) in
/-- The *projector locus*: the symmetric idempotent matrices of trace one. Over an ordered field
these are exactly the rank-one projectors of nonzero vectors
(`Projectivization.range_projector`). -/
def projectorLocus : Set (Matrix ι ι K) :=
  {A | A.IsSymm ∧ IsIdempotentElem A ∧ A.trace = 1}

@[simp]
theorem mem_projectorLocus {A : Matrix ι ι K} :
    A ∈ projectorLocus ι K ↔ A.IsSymm ∧ IsIdempotentElem A ∧ A.trace = 1 :=
  Iff.rfl

/-- The rank-one projector of a vector `x` with `xᵀ x ≠ 0` fixes `x`. -/
theorem rankOneProjector_mulVec_self {x : ι → K} (hx : x ⬝ᵥ x ≠ 0) :
    rankOneProjector x *ᵥ x = x := by
  rw [rankOneProjector_mulVec, div_self hx, one_smul]

theorem isIdempotentElem_rankOneProjector (x : ι → K) :
    IsIdempotentElem (rankOneProjector x) := by
  rcases eq_or_ne (x ⬝ᵥ x) 0 with hx | hx
  · simp [IsIdempotentElem, rankOneProjector, hx]
  rw [IsIdempotentElem, rankOneProjector, smul_mul_smul_comm, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hx, mul_one]

theorem trace_rankOneProjector {x : ι → K} (hx : x ⬝ᵥ x ≠ 0) :
    (rankOneProjector x).trace = 1 := by
  rw [rankOneProjector, trace_smul, trace_vecMulVec, smul_eq_mul, inv_mul_cancel₀ hx]

/-- A vector `x` with `xᵀ x ≠ 0` has the same rank-one projector as `y` if and only if `x` and
`y` span the same line. -/
theorem rankOneProjector_eq_rankOneProjector_iff {x y : ι → K} (hx : x ⬝ᵥ x ≠ 0) :
    rankOneProjector x = rankOneProjector y ↔ ∃ c : K, c • y = x := by
  refine ⟨fun h ↦ ⟨(y ⬝ᵥ x) / (y ⬝ᵥ y), ?_⟩, ?_⟩
  · rw [← rankOneProjector_mulVec, ← h, rankOneProjector_mulVec_self hx]
  · rintro ⟨c, rfl⟩
    exact rankOneProjector_smul (by rintro rfl; simp at hx) y

/-- The rank-one projector of a vector with `xᵀ x ≠ 0` lies in the projector locus. -/
theorem rankOneProjector_mem_projectorLocus {x : ι → K} (hx : x ⬝ᵥ x ≠ 0) :
    rankOneProjector x ∈ projectorLocus ι K :=
  ⟨isSymm_rankOneProjector x, isIdempotentElem_rankOneProjector x, trace_rankOneProjector hx⟩

variable [CharZero K]

/-- A matrix in the projector locus is the rank-one projector of each of its rows whose diagonal
entry is nonzero. This recovers the line of a point of the locus, and gives the inverse of the
projector map on the standard affine charts. -/
theorem rankOneProjector_row_eq_self {A : Matrix ι ι K} (hA : A ∈ projectorLocus ι K) {i : ι}
    (hi : A i i ≠ 0) : rankOneProjector (A i) = A := by
  obtain ⟨hS, hI, htr⟩ := hA
  -- The symmetric idempotent `A` fixes its row `A i`, which is also its column; in particular
  -- `A i ⬝ᵥ A i = A i i ≠ 0`.
  have hAv : A *ᵥ A i = A i := hS.mulVec_row_of_isIdempotentElem hI i
  have hv : A i ⬝ᵥ A i ≠ 0 := by
    rwa [← congr_fun hAv i, mulVec_apply, row_apply'] at hi
  -- So `A` fixes the line of `P = rankOneProjector (A i)`: `A * P = P`, and transposing gives
  -- `P * A = P`.
  have hAP : A * rankOneProjector (A i) = rankOneProjector (A i) := by
    rw [rankOneProjector, Matrix.mul_smul, mul_vecMulVec, hAv]
  have hPA : rankOneProjector (A i) * A = rankOneProjector (A i) := by
    simpa only [transpose_mul, (isSymm_rankOneProjector (A i)).eq, hS.eq] using
      congr_arg transpose hAP
  -- Hence `A - P` is an idempotent of trace zero, so it is zero.
  have hB : IsIdempotentElem (A - rankOneProjector (A i)) := by
    rw [IsIdempotentElem, sub_mul, mul_sub, mul_sub, hI.eq, hAP, hPA,
      (isIdempotentElem_rankOneProjector (A i)).eq]
    abel
  exact (sub_eq_zero.mp (Matrix.IsIdempotentElem.eq_zero_of_trace_eq_zero hB
    (by rw [trace_sub, htr, trace_rankOneProjector hv, sub_self]))).symm

/-- Every matrix in the projector locus is the rank-one projector of a nonzero vector. -/
theorem exists_rankOneProjector_eq_of_mem_projectorLocus {A : Matrix ι ι K}
    (hA : A ∈ projectorLocus ι K) : ∃ x : ι → K, x ≠ 0 ∧ rankOneProjector x = A := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hA.2.2 ▸ one_ne_zero : A.trace ≠ 0)
  exact ⟨A i, fun h ↦ hi (by simp [h]), rankOneProjector_row_eq_self hA hi⟩

end TauCeti

namespace Projectivization

open TauCeti

variable {ι K : Type*} [Fintype ι] [Field K]

/-- The rank-one projector of a line of `ι → K`: the matrix `x xᵀ / (xᵀ x)` for any nonzero
vector `x` spanning the line. -/
def projector (p : ℙ K (ι → K)) : Matrix ι ι K :=
  p.lift (fun x ↦ rankOneProjector x.1) fun x y c h ↦ by
    rw [h, rankOneProjector_smul]
    rintro rfl
    exact x.2 (by simp [h])

@[simp]
theorem projector_mk (x : ι → K) (hx : x ≠ 0) : projector (mk K x hx) = rankOneProjector x :=
  (rfl)

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Over an ordered field the projector of every line lies in the projector locus. -/
theorem projector_mem_projectorLocus (p : ℙ K (ι → K)) : projector p ∈ projectorLocus ι K := by
  induction p using ind with
  | h x hx => exact rankOneProjector_mem_projectorLocus (dotProduct_self_eq_zero.not.mpr hx)

/-- Over an ordered field the projector map is injective: distinct lines of `ι → K` have distinct
projectors. -/
theorem projector_injective : Function.Injective (projector : ℙ K (ι → K) → Matrix ι ι K) := by
  intro p q h
  induction p using ind with | h x hx =>
  induction q using ind with | h y hy =>
  rw [mk_eq_mk_iff']
  exact (rankOneProjector_eq_rankOneProjector_iff (dotProduct_self_eq_zero.not.mpr hx)).mp h

/-- The image of the projector map is exactly the projector locus. -/
theorem range_projector :
    Set.range (projector : ℙ K (ι → K) → Matrix ι ι K) = projectorLocus ι K := by
  refine Set.Subset.antisymm (Set.range_subset_iff.mpr projector_mem_projectorLocus) fun A hA ↦ ?_
  obtain ⟨x, hx, rfl⟩ := exists_rankOneProjector_eq_of_mem_projectorLocus hA
  exact ⟨mk K x hx, projector_mk x hx⟩

end Projectivization
