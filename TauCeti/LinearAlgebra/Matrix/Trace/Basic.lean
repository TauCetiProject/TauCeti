/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Ring.List

/-!
# Trace identities for matrices

Fix a matrix `S`. This file expands the quadratic map `M ↦ trace (M * S * M * S)` at a sum, so
that polarization recovers the symmetric bilinear map `(M, N) ↦ trace (M * S * N * S)` from it.
It also computes the trace of `2 P - 1`, which vanishes for a trace-one `2 × 2` matrix `P` such as
the orthogonal projector onto a line of `ℂ²`, and records that reindexing rows and columns along
one equivalence preserves the trace. Two square matrices intertwined by a matrix whose
determinant is a non-zero-divisor have the same trace; over a domain this applies to every
intertwiner of nonzero determinant, such as the inclusion matrix of a full-rank sublattice.
The trace of a product of two skew-Hermitian matrices is fixed by `star` (in particular,
it is real over `ℂ`). If `Y` maps the columns of `v` into the span of the columns of `w` with
matrix `N`, and `Z` is a left inverse of `w`, then `trace (v.submatrix id t * Z * Y)` is the sum of
the entries `N a (t a)`.

## Main results

* `Matrix.trace_add_mul_add_mul`: the expansion of `trace ((M + N) * S * (M + N) * S)` into the
  two pure terms and twice the mixed term.
* `Matrix.trace_two_mul_sub_one`: `trace (2 P - 1) = 2 trace P - n` for an `n × n` matrix `P`.
* `Matrix.trace_reindex_self`: reindexing rows and columns along one equivalence preserves the
  trace.
* `Matrix.trace_eq_of_mul_eq_mul`: if `A * P = P * B` and `det P` is a non-zero-divisor, then
  `trace A = trace B`.
* `Matrix.trace_list_prod_map_mapMatrix`: mapping a list of square matrices along a ring
  homomorphism commutes with taking the trace of its product.
* `Matrix.sum_trace_prod_update_lie`: the trace of an ordered product is invariant under
  simultaneous infinitesimal conjugation.
* `Matrix.star_trace_mul_of_conjTranspose_eq_neg`: the trace of a product of two skew-Hermitian
  matrices is fixed by `star`.
* `Matrix.sum_map_mul_comm`: the trace property for rectangular matrices over a possibly
  noncommutative ring, through an additive map `f` with `f (a * b) = f (b * a)`.
* `Matrix.trace_submatrix_mul_mul_eq_sum`: if `Z * w = 1` and `Y * v = w * N`, then
  `trace (v.submatrix id t * Z * Y) = ∑ a, N a (t a)`.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [CommSemiring R]

/-- The quadratic map `M ↦ trace (M * S * M * S)` expands at a sum into the two pure terms plus
twice the mixed term. The matrices may be rectangular. -/
theorem trace_add_mul_add_mul (M N : Matrix m n R) (S : Matrix n m R) :
    ((M + N) * S * (M + N) * S).trace =
      (M * S * M * S).trace + 2 * (M * S * N * S).trace + (N * S * N * S).trace := by
  have hcross : (N * S * M * S).trace = (M * S * N * S).trace := by
    simpa only [Matrix.mul_assoc] using trace_mul_comm (N * S) (M * S)
  simp only [Matrix.add_mul, Matrix.mul_add, trace_add, hcross]
  ring

/-- The trace of `2 P - 1` is `2 trace P - n` for an `n × n` matrix `P`. -/
theorem trace_two_mul_sub_one {R : Type*} [Ring R] [DecidableEq n] (P : Matrix n n R) :
    (2 * P - 1).trace = 2 * P.trace - Fintype.card n := by
  rw [two_mul, two_mul, trace_sub, trace_add, trace_one]

/-- Reindexing the rows and columns of a square matrix along the same equivalence preserves its
trace. -/
theorem trace_reindex_self {R : Type*} [AddCommMonoid R] (e : m ≃ n) (A : Matrix m m R) :
    (reindex e e A).trace = A.trace := by
  simpa [trace] using e.symm.sum_comp (fun i ↦ A i i)

/-- **Intertwined matrices have equal traces.** If `A * P = P * B` and the determinant of `P` is a
non-zero-divisor, then `trace A = trace B`. The matrix `P` need not be invertible; over `ℤ`, for
instance, it may be the inclusion matrix of a sublattice of finite index. -/
theorem trace_eq_of_mul_eq_mul {R : Type*} [CommRing R] [DecidableEq n] {A B P : Matrix n n R}
    (hP : P.det ∈ nonZeroDivisors R) (h : A * P = P * B) : A.trace = B.trace := by
  -- multiply both traces by `det P` and move `P` across with its adjugate
  refine (mul_cancel_left_mem_nonZeroDivisors hP).1 ?_
  calc P.det * A.trace = (A * (P * P.adjugate)).trace := by
        rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul]
    _ = (P.adjugate * (P * B)).trace := by
        rw [← Matrix.mul_assoc, h, trace_mul_comm]
    _ = P.det * B.trace := by
        rw [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul, trace_smul,
          smul_eq_mul]

/-- Mapping a list of square matrices along a ring homomorphism commutes with taking the trace of
its product. -/
theorem trace_list_prod_map_mapMatrix {R S : Type*} [DecidableEq n] [Semiring R] [Semiring S]
    (f : R →+* S) (l : List (Matrix n n R)) :
    trace (l.map f.mapMatrix).prod = f (trace l.prod) := by
  rw [← map_list_prod, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]

/-- The trace of an ordered product is invariant under the simultaneous infinitesimal
conjugation action on all its arguments. -/
theorem sum_trace_prod_update_lie {A : Type*} [CommRing A] [DecidableEq n] {k : ℕ}
    (Y : Matrix n n A) (v : Fin k → Matrix n n A) :
    ∑ i, trace (List.ofFn (Function.update v i ⁅Y, v i⁆)).prod = 0 := by
  have h := TauCeti.map_prod_ofFn_of_leibniz (fun X : Matrix n n A ↦ ⁅Y, X⁆)
    (fun X Z ↦ by simp only [Ring.lie_def]; noncomm_ring) v
  calc
    (∑ i, trace (List.ofFn (Function.update v i ⁅Y, v i⁆)).prod) =
        (traceAddMonoidHom n A)
          (∑ i, (List.ofFn (Function.update v i ⁅Y, v i⁆)).prod) := by rw [map_sum]; rfl
    _ = trace ⁅Y, (List.ofFn v).prod⁆ := congrArg trace h.symm
    _ = 0 := by rw [Ring.lie_def, trace_sub, trace_mul_comm, sub_self]

/-- The trace of a product of two skew-Hermitian matrices is fixed by `star`. -/
theorem star_trace_mul_of_conjTranspose_eq_neg {R : Type*} [NonUnitalNonAssocCommRing R]
    [StarRing R] {X Y : Matrix n n R} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    star (X * Y).trace = (X * Y).trace := by
  rw [← trace_conjTranspose, conjTranspose_mul, hX, hY, neg_mul_neg, trace_mul_comm]

/-- **Trace property for rectangular matrices.** If an additive map `f` satisfies
`f (a * b) = f (b * a)`, then for `u : Matrix m n R` and `v : Matrix n m R` the sums of `f` over the
diagonals of `u * v` and `v * u` agree. For commutative `R` and `f = id` this is
`Matrix.trace_mul_comm`. -/
theorem sum_map_mul_comm {R M F : Type*} [AddCommMonoid R] [Mul R] [AddCommMonoid M]
    [FunLike F R M] [AddMonoidHomClass F R M] (f : F) (hf : ∀ a b, f (a * b) = f (b * a))
    (u : Matrix m n R) (v : Matrix n m R) :
    ∑ i, f ((u * v) i i) = ∑ k, f ((v * u) k k) := by
  simp only [Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ hf _ _

/-- If `Z` is a left inverse of `w` and `Y` maps the columns of `v` into the span of the columns
of `w` with matrix `N`, then `tr (v_t Z Y) = ∑ N_{a, t a}` for the columns
`v_t = (v_{t a})_a` of `v`. -/
theorem trace_submatrix_mul_mul_eq_sum {k : Type*} [DecidableEq m] {v : Matrix n k R}
    {w : Matrix n m R} {Z : Matrix m n R} {Y : Matrix n n R} {N : Matrix m k R} {t : m → k}
    (hZ : Z * w = 1) (hN : Y * v = w * N) :
    (v.submatrix id t * Z * Y).trace = ∑ a, N a (t a) := by
  have h_cols : Y * v.submatrix id t = w * N.submatrix id t := by
    simpa only [submatrix_mul _ _ id id t Function.bijective_id, submatrix_id_id] using
      congrArg (·.submatrix id t) hN
  calc (v.submatrix id t * Z * Y).trace
        = (w * N.submatrix id t * Z).trace := by
        rw [trace_mul_comm, ← Matrix.mul_assoc, h_cols]
    _ = (N.submatrix id t).trace := by rw [trace_mul_cycle, hZ, Matrix.one_mul]
    _ = ∑ a, N a (t a) := by simp [Matrix.trace]

end Matrix
