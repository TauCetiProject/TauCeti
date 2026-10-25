/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.MvPolynomial
public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.Topology.Algebra.MvPolynomial.ZeroLocus

/-!
# Rank bounds are closed conditions

For a matrix `Z` and `r : ℕ`, the condition `rank Z ≤ r` says that every `(r + 1) × (r + 1)` minor
of `Z` vanishes (`Matrix.rank_le_iff_forall_det_submatrix_eq_zero`). Each such minor is a
polynomial in the entries of `Z`, with integer coefficients, and so is each minor of a power
`Z ^ j` of a square matrix. Hence the conditions `rank Z ≤ r` and `rank (Z ^ j) ≤ r` are Zariski
closed: they pass from a set of matrices to every point of the zero locus of the polynomials
vanishing on that set. Over a field with continuous ring operations and closed points, such as
`ℂ`, they are also closed in the usual topology. The Zariski closure is expressed through
Mathlib's `MvPolynomial.zeroLocus` and `MvPolynomial.vanishingIdeal`.

The same holds for a linear family `φ : V →ₗ[K] M →ₗ[K] N` of linear maps between
finite-dimensional spaces, read in the coordinates of a basis of the parameter space `V`: the
entries of the matrix of `φ x` are linear in the coordinates of `x`, so its minors are polynomials
in them. The bound `rank (φ x) ≤ p` is therefore Zariski closed in `x`. Over an infinite field the
complementary condition `p ≤ rank (φ x)` cuts out a Zariski-open set, which is Zariski dense as
soon as it is nonempty, because a nonzero polynomial cannot vanish on the complement of a
hypersurface. For the adjoint representation of a Lie algebra this gives the openness and density
of the elements whose centralizer has minimal dimension.

## Main results

* `Matrix.rank_le_of_mem_zeroLocus_vanishingIdeal` and
  `Matrix.rank_pow_le_of_mem_zeroLocus_vanishingIdeal`: a bound on the rank of a matrix, or of its
  `j`-th power, holding on a set of matrices holds on its Zariski closure.
* `Matrix.isClosed_setOfPred_rank_le` and `Matrix.isClosed_setOfPred_rank_pow_le`: the matrices of
  rank at most `r`, and the square matrices `Z` with `rank (Z ^ j) ≤ r`, form closed sets.
* `LinearMap.finrank_range_le_of_mem_zeroLocus_vanishingIdeal`: a rank bound on a linear family
  of linear maps passes to the Zariski closure in the coordinates of the parameter.
* `LinearMap.vanishingIdeal_setOfPred_le_finrank_range_eq_bot`: over an infinite field, a nonempty
  locus `p ≤ rank (φ x)` is Zariski dense.
-/

public section

open MvPolynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Zariski

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

omit [DecidableEq n] in
/-- **Rank bounds are Zariski closed.** If `rank Z ≤ r` for every matrix `Z` of a set `S`, then
`rank Y ≤ r` for every `Y` on which all polynomials vanishing on `S` vanish. -/
theorem rank_le_of_mem_zeroLocus_vanishingIdeal {m : Type*} [Finite m] {S : Set (Matrix m n K)}
    {r : ℕ} (hS : ∀ Z ∈ S, Z.rank ≤ r) {Y : Matrix m n K}
    (hY : Function.uncurry Y ∈ zeroLocus K (vanishingIdeal k (Function.uncurry '' S))) :
    Y.rank ≤ r := by
  rw [rank_le_iff_forall_det_submatrix_eq_zero]
  intro a b
  -- The minor of `Y` at `(a, b)` is the value at `Y` of a polynomial vanishing on `S`.
  rw [← aeval_det_submatrix_mvPolynomialX (R := k)]
  refine mem_zeroLocus_iff.1 hY _ (mem_vanishingIdeal_iff.2 ?_)
  -- The image under `Function.uncurry` sees `Z` as a function, so it is retyped as a matrix.
  rintro - ⟨Z, hZ, rfl⟩
  exact (aeval_det_submatrix_mvPolynomialX (Z : Matrix m n K) a b).trans
    (rank_le_iff_forall_det_submatrix_eq_zero.1 (hS Z hZ) a b)

/-- **Rank bounds are Zariski closed.** If `rank (Z ^ j) ≤ r` for every matrix `Z` of a set `S`,
then `rank (Y ^ j) ≤ r` for every `Y` on which all polynomials vanishing on `S` vanish. -/
theorem rank_pow_le_of_mem_zeroLocus_vanishingIdeal {S : Set (Matrix n n K)} {j r : ℕ}
    (hS : ∀ Z ∈ S, (Z ^ j).rank ≤ r) {Y : Matrix n n K}
    (hY : Function.uncurry Y ∈ zeroLocus K (vanishingIdeal k (Function.uncurry '' S))) :
    (Y ^ j).rank ≤ r := by
  rw [rank_le_iff_forall_det_submatrix_eq_zero]
  intro a b
  -- The minor of `Y ^ j` at `(a, b)` is the value at `Y` of a polynomial vanishing on `S`.
  rw [← aeval_det_submatrix_pow_mvPolynomialX (R := k)]
  refine mem_zeroLocus_iff.1 hY _ (mem_vanishingIdeal_iff.2 ?_)
  -- The image under `Function.uncurry` sees `Z` as a function, so it is retyped as a matrix.
  rintro - ⟨Z, hZ, rfl⟩
  exact (aeval_det_submatrix_pow_mvPolynomialX (Z : Matrix n n K) j a b).trans
    (rank_le_iff_forall_det_submatrix_eq_zero.1 (hS Z hZ) a b)

end Zariski

section Topological

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]

omit [DecidableEq n] in
/-- Over a field with continuous ring operations and closed points, the matrices of rank at most
`r` form a closed set. -/
theorem isClosed_setOfPred_rank_le {m : Type*} [Finite m] (r : ℕ) :
    IsClosed {A : Matrix m n K | A.rank ≤ r} := by
  refine isClosed_of_closure_subset fun Y hY ↦ rank_le_of_mem_zeroLocus_vanishingIdeal
    (k := K) (S := {A : Matrix m n K | A.rank ≤ r}) (fun _ hA ↦ hA)
    (closure_subset_zeroLocus_vanishingIdeal _ ?_)
  have huncurry : Continuous (Function.uncurry : Matrix m n K → m × n → K) :=
    continuous_pi fun p ↦ continuous_id.matrix_elem p.1 p.2
  exact mem_closure_image huncurry.continuousAt hY

/-- Over a field with continuous ring operations and closed points, the matrices `Z` with
`rank (Z ^ j) ≤ r` form a closed set. -/
theorem isClosed_setOfPred_rank_pow_le (j r : ℕ) :
    IsClosed {Z : Matrix n n K | (Z ^ j).rank ≤ r} :=
  (isClosed_setOfPred_rank_le r).preimage (continuous_pow j)

end Topological

end Matrix

namespace LinearMap

section LinearFamily

variable {K V M N ι : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M]
  [Module K M] [AddCommGroup N] [Module K N] [Finite ι] (b : Module.Basis ι K V)
  (φ : V →ₗ[K] M →ₗ[K] N)

/-- The minors of the matrices of a linear family of linear maps are polynomials in the
coordinates of the parameter. -/
private theorem exists_eval_eq_det_submatrix {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Finite κ'] (bM : Module.Basis κ K M) (bN : Module.Basis κ' K N) {p : ℕ} (r : Fin p → κ')
    (c : Fin p → κ) :
    ∃ q : MvPolynomial ι K, ∀ x : V,
      eval (b.equivFun x) q = ((toMatrix bM bN (φ x)).submatrix r c).det := by
  have := Fintype.ofFinite ι
  refine ⟨(Matrix.of fun i j ↦
    ∑ l, C (toMatrix bM bN (φ (b l)) (r i) (c j)) * X l).det, fun x ↦ ?_⟩
  -- The matrix of `φ x` is linear in the coordinates of `x`.
  have hx : toMatrix bM bN (φ x) = ∑ l, b.equivFun x l • toMatrix bM bN (φ (b l)) := by
    conv_lhs => rw [← b.sum_equivFun x]
    simp only [map_sum, map_smul]
  rw [RingHom.map_det, hx]
  congr 1
  ext i j
  simp [Matrix.sum_apply, mul_comm]

variable [FiniteDimensional K M] [FiniteDimensional K N]

/-- **Rank bounds on a linear family are Zariski closed.** Let `φ` be a linear family of linear
maps parametrized by a vector space `V` with basis `b`. If `rank (φ y) ≤ p` for every `y` in a set
`S`, then `rank (φ x) ≤ p` for every `x` whose coordinates lie in the common zero locus of the
polynomials vanishing on the coordinates of `S`. -/
theorem finrank_range_le_of_mem_zeroLocus_vanishingIdeal {S : Set V} {p : ℕ}
    (hS : ∀ y ∈ S, Module.finrank K (range (φ y)) ≤ p) {x : V}
    (hx : b.equivFun x ∈ zeroLocus K (vanishingIdeal K (b.equivFun '' S))) :
    Module.finrank K (range (φ x)) ≤ p := by
  classical
  let bM := Module.finBasis K M
  let bN := Module.finBasis K N
  rw [← Matrix.rank_toMatrix bM bN, Matrix.rank_le_iff_forall_det_submatrix_eq_zero]
  intro r c
  obtain ⟨q, hq⟩ := exists_eval_eq_det_submatrix b φ bM bN r c
  rw [← hq]
  refine mem_zeroLocus_iff.1 hx q (mem_vanishingIdeal_iff.2 ?_)
  rintro - ⟨y, hy, rfl⟩
  rw [aeval_eq_eval, hq]
  exact Matrix.rank_le_iff_forall_det_submatrix_eq_zero.1
    ((Matrix.rank_toMatrix bM bN _).trans_le (hS y hy)) r c

/-- **A nonempty rank lower bound locus is Zariski dense.** Over an infinite field, if some member
of a linear family `φ` of linear maps has rank at least `p`, then the only polynomial vanishing on
the coordinates of every `x` with `p ≤ rank (φ x)` is zero. -/
theorem vanishingIdeal_setOfPred_le_finrank_range_eq_bot [Infinite K] {p : ℕ} {x₀ : V}
    (hx₀ : p ≤ Module.finrank K (range (φ x₀))) :
    vanishingIdeal K (b.equivFun '' {x | p ≤ Module.finrank K (range (φ x))}) = ⊥ := by
  classical
  let bM := Module.finBasis K M
  let bN := Module.finBasis K N
  rw [← Matrix.rank_toMatrix bM bN, Matrix.le_rank_iff_exists_det_submatrix_ne_zero] at hx₀
  obtain ⟨r, c, hrc⟩ := hx₀
  -- A nonzero minor `q` at `x₀`. Wherever `q` does not vanish the rank is at least `p`, so every
  -- `f` vanishing on the locus has `f * q = 0` at every point.
  obtain ⟨q, hq⟩ := exists_eval_eq_det_submatrix b φ bM bN r c
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hrc (by rw [← hq, map_zero])
  refine eq_bot_iff.2 fun f hf ↦
    (mul_eq_zero.1 (MvPolynomial.funext fun c' ↦ ?_)).resolve_right hq0
  obtain ⟨x, rfl⟩ := b.equivFun.surjective c'
  rw [map_mul, map_zero, mul_eq_zero, or_iff_not_imp_right, hq]
  intro hx
  have hmem : x ∈ {x | p ≤ Module.finrank K (range (φ x))} := by
    rw [Set.mem_ofPred_eq, ← Matrix.rank_toMatrix bM bN,
      Matrix.le_rank_iff_exists_det_submatrix_ne_zero]
    exact ⟨r, c, hx⟩
  simpa using mem_vanishingIdeal_iff.1 hf _ ⟨x, hmem, rfl⟩

end LinearFamily

end LinearMap
