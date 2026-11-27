/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The reachable subspace and the Kalman rank condition

For a state matrix `A : Matrix n n R` and an input matrix `B : Matrix n m R`, describing the
linear time-invariant control system `x(k+1) = A x(k) + B u(k)` or `x' = A x + B u`, the
*reachable subspace* is the span of the columns of `B, A B, A² B, …`. It is the smallest
`A`-invariant submodule of `n → R` containing the columns of `B`, and the pair `(A, B)` is
*controllable* when it is the whole state space.

By the Cayley–Hamilton theorem, `A ^ N` with `N = Fintype.card n` is a linear combination of the
lower powers of `A`, so the powers `A ^ k` with `k ≥ N` add nothing: the reachable subspace is the
column space of the controllability matrix `[B, A B, …, A ^ (N - 1) B]`. Over a field this gives
the Kalman rank condition: `(A, B)` is controllable if and only if the controllability matrix has
rank `N`.

## Main definitions

* `Matrix.reachableSubspace A B`: the supremum over `k : ℕ` of the column spaces of `A ^ k * B`.
* `Matrix.IsControllable A B`: the reachable subspace is `⊤`.
* `Matrix.ctrbMatrix A B`: the controllability matrix, whose column `(k, j)` is column `j` of
  `A ^ k * B`, for `k < Fintype.card n`.

## Main results

* `Matrix.reachableSubspace_le`: the reachable subspace lies in every `A`-invariant submodule
  containing the columns of `B`.
* `Matrix.reachableSubspace_eq_iSup_fin_card`: the powers `A ^ k` with `k < Fintype.card n`
  already span the reachable subspace.
* `Matrix.range_mulVecLin_ctrbMatrix`: the column space of the controllability matrix is the
  reachable subspace.
* `Matrix.isControllable_iff_rank_ctrbMatrix`: the Kalman rank condition.

## References

* Eduardo D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*,
  second edition, Springer, 1998: Definition 3.3.1, Lemma 3.3.2 and Theorem 2 (pp. 88–92).
-/

public section

open Polynomial Module

namespace Matrix

variable {R K : Type*} {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

section CommSemiring

variable [CommSemiring R] (A : Matrix n n R) (B : Matrix n m R)

/-- The reachable subspace of the pair `(A, B)`: the span of the columns of `A ^ k * B` for all
`k : ℕ`. -/
noncomputable def reachableSubspace : Submodule R (n → R) :=
  ⨆ k : ℕ, LinearMap.range (A ^ k * B).mulVecLin

theorem reachableSubspace_def :
    reachableSubspace A B = ⨆ k : ℕ, LinearMap.range (A ^ k * B).mulVecLin :=
  (rfl)

/-- The pair `(A, B)` is controllable when its reachable subspace is the whole state space. -/
def IsControllable : Prop :=
  reachableSubspace A B = ⊤

theorem isControllable_iff : IsControllable A B ↔ reachableSubspace A B = ⊤ :=
  Iff.rfl

/-- The controllability matrix `[B, A B, …, A ^ (N - 1) B]` of `(A, B)`, with
`N = Fintype.card n` and columns indexed by pairs `(k, j)`: its column `(k, j)` is column `j` of
`A ^ k * B`. -/
def ctrbMatrix : Matrix n (Fin (Fintype.card n) × m) R :=
  of fun i kj => (A ^ (kj.1 : ℕ) * B) i kj.2

omit [Fintype m] in
@[simp]
theorem ctrbMatrix_apply (i : n) (k : Fin (Fintype.card n)) (j : m) :
    ctrbMatrix A B i (k, j) = (A ^ (k : ℕ) * B) i j :=
  (rfl)

variable {A B}

/-- The columns of each `A ^ k * B` span a submodule of the reachable subspace. -/
theorem range_mulVecLin_pow_mul_le_reachableSubspace (k : ℕ) :
    LinearMap.range (A ^ k * B).mulVecLin ≤ reachableSubspace A B :=
  le_iSup (fun k => LinearMap.range (A ^ k * B).mulVecLin) k

/-- The columns of each `A ^ k * B` lie in the reachable subspace. -/
theorem pow_mul_mulVec_mem_reachableSubspace (k : ℕ) (v : m → R) :
    (A ^ k * B) *ᵥ v ∈ reachableSubspace A B :=
  range_mulVecLin_pow_mul_le_reachableSubspace k ⟨v, rfl⟩

/-- The columns of `B` lie in the reachable subspace. -/
theorem mulVec_mem_reachableSubspace (v : m → R) : B *ᵥ v ∈ reachableSubspace A B := by
  simpa using pow_mul_mulVec_mem_reachableSubspace (A := A) (B := B) 0 v

/-- The reachable subspace is `A`-invariant. -/
theorem mulVec_mem_reachableSubspace_of_mem {x : n → R} (hx : x ∈ reachableSubspace A B) :
    A *ᵥ x ∈ reachableSubspace A B := by
  refine Submodule.iSup_induction (fun k : ℕ => LinearMap.range (A ^ k * B).mulVecLin)
    (motive := fun x => A *ᵥ x ∈ reachableSubspace A B) hx (fun k x hx => ?_) (by simp)
    fun x y hx hy => by simpa [mulVec_add] using add_mem hx hy
  obtain ⟨v, rfl⟩ := hx
  rw [mulVecLin_apply, mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']
  exact
    pow_mul_mulVec_mem_reachableSubspace (A := A) (B := B) (k + 1) v

/-- The reachable subspace is contained in every `A`-invariant submodule containing the columns
of `B`; together with `mulVec_mem_reachableSubspace` and
`mulVec_mem_reachableSubspace_of_mem`, it is the smallest such submodule. -/
theorem reachableSubspace_le {W : Submodule R (n → R)} (hB : ∀ v, B *ᵥ v ∈ W)
    (hA : ∀ x ∈ W, A *ᵥ x ∈ W) : reachableSubspace A B ≤ W := by
  refine iSup_le fun k => ?_
  rintro _ ⟨v, rfl⟩
  induction k with
  | zero => simpa using hB v
  | succ k ih => simpa [pow_succ', mul_assoc, ← mulVec_mulVec] using hA _ ih

/-- With no inputs, the reachable subspace is `0`. -/
@[simp]
theorem reachableSubspace_eq_bot_of_isEmpty [IsEmpty m] : reachableSubspace A B = ⊥ :=
  eq_bot_iff.2 <| reachableSubspace_le (fun v => by simp [Subsingleton.elim v 0]) fun x hx => by
    simp [(Submodule.mem_bot R).1 hx]

/-- With no states, every pair is controllable. -/
@[simp]
theorem isControllable_of_isEmpty [IsEmpty n] : IsControllable A B :=
  (isControllable_iff A B).2 (Subsingleton.elim _ _)

end CommSemiring

section CommRing

variable [CommRing R] (A : Matrix n n R) (B : Matrix n m R)

/-- By the Cayley–Hamilton theorem, every column of `A ^ k * B` lies in the span of the columns of
`A ^ j * B` with `j < Fintype.card n`. -/
private theorem pow_mul_mulVec_mem_iSup_fin_card (k : ℕ) (v : m → R) :
    (A ^ k * B) *ᵥ v ∈ ⨆ j : Fin (Fintype.card n), LinearMap.range (A ^ (j : ℕ) * B).mulVecLin := by
  nontriviality R
  obtain ⟨q, hqk⟩ : ∃ q, X ^ k %ₘ A.charpoly = q := ⟨_, rfl⟩
  by_cases hq : q = 0
  · simp [A.pow_eq_aeval_mod_charpoly k, hqk, hq]
  have hdeg : q.natDegree < Fintype.card n := by
    rw [← A.charpoly_natDegree_eq_dim]
    exact natDegree_lt_natDegree hq (hqk ▸ degree_modByMonic_lt _ A.charpoly_monic)
  rw [A.pow_eq_aeval_mod_charpoly k, hqk, aeval_eq_sum_range' hdeg, Matrix.sum_mul, sum_mulVec]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [Matrix.smul_mul, smul_mulVec]
  exact Submodule.smul_mem _ _ <|
    Submodule.mem_iSup_of_mem ⟨j, Finset.mem_range.1 hj⟩ ⟨v, rfl⟩

/-- The powers `A ^ k` with `k < Fintype.card n` already span the reachable subspace. -/
theorem reachableSubspace_eq_iSup_fin_card :
    reachableSubspace A B =
      ⨆ k : Fin (Fintype.card n), LinearMap.range (A ^ (k : ℕ) * B).mulVecLin :=
  le_antisymm
    (iSup_le fun k => by rintro _ ⟨v, rfl⟩; exact pow_mul_mulVec_mem_iSup_fin_card A B k v)
    (iSup_le fun k => range_mulVecLin_pow_mul_le_reachableSubspace (k : ℕ))

/-- The column space of the controllability matrix is the reachable subspace. -/
theorem range_mulVecLin_ctrbMatrix :
    LinearMap.range (ctrbMatrix A B).mulVecLin = reachableSubspace A B := by
  have hcols : Set.range (ctrbMatrix A B).col = ⋃ k : Fin (Fintype.card n),
      Set.range (A ^ (k : ℕ) * B).col := by
    ext x
    simp only [Set.mem_range, Set.mem_iUnion, Prod.exists]
    refine exists_congr fun k => exists_congr fun j => ?_
    rw [funext_iff, funext_iff]
    simp
  rw [reachableSubspace_eq_iSup_fin_card, range_mulVecLin, hcols, Submodule.span_iUnion]
  simp only [range_mulVecLin]

/-- The rank of the controllability matrix is the dimension of the reachable subspace. -/
theorem rank_ctrbMatrix : (ctrbMatrix A B).rank = finrank R (reachableSubspace A B) := by
  rw [← finrank_range_mulVecLin, range_mulVecLin_ctrbMatrix]

end CommRing

section Field

variable [Field K] (A : Matrix n n K) (B : Matrix n m K)

/-- The Kalman rank condition: `(A, B)` is controllable if and only if its controllability matrix
has rank `Fintype.card n`. -/
theorem isControllable_iff_rank_ctrbMatrix :
    IsControllable A B ↔ (ctrbMatrix A B).rank = Fintype.card n := by
  rw [rank_ctrbMatrix, isControllable_iff, ← finrank_fintype_fun_eq_card (R := K)]
  exact ⟨fun h => by rw [h, finrank_top], Submodule.eq_top_of_finrank_eq⟩

end Field

end Matrix
