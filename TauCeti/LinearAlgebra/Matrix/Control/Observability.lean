/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Control.Reachable
import TauCeti.LinearAlgebra.Matrix.Charpoly.CayleyHamilton

/-!
# The unobservable subspace, observability and duality

For a state matrix `A : Matrix n n R` and an output matrix `C : Matrix p n R`, describing the free
linear time-invariant system `x(k+1) = A x(k)`, `y(k) = C x(k)` (or `x' = A x`, `y = C x`), the
*unobservable subspace* is the intersection of the kernels of `C, C A, C A², …`: the initial
states whose free output vanishes at every time. It is the largest `A`-invariant submodule of
`n → R` contained in `ker C`, and the pair `(A, C)` is *observable* when it is `⊥`.

By `Matrix.exists_pow_card_add_sum_eq_sum`, the Cayley–Hamilton theorem (transferred via universal
multivariate polynomials to any commutative semiring) shows that powers `A ^ k` with
`k ≥ Fintype.card n` add no further constraints, so the unobservable subspace is already the kernel
of `(ctrbMatrix Aᵀ Cᵀ).vecMulLinear`. Over a commutative
ring this identifies observability with injectivity of the finite-horizon output map
`x ↦ (k ↦ (C * A ^ k) *ᵥ x)` for `k < Fintype.card n`; over a field, rank–nullity and
`Matrix.rank_transpose` yield Kalman duality: `(A, C)` is observable if and only if `(Aᵀ, Cᵀ)`
is controllable.

## Main definitions

* `Matrix.unobservableSubspace A C`: the infimum over `k : ℕ` of the kernels of `C * A ^ k`.
* `Matrix.IsObservable A C`: the unobservable subspace is `⊥`.

## Main results

* `Matrix.le_unobservableSubspace`: the unobservable subspace contains every `A`-invariant
  submodule lying in `ker C`.
* `Matrix.unobservableSubspace_eq_iInf_fin_card`: the powers `A ^ k` with `k < Fintype.card n`
  already determine the unobservable subspace.
* `Matrix.ker_vecMulLinear_transpose_ctrbMatrix`: the kernel of
  `(ctrbMatrix Aᵀ Cᵀ).vecMulLinear` is the unobservable subspace of `(A, C)`.
* `Matrix.isObservable_iff_free_outputs_eq_zero`: observability is equivalent to the only state
  whose free output vanishes at every time being zero.
* `Matrix.isObservable_iff_injective`: over a commutative ring, `(A, C)` is observable if and only
  if the first `Fintype.card n` free outputs determine the initial state.
* `Matrix.isObservable_iff_isControllable_transpose`: over a field, `(A, C)` is observable if and
  only if `(Aᵀ, Cᵀ)` is controllable.

## References

* Eduardo D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*,
  second edition, Springer, 1998: Theorems 23 and 24 and Corollary 6.2.4 (p. 271).
* Karl Johan Åström and Richard M. Murray, *Feedback Systems: An Introduction for Scientists and
  Engineers*, second edition, Princeton University Press, 2021: Theorem 8.1 (p. 8-3).
-/

public section

open Module

namespace Matrix

variable {R K : Type*} {n p : Type*} [Fintype n] [DecidableEq n]

section CommSemiring

variable [CommSemiring R] (A : Matrix n n R) (C : Matrix p n R)

/-- The unobservable subspace of the pair `(A, C)`: the initial states `x` with
`(C * A ^ k) *ᵥ x = 0` for all `k : ℕ`. -/
noncomputable def unobservableSubspace : Submodule R (n → R) :=
  ⨅ k : ℕ, LinearMap.ker (C * A ^ k).mulVecLin

theorem unobservableSubspace_def :
    unobservableSubspace A C = ⨅ k : ℕ, LinearMap.ker (C * A ^ k).mulVecLin :=
  (rfl)

/-- The pair `(A, C)` is observable when its unobservable subspace is zero. -/
def IsObservable : Prop :=
  unobservableSubspace A C = ⊥

theorem isObservable_iff : IsObservable A C ↔ unobservableSubspace A C = ⊥ :=
  Iff.rfl

variable {A C}

/-- A state lies in the unobservable subspace if and only if every free output `(C * A ^ k) *ᵥ x`
vanishes. -/
@[simp]
theorem mem_unobservableSubspace {x : n → R} :
    x ∈ unobservableSubspace A C ↔ ∀ k : ℕ, (C * A ^ k) *ᵥ x = 0 := by
  simp [unobservableSubspace, Submodule.mem_iInf]

/-- `(A, C)` is observable if and only if the only state whose free output vanishes at every time
is zero. -/
theorem isObservable_iff_free_outputs_eq_zero :
    IsObservable A C ↔ ∀ x : n → R, (∀ k : ℕ, (C * A ^ k) *ᵥ x = 0) → x = 0 := by
  rw [isObservable_iff]
  constructor
  · intro h x hx
    have hx' : x ∈ unobservableSubspace A C := mem_unobservableSubspace.2 hx
    rw [h] at hx'
    exact (Submodule.mem_bot R).1 hx'
  · intro h
    apply eq_bot_iff.2
    intro x hx
    exact (Submodule.mem_bot R).2 (h x (mem_unobservableSubspace.1 hx))

/-- The unobservable subspace is contained in the kernel of each `C * A ^ k`. -/
theorem unobservableSubspace_le_ker_mulVecLin_mul_pow (k : ℕ) :
    unobservableSubspace A C ≤ LinearMap.ker (C * A ^ k).mulVecLin :=
  fun _ hx => (mem_unobservableSubspace.1 hx) k

/-- Every unobservable state lies in the kernel of `C`. -/
theorem mulVec_eq_zero_of_mem_unobservableSubspace {x : n → R}
    (hx : x ∈ unobservableSubspace A C) : C *ᵥ x = 0 := by
  simpa using (mem_unobservableSubspace.1 hx) 0

/-- The unobservable subspace is `A`-invariant. -/
theorem mulVec_mem_unobservableSubspace_of_mem {x : n → R} (hx : x ∈ unobservableSubspace A C) :
    A *ᵥ x ∈ unobservableSubspace A C :=
  mem_unobservableSubspace.2 fun k => by
    rw [mulVec_mulVec, Matrix.mul_assoc, ← pow_succ]
    exact (mem_unobservableSubspace.1 hx) (k + 1)

/-- The unobservable subspace contains every `A`-invariant submodule in the kernel of `C`; together
with `mulVec_eq_zero_of_mem_unobservableSubspace` and `mulVec_mem_unobservableSubspace_of_mem`, it
is the largest such submodule. -/
theorem le_unobservableSubspace {W : Submodule R (n → R)} (hC : ∀ x ∈ W, C *ᵥ x = 0)
    (hA : ∀ x ∈ W, A *ᵥ x ∈ W) : W ≤ unobservableSubspace A C := by
  intro x hx
  refine mem_unobservableSubspace.2 fun k => ?_
  induction k generalizing x with
  | zero => simpa using hC x hx
  | succ k ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ← mulVec_mulVec]
    exact ih (hA x hx)

/-- With no outputs, the unobservable subspace is the whole state space. -/
@[simp]
theorem unobservableSubspace_eq_top_of_isEmpty [IsEmpty p] : unobservableSubspace A C = ⊤ :=
  eq_top_iff.2 <| le_unobservableSubspace (fun _ _ => Subsingleton.elim _ _) fun _ _ => trivial

/-- With no states, every pair is observable. -/
@[simp]
theorem isObservable_of_isEmpty [IsEmpty n] : IsObservable A C :=
  (isObservable_iff A C).2 (Subsingleton.elim _ _)

/-- The powers `A ^ k` with `k < Fintype.card n` already determine the unobservable subspace. -/
theorem unobservableSubspace_eq_iInf_fin_card (A : Matrix n n R) (C : Matrix p n R) :
    unobservableSubspace A C =
      ⨅ k : Fin (Fintype.card n), LinearMap.ker (C * A ^ (k : ℕ)).mulVecLin := by
  refine le_antisymm (le_iInf fun k => unobservableSubspace_le_ker_mulVecLin_mul_pow (k : ℕ)) ?_
  intro x hx
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, mulVecLin_apply] at hx
  obtain ⟨c₁, c₂, hCH⟩ := exists_pow_card_add_sum_eq_sum A
  refine mem_unobservableSubspace.2 fun k => ?_
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < Fintype.card n
    · exact hx ⟨k, hk⟩
    · set d := k - Fintype.card n
      have hkd : Fintype.card n + d = k := Nat.add_sub_cancel' (Nat.le_of_not_lt hk)
      have hmul := congrArg (fun M => (C * M * A ^ d) *ᵥ x) hCH
      have hlt : ∀ j : Fin (Fintype.card n), (C * A ^ ((j : ℕ) + d)) *ᵥ x = 0 := fun j =>
        ih ((j : ℕ) + d) (by omega)
      simp only [Matrix.mul_add, Matrix.add_mul, add_mulVec, Matrix.mul_sum, Matrix.sum_mul,
        sum_mulVec, Matrix.mul_smul, Matrix.smul_mul, smul_mulVec, Matrix.mul_assoc, ← pow_add,
        hkd, hlt, smul_zero, Finset.sum_const_zero, add_zero] at hmul
      exact hmul

/-- The kernel of `(ctrbMatrix Aᵀ Cᵀ).vecMulLinear` is the unobservable subspace of `(A, C)`. -/
@[simp]
theorem ker_vecMulLinear_transpose_ctrbMatrix (A : Matrix n n R) (C : Matrix p n R) :
    LinearMap.ker (ctrbMatrix Aᵀ Cᵀ).vecMulLinear = unobservableSubspace A C := by
  rw [← mulVecLin_transpose]
  rw [unobservableSubspace_eq_iInf_fin_card]
  ext x
  simp only [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_iInf, funext_iff, Prod.forall,
    Pi.zero_apply, transpose_ctrbMatrix_mulVec]

end CommSemiring

section CommRing

variable [CommRing R] (A : Matrix n n R) (C : Matrix p n R)

/-- `(A, C)` is observable if and only if the first `Fintype.card n` outputs
`C * A ^ k * x` of the free discrete-time system determine the initial state `x`. -/
theorem isObservable_iff_injective :
    IsObservable A C ↔
      Function.Injective fun x : n → R => fun k : Fin (Fintype.card n) =>
        (C * A ^ (k : ℕ)) *ᵥ x := by
  rw [isObservable_iff, ← ker_vecMulLinear_transpose_ctrbMatrix, LinearMap.ker_eq_bot,
    ← mulVecLin_transpose]
  have hcomp :
      (fun x : n → R => fun k : Fin (Fintype.card n) => (C * A ^ (k : ℕ)) *ᵥ x) =
        Equiv.curry (Fin (Fintype.card n)) p R ∘ (ctrbMatrix Aᵀ Cᵀ)ᵀ.mulVecLin := by
    ext x k i
    exact (transpose_ctrbMatrix_mulVec A C x k i).symm
  rw [hcomp]
  exact ((Equiv.curry (Fin (Fintype.card n)) p R).injective.of_comp_iff _).symm

end CommRing

section Field

variable [Field K] [Fintype p] (A : Matrix n n K) (C : Matrix p n K)

/-- Duality: `(A, C)` is observable if and only if `(Aᵀ, Cᵀ)` is controllable. -/
theorem isObservable_iff_isControllable_transpose :
    IsObservable A C ↔ IsControllable Aᵀ Cᵀ := by
  have h := (ctrbMatrix Aᵀ Cᵀ)ᵀ.mulVecLin.finrank_range_add_finrank_ker
  rw [finrank_range_mulVecLin, rank_transpose, mulVecLin_transpose,
    ker_vecMulLinear_transpose_ctrbMatrix, finrank_fintype_fun_eq_card] at h
  rw [isObservable_iff, isControllable_iff_rank_ctrbMatrix, ← Submodule.finrank_eq_zero]
  omega

end Field

end Matrix
