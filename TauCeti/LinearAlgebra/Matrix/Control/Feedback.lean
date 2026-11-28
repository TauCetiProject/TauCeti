/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Control.Reachable

/-!
# Invariance of the reachable subspace under feedback and coordinate changes

For a linear time-invariant control system with state matrix `A : Matrix n n R` and input matrix
`B : Matrix n m R`, the reachable subspace `Matrix.reachableSubspace A B` and controllability
`Matrix.IsControllable A B` are invariant under the feedback group:

* State feedback `u = F x`, replacing `A` by `A + B * F`, leaves the reachable subspace unchanged
  over any commutative ring (and never enlarges it over any commutative semiring).
* An invertible change of input coordinates `G`, replacing `B` by `B * G` (or more generally
  right-multiplying `B` by any matrix with surjective `mulVecLin`), leaves the reachable subspace
  unchanged over any commutative semiring.
* Any intertwining map `M` satisfying `A' * M = M * A` maps `Matrix.reachableSubspace A B` onto
  `Matrix.reachableSubspace A' (M * B)`; in particular, a change of state coordinates `P` maps the
  reachable subspace by `P.mulVecLin` and preserves controllability.

Combining the three actions shows that `(P (A + B F) P⁻¹, P B G)` is controllable if and only if
`(A, B)` is, over any commutative ring.

## Main results

* `Matrix.reachableSubspace_add_mul_le`: state feedback cannot enlarge the reachable subspace over
  a commutative semiring.
* `Matrix.reachableSubspace_mul_right_of_surjective`, `Matrix.reachableSubspace_mul_units`:
  right-multiplying `B` by a surjective matrix or a unit preserves the reachable subspace.
* `Matrix.reachableSubspace_mul_of_mul_eq`, `Matrix.reachableSubspace_units_conj`: equivariance of
  the reachable subspace under intertwining maps and changes of state coordinates.
* `Matrix.reachableSubspace_add_mul`: state feedback leaves the reachable subspace unchanged over
  a commutative ring.
* `Matrix.isControllable_units_conj_iff`: controllability is invariant under changes of state and
  input coordinates and state feedback.

## References

* Eduardo D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*,
  second edition, Springer, 1998: Lemma/Exercise 5.1.2 (p. 184) and Lemma/Exercise 5.1.8 (p. 185).
-/

public section

namespace Matrix

variable {R : Type*} {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

section CommSemiring

variable [CommSemiring R]

/-- Adding state feedback `B * F` cannot enlarge the reachable subspace. -/
theorem reachableSubspace_add_mul_le (A : Matrix n n R) (B : Matrix n m R) (F : Matrix m n R) :
    reachableSubspace (A + B * F) B ≤ reachableSubspace A B :=
  reachableSubspace_le (mulVec_mem_reachableSubspace (A := A) (B := B)) fun x hx => by
    rw [add_mulVec, ← mulVec_mulVec]
    exact add_mem (mulVec_mem_reachableSubspace_of_mem hx) (mulVec_mem_reachableSubspace _)

/-- Right-multiplying the input matrix `B` by any matrix `M` can only shrink the reachable
subspace. -/
theorem reachableSubspace_mul_right_le {m' : Type*} [Fintype m']
    (A : Matrix n n R) (B : Matrix n m R) (M : Matrix m m' R) :
    reachableSubspace A (B * M) ≤ reachableSubspace A B :=
  reachableSubspace_le
    (fun v => by rw [← mulVec_mulVec]; exact mulVec_mem_reachableSubspace _)
    fun _ => mulVec_mem_reachableSubspace_of_mem

/-- Right-multiplying the input matrix `B` by a matrix with surjective `mulVecLin` preserves the
reachable subspace. -/
theorem reachableSubspace_mul_right_of_surjective {m' : Type*} [Fintype m']
    (A : Matrix n n R) (B : Matrix n m R) {M : Matrix m m' R}
    (hM : Function.Surjective M.mulVecLin) :
    reachableSubspace A (B * M) = reachableSubspace A B :=
  le_antisymm (reachableSubspace_mul_right_le A B M) <|
    reachableSubspace_le (fun v => by
      obtain ⟨w, hw⟩ := hM v
      rw [← hw, mulVecLin_apply, mulVec_mulVec]
      exact mulVec_mem_reachableSubspace (A := A) (B := B * M) w)
      fun _ => mulVec_mem_reachableSubspace_of_mem

/-- An invertible change of input coordinates `G` preserves the reachable subspace.
The simplifier removes the input change before simplifying either matrix. -/
@[simp↓]
theorem reachableSubspace_mul_units [DecidableEq m] (A : Matrix n n R) (B : Matrix n m R)
    (G : (Matrix m m R)ˣ) :
    reachableSubspace A (B * (G : Matrix m m R)) = reachableSubspace A B :=
  reachableSubspace_mul_right_of_surjective A B fun v =>
    ⟨(↑G⁻¹ : Matrix m m R) *ᵥ v, by simp [mulVec_mulVec]⟩

/-- An invertible change of input coordinates `G` preserves controllability. -/
@[simp↓]
theorem isControllable_mul_units_iff [DecidableEq m] (A : Matrix n n R) (B : Matrix n m R)
    (G : (Matrix m m R)ˣ) :
    IsControllable A (B * (G : Matrix m m R)) ↔ IsControllable A B := by
  simp only [isControllable_iff, reachableSubspace_mul_units]

/-- If `M` intertwines `A` and `A'` (`A' * M = M * A`), then `M.mulVecLin` maps the reachable
subspace of `(A, B)` onto that of `(A', M * B)`. -/
theorem reachableSubspace_mul_of_mul_eq {n' : Type*} [Fintype n'] [DecidableEq n']
    {A : Matrix n n R} {A' : Matrix n' n' R} (B : Matrix n m R) {M : Matrix n' n R}
    (hMA : A' * M = M * A) :
    reachableSubspace A' (M * B) = (reachableSubspace A B).map M.mulVecLin := by
  refine le_antisymm ?_ ?_
  · refine reachableSubspace_le (fun v => ?_) ?_
    · rw [← mulVec_mulVec]
      exact Submodule.mem_map_of_mem (mulVec_mem_reachableSubspace v)
    · rintro _ ⟨x, hx, rfl⟩
      rw [mulVecLin_apply, mulVec_mulVec, hMA, ← mulVec_mulVec]
      exact Submodule.mem_map_of_mem (mulVec_mem_reachableSubspace_of_mem hx)
  · rw [Submodule.map_le_iff_le_comap]
    refine reachableSubspace_le (fun v => ?_) fun x hx => ?_
    · rw [Submodule.mem_comap, mulVecLin_apply, mulVec_mulVec]
      exact mulVec_mem_reachableSubspace v
    · rw [Submodule.mem_comap, mulVecLin_apply] at hx ⊢
      rw [mulVec_mulVec, ← hMA, ← mulVec_mulVec]
      exact mulVec_mem_reachableSubspace_of_mem hx

/-- If `M` intertwines `A` and `A'` (`A' * M = M * A`) and `M.mulVecLin` is bijective, then
`(A', M * B)` is controllable if and only if `(A, B)` is. -/
theorem isControllable_mul_of_mul_eq_iff {n' : Type*} [Fintype n'] [DecidableEq n']
    {A : Matrix n n R} {A' : Matrix n' n' R} (B : Matrix n m R) {M : Matrix n' n R}
    (hMA : A' * M = M * A) (hM : Function.Bijective M.mulVecLin) :
    IsControllable A' (M * B) ↔ IsControllable A B := by
  rw [isControllable_iff, isControllable_iff, reachableSubspace_mul_of_mul_eq B hMA]
  exact map_eq_top_iff (Submodule.orderIsoMapComapOfBijective M.mulVecLin hM)

/-- Under a change of state coordinates `P`, the reachable subspace transforms by
`P.mulVecLin`. The simplifier applies this before rewriting the coerced inverse. -/
@[simp↓]
theorem reachableSubspace_units_conj (A : Matrix n n R) (B : Matrix n m R)
    (P : (Matrix n n R)ˣ) :
    reachableSubspace ((P : Matrix n n R) * A * ((P⁻¹ : (Matrix n n R)ˣ) : Matrix n n R))
        ((P : Matrix n n R) * B) =
      (reachableSubspace A B).map (P : Matrix n n R).mulVecLin :=
  reachableSubspace_mul_of_mul_eq B (by simp [Matrix.mul_assoc])

/-- A change of state coordinates `P` preserves controllability. -/
@[simp↓]
theorem isControllable_units_conj_mul_iff (A : Matrix n n R) (B : Matrix n m R)
    (P : (Matrix n n R)ˣ) :
    IsControllable ((P : Matrix n n R) * A * ((P⁻¹ : (Matrix n n R)ˣ) : Matrix n n R))
        ((P : Matrix n n R) * B) ↔
      IsControllable A B :=
  isControllable_mul_of_mul_eq_iff B (by simp [Matrix.mul_assoc]) <|
    Function.bijective_iff_has_inverse.2
      ⟨((P⁻¹ : (Matrix n n R)ˣ) : Matrix n n R).mulVecLin,
        fun x => by simp [mulVec_mulVec], fun x => by simp [mulVec_mulVec]⟩

end CommSemiring

section CommRing

variable [CommRing R]

/-- State feedback does not change the reachable subspace:
`reachableSubspace (A + B * F) B = reachableSubspace A B` for every `F`. -/
@[simp]
theorem reachableSubspace_add_mul (A : Matrix n n R) (B : Matrix n m R) (F : Matrix m n R) :
    reachableSubspace (A + B * F) B = reachableSubspace A B :=
  le_antisymm (reachableSubspace_add_mul_le A B F) <| by
    simpa [Matrix.mul_neg, add_neg_cancel_right] using
      reachableSubspace_add_mul_le (A + B * F) B (-F)

/-- State feedback preserves controllability. -/
@[simp]
theorem isControllable_add_mul_iff (A : Matrix n n R) (B : Matrix n m R) (F : Matrix m n R) :
    IsControllable (A + B * F) B ↔ IsControllable A B := by
  simp only [isControllable_iff, reachableSubspace_add_mul]

/-- Under a change of state coordinates `P`, an invertible change of input coordinates `G` and
state feedback `F`, the reachable subspace transforms by `P.mulVecLin`. -/
theorem reachableSubspace_units_conj_add_mul [DecidableEq m] (A : Matrix n n R)
    (B : Matrix n m R) (P : (Matrix n n R)ˣ) (G : (Matrix m m R)ˣ) (F : Matrix m n R) :
    reachableSubspace
        ((P : Matrix n n R) * (A + B * F) * ((P⁻¹ : (Matrix n n R)ˣ) : Matrix n n R))
        ((P : Matrix n n R) * B * (G : Matrix m m R)) =
      (reachableSubspace A B).map (P : Matrix n n R).mulVecLin := by
  rw [reachableSubspace_mul_units, reachableSubspace_units_conj, reachableSubspace_add_mul]

/-- Controllability is invariant under a change of state coordinates `P`, an invertible change of
input coordinates `G` and state feedback `F`. -/
theorem isControllable_units_conj_iff [DecidableEq m] (A : Matrix n n R) (B : Matrix n m R)
    (P : (Matrix n n R)ˣ) (G : (Matrix m m R)ˣ) (F : Matrix m n R) :
    IsControllable
        ((P : Matrix n n R) * (A + B * F) * ((P⁻¹ : (Matrix n n R)ˣ) : Matrix n n R))
        ((P : Matrix n n R) * B * (G : Matrix m m R)) ↔
      IsControllable A B := by
  rw [isControllable_mul_units_iff, isControllable_units_conj_mul_iff, isControllable_add_mul_iff]

end CommRing

end Matrix
