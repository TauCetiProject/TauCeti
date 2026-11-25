/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Reversal of the volume element of a Clifford algebra

For a list `l` of vectors, the ordered Clifford product `(l.map (ι Q)).prod` is the volume element
studied in `TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Basic.lean`. This file proves the
two facts about it that need nothing beyond Mathlib: a vector orthogonal to every factor crosses
it at the cost of `(-1) ^ n`, and reversal multiplies it by `(-1) ^ (n.choose 2)` when the factors
are pairwise orthogonal. Keeping them here lets the exterior algebra, which is the Clifford algebra
of the zero form and where every pair of vectors is orthogonal, use them
(`ExteriorAlgebra.reverse_basis` in `TauCeti/LinearAlgebra/ExteriorAlgebra/Contraction.lean`)
without importing the rest of the Clifford-algebra theory.

## Main results

* `CliffordAlgebra.prod_map_ι_mul_ι_of_forall_isOrtho`: a vector orthogonal to every factor
  moves across the product at the cost of `(-1) ^ n`.
* `CliffordAlgebra.reverse_prod_map_ι_of_pairwise_isOrtho`: reversal multiplies the volume
  element of a pairwise orthogonal list by the sign `(-1) ^ (n.choose 2)`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

/-- **A vector orthogonal to every factor crosses the volume element at the cost of `(-1) ^ n`**,
`n` the number of factors: each transposition with a factor contributes one sign. -/
theorem prod_map_ι_mul_ι_of_forall_isOrtho {l : List M} {m : M}
    (h : ∀ x ∈ l, Q.IsOrtho x m) :
    (l.map (ι Q)).prod * ι Q m = ((-1 : R) ^ l.length) • (ι Q m * (l.map (ι Q)).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : Q.IsOrtho a m := h a List.mem_cons_self
    have hl : ∀ x ∈ l, Q.IsOrtho x m := fun x hx => h x (List.mem_cons_of_mem _ hx)
    calc ((a :: l).map (ι Q)).prod * ι Q m
        = ι Q a * ((l.map (ι Q)).prod * ι Q m) := by
          simp only [List.map_cons, List.prod_cons, mul_assoc]
      _ = ((-1 : R) ^ l.length) • (ι Q a * ι Q m * (l.map (ι Q)).prod) := by
          rw [ih hl, mul_smul_comm, mul_assoc]
      _ = ((-1 : R) ^ l.length) • -(ι Q m * ((a :: l).map (ι Q)).prod) := by
          simp only [List.map_cons, List.prod_cons]
          rw [ι_mul_ι_comm_of_isOrtho ha, neg_mul, mul_assoc]
      _ = ((-1 : R) ^ (a :: l).length) • (ι Q m * ((a :: l).map (ι Q)).prod) := by
          rw [smul_neg, List.length_cons, pow_succ, mul_neg_one, neg_smul]

/-- **Reversal multiplies the volume element of a pairwise orthogonal list by
`(-1) ^ (n.choose 2)`**, the same sign as in its square
(`CliffordAlgebra.prod_map_ι_sq_scalar` in `VolumeElement/Basic.lean`). In particular the
volume element is reverse-symmetric for `n ≡ 0, 1 (mod 4)` and reverse-antisymmetric for
`n ≡ 2, 3 (mod 4)`. -/
@[simp]
theorem reverse_prod_map_ι_of_pairwise_isOrtho {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    reverse (l.map (ι Q)).prod = ((-1 : R) ^ l.length.choose 2) • (l.map (ι Q)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ha, hl'⟩ := hl
    have hsym : ∀ x ∈ l, Q.IsOrtho x a := fun x hx => (ha x hx).symm
    have hchoose : (a :: l).length.choose 2 = l.length + l.length.choose 2 := by
      rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right]
    rw [List.map_cons, List.prod_cons, reverse.map_mul, reverse_ι, ih hl', smul_mul_assoc,
      prod_map_ι_mul_ι_of_forall_isOrtho hsym, smul_smul, hchoose, pow_add, mul_comm]

end CliffordAlgebra
