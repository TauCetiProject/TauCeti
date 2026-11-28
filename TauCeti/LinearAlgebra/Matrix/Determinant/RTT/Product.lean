/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.RTT.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NoncommRing

/-!
# Products of RTT families

Pointwise matrix multiplication preserves the rational RTT exchange relation when the two
families commute entrywise with one another, at independent spectral parameters. In size two
the quantum determinant of the product is the product of quantum determinants. This second
identity only needs the first family to satisfy RTT: it is the adjacent-parameter
Cauchy–Binet identity, with the repeated intermediate columns contributing zero.

These are the matrix-product and quantum-determinant identities underlying the Yangian
coproduct; see A. Molev, M. Nazarov and G. Olshanski, *Yangians and classical Lie algebras*, §2.
-/

public section

namespace TauCeti

variable {K A ι : Type*} [CommRing K] [Ring A] [Algebra K A]

/-- The pointwise matrix product of two RTT families is RTT if every entry of the first
family commutes with every entry of the second, at independent parameters. -/
theorem IsRTT.mul [Fintype ι] {a b : K → Matrix ι ι A} (ha : IsRTT a) (hb : IsRTT b)
    (hab : ∀ u v i j k l, Commute (a u i j) (b v k l)) : IsRTT (fun u ↦ a u * b u) := by
  refine isRTT_iff.mpr fun u v i j k l ↦ ?_
  -- Group the two entries of each family before applying its exchange relation.
  have hmove (x y : K) (i j k l : ι) (z w : A) :=
    (hab y x k l i j).symm.mul_mul_mul_comm z w
  simp only [Matrix.mul_apply, Fintype.sum_mul_sum, hmove, smul_sub, Finset.smul_sum]
  rw [Finset.sum_comm (f := fun p q : ι ↦ (u - v) • ((a v k p * a u i q) * (b v p l * b u q j)))]
  simp only [← Finset.sum_sub_distrib]
  calc
    _ = ∑ p, ∑ q,
        (((a u k p * a v i q) * (b u p j * b v q l) -
          (a v k p * a u i q) * (b u p j * b v q l)) +
        ((a v k q * a u i p) * (b u q j * b v p l) -
          (a v k q * a u i p) * (b v q j * b u p l))) := by
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
      rw [← smul_sub]
      calc
        _ = ((u - v) • (a u i p * a v k q - a v k q * a u i p)) * (b u p j * b v q l) +
            (a v k q * a u i p) * ((u - v) • (b u p j * b v q l - b v q l * b u p j)) := by
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_add]
          congr 1
          noncomm_ring
        _ = _ := by
          rw [isRTT_iff.mp ha u v i p k q, isRTT_iff.mp hb u v p j q l, sub_mul, mul_sub]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun p q : ι ↦ (a v k q * a u i p) * (b u q j * b v p l)),
        Finset.sum_comm (f := fun p q : ι ↦ (a v k q * a u i p) * (b v q j * b u p l))]
      abel

/-- Adjacent-parameter Cauchy–Binet in size two: the quantum determinant is multiplicative
if the first family satisfies RTT and its unshifted entries commute with the shifted entries
of the second family. No exchange relation on the second family is needed. -/
theorem IsRTT.quantumDetTwo_mul {a b : K → Matrix (Fin 2) (Fin 2) A} (ha : IsRTT a) (v : K)
    (hab : ∀ i j k l, Commute (a v i j) (b (v + 1) k l)) :
    quantumDetTwo (fun u ↦ a u * b u) v = quantumDetTwo a v * quantumDetTwo b v := by
  have hmove (i j k l : Fin 2) (z w : A) := (hab k l i j).symm.mul_mul_mul_comm z w
  simp only [quantumDetTwo_def, Matrix.mul_apply, Fintype.sum_mul_sum, hmove,
    ← Finset.sum_sub_distrib, ← sub_mul]
  have h₀ := ha.mul_adjacent_same_col v 0 1 0
  have h₁ := ha.mul_adjacent_same_col v 0 1 1
  have hswap := ha.minor_eq_neg_swap_cols v 0 1 1 0
  -- Cancel the equal-column terms and move the column-swap sign into the second minor.
  simp only [Fin.sum_univ_two, h₀, h₁, sub_self, hswap, zero_mul, zero_add, add_zero, neg_mul]
  noncomm_ring

end TauCeti
