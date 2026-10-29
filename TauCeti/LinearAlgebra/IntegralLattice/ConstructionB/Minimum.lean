/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Weight.Euclidean
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionB.Basic

/-!
# Short vectors of Construction B and of its odd shifted coset

Let `C` be a binary linear code with coordinates `ι`. This file proves the two elementary norm
bounds behind the absence of roots in the Construction B model of the Leech lattice. They are
stated for integer vectors, in the coordinates in which the congruence conditions are read off.

* **The Construction B vectors.** If every nonzero codeword of `C` has weight at least eight,
  then every nonzero integer vector `z` reducing into `C` modulo two, with `4 ∣ ∑ zᵢ`, satisfies
  `∑ zᵢ² ≥ 8`. If `z` reduces to a nonzero codeword, at least eight coordinates are odd. If it
  reduces to zero, then `z = 2w` with `∑ wᵢ` even. Since `wᵢ² ≡ wᵢ (mod 2)`, the positive
  integer `∑ wᵢ²` is even, so it is at least two.
* **The odd shifted coset.** If `C` is doubly even and `8 ∣ #ι`, then every vector
  `a = 2z + 𝟙` with `z` reducing into `C` modulo two and `∑ aᵢ ≡ 4 (mod 8)` satisfies
  `∑ aᵢ² ≥ #ι + 8`. Each `aᵢ² - 1 = 4 zᵢ (zᵢ + 1)` is a nonnegative multiple of eight. If all of
  them vanish, then every `aᵢ` is `±1`, and the coordinates equal to `-1` are the support of the
  reduction `c` of `z`. Then `∑ aᵢ = #ι - 2 wt(c) ≡ 0 (mod 8)`, since `4 ∣ wt(c)`. This
  contradicts the sum congruence.

In the Construction A form, the dot product halved, the first bound says that a nonzero vector of
the Construction B carrier has norm at least `4` (`four_le_form_self`).

## Main declarations

* `TauCeti.ConstructionB.eight_le_sum_sq`: the bound for Construction B vectors.
* `TauCeti.ConstructionB.four_le_form_self`: the same bound for the halved dot product.
* `TauCeti.ConstructionB.card_add_eight_le_sum_sq`: the bound for the odd shifted coset.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11, and
  Chapter 10, §1.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti.ConstructionB

open Finset

variable {ι : Type*} [Fintype ι] {C : LinearCode (ZMod 2) ι}

/-- **Construction B vectors are not short.** If every nonzero codeword of `C` has weight at least
eight, a nonzero integer vector reducing into `C` modulo two whose coordinate sum is divisible by
four has squared length at least eight. -/
theorem eight_le_sum_sq (hC : ∀ c ∈ C, c ≠ 0 → 8 ≤ hammingNorm c) {z : ι → ℤ}
    (hz : (fun i ↦ (z i : ZMod 2)) ∈ C) (hsum : 4 ∣ ∑ i, z i) (hne : z ≠ 0) :
    8 ≤ ∑ i, z i ^ 2 := by
  by_cases hc : (fun i ↦ (z i : ZMod 2)) = 0
  · -- Every coordinate is even: write `z = 2w`.
    have heven (i : ι) : (2 : ℤ) ∣ z i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hc i)
    choose w hw using heven
    have hsq : ∑ i, z i ^ 2 = 4 * ∑ i, w i ^ 2 := by
      simp_rw [hw, mul_pow, ← mul_sum]
      norm_num
    have hsumw : ∑ i, z i = 2 * ∑ i, w i := by
      simp_rw [hw, ← mul_sum]
    -- `∑ wᵢ²` and `∑ wᵢ` have the same parity.
    have hpar : (2 : ℤ) ∣ ∑ i, w i ^ 2 - ∑ i, w i := by
      rw [← sum_sub_distrib]
      refine dvd_sum fun i _ ↦ ?_
      rw [sq, ← mul_sub_one]
      exact even_iff_two_dvd.mp (Int.even_mul_pred_self (w i))
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra! h
      exact hne (funext fun i ↦ by rw [hw, h, mul_zero, Pi.zero_apply])
    have hpos : 0 < ∑ i, w i ^ 2 :=
      sum_pos' (fun i _ ↦ sq_nonneg (w i)) ⟨j, mem_univ j, sq_pos_of_ne_zero hj⟩
    omega
  · -- The reduction is a nonzero codeword, so it has at least eight odd coordinates.
    have hweight := hC _ hz hc
    have := hammingNorm_intCast_le_sum_sq z
    omega

/-- **Construction B vectors have norm at least four.** If every nonzero codeword of `C` has
weight at least eight, every nonzero vector of the Construction B carrier has Construction A norm,
the dot product halved, at least `4`. -/
theorem four_le_form_self (hC : ∀ c ∈ C, c ≠ 0 → 8 ≤ hammingNorm c) {x : ι → ℚ}
    (hx : x ∈ lattice C) (hne : x ≠ 0) : 4 ≤ ConstructionA.form 2 x x := by
  obtain ⟨z, -, rfl⟩ := (ConstructionA.mem_lattice 2).mp (lattice_le C hx)
  rw [intCast_mem_lattice] at hx
  have hz : z ≠ 0 := by
    rintro rfl
    exact hne (funext fun i ↦ by simp)
  have h8 : ((8 : ℤ) : ℚ) ≤ ((∑ i, z i ^ 2 : ℤ) : ℚ) := by
    exact_mod_cast eight_le_sum_sq hC hx.1 hx.2 hz
  rw [ConstructionA.form_apply, dotProduct]
  push_cast at h8 ⊢
  simp_rw [← sq]
  linarith

/-- **The odd shifted coset of Construction B is not short.** If `C` is doubly even and the
length is divisible by eight, every odd vector `a = 2z + 𝟙` with `z` reducing into `C` modulo two
and `∑ aᵢ ≡ 4 (mod 8)` has squared length at least the length plus eight. -/
theorem card_add_eight_le_sum_sq (hC : BinaryCode.IsDoublyEven C) (hι : 8 ∣ Fintype.card ι)
    {z : ι → ℤ} (hz : (fun i ↦ (z i : ZMod 2)) ∈ C)
    (hsum : ∑ i, (2 * z i + 1) ≡ 4 [ZMOD 8]) :
    (Fintype.card ι : ℤ) + 8 ≤ ∑ i, (2 * z i + 1) ^ 2 := by
  have hsq : ∑ i, (2 * z i + 1) ^ 2 = Fintype.card ι + 4 * ∑ i, z i * (z i + 1) := by
    have h (i : ι) : (2 * z i + 1) ^ 2 = 1 + 4 * (z i * (z i + 1)) := by ring
    simp_rw [h, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one]
  have hnonneg (i : ι) : 0 ≤ z i * (z i + 1) := by
    rcases le_or_gt 0 (z i) with h | h <;> nlinarith
  have hpar : (2 : ℤ) ∣ ∑ i, z i * (z i + 1) :=
    dvd_sum fun i _ ↦ even_iff_two_dvd.mp (Int.even_mul_succ_self (z i))
  rcases (sum_nonneg fun i (_ : i ∈ univ) ↦ hnonneg i).lt_or_eq with hpos | hzero
  · omega
  · -- Otherwise every coordinate of `z` is `0` or `-1`, so every coordinate of `a` is `±1`.
    exfalso
    have hz01 (i : ι) : z i = -((z i : ZMod 2).val : ℤ) := by
      have hi := (sum_eq_zero_iff_of_nonneg fun i (_ : i ∈ univ) ↦ hnonneg i).mp hzero.symm i
        (mem_univ i)
      rcases mul_eq_zero.mp hi with h | h
      · rw [h]
        decide
      · rw [show z i = -1 by omega]
        decide
    have hsumz : ∑ i, z i = -(hammingNorm (fun i ↦ (z i : ZMod 2)) : ℤ) := by
      rw [← sum_val_eq_hammingNorm, Nat.cast_sum, ← sum_neg_distrib]
      exact sum_congr rfl fun i _ ↦ hz01 i
    obtain ⟨t, ht⟩ := BinaryCode.isDoublyEven_iff.mp hC _ hz
    obtain ⟨u, hu⟩ := hι
    rw [sum_add_distrib, ← mul_sum, hsumz, ht, sum_const, card_univ, hu] at hsum
    simp only [Int.ModEq, nsmul_eq_mul, mul_one] at hsum
    push_cast at hsum
    omega

end TauCeti.ConstructionB
