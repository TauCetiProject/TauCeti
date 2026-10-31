/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Minimum
import TauCeti.Data.Finset.Basic

/-!
# The minimal vectors of the Leech lattice

The Leech lattice `Λ ⊆ ℚ^(Fin 24)` has minimum `4`. This file lists all of its vectors of norm `4`
and counts them. In the congruence coordinates `x = a / 2` of
`TauCeti.mem_leechLattice_carrier_iff_exists`, where the norm is `∑ aᵢ² / 8`, a minimal vector
is an integer vector `a` with `∑ aᵢ² = 32`, and there are three exhaustive, pairwise disjoint
families of them:

* `TauCeti.leechPairVector`: two coordinates `±4`, the others `0`. There are
  `(24 choose 2) · 2² = 1104` of them.
* `TauCeti.leechOctadVector`: the coordinates `±2` on an octad, a Golay codeword of weight eight,
  with an even number of minus signs, and `0` off it. There are `759 · 2⁷ = 97152` of them.
* `TauCeti.leechOddVector`: one coordinate `±3` and the others `±1`. Such a vector is determined
  by an arbitrary Golay codeword `c` and the distinguished coordinate `j`: off `j`, the
  coordinate is `-1` on the support of `c` and `1` off it, while the coordinate at `j` is `3` if
  `j` lies in the support and `-3` otherwise. There are `4096 · 24 = 98304` of them.

Together the Leech lattice has `1104 + 97152 + 98304 = 196560` minimal vectors, which is its
kissing number.

The classification reads the congruence model coordinatewise. A vector `a = 2b` of the even class
has `∑ bᵢ² = 8`. If `b` reduces to the zero codeword then `b = 2w` with `∑ wᵢ² = 2`, giving the
first family. Otherwise `b` reduces to a codeword of weight at least eight, each of whose odd
coordinates contributes at least one to `∑ bᵢ²`; equality forces the codeword to be an octad
and `b` to be `±1` on it and `0` off it, and the sum congruence becomes the parity of the minus
signs. A vector `a = 2b + 𝟙` of the odd class has `∑ (aᵢ² - 1) = 8` with every
`aᵢ² - 1 = 4 bᵢ (bᵢ + 1)` divisible by eight, so exactly one coordinate is `±3`. Here the sum
congruence holds automatically, because Golay weights are divisible by four. The counts use the
`759` octads and `4096` codewords of the Golay code, from
`TauCeti.BinaryGolay.weightDistribution_code` and `TauCeti.BinaryGolay.natCard_code`.

## Main definitions

* `TauCeti.leechPairVector`, `TauCeti.leechOctadVector`, `TauCeti.leechOddVector`: the three
  shapes of minimal vectors, in congruence coordinates.
* `TauCeti.leechPairVectors`, `TauCeti.leechOctadVectors`, `TauCeti.leechOddVectors`: the three
  families, as sets of integer vectors.

## Main results

* `TauCeti.intCast_div_two_mem_leechLattice_carrier_and_sum_sq_eq_iff`: the classification of the
  minimal vectors in congruence coordinates.
* `TauCeti.mem_vectorsOfNorm_four_leechLattice_iff`: the same classification for vectors of the
  lattice.
* `TauCeti.ncard_leechPairVectors`, `TauCeti.ncard_leechOctadVectors`,
  `TauCeti.ncard_leechOddVectors`: the three counts `1104`, `97152` and `98304`.
* `TauCeti.ncard_vectorsOfNorm_four_leechLattice` and `TauCeti.kissingNumber_leechLattice`: the
  Leech lattice has `196560` minimal vectors.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

open Finset

namespace TauCeti

open BinaryGolay IntegralLattice

/-! ### The three shapes -/

/-- **The first shape of Leech minimal vectors**, in congruence coordinates: the integer vector
equal to `4s` at `i`, to `4t` at `j` (unless `j = i`) and to `0` elsewhere, for signs
`s t : ℤˣ`. For `i ≠ j`, halved, it is the Leech lattice vector `2s eᵢ + 2t eⱼ` of norm `4`
(`TauCeti.leechPairVector_mem`). -/
def leechPairVector (i j : Fin 24) (s t : ℤˣ) : Fin 24 → ℤ :=
  fun k ↦ if k = i then 4 * (s : ℤ) else if k = j then 4 * (t : ℤ) else 0

/-- The coordinates of a vector of the first shape. -/
@[simp]
theorem leechPairVector_apply (i j : Fin 24) (s t : ℤˣ) (k : Fin 24) :
    leechPairVector i j s t k = if k = i then 4 * (s : ℤ) else if k = j then 4 * (t : ℤ) else 0 :=
  (rfl)

/-- **The second shape of Leech minimal vectors**, in congruence coordinates: for binary words
`c` and `d`, the integer vector equal to `2` where `c` is `1` and `d` is `0`, to `-2` where both
are `1`, and to `0` where `c` is `0`. For `c` an octad and `d` an even subword of `c`, this is the
vector `±2` on the octad with minus signs on `d`. -/
def leechOctadVector (c d : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun k ↦ 2 * (c k).val * (1 - 2 * (d k).val)

/-- The coordinates of a vector of the second shape. -/
@[simp]
theorem leechOctadVector_apply (c d : Fin 24 → ZMod 2) (k : Fin 24) :
    leechOctadVector c d k = 2 * (c k).val * (1 - 2 * (d k).val) :=
  (rfl)

/-- **The third shape of Leech minimal vectors**, in congruence coordinates: for a binary word `c`
and a coordinate `j`, the integer vector whose coordinate `k ≠ j` is `-1` where `c` is `1` and
`1` where `c` is `0`, and whose coordinate `j` is `3` where `c` is `1` and `-3` where `c` is
`0`. For `c` a Golay codeword, halved, it is a Leech lattice vector of norm `4`
(`TauCeti.leechOddVector_mem`). -/
def leechOddVector (c : Fin 24 → ZMod 2) (j : Fin 24) : Fin 24 → ℤ :=
  fun k ↦ (if k = j then -3 else 1) * (1 - 2 * (c k).val)

/-- The coordinates of a vector of the third shape. -/
@[simp]
theorem leechOddVector_apply (c : Fin 24 → ZMod 2) (j k : Fin 24) :
    leechOddVector c j k = (if k = j then -3 else 1) * (1 - 2 * (c k).val) :=
  (rfl)

/-- The Leech minimal vectors of the first shape, `(±4², 0²²)`, in congruence coordinates. -/
def leechPairVectors : Set (Fin 24 → ℤ) :=
  {a | ∃ i j, i < j ∧ ∃ s t, leechPairVector i j s t = a}

/-- The Leech minimal vectors of the second shape, `(±2⁸, 0¹⁶)` on an octad with an even number
of minus signs, in congruence coordinates. -/
def leechOctadVectors : Set (Fin 24 → ℤ) :=
  {a | ∃ c ∈ code, hammingNorm c = 8 ∧ ∃ d : Fin 24 → ZMod 2, (∀ k, c k = 0 → d k = 0) ∧
    Even (hammingNorm d) ∧ leechOctadVector c d = a}

/-- The Leech minimal vectors of the third shape, `(∓3, ±1²³)`, in congruence coordinates. -/
def leechOddVectors : Set (Fin 24 → ℤ) :=
  {a | ∃ c ∈ code, ∃ j, leechOddVector c j = a}

/-- Membership in the first family. -/
@[simp]
theorem mem_leechPairVectors {a : Fin 24 → ℤ} :
    a ∈ leechPairVectors ↔ ∃ i j, i < j ∧ ∃ s t, leechPairVector i j s t = a :=
  Iff.rfl

/-- Membership in the second family. -/
@[simp]
theorem mem_leechOctadVectors {a : Fin 24 → ℤ} :
    a ∈ leechOctadVectors ↔ ∃ c ∈ code, hammingNorm c = 8 ∧ ∃ d : Fin 24 → ZMod 2,
      (∀ k, c k = 0 → d k = 0) ∧ Even (hammingNorm d) ∧ leechOctadVector c d = a :=
  Iff.rfl

/-- Membership in the third family. -/
@[simp]
theorem mem_leechOddVectors {a : Fin 24 → ℤ} :
    a ∈ leechOddVectors ↔ ∃ c ∈ code, ∃ j, leechOddVector c j = a :=
  Iff.rfl

/-! ### The three shapes are minimal vectors -/

/-- An even vector `2b`, with `b` reducing to a Golay codeword and `∑ 2bᵢ ≡ 0 (mod 8)`, halves
into the Leech lattice. -/
private theorem two_mul_mem {b : Fin 24 → ℤ} (hb : (fun i ↦ (b i : ZMod 2)) ∈ code)
    (hsum : ∑ i, 2 * b i ≡ 0 [ZMOD 8]) :
    (fun i ↦ ((2 * b i : ℤ) : ℚ) / 2) ∈ leechLattice.carrier :=
  (mem_leechLattice_carrier_iff_exists _).2
    ⟨0, Or.inl rfl, b, hb, by simpa using hsum, by simp⟩

/-- An odd vector `2b + 𝟙`, with `b` reducing to a Golay codeword and `∑ (2bᵢ + 1) ≡ 4 (mod 8)`,
halves into the Leech lattice. -/
private theorem two_mul_add_one_mem {b : Fin 24 → ℤ} (hb : (fun i ↦ (b i : ZMod 2)) ∈ code)
    (hsum : ∑ i, (2 * b i + 1) ≡ 4 [ZMOD 8]) :
    (fun i ↦ ((2 * b i + 1 : ℤ) : ℚ) / 2) ∈ leechLattice.carrier :=
  (mem_leechLattice_carrier_iff_exists _).2 ⟨1, Or.inr rfl, b, hb, by simpa using hsum, rfl⟩

/-- A vector of the first shape, with `i ≠ j`, halves into the Leech lattice and has
`∑ aᵢ² = 32`. -/
theorem leechPairVector_mem {i j : Fin 24} (hij : i ≠ j) (s t : ℤˣ) :
    (fun k ↦ (leechPairVector i j s t k : ℚ) / 2) ∈ leechLattice.carrier ∧
      ∑ k, leechPairVector i j s t k ^ 2 = 32 := by
  set b : Fin 24 → ℤ := fun k ↦ if k = i then 2 * (s : ℤ) else if k = j then 2 * (t : ℤ) else 0
  have hab : leechPairVector i j s t = fun k ↦ 2 * b k := by
    funext k
    simp only [leechPairVector_apply, b]
    split_ifs <;> ring
  have hb : (fun k ↦ (b k : ZMod 2)) = 0 := by
    funext k
    simp only [b, Pi.zero_apply]
    split_ifs <;> push_cast <;> simp [show (2 : ZMod 2) = 0 from rfl]
  have hzero : ∀ k, k ≠ i ∧ k ≠ j → leechPairVector i j s t k = 0 := fun k hk ↦ by
    simp [leechPairVector_apply, hk.1, hk.2]
  have hsum : ∑ k, leechPairVector i j s t k = 4 * s + 4 * t := by
    rw [Fintype.sum_eq_add i j hij hzero]
    simp [leechPairVector_apply, hij.symm]
  have hsq : ∑ k, leechPairVector i j s t k ^ 2 = 32 := by
    rw [Fintype.sum_eq_add i j hij fun k hk ↦ by rw [hzero k hk]; ring]
    simp only [leechPairVector_apply, hij.symm, ↓reduceIte, mul_pow, ← Units.val_pow_eq_pow_val,
      Int.units_sq, Units.val_one]
    norm_num
  refine ⟨?_, hsq⟩
  rw [hab]
  refine two_mul_mem (hb ▸ zero_mem _) ?_
  rw [← hab, hsum]
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    decide

/-- A vector of the second shape, on an octad `c` with signs `d` of even weight inside it,
halves into the Leech lattice and has `∑ aᵢ² = 32`. -/
theorem leechOctadVector_mem {c d : Fin 24 → ZMod 2} (hc : c ∈ code)
    (hc8 : hammingNorm c = 8) (hdc : ∀ k, c k = 0 → d k = 0) (hd : Even (hammingNorm d)) :
    (fun k ↦ (leechOctadVector c d k : ℚ) / 2) ∈ leechLattice.carrier ∧
      ∑ k, leechOctadVector c d k ^ 2 = 32 := by
  set b : Fin 24 → ℤ := fun k ↦ (c k).val * (1 - 2 * (d k).val)
  have hab : leechOctadVector c d = fun k ↦ 2 * b k := by
    funext k
    simp only [leechOctadVector_apply, b]
    ring
  -- Coordinatewise: `b` reduces to `c`, `bₖ = cₖ - 2dₖ`, and `(2bₖ)² = 4cₖ`.
  have hcoord : ∀ k, ((b k : ZMod 2) = c k ∧ b k = ((c k).val : ℤ) - 2 * ((d k).val : ℤ)) ∧
      (2 * b k) ^ 2 = 4 * ((c k).val : ℤ) := by
    intro k
    simp only [b]
    rcases eq_zero_or_one_of_sq_eq_self (ZMod.pow_card (c k)) with h | h
    · rw [h, hdc k h]
      decide
    · rcases eq_zero_or_one_of_sq_eq_self (ZMod.pow_card (d k)) with h' | h' <;> rw [h, h'] <;>
        decide
  have hred : (fun k ↦ (b k : ZMod 2)) = c := funext fun k ↦ (hcoord k).1.1
  have hsum : ∑ k, b k = 8 - 2 * (hammingNorm d : ℤ) := by
    simp only [fun k ↦ (hcoord k).1.2, sum_sub_distrib, ← mul_sum, ← Nat.cast_sum,
      sum_val_eq_hammingNorm, hc8]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [hab]
    refine two_mul_mem (hred ▸ hc) ?_
    obtain ⟨r, hr⟩ := hd
    rw [← mul_sum, hsum, hr, Int.ModEq]
    push_cast
    omega
  · simp only [hab, fun k ↦ (hcoord k).2, ← mul_sum, ← Nat.cast_sum, sum_val_eq_hammingNorm, hc8]
    norm_num

/-- A vector of the third shape, attached to a Golay codeword `c` and a coordinate `j`, halves
into the Leech lattice and has `∑ aᵢ² = 32`. -/
theorem leechOddVector_mem {c : Fin 24 → ZMod 2} (hc : c ∈ code) (j : Fin 24) :
    (fun k ↦ (leechOddVector c j k : ℚ) / 2) ∈ leechLattice.carrier ∧
      ∑ k, leechOddVector c j k ^ 2 = 32 := by
  set b : Fin 24 → ℤ := fun k ↦ if k = j then -2 + 3 * ((c k).val : ℤ) else -((c k).val : ℤ)
  -- Coordinatewise: `aₖ = 2bₖ + 1`, `b` reduces to `c`, `aₖ` is `1 - 2cₖ` plus a correction at
  -- `j`, and `aₖ² = 1` off `j` and `9` at `j`.
  have hcoord : ∀ k, (leechOddVector c j k = 2 * b k + 1 ∧ (b k : ZMod 2) = c k) ∧
      (leechOddVector c j k =
        1 - 2 * ((c k).val : ℤ) + if k = j then -4 + 8 * ((c k).val : ℤ) else 0) ∧
      leechOddVector c j k ^ 2 = 1 + if k = j then 8 else 0 := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp only [leechOddVector_apply, b, ↓reduceIte]
      generalize c k = x
      revert x
      decide
    · simp only [leechOddVector_apply, b, hk, ↓reduceIte]
      generalize c k = x
      revert x
      decide
  have hab : leechOddVector c j = fun k ↦ 2 * b k + 1 := funext fun k ↦ (hcoord k).1.1
  have hred : (fun k ↦ (b k : ZMod 2)) = c := funext fun k ↦ (hcoord k).1.2
  refine ⟨?_, ?_⟩
  · rw [hab]
    refine two_mul_add_one_mem (hred ▸ hc) ?_
    rw [← hab]
    simp only [fun k ↦ (hcoord k).2.1, sum_add_distrib, sum_sub_distrib, ← mul_sum,
      ← Nat.cast_sum, sum_val_eq_hammingNorm, sum_ite_eq', mem_univ, ite_true, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    obtain ⟨r, hr⟩ := BinaryCode.isDoublyEven_iff.mp isDoublyEven_code c hc
    rw [hr, Int.ModEq]
    have := (c j).val_lt
    push_cast
    omega
  · simp only [fun k ↦ (hcoord k).2.2, sum_add_distrib, sum_ite_eq', mem_univ, ite_true,
      sum_const, card_univ, Fintype.card_fin]
    norm_num

/-! ### Every minimal vector has one of the three shapes -/

/-- **The even class with zero reduction**: if `b = 2w` has `∑ bᵢ² = 8`, then `2b` is a vector of
the first shape. -/
private theorem two_mul_mem_leechPairVectors {b : Fin 24 → ℤ}
    (hc : (fun i ↦ (b i : ZMod 2)) = 0) (hsq : ∑ i, b i ^ 2 = 8) :
    (fun i ↦ 2 * b i) ∈ leechPairVectors := by
  choose w hw using fun i ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (congrFun hc i)
  have hw2 : ∑ i, w i ^ 2 = 2 := by
    simp_rw [hw, mul_pow, ← mul_sum] at hsq
    omega
  have hnonneg : ∀ i ∈ (univ : Finset (Fin 24)), 0 ≤ w i ^ 2 := fun i _ ↦ sq_nonneg _
  -- A first nonzero coordinate `i`, which is a sign.
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := fun i ↦ w i ^ 2)
    (by rw [hw2]; norm_num)
  have hi0 : w i ≠ 0 := fun h ↦ hi (by rw [h]; ring)
  have hile : w i ^ 2 ≤ 2 := hw2 ▸ single_le_sum hnonneg (mem_univ i)
  obtain ⟨s, hs⟩ := Int.isUnit_iff.2 <|
    sq_eq_one_iff.1 (Int.sq_eq_one_of_sq_le_three (by linarith) hi0)
  have hrest : ∑ k ∈ univ.erase i, w k ^ 2 = 1 := by
    have := add_sum_erase univ (fun k ↦ w k ^ 2) (mem_univ i)
    rw [hw2, ← hs, ← Units.val_pow_eq_pow_val, Int.units_sq] at this
    push_cast at this
    omega
  -- A second nonzero coordinate `j`, which is a sign.
  obtain ⟨j, hj, hj'⟩ := exists_ne_zero_of_sum_ne_zero (s := univ.erase i)
    (f := fun k ↦ w k ^ 2) (by rw [hrest]; norm_num)
  have hj0 : w j ≠ 0 := fun h ↦ hj' (by rw [h]; ring)
  have hjle : w j ^ 2 ≤ 1 := hrest ▸ single_le_sum (fun k _ ↦ sq_nonneg (w k)) hj
  obtain ⟨t, ht⟩ := Int.isUnit_iff.2 <|
    sq_eq_one_iff.1 (Int.sq_eq_one_of_sq_le_three (by linarith) hj0)
  have hji : j ≠ i := ne_of_mem_erase hj
  have hrest' : ∑ k ∈ (univ.erase i).erase j, w k ^ 2 = 0 := by
    have := add_sum_erase (univ.erase i) (fun k ↦ w k ^ 2) hj
    rw [hrest, ← ht, ← Units.val_pow_eq_pow_val, Int.units_sq] at this
    push_cast at this
    omega
  -- Every other coordinate vanishes.
  have hzero : ∀ k, k ≠ i → k ≠ j → w k = 0 := fun k hki hkj ↦
    pow_eq_zero_iff (n := 2) two_ne_zero |>.mp <|
      (sum_eq_zero_iff_of_nonneg fun k _ ↦ sq_nonneg (w k)).mp hrest' k
        (mem_erase.2 ⟨hkj, mem_erase.2 ⟨hki, mem_univ k⟩⟩)
  have hval : ∀ k, 2 * b k = leechPairVector i j s t k := fun k ↦ by
    rw [leechPairVector_apply, hw]
    split_ifs with hki hkj
    · rw [hki, hs]
      ring
    · rw [hkj, ht]
      ring
    · rw [hzero k hki hkj]
      ring
  rcases lt_or_gt_of_ne hji with hlt | hlt
  · refine ⟨j, i, hlt, t, s, funext fun k ↦ ?_⟩
    rw [hval k, leechPairVector_apply, leechPairVector_apply]
    split_ifs <;> simp_all
  · exact ⟨i, j, hlt, s, t, funext fun k ↦ (hval k).symm⟩

/-- **The even class with nonzero reduction**: if `b` reduces to a nonzero Golay codeword, has
`∑ bᵢ² = 8`, and `∑ 2bᵢ ≡ 0 (mod 8)`, then `2b` is a vector of the second shape. -/
private theorem two_mul_mem_leechOctadVectors {b : Fin 24 → ℤ}
    (hb : (fun i ↦ (b i : ZMod 2)) ∈ code) (hc : (fun i ↦ (b i : ZMod 2)) ≠ 0)
    (hsq : ∑ i, b i ^ 2 = 8) (hsum : ∑ i, 2 * b i ≡ 0 [ZMOD 8]) :
    (fun i ↦ 2 * b i) ∈ leechOctadVectors := by
  set c : Fin 24 → ZMod 2 := fun i ↦ (b i : ZMod 2)
  have h8 := eight_le_hammingNorm hb hc
  -- Each odd coordinate contributes at least one to `∑ bᵢ² = 8`, and there are at least eight of
  -- them, so each contributes exactly one and the even coordinates vanish.
  have hle : ∀ k ∈ (univ : Finset (Fin 24)), 0 ≤ b k ^ 2 - if c k ≠ 0 then (1 : ℤ) else 0 := by
    intro k _
    split_ifs with h
    · have : b k ≠ 0 := fun h' ↦ h (by simp [c, h'])
      have := sq_pos_of_ne_zero this
      omega
    · simpa using sq_nonneg (b k)
  have hwt : ∑ k, (if c k ≠ 0 then (1 : ℤ) else 0) = hammingNorm c := by
    simp only [sum_boole, hammingNorm]
  have hsum0 : ∑ k, (b k ^ 2 - if c k ≠ 0 then (1 : ℤ) else 0) = 8 - (hammingNorm c : ℤ) := by
    rw [sum_sub_distrib, hsq, hwt]
  have hc8 : hammingNorm c = 8 := by
    have := sum_nonneg hle
    omega
  have hsq1 : ∀ k, b k ^ 2 = if c k ≠ 0 then 1 else 0 := fun k ↦ by
    have := (sum_eq_zero_iff_of_nonneg hle).mp (by rw [hsum0, hc8]; norm_num) k (mem_univ k)
    omega
  -- The signs: `dₖ = 1` exactly where `bₖ = -1`.
  set d : Fin 24 → ZMod 2 := fun k ↦ if b k = -1 then 1 else 0
  have hcoord : ∀ k, (c k = 0 → d k = 0) ∧ leechOctadVector c d k = 2 * b k ∧
      b k = ((c k).val : ℤ) - 2 * ((d k).val : ℤ) := by
    intro k
    have hk := hsq1 k
    simp only [leechOctadVector_apply, c, d] at hk ⊢
    split_ifs at hk with h
    · rcases sq_eq_one_iff.mp hk with h' | h' <;> rw [h'] <;> decide
    · have h' : b k = 0 := pow_eq_zero_iff two_ne_zero |>.mp hk
      rw [h']
      decide
  have hdsum : ∑ k, b k = 8 - 2 * (hammingNorm d : ℤ) := by
    simp only [fun k ↦ (hcoord k).2.2, sum_sub_distrib, ← mul_sum, ← Nat.cast_sum,
      sum_val_eq_hammingNorm, hc8]
    push_cast
    ring
  refine ⟨c, hb, hc8, d, fun k ↦ (hcoord k).1, ?_, funext fun k ↦ (hcoord k).2.1⟩
  rw [← mul_sum, hdsum, Int.ModEq] at hsum
  rw [Nat.even_iff]
  omega

/-- **The odd class**: if `b` reduces to a Golay codeword and `∑ (2bᵢ + 1)² = 32`, then `2b + 𝟙`
is a vector of the third shape. -/
private theorem two_mul_add_one_mem_leechOddVectors {b : Fin 24 → ℤ}
    (hb : (fun i ↦ (b i : ZMod 2)) ∈ code) (hsq : ∑ i, (2 * b i + 1) ^ 2 = 32) :
    (fun i ↦ 2 * b i + 1) ∈ leechOddVectors := by
  -- With `tₖ = bₖ (bₖ + 1) ≥ 0`, even, `(2bₖ + 1)² = 1 + 4tₖ`, so `∑ tₖ = 2`.
  have hnonneg : ∀ k ∈ (univ : Finset (Fin 24)), 0 ≤ b k * (b k + 1) := fun k _ ↦ by
    rcases le_or_gt 0 (b k) with h | h <;> nlinarith
  have ht : ∑ k, b k * (b k + 1) = 2 := by
    have h (k : Fin 24) : (2 * b k + 1) ^ 2 = 1 + 4 * (b k * (b k + 1)) := by ring
    simp_rw [h, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin] at hsq
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hsq
    omega
  obtain ⟨j, -, hj⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := fun k ↦ b k * (b k + 1))
    (by rw [ht]; norm_num)
  have hjeven : Even (b j * (b j + 1)) := Int.even_mul_succ_self (b j)
  have hjle : b j * (b j + 1) ≤ 2 := ht ▸ single_le_sum hnonneg (mem_univ j)
  have hj2 : b j * (b j + 1) = 2 := by
    have := hnonneg j (mem_univ j)
    obtain ⟨r, hr⟩ := hjeven
    omega
  have hrest : ∑ k ∈ univ.erase j, b k * (b k + 1) = 0 := by
    have := add_sum_erase univ (fun k ↦ b k * (b k + 1)) (mem_univ j)
    omega
  -- Off `j`, `bₖ ∈ {0, -1}`; at `j`, `bⱼ ∈ {1, -2}`.
  have hoff : ∀ k, k ≠ j → b k = 0 ∨ b k = -1 := fun k hk ↦ by
    have := (sum_eq_zero_iff_of_nonneg fun k hk ↦ hnonneg k (mem_of_mem_erase hk)).mp hrest k
      (mem_erase.2 ⟨hk, mem_univ k⟩)
    rcases mul_eq_zero.mp this with h | h <;> omega
  have hon : b j = 1 ∨ b j = -2 := by
    have h1 : b j ≤ 1 := by nlinarith
    have h2 : -2 ≤ b j := by nlinarith
    interval_cases h : b j <;> simp_all
  refine ⟨fun k ↦ (b k : ZMod 2), hb, j, funext fun k ↦ ?_⟩
  rw [leechOddVector_apply]
  by_cases hk : k = j
  · subst hk
    rcases hon with h | h <;> simp only [↓reduceIte, h] <;> decide
  · rcases hoff k hk with h | h <;> simp only [hk, ↓reduceIte, h] <;> decide

/-- **The classification of the minimal vectors of the Leech lattice**, in congruence coordinates:
an integer vector `a` halves into a Leech lattice vector of norm `4`, that is with `∑ aᵢ² = 32`,
exactly when it has one of the three shapes. -/
theorem intCast_div_two_mem_leechLattice_carrier_and_sum_sq_eq_iff (a : Fin 24 → ℤ) :
    (fun i ↦ (a i : ℚ) / 2) ∈ leechLattice.carrier ∧ ∑ i, a i ^ 2 = 32 ↔
      a ∈ leechPairVectors ∪ leechOctadVectors ∪ leechOddVectors := by
  constructor
  · rintro ⟨ha, hsq⟩
    obtain ⟨m, hm, b, hb, hsum, hx⟩ := (mem_leechLattice_carrier_iff_exists _).1 ha
    have hab : a = fun i ↦ 2 * b i + m := funext fun i ↦ by
      have := congrFun hx i
      exact_mod_cast (div_left_inj' two_ne_zero).mp this
    subst hab
    rcases hm with rfl | rfl
    · simp only [add_zero, mul_zero] at hsq hsum ⊢
      have hsq' : ∑ i, b i ^ 2 = 8 := by
        simp_rw [mul_pow, ← mul_sum] at hsq
        omega
      by_cases hc : (fun i ↦ (b i : ZMod 2)) = 0
      · exact Or.inl (Or.inl (two_mul_mem_leechPairVectors hc hsq'))
      · exact Or.inl (Or.inr (two_mul_mem_leechOctadVectors hb hc hsq' hsum))
    · exact Or.inr (two_mul_add_one_mem_leechOddVectors hb hsq)
  · rintro ((⟨i, j, hij, s, t, rfl⟩ | ⟨c, hc, hc8, d, hdc, hd, rfl⟩) | ⟨c, hc, j, rfl⟩)
    · exact leechPairVector_mem hij.ne s t
    · exact leechOctadVector_mem hc hc8 hdc hd
    · exact leechOddVector_mem hc j

/-- **The minimal vectors of the Leech lattice**: a lattice vector has norm `4` exactly when it is
half of an integer vector of one of the three shapes. -/
theorem mem_vectorsOfNorm_four_leechLattice_iff (x : leechLattice) :
    x ∈ leechLattice.vectorsOfNorm 4 ↔
      ∃ a ∈ leechPairVectors ∪ leechOctadVectors ∪ leechOddVectors,
        (x : Fin 24 → ℚ) = fun i ↦ (a i : ℚ) / 2 := by
  rw [mem_vectorsOfNorm]
  constructor
  · intro hx
    obtain ⟨m, -, b, -, -, hxb⟩ := (mem_leechLattice_carrier_iff_exists _).1 x.2
    refine ⟨fun i ↦ 2 * b i + m,
      (intCast_div_two_mem_leechLattice_carrier_and_sum_sq_eq_iff _).1 ⟨hxb ▸ x.2, ?_⟩, hxb⟩
    rw [hxb, leechLattice_norm_intCast_div_two] at hx
    have : ((∑ i, (2 * b i + m) ^ 2 : ℤ) : ℚ) = ((32 : ℤ) : ℚ) := by
      push_cast at hx ⊢
      linarith
    exact_mod_cast this
  · rintro ⟨a, ha, hxa⟩
    rw [hxa, leechLattice_norm_intCast_div_two,
      ((intCast_div_two_mem_leechLattice_carrier_and_sum_sq_eq_iff a).2 ha).2]
    norm_num

/-! ### Counting the three families -/

/-- The support of a vector of the first shape is `{i, j}`. -/
theorem leechPairVector_ne_zero_iff (i j : Fin 24) (s t : ℤˣ) (k : Fin 24) :
    leechPairVector i j s t k ≠ 0 ↔ k = i ∨ k = j := by
  rw [leechPairVector_apply]
  split_ifs with hki hkj
  · simp [hki, s.ne_zero]
  · simp [hkj, t.ne_zero]
  · simp [hki, hkj]

/-- The parametrization of the first family by ordered pairs of coordinates and two signs. -/
private def pairParam : {p : Fin 24 × Fin 24 // p.1 < p.2} × ℤˣ × ℤˣ → Fin 24 → ℤ :=
  fun p ↦ leechPairVector p.1.1.1 p.1.1.2 p.2.1 p.2.2

private theorem pairParam_injective : Function.Injective pairParam := by
  rintro ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ ⟨⟨⟨i', j'⟩, hij'⟩, s', t'⟩ h
  simp only [pairParam] at h hij hij'
  have hsupp : ∀ k, (k = i ∨ k = j) ↔ (k = i' ∨ k = j') := fun k ↦ by
    rw [← leechPairVector_ne_zero_iff i j s t, ← leechPairVector_ne_zero_iff i' j' s' t', h]
  have h1 := (hsupp i).1 (Or.inl rfl)
  have h2 := (hsupp j).1 (Or.inr rfl)
  have h3 := (hsupp i').2 (Or.inl rfl)
  have hlt : i.val < j.val := hij
  have hlt' : i'.val < j'.val := hij'
  simp only [Fin.ext_iff] at h1 h2 h3
  have hi : i = i' := Fin.ext (by omega)
  have hj : j = j' := Fin.ext (by omega)
  subst hi hj
  have hs := congrFun h i
  have ht := congrFun h j
  simp only [leechPairVector_apply, hij.ne', ↓reduceIte] at hs ht
  have hs' : s = s' := Units.ext (by omega)
  have ht' : t = t' := Units.ext (by omega)
  subst hs' ht'
  rfl

private theorem leechPairVectors_eq_range : leechPairVectors = Set.range pairParam := by
  ext a
  constructor
  · rintro ⟨i, j, hij, s, t, rfl⟩
    exact ⟨⟨⟨(i, j), hij⟩, s, t⟩, rfl⟩
  · rintro ⟨⟨⟨⟨i, j⟩, hij⟩, s, t⟩, rfl⟩
    exact ⟨i, j, hij, s, t, rfl⟩

private theorem card_lt_pairs : Fintype.card {p : Fin 24 × Fin 24 // p.1 < p.2} = 276 := by
  decide +kernel

/-- **There are `1104` minimal vectors of the first shape**: `(24 choose 2) = 276` pairs of
coordinates, each with four choices of signs. -/
theorem ncard_leechPairVectors : leechPairVectors.ncard = 1104 := by
  rw [leechPairVectors_eq_range, Set.ncard_range_of_injective pairParam_injective, Nat.card_prod,
    Nat.card_prod, Nat.card_eq_fintype_card, card_lt_pairs, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

/-- The octads, the Golay codewords of weight eight. -/
private abbrev Octad : Type :=
  {c : Fin 24 → ZMod 2 // c ∈ (code : Set (Fin 24 → ZMod 2)) ∧ hammingNorm c = 8}

/-- The sign patterns on an octad: binary words inside it of even weight. -/
private abbrev OctadSigns (c : Octad) : Type :=
  {d : Fin 24 → ZMod 2 // (∀ k, c.1 k = 0 → d k = 0) ∧ Even (hammingNorm d)}

private theorem natCard_octad : Nat.card Octad = 759 := by
  rw [← Set.weightDistribution_def, weightDistribution_code]
  norm_num

/-- A binary word inside the octad `c` is the indicator of a subset of its support. -/
private def octadSignsEquiv (c : Octad) :
    OctadSigns c ≃ {t : Finset (Fin 24) // (∀ k ∈ t, c.1 k ≠ 0) ∧ Even #t} where
  toFun d := ⟨({k | d.1 k ≠ 0} : Finset (Fin 24)),
    fun k hk h ↦ (mem_filter.1 hk).2 (d.2.1 k h), d.2.2⟩
  invFun t := ⟨fun k ↦ if k ∈ t.1 then 1 else 0, by
    refine ⟨fun k hk ↦ ?_, ?_⟩
    · have : k ∉ t.1 := fun h ↦ t.2.1 k h hk
      simp [this]
    · have hnorm : hammingNorm (fun k ↦ if k ∈ t.1 then (1 : ZMod 2) else 0) = #t.1 := by
        unfold hammingNorm
        congr 1
        ext k
        by_cases h : k ∈ t.1 <;> simp [h]
      exact hnorm ▸ t.2.2⟩
  left_inv d := by
    refine Subtype.ext (funext fun k ↦ ?_)
    rcases eq_zero_or_one_of_sq_eq_self (ZMod.pow_card (d.1 k)) with h | h <;> simp [h]
  right_inv t := by
    refine Subtype.ext (Finset.ext fun k ↦ ?_)
    by_cases h : k ∈ t.1 <;> simp [h]

/-- An octad carries `2⁷` sign patterns: the subsets of even cardinality of its eight-element
support. -/
private theorem natCard_octadSigns (c : Octad) : Nat.card (OctadSigns c) = 128 := by
  have hsupp : Nat.card {k // c.1 k ≠ 0} = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact c.2.2
  -- Subsets of the support, read in `Fin 24`, keep their cardinality.
  let e : {S : Finset {k // c.1 k ≠ 0} // Even #S} ≃
      {t : Finset (Fin 24) // (∀ k ∈ t, c.1 k ≠ 0) ∧ Even #t} :=
    ((Equiv.finsetSubtypeComm _).subtypeEquiv fun S ↦ by
      simp [Equiv.finsetSubtypeComm_apply_coe]).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ fun t ↦ Even #t)
  rw [Nat.card_congr ((octadSignsEquiv c).trans e.symm), card_even_card_finset, hsupp]
  norm_num

/-- The parametrization of the second family by octads and their sign patterns. -/
private def octadParam : (Σ c : Octad, OctadSigns c) → Fin 24 → ℤ :=
  fun p ↦ leechOctadVector p.1.1 p.2.1

private theorem octadParam_injective : Function.Injective octadParam := by
  rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨c', hc'⟩, ⟨d', hd'⟩⟩ h
  -- Coordinatewise, the value `0`, `2` or `-2` determines the pair of digits.
  have hcoord : ∀ k, c k = c' k ∧ d k = d' k := fun k ↦ by
    have key : ∀ x y x' y' : ZMod 2, (x = 0 → y = 0) → (x' = 0 → y' = 0) →
        2 * (x.val : ℤ) * (1 - 2 * (y.val : ℤ)) = 2 * (x'.val : ℤ) * (1 - 2 * (y'.val : ℤ)) →
          x = x' ∧ y = y' := by
      decide
    exact key _ _ _ _ (hd.1 k) (hd'.1 k) (congrFun h k)
  obtain rfl : c = c' := funext fun k ↦ (hcoord k).1
  obtain rfl : d = d' := funext fun k ↦ (hcoord k).2
  rfl

private theorem leechOctadVectors_eq_range : leechOctadVectors = Set.range octadParam := by
  ext a
  constructor
  · rintro ⟨c, hc, hc8, d, hdc, hd, rfl⟩
    exact ⟨⟨⟨c, hc, hc8⟩, ⟨d, hdc, hd⟩⟩, rfl⟩
  · rintro ⟨⟨⟨c, hc, hc8⟩, ⟨d, hdc, hd⟩⟩, rfl⟩
    exact ⟨c, hc, hc8, d, hdc, hd, rfl⟩

/-- **There are `97152` minimal vectors of the second shape**: `759` octads, each with `2⁷`
sign patterns having an even number of minus signs. -/
theorem ncard_leechOctadVectors : leechOctadVectors.ncard = 97152 := by
  have : Fintype Octad := Fintype.ofFinite _
  rw [leechOctadVectors_eq_range, Set.ncard_range_of_injective octadParam_injective,
    Nat.card_sigma]
  simp only [natCard_octadSigns, sum_const, card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, natCard_octad]

/-- The parametrization of the third family by Golay codewords and a coordinate. -/
private def oddParam : code × Fin 24 → Fin 24 → ℤ :=
  fun p ↦ leechOddVector p.1 p.2

/-- The squared coordinates of a vector of the third shape: `9` at the distinguished coordinate
and `1` elsewhere. -/
theorem leechOddVector_sq (c : Fin 24 → ZMod 2) (j k : Fin 24) :
    leechOddVector c j k ^ 2 = if k = j then 9 else 1 := by
  by_cases hk : k = j
  · subst hk
    simp only [leechOddVector_apply, ↓reduceIte]
    generalize c k = x
    revert x
    decide
  · simp only [leechOddVector_apply, hk, ↓reduceIte]
    generalize c k = x
    revert x
    decide

private theorem oddParam_injective : Function.Injective oddParam := by
  rintro ⟨c, j⟩ ⟨c', j'⟩ h
  simp only [oddParam] at h
  -- The distinguished coordinate is the one where the square is `9`.
  have hj : j = j' := by
    by_contra hne
    have := congrArg (· ^ 2) (congrFun h j)
    simp only [leechOddVector_sq] at this
    simp [hne] at this
  subst hj
  refine Prod.ext (Subtype.ext (funext fun k ↦ ?_)) rfl
  have hk := congrFun h k
  simp only [leechOddVector_apply] at hk
  have hval : (c.1 k).val = (c'.1 k).val := by
    split_ifs at hk <;> omega
  exact ZMod.val_injective _ hval

private theorem leechOddVectors_eq_range : leechOddVectors = Set.range oddParam := by
  ext a
  constructor
  · rintro ⟨c, hc, j, rfl⟩
    exact ⟨(⟨c, hc⟩, j), rfl⟩
  · rintro ⟨⟨⟨c, hc⟩, j⟩, rfl⟩
    exact ⟨c, hc, j, rfl⟩

/-- **There are `98304` minimal vectors of the third shape**: one for each of the `4096` Golay
codewords and each of the `24` coordinates. -/
theorem ncard_leechOddVectors : leechOddVectors.ncard = 98304 := by
  rw [leechOddVectors_eq_range, Set.ncard_range_of_injective oddParam_injective, Nat.card_prod,
    natCard_code, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### The three families are disjoint -/

/-- No vector has both of the first two shapes: the second has a coordinate `±2`, while the
coordinates of the first are `0` and `±4`. -/
theorem disjoint_leechPairVectors_leechOctadVectors :
    Disjoint leechPairVectors leechOctadVectors := by
  rw [Set.disjoint_left]
  rintro a ⟨i, j, -, s, t, rfl⟩ ⟨c, -, hc8, d, -, -, h⟩
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra! h0
    have : c = 0 := funext h0
    simp [this] at hc8
  have h2 : leechOctadVector c d k = 2 ∨ leechOctadVector c d k = -2 := by
    rw [leechOctadVector_apply,
      (eq_zero_or_one_of_sq_eq_self (ZMod.pow_card (c k))).resolve_left hk]
    generalize d k = x
    revert x
    decide
  have h4 : leechPairVector i j s t k = 0 ∨ leechPairVector i j s t k = 4 ∨
      leechPairVector i j s t k = -4 := by
    rw [leechPairVector_apply]
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
      split_ifs <;> decide
  rw [← h] at h4
  omega

/-- The coordinates of a vector of the third shape are odd. -/
theorem odd_leechOddVector (c : Fin 24 → ZMod 2) (j k : Fin 24) :
    Odd (leechOddVector c j k) := by
  by_cases hk : k = j
  · subst hk
    simp only [leechOddVector_apply, ↓reduceIte]
    generalize c k = x
    revert x
    decide
  · simp only [leechOddVector_apply, hk, ↓reduceIte]
    generalize c k = x
    revert x
    decide

/-- No vector has both the first and the third shape: the first is even, the third odd. -/
theorem disjoint_leechPairVectors_leechOddVectors :
    Disjoint leechPairVectors leechOddVectors := by
  rw [Set.disjoint_left]
  rintro a ⟨i, j, -, s, t, rfl⟩ ⟨c, -, j', h⟩
  have hodd := h ▸ odd_leechOddVector c j' 0
  rw [leechPairVector_apply] at hodd
  split_ifs at hodd <;> simp [Int.odd_iff] at hodd <;> omega

/-- No vector has both the second and the third shape: the second is even, the third odd. -/
theorem disjoint_leechOctadVectors_leechOddVectors :
    Disjoint leechOctadVectors leechOddVectors := by
  rw [Set.disjoint_left]
  rintro a ⟨c, -, -, d, -, -, rfl⟩ ⟨c', -, j, h⟩
  have hodd := h ▸ odd_leechOddVector c' j 0
  rw [leechOctadVector_apply, mul_assoc] at hodd
  exact Int.not_even_iff_odd.2 hodd (even_two_mul _)

/-! ### The kissing number -/

/-- The three families of minimal vectors have `196560` members altogether. -/
private theorem ncard_union_leechVectors :
    (leechPairVectors ∪ leechOctadVectors ∪ leechOddVectors).ncard = 196560 := by
  have hP : leechPairVectors.Finite := leechPairVectors_eq_range ▸ Set.finite_range _
  have hO : leechOctadVectors.Finite := by
    have : Finite Octad := inferInstance
    exact leechOctadVectors_eq_range ▸ Set.finite_range _
  have hD : leechOddVectors.Finite := leechOddVectors_eq_range ▸ Set.finite_range _
  rw [Set.ncard_union_eq _ (hP.union hO) hD, Set.ncard_union_eq _ hP hO, ncard_leechPairVectors,
    ncard_leechOctadVectors, ncard_leechOddVectors]
  · exact disjoint_leechPairVectors_leechOctadVectors
  · exact Disjoint.union_left disjoint_leechPairVectors_leechOddVectors
      disjoint_leechOctadVectors_leechOddVectors

/-- **The Leech lattice has `196560` vectors of norm four.** -/
theorem ncard_vectorsOfNorm_four_leechLattice :
    (leechLattice.vectorsOfNorm 4).ncard = 196560 := by
  rw [← ncard_union_leechVectors]
  symm
  refine Set.ncard_congr (fun a ha ↦ ⟨fun i ↦ (a i : ℚ) / 2,
    ((intCast_div_two_mem_leechLattice_carrier_and_sum_sq_eq_iff a).2 ha).1⟩) ?_ ?_ ?_
  · intro a ha
    exact (mem_vectorsOfNorm_four_leechLattice_iff _).2 ⟨a, ha, rfl⟩
  · intro a a' _ _ h
    funext i
    have := congrFun (congrArg Subtype.val h) i
    simp only at this
    exact_mod_cast (div_left_inj' two_ne_zero).mp this
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := (mem_vectorsOfNorm_four_leechLattice_iff x).1 hx
    exact ⟨a, ha, Subtype.ext hxa.symm⟩

/-- **The kissing number of the Leech lattice is `196560`.** -/
@[simp]
theorem kissingNumber_leechLattice : leechLattice.kissingNumber = 196560 := by
  rw [kissingNumber_eq_representationNumber (by simp), representationNumber_def,
    minimum_leechLattice, Nat.cast_ofNat, ncard_vectorsOfNorm_four_leechLattice]

end TauCeti
