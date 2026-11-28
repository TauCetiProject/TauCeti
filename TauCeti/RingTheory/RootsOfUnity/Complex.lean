/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import TauCeti.RingTheory.RootsOfUnity.Adjoin

/-!
# The average of a multiset of complex roots of unity

A sum of `d` complex roots of unity has absolute value at most `d`. This file proves an arithmetic
sharpening: if the **average** of the summands happens to be an algebraic integer, then the sum is
either `0` or of absolute value exactly `d`, with nothing in between possible.

The proof is Kronecker's theorem. Fix a primitive `n`-th root of unity `ζ`; the number field
`ℚ(ζ)` contains every `n`-th root of unity, hence the sum `x` and its average `α = x / d`. A field
embedding of `ℚ(ζ)` into `ℂ` sends each summand to an `n`-th root of unity, so it sends `x` to a
sum of `d` complex numbers of modulus one; therefore `‖α‖ ≤ 1` at *every* embedding, not just the
inclusion we started with. A nonzero algebraic integer with that property is a root of unity
(`NumberField.Embeddings.pow_eq_one_of_norm_le_one`), so `‖α‖ = 1`.

The hypothesis on the average is what makes the statement bite: without it the bound `‖x‖ ≤ d` is
all there is, and intermediate absolute values really do occur, `1 + i` being a sum of two fourth
roots of unity of absolute value `√2`.

## Main statements

* `TauCeti.sum_eq_zero_or_norm_sum_eq_card_of_isIntegral`: a multiset of `n`-th roots of unity
  whose average is integral over `ℤ` has sum `0`, or a sum whose absolute value is its
  cardinality.
* `TauCeti.norm_map_multiset_sum_le_card`: the image in `ℂ` of a sum of `n`-th roots of unity has
  absolute value at most the number of summands, under any ring homomorphism.
* `Complex.div_norm_zpow_mul_eq_one_of_pow_eq_one`: multiple-of-`n` integer powers of a unit-norm
  normalized complex `n`-th root of unity equal `1`.
* `Complex.isPrimitiveRoot_four_iff`: the complex primitive fourth roots of unity are `± I`.
* `Complex.im_three_add_four_I_div_five_zpow_ne_zero`: no nonzero integer power of `(3 + 4i) / 5`
  is real (in particular, `(3 + 4i) / 5` is not a root of unity).
* `Complex.two_add_I_div_two_sub_I`: in `ℂ`, `(2 + i) / (2 - i) = (3 + 4i) / 5`.

## References

* Kronecker's theorem on algebraic integers in the closed unit disc, in Mathlib as
  `NumberField.Embeddings.pow_eq_one_of_norm_le_one`.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 3.8, where this is the
  Kronecker half of Burnside's vanishing theorem for character values, applied to the average once
  the arithmetic half has shown that average to be an algebraic integer.
-/

public section

namespace TauCeti

/-- A ring homomorphism into `ℂ` sends a multiset of `n`-th roots of unity to complex numbers of
modulus one, so it sends their sum to a complex number of modulus at most the cardinality. -/
theorem norm_map_multiset_sum_le_card {K : Type*} [Semiring K] {n : ℕ} (hn : n ≠ 0)
    {t : Multiset K} (ht : ∀ ν ∈ t, ν ^ n = 1) (φ : K →+* ℂ) :
    ‖φ t.sum‖ ≤ Multiset.card t := by
  have hmap : (t.map φ).map (‖·‖) = t.map fun _ => (1 : ℝ) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun ν hν =>
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ht ν hν, map_one]) hn
  calc ‖φ t.sum‖ = ‖(t.map φ).sum‖ := by rw [map_multiset_sum]
    _ ≤ ((t.map φ).map (‖·‖)).sum := norm_multiset_sum_le _
    _ = Multiset.card t := by rw [hmap]; simp

/-- **The average of a multiset of roots of unity is `0` or of modulus one, once it is an
algebraic integer.** If every element of a multiset `s` of complex numbers is an `n`-th root of
unity and the average `s.sum / #s` is integral over `ℤ`, then either `s.sum = 0` or
`‖s.sum‖ = #s`.

This is Kronecker's theorem applied inside `ℚ(ζ)` for `ζ` a primitive `n`-th root of unity: the
average is an algebraic integer all of whose conjugates lie in the closed unit disc, because each
conjugate is again an average of `#s` complex numbers of modulus one. -/
theorem sum_eq_zero_or_norm_sum_eq_card_of_isIntegral {n : ℕ} (hn : n ≠ 0) {s : Multiset ℂ}
    (hs : ∀ μ ∈ s, μ ^ n = 1) (hint : IsIntegral ℤ (s.sum / (Multiset.card s : ℂ))) :
    s.sum = 0 ∨ ‖s.sum‖ = Multiset.card s := by
  have : NeZero n := ⟨hn⟩
  rcases Nat.eq_zero_or_pos (Multiset.card s) with hcard | hcard
  · exact Or.inl (by rw [Multiset.card_eq_zero.mp hcard, Multiset.sum_zero])
  have hd : ((Multiset.card s : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hcard.ne'
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n := ⟨_, Complex.isPrimitiveRoot_exp n hn⟩
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional
      ((hζ.isIntegral (Nat.pos_of_ne_zero hn)).tower_top (A := ℚ))
  have : NumberField K := ⟨⟩
  -- `s`, read inside `K`
  set t : Multiset K :=
    s.attach.map fun p => (⟨p.val, hζ.mem_adjoin_of_pow_eq_one (hs p.val p.property)⟩ : K) with
        htdef
  have hcoe : t.map (algebraMap K ℂ) = s := by
    rw [htdef, Multiset.map_map]
    exact Multiset.attach_map_val s
  have hcardt : Multiset.card t = Multiset.card s := by
    rw [htdef, Multiset.card_map, Multiset.card_attach]
  have hroot : ∀ ν ∈ t, ν ^ n = 1 := by
    intro ν hν
    rw [htdef, Multiset.mem_map] at hν
    obtain ⟨p, -, rfl⟩ := hν
    exact Subtype.ext (by simpa using hs p.val p.property)
  have hsum : algebraMap K ℂ t.sum = s.sum := by rw [map_multiset_sum, hcoe]
  -- the average, read inside `K`
  set α : K := t.sum / (Multiset.card s : K) with hαdef
  have hαcoe : algebraMap K ℂ α = s.sum / (Multiset.card s : ℂ) := by
    rw [hαdef, map_div₀, hsum, map_natCast]
  have hαint : IsIntegral ℤ α :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := ℂ)).1 (hαcoe ▸ hint)
  have hbound : ∀ φ : K →+* ℂ, ‖φ α‖ ≤ 1 := by
    intro φ
    rw [hαdef, map_div₀, map_natCast, norm_div, Complex.norm_natCast,
      div_le_one (by positivity)]
    exact hcardt ▸ norm_map_multiset_sum_le_card hn hroot φ
  rcases eq_or_ne α 0 with hα0 | hα0
  · refine Or.inl ?_
    rw [hα0, map_zero, eq_comm, div_eq_zero_iff] at hαcoe
    exact hαcoe.resolve_right hd
  · refine Or.inr ?_
    obtain ⟨m, hm, hpow⟩ :=
      NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hα0 hαint hbound
    have hnorm : ‖algebraMap K ℂ α‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hpow, map_one]) hm.ne'
    rw [hαcoe, norm_div, Complex.norm_natCast, div_eq_one_iff_eq (by positivity)] at hnorm
    exact hnorm

end TauCeti

namespace Complex

/-- Normalizing a complex `n`-th root of unity by its norm and raising to any integer multiple of
`n` yields `1`. -/
theorem div_norm_zpow_mul_eq_one_of_pow_eq_one {z : ℂ} {n : ℕ} (hz : z ^ n = 1) (m : ℤ) :
    (z / (‖z‖ : ℂ)) ^ ((n : ℤ) * m) = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [norm_eq_one_of_pow_eq_one hz hn, ofReal_one, div_one, zpow_mul, zpow_natCast, hz,
      one_zpow]

/-- The complex primitive fourth roots of unity are `Complex.I` and `-Complex.I`. -/
theorem isPrimitiveRoot_four_iff {ζ : ℂ} :
    IsPrimitiveRoot ζ 4 ↔ ζ = I ∨ ζ = -I := by
  refine ⟨fun hζ ↦ ?_, ?_⟩
  · have hsq : ζ ^ 2 = I ^ 2 := by
      rw [I_sq]
      exact (hζ.pow (by norm_num) (by norm_num : 4 = 2 * 2)).eq_neg_one_of_two_right
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  · rintro (rfl | rfl)
    · exact isPrimitiveRoot_I
    · exact isPrimitiveRoot_neg_I

/-- **No nonzero integer power of `(3 + 4i) / 5` is real**: every nonzero integer power has
nonzero imaginary part, since every positive power of `3 + 4i` has Gaussian integer coordinates
congruent to `(3, 4)` modulo `5`. -/
theorem im_three_add_four_I_div_five_zpow_ne_zero {m : ℤ} (hm : m ≠ 0) :
    ((((3 : ℂ) + 4 * I) / 5) ^ m).im ≠ 0 := by
  have hcongr : ∀ {n : ℕ}, n ≠ 0 → ∃ a b : ℤ,
      ((3 : ℂ) + 4 * I) ^ n = (a : ℂ) + (b : ℂ) * I ∧ a % 5 = 3 ∧ b % 5 = 4 := by
    intro n hn
    induction n with
    | zero => exact absurd rfl hn
    | succ k ih =>
      rcases eq_or_ne k 0 with rfl | hk
      · exact ⟨3, 4, by simp, by decide, by decide⟩
      · obtain ⟨a, b, hpow, ha, hb⟩ := ih hk
        refine ⟨3 * a - 4 * b, 4 * a + 3 * b, ?_, by omega, by omega⟩
        rw [pow_succ, hpow]
        push_cast
        linear_combination (4 * (b : ℂ)) * I_sq
  have hnat {n : ℕ} (hn : n ≠ 0) : ((((3 : ℂ) + 4 * I) / 5) ^ n).im ≠ 0 := by
    obtain ⟨a, b, hpow, -, hb⟩ := hcongr hn
    have hb_ne : b ≠ 0 := by omega
    have hb0 : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb_ne
    have h5 : (5 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hrew : (((3 : ℂ) + 4 * I) / 5) ^ n =
        ((a : ℝ) / (5 : ℝ) ^ n : ℝ) + (((b : ℝ) / (5 : ℝ) ^ n : ℝ) : ℂ) * I := by
      rw [div_pow, hpow]
      push_cast
      ring
    have him : ((((3 : ℂ) + 4 * I) / 5) ^ n).im = (b : ℝ) / (5 : ℝ) ^ n := by
      rw [hrew, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
    rw [him]
    exact div_ne_zero hb0 h5
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · have hn : n ≠ 0 := by omega
    simpa only [zpow_natCast] using hnat hn
  · have hn : n ≠ 0 := by omega
    rw [zpow_neg, zpow_natCast, inv_im]
    intro him
    rcases div_eq_zero_iff.mp him with hneg | hnsq
    · exact hnat hn (neg_eq_zero.mp hneg)
    · have hz0 : (((3 : ℂ) + 4 * I) / 5) ^ n = 0 := normSq_eq_zero.mp hnsq
      exact hnat hn (by simp [hz0])

/-- In `ℂ`, `(2 + i) / (2 - i) = (3 + 4i) / 5`. -/
theorem two_add_I_div_two_sub_I :
    ((2 : ℂ) + I) / (2 - I) = ((3 : ℂ) + 4 * I) / 5 := by
  have hne : (2 : ℂ) - I ≠ 0 := fun h ↦ by simpa using congrArg im h
  rw [div_eq_div_iff hne (by norm_num)]
  linear_combination 4 * I_sq

end Complex
