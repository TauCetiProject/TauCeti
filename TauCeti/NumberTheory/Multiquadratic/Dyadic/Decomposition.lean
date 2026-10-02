/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Dyadic.Inertia
import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# The number of primes above two in a multiquadratic field

For `K = ℚ(√d₁, …, √dₙ)` with integer radicands not divisible by four, this file gives
the prime count at two directly in terms of the radicands, including when two ramifies.
The ramification index is `2 ^ a`, where `a = 2` when the radicands generate two ramified
dyadic square classes, `a = 0` when all radicands are one modulo four, and `a = 1` otherwise.
The residue degree is `2 ^ b`, where `b = 1` precisely when the squarefree part of a subset
product is five modulo eight, and `b = 0` otherwise.

Thus the number of primes above two is `[K : ℚ] / 2 ^ (a + b)`. Under square-class independence,
`ncard_primesOver_two_eq_two_pow_sub` gives `2 ^ (n - (a + b))`, using the
equivalent rational square-class test for `b`. The companion `dyadic_exponents_add_le_card`
exposes the bound `a + b ≤ n`, so subtraction cannot conceal an impossible decomposition type.
Independence is unnecessary for the formula in terms of the field degree.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.B.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter II, §5.
* Mathlib, `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`
  (the Galois fundamental identity).
-/

public section

open NumberField Ideal Module
open scoped NumberField

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]
  {d : ι → ℤ} {r : ι → K}

open Classical in
/-- **The dyadic decomposition identity, without square-class independence.** The number of
primes above two multiplied by `2 ^ (a + b)` equals `[K : ℚ]`, where the displayed arithmetic
tests determine the ramification index `e = 2 ^ a` and residue degree `f = 2 ^ b`.
In particular, `2 ^ (a + b)` divides the field degree, including when two ramifies. -/
theorem ncard_primesOver_two_mul_two_pow_eq_finrank
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hd : ∀ i, ¬ (4 : ℤ) ∣ d i) :
    let a : ℕ := if ((∃ i j, d i % 4 = 3 ∧ 2 ∣ d j) ∨
      ∃ i j, d i % 8 = 2 ∧ d j % 8 = 6) then 2 else if ∀ i, d i % 4 = 1 then 0 else 1
    let b : ℕ := if (∃ (T : Finset ι) (s t : ℤ),
      Squarefree s ∧ t ≠ 0 ∧ ∏ i ∈ T, d i = s * t ^ 2 ∧ s % 8 = 5) then 1 else 0
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard * 2 ^ (a + b) = finrank ℚ K := by
  classical
  have := isGalois_rat hr htop
  have : (span {(2 : ℤ)} : Ideal ℤ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨Q, _, _⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (span {(2 : ℤ)})
  dsimp only
  -- Read off the common ramification index and residue degree at a prime above two.
  have he : Q.ramificationIdx ℤ = 2 ^ (if ((∃ i j, d i % 4 = 3 ∧ 2 ∣ d j) ∨
      ∃ i j, d i % 8 = 2 ∧ d j % 8 = 6) then 2 else if ∀ i, d i % 4 = 1 then 0 else 1) := by
    split_ifs with hfour hone
    · exact (ramificationIdx_eq_four_iff hr htop hd Q).mpr hfour
    · rw [← Ideal.card_inertia_eq_ramificationIdx ℤ (K ≃ₐ[ℚ] K) Q,
        (inertia_eq_bot_iff_forall_mod_four_eq_one hr htop hd Q).mpr hone]
      simp
    · exact (ramificationIdx_eq_two_iff_of_liesOver_two hr htop hd Q).mpr
        ⟨not_forall.mp hone, hfour⟩
  have hf : Q.inertiaDeg ℤ = 2 ^ (if (∃ (T : Finset ι) (s t : ℤ),
      Squarefree s ∧ t ≠ 0 ∧ ∏ i ∈ T, d i = s * t ^ 2 ∧ s % 8 = 5) then 1 else 0) := by
    split_ifs with hfive
    · exact (inertiaDeg_eq_two_iff_exists_squarefree_prod_eq_mod_eight_eq_five_mul_sq
        hr htop Q).mpr hfive
    · rw [pow_zero, inertiaDeg_eq_one_iff_not_exists_prod_eq_mod_eight_eq_five_mul_sq
        hr htop Q]
      simpa only [← Int.cast_prod,
        Int.exists_eq_mod_eight_eq_five_mul_sq_iff_exists_squarefree_mod_eight_eq_five_mul_sq]
        using hfive
  -- Substitute these values in the Galois fundamental identity.
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(2 : ℤ)}) (𝓞 K) (K ≃ₐ[ℚ] K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (K ≃ₐ[ℚ] K),
    Ideal.inertiaDegIn_eq_inertiaDeg _ Q (K ≃ₐ[ℚ] K),
    IsGalois.card_aut_eq_finrank, he, hf, ← pow_add] at h
  exact h

open Classical in
/-- **The number of primes above two, without square-class independence.** The exponents `a`
and `b` read the ramification index and residue degree from the radicands: `e = 2 ^ a` and
`f = 2 ^ b`. The number of primes is therefore `[K : ℚ] / 2 ^ (a + b)`, whether or not two
ramifies. Radicands need only be indivisible by four, rather than squarefree. -/
theorem ncard_primesOver_two_eq_finrank_div
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hd : ∀ i, ¬ (4 : ℤ) ∣ d i) :
    let a : ℕ := if ((∃ i j, d i % 4 = 3 ∧ 2 ∣ d j) ∨
      ∃ i j, d i % 8 = 2 ∧ d j % 8 = 6) then 2 else if ∀ i, d i % 4 = 1 then 0 else 1
    let b : ℕ := if (∃ (T : Finset ι) (s t : ℤ),
      Squarefree s ∧ t ≠ 0 ∧ ∏ i ∈ T, d i = s * t ^ 2 ∧ s % 8 = 5) then 1 else 0
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = finrank ℚ K / 2 ^ (a + b) := by
  classical
  dsimp only
  rw [← ncard_primesOver_two_mul_two_pow_eq_finrank hr htop hd,
    Nat.mul_div_cancel _ (pow_pos two_pos _)]

open Classical in
/-- **The dyadic exponents fit within the number of independent radicands.** The displayed
ramification and residue-degree exponents satisfy `a + b ≤ Nat.card ι`, ensuring that natural
subtraction of their sum from the number of radicands does not truncate. -/
theorem dyadic_exponents_add_le_card
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hd : ∀ i, ¬ (4 : ℤ) ∣ d i)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ))) :
    let a : ℕ := if ((∃ i j, d i % 4 = 3 ∧ 2 ∣ d j) ∨
      ∃ i j, d i % 8 = 2 ∧ d j % 8 = 6) then 2 else if ∀ i, d i % 4 = 1 then 0 else 1
    let b : ℕ := if (∃ (T : Finset ι) (s t : ℤ),
      Squarefree s ∧ t ≠ 0 ∧ ∏ i ∈ T, d i = s * t ^ 2 ∧ s % 8 = 5) then 1 else 0
    a + b ≤ Nat.card ι := by
  classical
  exact le_card_of_mul_two_pow_eq_finrank hr htop hindep
    (ncard_primesOver_two_mul_two_pow_eq_finrank hr htop hd)

open Classical in
/-- **The number of primes above `2`.** Let `K` be generated over `ℚ` by square roots of `n`
square-class independent integers `d i` (no nonempty subset product is a square) not divisible by
`4`. Then there are exactly `2 ^ (n - a - b)` primes of `𝓞 K` above `2`, where the ramification
index is `e = 2 ^ a` and the residue degree is `f = 2 ^ b`:

* `a = 2` when some `d i` is `3` modulo `4` and some `d j` is even, or some `d i` is `2` and some
  `d j` is `6` modulo `8`; otherwise `a = 0` when every `d i` is `1` modulo `4`, and `a = 1` when
  not;
* `b = 1` when some subset product `∏_{i ∈ T} dᵢ` lies in the rational square class of an integer
  that is `5` modulo `8`, and `b = 0` otherwise. -/
theorem ncard_primesOver_two_eq_two_pow_sub
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    (hd : ∀ i, ¬ (4 : ℤ) ∣ d i)
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, (d i : ℚ))) :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 2 ^ (Nat.card ι -
      ((if (∃ i j, d i % 4 = 3 ∧ 2 ∣ d j) ∨ ∃ i j, d i % 8 = 2 ∧ d j % 8 = 6 then 2
        else if ∀ i, d i % 4 = 1 then 0 else 1) +
      if ∃ (T : Finset ι) (c : ℤ) (q : ℚ), c % 8 = 5 ∧ q ≠ 0 ∧ ∏ i ∈ T, (d i : ℚ) = c * q ^ 2
        then 1 else 0)) := by
  classical
  refine eq_two_pow_sub_of_mul_two_pow_eq_finrank hr htop hindep ?_
  simpa only [← Int.cast_prod,
    TauCeti.Int.exists_eq_mod_eight_eq_five_mul_sq_iff_exists_squarefree_mod_eight_eq_five_mul_sq]
    using ncard_primesOver_two_mul_two_pow_eq_finrank hr htop hd

end TauCeti.Multiquadratic
