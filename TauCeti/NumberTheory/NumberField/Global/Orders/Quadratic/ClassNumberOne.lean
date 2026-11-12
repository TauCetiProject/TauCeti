/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.OrderOfConductor
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Units
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Orders of class number one in imaginary quadratic fields

Let `K` be an imaginary quadratic field with discriminant `D` and let `O_f = ℤ + f 𝓞 K` be its
order of conductor `f ≥ 1`. The class number formula for orders, written as a product of local
factors (`card_pic_intAddMulOrder_mul_index_eq`), reads

```text
#Pic O_f · [(𝓞 K)ˣ : O_fˣ] = h_K · ∏_{p ∣ f} p ^ (v_p(f) - 1) · (p - χ_D(p)).
```

Every local factor is a positive integer, at least `p - χ_D(p) ≥ p - 1`, and it equals `1` only
for `p = 2` with `v_2(f) = 1` and `χ_D(2) = 1`. The unit index is `1` unless `f > 1` and
`D ∈ {-3, -4}`, when it is `3` or `2`. The Picard group surjects onto the class group, so `O_f` has
class number one only if `K` does, and comparing the two sides then shows that `O_f` has class
number one iff `h_K = 1` and

* `f = 1`, or
* `f = 2` and `D ≡ 1 (mod 8)`, that is, `2` splits in `K`, or
* `D = -3` and `f ∈ {2, 3}`, or
* `D = -4` and `f = 2`.

This bounds the conductor of an imaginary quadratic order of class number one by `3`. Combined
with the list of the nine imaginary quadratic fields of class number one, in which only `D = -7`
has `D ≡ 1 (mod 8)`, it gives the thirteen discriminants `f² D` of such orders.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.card_pic_intAddMulOrder_eq_one_iff`: the order of
  conductor `f` in an imaginary quadratic field has class number one iff `h_K = 1` and `(D, f)` is
  as above.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (Theorem 7.24 and the orders of class number
  one).
-/

public section

open NumberField Module
open TauCeti.Multiquadratic (fundamentalDiscriminantChar isFundamentalDiscr_discr
  fundamentalDiscriminantChar_le_one fundamentalDiscriminantChar_two_eq_one_iff
  fundamentalDiscriminantChar_neg_four fundamentalDiscriminantChar_neg_three)

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

/-! ### The local factors

Throughout, `c : ℕ → ℤ` stands for the values `χ_D(p) ≤ 1` of the character, and the local factor
of `f` at a prime `p ∣ f` is `p ^ (v_p(f) - 1) · (p - c(p))`.
-/

variable {c : ℕ → ℤ} {f : ℕ}

/-- A local factor is at least `p - c(p) ≥ 1`. -/
private theorem sub_le_pow_mul_sub (hc : ∀ p, c p ≤ 1) {p : ℕ} (hp : p ∈ f.primeFactors) :
    1 ≤ (p : ℤ) - c p ∧ (p : ℤ) - c p ≤ (p : ℤ) ^ (f.factorization p - 1) * (p - c p) := by
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have h1 : (1 : ℤ) ≤ (p : ℤ) ^ (f.factorization p - 1) := one_le_pow₀ (by linarith)
  exact ⟨by linarith [hc p], le_mul_of_one_le_left (by linarith [hc p]) h1⟩

/-- If the product of the local factors of `f` is `n`, then every prime factor `p` of `f`
satisfies `p - c(p) ≤ n`, and if `p - c(p) = n`, then `p` divides `f` exactly once. -/
private theorem sub_le_of_prod_eq (hc : ∀ p, c p ≤ 1) {n : ℤ}
    (h : ∏ p ∈ f.primeFactors, (p : ℤ) ^ (f.factorization p - 1) * (p - c p) = n) {p : ℕ}
    (hp : p ∈ f.primeFactors) :
    (p : ℤ) - c p ≤ n ∧ ((p : ℤ) - c p = n → f.factorization p = 1) := by
  obtain ⟨hp1, hle⟩ := sub_le_pow_mul_sub hc hp
  -- Each local factor is positive and divides the product, so it is at most `n`.
  have hpn : (p : ℤ) ^ (f.factorization p - 1) * (p - c p) ≤ n := h ▸ Int.le_of_dvd
    (Finset.prod_pos fun q hq ↦ by linarith [sub_le_pow_mul_sub hc hq])
    (Finset.dvd_prod_of_mem _ hp)
  refine ⟨hle.trans hpn, fun hn ↦ ?_⟩
  obtain ⟨hp, hpf, hf⟩ := Nat.mem_primeFactors.mp hp
  have hv := hp.factorization_pos_of_dvd hf hpf
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  by_contra hv1
  have : (p : ℤ) ≤ (p : ℤ) ^ (f.factorization p - 1) := le_self_pow₀ (by linarith) (by omega)
  nlinarith

/-- If `q` is the only prime factor of `f ≠ 0` and it divides `f` exactly once, then `f = q`. -/
private theorem eq_of_forall_mem_primeFactors_eq {q : ℕ} (hf : f ≠ 0) (hq : q.Prime)
    (h : ∀ p ∈ f.primeFactors, p = q) (hv : f.factorization q = 1) : f = q := by
  have hfq := Nat.eq_prime_pow_of_unique_prime_dvd (p := q) hf fun hd hdvd ↦
    h _ (Nat.mem_primeFactors.mpr ⟨hd, hdvd, hf⟩)
  rw [hfq, Nat.factorization_pow_self hq] at hv
  rwa [hv, pow_one] at hfq

/-- If the local factors of `f > 1` multiply to `1`, then `f = 2` and `c(2) = 1`. -/
private theorem eq_two_of_prod_eq_one (hc : ∀ p, c p ≤ 1) (hf : 1 < f)
    (h : ∏ p ∈ f.primeFactors, (p : ℤ) ^ (f.factorization p - 1) * (p - c p) = 1) :
    f = 2 ∧ c 2 = 1 := by
  have hpf : ∀ p ∈ f.primeFactors, p = 2 ∧ c 2 = 1 ∧ f.factorization p = 1 := by
    intro p hp
    obtain ⟨hp1, hv⟩ := sub_le_of_prod_eq hc h hp
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    obtain rfl : p = 2 := by linarith [hc p]
    have h21 : c 2 = 1 := by push_cast at hp1; linarith [hc 2]
    exact ⟨rfl, h21, hv (by push_cast; rw [h21]; norm_num)⟩
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hf
  obtain ⟨rfl, h21, hv⟩ := hpf p hp
  -- `2` is the only prime factor of `f`, and it occurs once.
  exact ⟨eq_of_forall_mem_primeFactors_eq (by omega) Nat.prime_two (fun p hp ↦ (hpf p hp).1) hv,
    h21⟩

/-- If `c(2) = 0`, `c(3) = -1` and the local factors of `f > 1` multiply to `2`, then `f = 2`. -/
private theorem eq_two_of_prod_eq_two (hc : ∀ p, c p ≤ 1) (hc2 : c 2 = 0) (hc3 : c 3 = -1)
    (hf : 1 < f)
    (h : ∏ p ∈ f.primeFactors, (p : ℤ) ^ (f.factorization p - 1) * (p - c p) = 2) : f = 2 := by
  have hpf : ∀ p ∈ f.primeFactors, p = 2 ∧ f.factorization p = 1 := by
    intro p hp
    obtain ⟨hp2, hv⟩ := sub_le_of_prod_eq hc h hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    obtain rfl : p = 2 := by
      have hp23 : p = 2 ∨ p = 3 := by have := hc p; omega
      rcases hp23 with h | rfl
      · exact h
      · push_cast at hp2
        linarith
    exact ⟨rfl, hv (by push_cast; rw [hc2]; norm_num)⟩
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hf
  obtain ⟨rfl, hv⟩ := hpf p hp
  -- `2` is the only prime factor of `f`, and it occurs once.
  exact eq_of_forall_mem_primeFactors_eq (by omega) Nat.prime_two (fun p hp ↦ (hpf p hp).1) hv

/-- If `c(2) = -1`, `c(3) = 0` and the local factors of `f > 1` multiply to `3`, then `f = 2` or
`f = 3`. -/
private theorem eq_two_or_eq_three_of_prod_eq_three (hc : ∀ p, c p ≤ 1) (hc2 : c 2 = -1)
    (hc3 : c 3 = 0) (hf : 1 < f)
    (h : ∏ p ∈ f.primeFactors, (p : ℤ) ^ (f.factorization p - 1) * (p - c p) = 3) :
    f = 2 ∨ f = 3 := by
  -- Every prime factor of `f` is `2` or `3`, to the first power.
  have hpf : ∀ p ∈ f.primeFactors, (p = 2 ∨ p = 3) ∧ f.factorization p = 1 := by
    intro p hp
    obtain ⟨hp3, hv⟩ := sub_le_of_prod_eq hc h hp
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp23 : p = 2 ∨ p = 3 := by
      have hp4 : p ≤ 4 := by have := hc p; omega
      interval_cases p
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (Nat.prime_of_mem_primeFactors hp) (by decide)
    exact ⟨hp23, hv (by rcases hp23 with rfl | rfl <;> simp [hc2, hc3])⟩
  -- They are not both prime factors, since `3 · 3` does not divide `3`.
  have hnot : ¬ (2 ∈ f.primeFactors ∧ 3 ∈ f.primeFactors) := by
    rintro ⟨h2f, h3f⟩
    have hdvd := Finset.prod_dvd_prod_of_subset {2, 3} f.primeFactors
      (fun p ↦ (p : ℤ) ^ (f.factorization p - 1) * (p - c p))
      (Finset.insert_subset h2f (Finset.singleton_subset_iff.mpr h3f))
    rw [Finset.prod_pair (by decide), h, (hpf 2 h2f).2, (hpf 3 h3f).2, hc2, hc3] at hdvd
    norm_num at hdvd
  -- So some prime factor `q` is the only one, and it occurs once.
  obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr hf
  have hall : ∀ p ∈ f.primeFactors, p = q := fun p hp ↦ by
    rcases (hpf p hp).1 with rfl | rfl <;> rcases (hpf q hq).1 with rfl | rfl <;> tauto
  obtain ⟨hq23, hv⟩ := hpf q hq
  rwa [eq_of_forall_mem_primeFactors_eq (by omega) (Nat.prime_of_mem_primeFactors hq) hall hv]

/-- The product of the local factors of a prime `p` is `p - c(p)`. -/
private theorem prod_pow_mul_sub_prime {p : ℕ} (hp : p.Prime) :
    ∏ q ∈ p.primeFactors, (q : ℤ) ^ (p.factorization q - 1) * (q - c q) = p - c p := by
  simp [hp.primeFactors, hp.factorization_self]

/-! ### The character at `2` and `3` -/

variable {D : ℤ}

/-- For `D = -4`, `χ_D(2) = 0` and `χ_D(3) = -1`. -/
private theorem fundamentalDiscriminantChar_two_three_of_eq_neg_four
    (hD : Int.IsFundamentalDiscr D) (h : D = -4) :
    fundamentalDiscriminantChar D hD (2 : ℕ) = 0 ∧
      fundamentalDiscriminantChar D hD (3 : ℕ) = -1 := by
  subst h
  rw [← Int.cast_natCast, ← Int.cast_natCast (R := ZMod _), fundamentalDiscriminantChar_neg_four,
    fundamentalDiscriminantChar_neg_four]
  decide

/-- For `D = -3`, `χ_D(2) = -1` and `χ_D(3) = 0`. -/
private theorem fundamentalDiscriminantChar_two_three_of_eq_neg_three
    (hD : Int.IsFundamentalDiscr D) (h : D = -3) :
    fundamentalDiscriminantChar D hD (2 : ℕ) = -1 ∧
      fundamentalDiscriminantChar D hD (3 : ℕ) = 0 := by
  subst h
  rw [← Int.cast_natCast, ← Int.cast_natCast (R := ZMod _), fundamentalDiscriminantChar_neg_three,
    fundamentalDiscriminantChar_neg_three]
  norm_num

/-! ### Class number one -/

variable {K : Type*} [Field K] [NumberField K]

/-- **The orders of class number one in an imaginary quadratic field.** Let `K` be an imaginary
quadratic field with discriminant `D` and `f ≥ 1`. The order `O_f = ℤ + f 𝓞 K` of conductor `f`
has class number one iff `K` has class number one and either `f = 1`, or `f = 2` and
`D ≡ 1 (mod 8)` (so that `2` splits in `K`), or `D = -3` and `f ∈ {2, 3}`, or `D = -4` and
`f = 2`. -/
theorem card_pic_intAddMulOrder_eq_one_iff [IsTotallyComplex K] (hK : finrank ℚ K = 2) (f : ℕ)
    [NeZero f] :
    Nat.card (Pic (intAddMulOrder K f)) = 1 ↔ Nat.card (ClassGroup (𝓞 K)) = 1 ∧
      (f = 1 ∨ (f = 2 ∧ NumberField.discr K % 8 = 1) ∨
        (NumberField.discr K = -3 ∧ (f = 2 ∨ f = 3)) ∨ (NumberField.discr K = -4 ∧ f = 2)) := by
  have hD := isFundamentalDiscr_discr hK
  set c : ℕ → ℤ := fun p ↦ fundamentalDiscriminantChar (NumberField.discr K) hD p
  have hc : ∀ p, c p ≤ 1 := fun p ↦ fundamentalDiscriminantChar_le_one hD p
  have key : (Nat.card (Pic (intAddMulOrder K f)) : ℤ) *
      (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
        (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index =
      Nat.card (ClassGroup (𝓞 K)) *
        ∏ p ∈ f.primeFactors, (p : ℤ) ^ (f.factorization p - 1) * (p - c p) :=
    card_pic_intAddMulOrder_mul_index_eq hK f
  rw [index_range_unitsMap_intAddMulOrder hK] at key
  constructor
  · intro h1
    -- The class group is a quotient of the Picard group, so it is trivial too.
    have hh : Nat.card (ClassGroup (𝓞 K)) = 1 :=
      le_antisymm (h1 ▸ Nat.card_le_card_of_surjective _ (picToClassGroup_surjective _))
        Nat.card_pos
    refine ⟨hh, ?_⟩
    rw [h1, hh, Nat.cast_one, one_mul, one_mul] at key
    rcases eq_or_ne f 1 with rfl | hf1
    · exact Or.inl rfl
    have hf : 1 < f := by have := NeZero.ne f; omega
    -- The local factors multiply to the unit index `2`, `3` or `1`.
    simp only [hf1, ↓reduceIte] at key
    split_ifs at key with h4 h3 <;> push_cast at key
    · obtain ⟨h20, h3⟩ := fundamentalDiscriminantChar_two_three_of_eq_neg_four hD h4
      exact Or.inr (Or.inr (Or.inr ⟨h4, eq_two_of_prod_eq_two hc h20 h3 hf key.symm⟩))
    · obtain ⟨h2, h30⟩ := fundamentalDiscriminantChar_two_three_of_eq_neg_three hD h3
      exact Or.inr (Or.inr (Or.inl ⟨h3,
        eq_two_or_eq_three_of_prod_eq_three hc h2 h30 hf key.symm⟩))
    · obtain ⟨rfl, h21⟩ := eq_two_of_prod_eq_one hc hf key.symm
      exact Or.inr (Or.inl ⟨rfl, (fundamentalDiscriminantChar_two_eq_one_iff hD).mp h21⟩)
  · rintro ⟨hh, hcase⟩
    rw [hh, Nat.cast_one, one_mul] at key
    -- In each case the product of the local factors equals the unit index.
    suffices (Nat.card (Pic (intAddMulOrder K f)) : ℤ) = 1 by exact_mod_cast this
    rcases hcase with rfl | ⟨rfl, h8⟩ | ⟨h3, rfl | rfl⟩ | ⟨h4, rfl⟩
    · simpa using key
    · have h21 : c 2 = 1 := (fundamentalDiscriminantChar_two_eq_one_iff hD).mpr h8
      have h4 : NumberField.discr K ≠ -4 := by omega
      have h3 : NumberField.discr K ≠ -3 := by omega
      simpa [prod_pow_mul_sub_prime Nat.prime_two, h21, h4, h3] using key
    · have h2 : c 2 = -1 := (fundamentalDiscriminantChar_two_three_of_eq_neg_three hD h3).1
      simpa [prod_pow_mul_sub_prime Nat.prime_two, h2, h3] using key
    · have h30 : c 3 = 0 := (fundamentalDiscriminantChar_two_three_of_eq_neg_three hD h3).2
      simpa [prod_pow_mul_sub_prime Nat.prime_three, h30, h3] using key
    · have h20 : c 2 = 0 := (fundamentalDiscriminantChar_two_three_of_eq_neg_four hD h4).1
      simpa [prod_pow_mul_sub_prime Nat.prime_two, h20, h4] using key

end TauCeti.GlobalNumberFields.NumberFieldOrder
