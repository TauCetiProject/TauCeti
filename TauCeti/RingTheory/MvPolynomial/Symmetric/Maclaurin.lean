/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Maclaurin's bound by the arithmetic mean

For a multiset of `n` nonnegative elements of a linearly ordered field, its `k`th elementary
symmetric function is at most `n.choose k` times the `k`th power of the arithmetic mean.
The proof replaces two entries on opposite sides of the mean by the mean and their remaining
sum. This increases their product while preserving their sum. Each replacement fixes at least one
more entry at the mean, so the argument terminates without using completeness of the field.

See Hardy, Littlewood and Pólya, *Inequalities*, 2nd ed., Chapter II, for the symmetric means.
-/

public section

namespace Multiset

/-- The `k`th elementary symmetric function of `n` copies of `c` is `n.choose k * c^k`. -/
@[simp] theorem esymm_replicate {R : Type*} [CommSemiring R] (n : ℕ) (c : R) (k : ℕ) :
    (replicate n c).esymm k = (n.choose k : R) * c ^ k := by
  rw [esymm]
  calc
    _ = (((replicate n c).powersetCard k).map fun _ ↦ c ^ k).sum := by
      congr 1
      refine map_congr rfl fun t ht ↦ ?_
      obtain ⟨hle, hcard⟩ := mem_powersetCard.mp ht
      rw [t.eq_replicate_of_mem (fun a ha ↦ eq_of_mem_replicate (mem_of_le hle ha)),
        prod_replicate, hcard]
    _ = _ := by simp [map_const', card_powersetCard, nsmul_eq_mul]

/-- Nonnegative entries have nonnegative elementary symmetric functions. -/
theorem esymm_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {s : Multiset R} (hs : ∀ a ∈ s, 0 ≤ a) (k : ℕ) : 0 ≤ s.esymm k := by
  rw [esymm]
  refine sum_nonneg fun _ hx ↦ ?_
  obtain ⟨t, ht, rfl⟩ := mem_map.mp hx
  exact prod_nonneg fun a ha ↦ hs a (mem_of_le (mem_powersetCard.mp ht).1 ha)

grind_pattern esymm_nonneg => s.esymm k

/-- At fixed pair sum, increasing the pair product increases the elementary symmetric functions
of the multiset obtained by adjoining the pair to a nonnegative multiset. -/
theorem esymm_cons_cons_le {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {s : Multiset R} (hs : ∀ x ∈ s, 0 ≤ x) {a b c d : R}
    (hsum : a + b = c + d) (hprod : a * b ≤ c * d) (k : ℕ) :
    (a ::ₘ b ::ₘ s).esymm k ≤ (c ::ₘ d ::ₘ s).esymm k := by
  rcases k with _ | _ | k
  · simp
  · simp only [Nat.zero_add, esymm_one, sum_cons, ← add_assoc, hsum, le_refl]
  · calc
      _ = s.esymm (k + 2) + (a + b) * s.esymm (k + 1) + a * b * s.esymm k := by
        simp only [esymm_cons]; ring
      _ ≤ s.esymm (k + 2) + (c + d) * s.esymm (k + 1) + c * d * s.esymm k := by
        rw [hsum]
        exact add_le_add_right (mul_le_mul_of_nonneg_right hprod (esymm_nonneg hs k)) _
      _ = _ := by simp only [esymm_cons]; ring

/-- Replacing a nonnegative multiset by a constant multiset of the same size and sum can only
increase its elementary symmetric functions. -/
theorem esymm_le_esymm_replicate_of_sum_eq {R : Type*} [CommRing R] [LinearOrder R]
    [IsOrderedRing R] {s : Multiset R} {c : R} (hs : ∀ a ∈ s, 0 ≤ a)
    (hc : s.sum = (s.card : R) * c) (k : ℕ) : s.esymm k ≤ (replicate s.card c).esymm k := by
  classical
  induction hn : (s.filter (· ≠ c)).card using Nat.strong_induction_on generalizing s with
  | ind n ih =>
    by_cases hall : ∀ a ∈ s, a = c
    · exact le_of_eq (congrArg (fun t ↦ esymm t k) (s.eq_replicate_of_mem hall))
    -- Unless all entries are equal, equality of sums forces an entry on each side of `c`.
    have hlt : ∃ a ∈ s, a < c := by
      by_contra! h
      push Not at hall
      obtain ⟨a, ha, hne⟩ := hall
      have hstrict := sum_lt_sum (f := fun _ : R ↦ c) (g := id) h
        ⟨a, ha, lt_of_le_of_ne (h a ha) hne.symm⟩
      simp [map_const', sum_replicate, nsmul_eq_mul, hc] at hstrict
    have hgt : ∃ b ∈ s, c < b := by
      by_contra! h
      obtain ⟨a, ha, hac⟩ := hlt
      have hstrict := sum_lt_sum (f := id) (g := fun _ : R ↦ c) h ⟨a, ha, hac⟩
      simp [map_const', sum_replicate, nsmul_eq_mul, hc] at hstrict
    obtain ⟨a, ha, hac⟩ := hlt
    obtain ⟨b, hb, hcb⟩ := hgt
    obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
    have hba : b ≠ a := (hac.trans hcb).ne'
    obtain ⟨u, rfl⟩ := exists_cons_of_mem ((mem_cons.mp hb).resolve_left hba)
    let d := a + b - c
    have hsum : a + b = c + d := by dsimp [d]; ring
    have ha₀ := hs a (mem_cons_self _ _)
    have hd : a ≤ d := le_sub_iff_add_le.mpr (add_le_add_right hcb.le a)
    -- The pair product increases by `(c - a) * (b - c)`.
    have hp : a * b ≤ c * d := by
      rw [← sub_nonneg]
      convert mul_nonneg (sub_nonneg.mpr hac.le) (sub_nonneg.mpr hcb.le) using 1
      dsimp [d]
      ring
    have hu : ∀ x ∈ u, 0 ≤ x := fun x hx ↦ hs x (mem_cons_of_mem (mem_cons_of_mem hx))
    have hnew : ∀ x ∈ c ::ₘ d ::ₘ u, 0 ≤ x := by
      simpa only [mem_cons, forall_eq_or_imp] using
        And.intro (ha₀.trans hac.le) (And.intro (ha₀.trans hd) hu)
    have hcard : ((c ::ₘ d ::ₘ u).filter (· ≠ c)).card < n := by
      rw [← hn]
      rw [filter_cons_of_neg _ (p := (· ≠ c)) (by simp),
        filter_cons_of_pos _ (p := (· ≠ c)) hac.ne,
        filter_cons_of_pos _ (p := (· ≠ c)) hcb.ne']
      by_cases hdc : d = c <;> simp [hdc]
    refine (esymm_cons_cons_le hu hsum hp k).trans ?_
    simpa only [card_cons] using ih _ hcard hnew (by
      simp only [sum_cons, card_cons] at hc ⊢
      rw [← add_assoc, ← hsum, add_assoc, hc]) rfl

/-- **Maclaurin's bound.** The `k`th elementary symmetric function of nonnegative entries is
at most the number of `k`-element subsets times the `k`th power of their arithmetic mean. -/
theorem esymm_le_choose_mul_mean_pow {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Multiset R) (hs : ∀ a ∈ s, 0 ≤ a) (k : ℕ) :
    s.esymm k ≤ (s.card.choose k : R) * (s.sum / s.card) ^ k := by
  rcases eq_or_ne s 0 with rfl | hne
  · rcases k with _ | k
    · simp
    · rw [esymm_of_card_lt (by simp : card (0 : Multiset R) < k + 1)]
      simp
  rw [← esymm_replicate]
  apply esymm_le_esymm_replicate_of_sum_eq hs
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (mt card_eq_zero.mp hne))]

end Multiset
