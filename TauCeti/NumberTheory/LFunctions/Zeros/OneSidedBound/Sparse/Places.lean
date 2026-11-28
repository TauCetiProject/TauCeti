/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TowerUnits
import TauCeti.Combinatorics.Additive.NoRelation
import TauCeti.Data.ZMod.SignedPowers
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Sparse.Exponents

/-!
# Sparse sets of cyclotomic place labels

`Parameters.IsSparse` excludes pairs of short signed prime powers between labels after
reduction away from the prime. `Parameters.exists_sparse_tower_places` and
`Parameters.exists_large_sparse_tower_places` give sets of labels of class `-1` with explicit
cardinality bounds. The labels are powers of `Parameters.towerUnit` with exponents from
modular Behrend sets. The obstructions to the signed powers are
`ZMod.not_exists_signed_two_pow_relation` and `ZMod.not_exists_signed_pow_relations`.

The construction follows `New.Parameters.exists_large_isSparse` and
`New.Parameters.exists_isSparse` in `grh/src/New/Reduction/Data/Existence.lean` of the shorter
GRH formalization (<https://github.com/lsernau/grh-lean>, commit `72fead1`,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Finset Nat

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- A set of cyclotomic place labels is sparse up to `L` if, after reducing away from each
prime `p ≤ L`, no two distinct positive powers of `p` of exponent less than `l₀ s`, with
either sign, carry one label of the set to two labels of the set. The three labels may coincide.
The relations are written after multiplication by the common starting label. -/
structure IsSparse {s : ℕ} (L : ℕ) (S : Set (ZMod (P.q₁ s))ˣ) : Prop where
  /-- The two signed-power relations cannot hold simultaneously in the prime-to-`p` part. -/
  not_signed_pow_pair :
    ∀ ⦃p i j : ℕ⦄, p.Prime → p ≤ L → 0 < i → i < j → j < l₀ s →
      ∀ ⦃x y z : (ZMod (P.q₁ s))ˣ⦄, x ∈ S → y ∈ S → z ∈ S →
      ∀ ⦃e f : ℤ⦄, (e = 1 ∨ e = -1) → (f = 1 ∨ f = -1) →
        ¬ (ZMod.cast (y : ZMod (P.q₁ s)) =
            (e : ZMod (ordCompl[p] (P.q₁ s))) * p ^ i * ZMod.cast (x : ZMod (P.q₁ s)) ∧
          ZMod.cast (z : ZMod (P.q₁ s)) =
            (f : ZMod (ordCompl[p] (P.q₁ s))) * p ^ j * ZMod.cast (x : ZMod (P.q₁ s)))

/-- The empty set of place labels is sparse at every prime bound. -/
@[simp] theorem isSparse_empty {s L : ℕ} : P.IsSparse L (∅ : Set (ZMod (P.q₁ s))ˣ) := by
  constructor
  simp only [Set.mem_empty_iff_false, false_implies, implies_true]

-- The signed-power lemmas work even for signs that are arbitrary square roots of one.
private theorem not_exists_signed_pow_towerUnit {s p i j a b c : ℕ}
    (hp : p.Prime) (hi : 0 < i) (hij : i ≤ j) (hil : i < l₀ s)
    (hsize : 2 * i * (p + 1) < 2 ^ s)
    (hmean : (2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) → a = b) :
    ¬ ∃ e f : ZMod (ordCompl[p] (P.q₁ s)), e ^ 2 = 1 ∧ f ^ 2 = 1 ∧
      (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s)) : ZMod (ordCompl[p] (P.q₁ s))) ^ b =
        e * p ^ i * (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s))) ^ a ∧
      (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s)) : ZMod (ordCompl[p] (P.q₁ s))) ^ c =
        f * p ^ j * (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s))) ^ a := by
  have hc : (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s)) : ZMod (ordCompl[p] (P.q₁ s))) =
      1 + (3 * l₀ s * P.q₀ : ℕ) := by
    rw [P.coe_towerUnit, ZMod.cast_add (Nat.ordCompl_dvd _ _),
      ZMod.cast_one (Nat.ordCompl_dvd _ _), ZMod.cast_natCast (Nat.ordCompl_dvd _ _)]
  by_cases hp₂ : p = 2
  · subst p
    have hd : 3 ^ (Nat.log 3 s + 4 + 1) ∣ ordCompl[2] (P.q₁ s) := by
      apply Nat.dvd_ordCompl_of_dvd_not_dvd
      · rw [P.q₁_def, towerDeg_eq]
        exact (dvd_mul_right _ _).trans (dvd_mul_left _ _)
      · exact fun h ↦ (by decide : ¬2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow h)
    have hg : ZMod.castHom hd (ZMod (3 ^ (Nat.log 3 s + 4 + 1)))
        (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s))) = 1 := by
      rw [hc, map_add, map_one, map_natCast]
      have hz : ((3 * l₀ s * P.q₀ : ℕ) : ZMod (3 ^ (Nat.log 3 s + 4 + 1))) = 0 := by
        rw [ZMod.natCast_eq_zero_iff, pow_succ', ← l₀_def]
        exact dvd_mul_right _ _
      rw [hz, add_zero]
    rintro ⟨e, _, he, _, hb, _⟩
    exact ZMod.not_exists_signed_two_pow_relation hd hg hi (l₀_def s ▸ hil) ⟨e, he, hb⟩
  · have h₄ : 4 ∣ 3 * l₀ s * P.q₀ :=
      dvd_mul_of_dvd_right ((by norm_num : 4 ∣ 18480).trans P.dvd_q₀) _
    obtain ⟨m, hm⟩ := h₄
    have hm₀ : m ≠ 0 := by
      have hpos : 0 < 3 * l₀ s * P.q₀ := by rw [l₀_def]; exact Nat.mul_pos (by positivity) P.q₀_pos
      omega
    obtain ⟨v, u, hu, hm'⟩ := Nat.exists_eq_two_pow_mul_odd hm₀
    have hbase : 3 * l₀ s * P.q₀ = 2 ^ (v + 2) * u := by
      rw [hm, hm', pow_add, (by decide : (2 : ℕ) ^ 2 = 4)]
      ac_rfl
    have hd : 2 ^ (s + (v + 2)) ∣ ordCompl[p] (P.q₁ s) := by
      apply Nat.dvd_ordCompl_of_dvd_not_dvd
      · rw [P.q₁_def, towerDeg_def, ← mul_assoc, mul_comm P.q₀]
        rw [hbase, pow_add]
        exact ⟨u, by ac_rfl⟩
      · exact fun h ↦ hp₂ (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h)
    rw [hc, hbase]
    push_cast
    exact ZMod.not_exists_signed_pow_relations hu hd hp.one_lt hi hij hsize hmean

/-- The image of a modular weighted-mean-free set of exponents under `a ↦ -g ^ a` is sparse
up to `L`, provided `2 * l₀ s * (L + 1) < 2 ^ s`. -/
theorem isSparse_image_neg_pow_towerUnit {s L : ℕ} {A : Set ℕ}
    (hsize : 2 * l₀ s * (L + 1) < 2 ^ s)
    (hmean : ∀ ⦃a b c : ℕ⦄, a ∈ A → b ∈ A → c ∈ A →
      ∀ ⦃u v : ℕ⦄, 0 < u → 0 < v → u + v ≤ 2 * l₀ s →
        (u + v) * b ≡ u * a + v * c [MOD 2 ^ s] → a = b) :
    P.IsSparse L ((fun a : ℕ ↦ -(P.towerUnit s ^ a)) '' A) := by
  constructor
  intro p i j hp hpL hi hij hj x y z hx hy hz e f he hf
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨c, hc, rfl⟩ := hz
  have hsum : 2 * (j - i) + 2 * i = 2 * j := by lia
  have hm (h : 2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) : a = b :=
    hmean ha hb hc (u := 2 * (j - i)) (v := 2 * i) (by lia) (by lia) (by lia) (by rwa [hsum])
  have hd := Nat.ordCompl_dvd (P.q₁ s) p
  have hsign (t : ℤ) (ht : t = 1 ∨ t = -1) :
      (t : ZMod (ordCompl[p] (P.q₁ s))) ^ 2 = 1 := by
    rcases ht with rfl | rfl <;> simp
  rintro ⟨h₁, h₂⟩
  simp only [Units.val_neg, Units.val_pow_eq_pow_val, ZMod.cast_neg hd, ZMod.cast_pow hd,
    mul_neg, neg_inj] at h₁ h₂
  have hbudget : 2 * i * (p + 1) < 2 ^ s := lt_of_le_of_lt (by gcongr; lia) hsize
  exact P.not_exists_signed_pow_towerUnit hp hi hij.le (hij.trans hj) hbudget hm
    ⟨e, f, hsign e he, hsign f hf, h₁, h₂⟩

-- Both cardinality estimates use the same injective map into the negative place class.
private theorem exists_sparse_tower_places_of_exponents {s L : ℕ} {A : Finset ℕ}
    (hsize : 2 * l₀ s * (L + 1) < 2 ^ s)
    (hmean : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ u v : ℕ, 0 < u → 0 < v →
      u + v ≤ 2 * l₀ s → (u + v) * b ≡ u * a + v * c [MOD 2 ^ s] → a = b) :
    ∃ S : Finset (ZMod (P.q₁ s))ˣ, P.IsSparse L (S : Set (ZMod (P.q₁ s))ˣ) ∧
      (∀ x ∈ S, ZMod.unitsMap (P.q₀_dvd_q₁ s) x = -1) ∧ S.card = A.card := by
  refine ⟨A.image (fun a ↦ -(P.towerUnit s ^ a)), ?_, ?_, ?_⟩
  · rw [Finset.coe_image]
    apply P.isSparse_image_neg_pow_towerUnit hsize
    exact fun a b c ha hb hc u v hu hv huv h ↦ hmean a ha b hb c hc u v hu hv huv h
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact P.unitsMap_neg_pow_towerUnit (dvd_mul_left _ _) (P.q₀_dvd_q₁ s) a
  · apply Finset.card_image_of_injOn
    intro a ha b hb h
    have hp := neg_injective h
    rw [pow_eq_pow_iff_modEq, P.orderOf_towerUnit] at hp
    exact hmean a ha b hb a ha 1 1 one_pos one_pos (by have := lt_l₀ s; lia)
      (by simpa only [one_add_one_eq_two, one_mul, two_mul] using hp.symm.add hp.symm)

/-- At a fixed digit box there exists a sparse set of labels of class `-1` with at least
`H ^ n / (n * H ^ 2)` elements. -/
theorem exists_sparse_tower_places {s n H L : ℕ} (hfit : (2 * l₀ s * H) ^ n ≤ 2 ^ s)
    (hsize : 2 * l₀ s * (L + 1) < 2 ^ s) :
    ∃ S : Finset (ZMod (P.q₁ s))ˣ, P.IsSparse L (S : Set (ZMod (P.q₁ s))ˣ) ∧
      (∀ x ∈ S, ZMod.unitsMap (P.q₀_dvd_q₁ s) x = -1) ∧
      (H : ℝ) ^ n / ((n : ℝ) * (H : ℝ) ^ 2) ≤ S.card := by
  have hpos : 0 < 2 * l₀ s := by rw [l₀_def]; positivity
  obtain ⟨A, _, hcard, hmean⟩ := exists_eq_and_eq_of_add_mul_modEq hpos hfit
  obtain ⟨S, hS, hclass, hcard'⟩ := P.exists_sparse_tower_places_of_exponents hsize
    (fun a ha b hb c hc u v hu hv huv h ↦ (hmean a ha b hb c hc u v hu hv huv h).1)
  refine ⟨S, hS, hclass, ?_⟩
  rw [hcard']
  push_cast at hcard
  exact hcard

/-- If a digit box of dimension `n + 1` costs at most `W` and `2 ^ s ≤ W ^ (n + 2)`,
there is a sparse set of labels of class `-1` whose cardinality times `W ^ 6` covers the tower
degree. -/
theorem exists_large_sparse_tower_places {s n L : ℕ} {W : ℝ}
    (ho : (2 : ℝ) ^ s ≤ W ^ (n + 2)) (hbase : (2 * (l₀ s : ℝ)) ^ (n + 1) ≤ W)
    (hsize : 2 * l₀ s * (L + 1) < 2 ^ s) :
    ∃ S : Finset (ZMod (P.q₁ s))ˣ, P.IsSparse L (S : Set (ZMod (P.q₁ s))ˣ) ∧
      (∀ x ∈ S, ZMod.unitsMap (P.q₀_dvd_q₁ s) x = -1) ∧
      (towerDeg s : ℝ) ≤ S.card * W ^ 6 := by
  obtain ⟨A, _, hcard, hmean⟩ := exists_large_sparse_exponents (Nat.succ_pos n) ho hbase
  obtain ⟨S, hS, hclass, hcard'⟩ := P.exists_sparse_tower_places_of_exponents hsize
    (fun a ha b hb c hc u v hu hv huv h ↦ (hmean a ha b hb c hc u v hu hv huv h).1)
  exact ⟨S, hS, hclass, by rwa [hcard']⟩

end TauCeti.OneSidedBound.Parameters
