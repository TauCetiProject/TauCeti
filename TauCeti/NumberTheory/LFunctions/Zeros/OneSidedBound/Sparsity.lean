/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TowerUnits
import Mathlib.Data.Int.Order.Units
import TauCeti.Combinatorics.Additive.NoRelation
import TauCeti.Data.ZMod.SignedPowers

/-!
# Sparse families of cyclotomic place labels

`Parameters.IsSparse` excludes two short signed prime-power ratios from a common label
after removing the prime part of the modulus. `Parameters.exists_large_sparse_place_labels`
constructs a family of class `-1` modulo `q₀` with the cardinality bound of a Behrend digit box.
Under the identification of unit labels with the infinite places of the cyclotomic extension,
these families provide candidates for the set `Φ_b` of places assigned weight `b` in the
admissible data for the one-sided prime sum bound. The cardinality bound helps meet the size
requirement on `Φ_b` while preserving sparsity up to the required prime cutoff.

The cardinality bound comes from `exists_eq_and_eq_of_add_mul_modEq` and is preserved on passing
to labels by `Parameters.injOn_neg_pow_towerUnit`.

The sparsity condition and construction follow `New.Parameters.IsSparse` in
`grh/src/New/Reduction/Data/AdmissibleData.lean` and `New.Parameters.exists_large_isSparse` in
`grh/src/New/Reduction/Data/Existence.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207)
(Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section
open Finset

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- A family of labels is sparse up to `L` if no label in it admits both signed prime-power
ratios with exponents `0 < i < j < l₀ s` to labels in the family, modulo the prime-to-`p`
part of the level for any prime `p ≤ L`. The three labels may coincide. -/
def IsSparse (s L : ℕ) (S : Set (ZMod (P.q₁ s))ˣ) : Prop :=
  ∀ ⦃p : ℕ⦄, p.Prime → p ≤ L → ∀ ⦃i j : ℕ⦄, 0 < i → i < j → j < l₀ s →
    ∀ σ ∈ S, ∀ τ ∈ S, ∀ ρ ∈ S, ¬ ∃ ε ε' : ℤˣ,
      (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) τ : ZMod (ordCompl[p] (P.q₁ s))) =
        (ε : ℤ) * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ i *
          (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) σ : ZMod (ordCompl[p] (P.q₁ s))) ∧
      (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) ρ : ZMod (ordCompl[p] (P.q₁ s))) =
        (ε' : ℤ) * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ j *
          (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) σ : ZMod (ordCompl[p] (P.q₁ s)))

-- Keep the quantified defining formula out of the simp set.
/-- Sparsity expressed as exclusion of signed-power relations in the reduced residue ring. -/
theorem isSparse_iff {P : Parameters} {s L : ℕ} {S : Set (ZMod (P.q₁ s))ˣ} :
    P.IsSparse s L S ↔
      ∀ ⦃p : ℕ⦄, p.Prime → p ≤ L → ∀ ⦃i j : ℕ⦄, 0 < i → i < j → j < l₀ s →
        ∀ σ ∈ S, ∀ τ ∈ S, ∀ ρ ∈ S, ¬ ∃ ε ε' : ℤˣ,
          (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) τ : ZMod (ordCompl[p] (P.q₁ s))) =
            (ε : ℤ) * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ i *
              (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) σ : ZMod (ordCompl[p] (P.q₁ s))) ∧
          (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) ρ : ZMod (ordCompl[p] (P.q₁ s))) =
            (ε' : ℤ) * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ j *
              (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) σ : ZMod (ordCompl[p] (P.q₁ s))) :=
  (Iff.rfl)

/-- Sparsity is preserved by passing to a subset and lowering the prime cutoff. -/
theorem IsSparse.mono {P : Parameters} {s L L' : ℕ} {S T : Set (ZMod (P.q₁ s))ˣ}
    (h : P.IsSparse s L' T) (hST : S ⊆ T) (hL : L ≤ L') : P.IsSparse s L S := by
  rw [isSparse_iff] at h ⊢
  intro p hp hpL i j hi hij hj σ hσ τ hτ ρ hρ
  exact h hp (hpL.trans hL) hi hij hj σ (hST hσ) τ (hST hτ) ρ (hST hρ)

/-- The empty family is sparse for every prime cutoff. -/
@[simp] theorem isSparse_empty (s L : ℕ) : P.IsSparse s L ∅ := by
  simp only [isSparse_iff, Set.mem_empty_iff_false, false_implies, implies_true]

-- This specialization supplies the prime-two branch of the tower sparsity proof.
-- The general exclusion is `ZMod.not_exists_signed_two_pow_relation`.
private theorem not_exists_signed_two_pow_towerUnit {s i a b : ℕ}
    (hi : 0 < i) (hir : i < l₀ s) :
    ¬ ∃ ε : ZMod (ordCompl[2] (P.q₁ s)), ε ^ 2 = 1 ∧
      (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s)) : ZMod (ordCompl[2] (P.q₁ s))) ^ b =
        ε * 2 ^ i * (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s)) :
          ZMod (ordCompl[2] (P.q₁ s))) ^ a := by
  rw [← ZMod.castHom_apply (h := Nat.ordCompl_dvd (P.q₁ s) 2)]
  let f := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) 2) (ZMod (ordCompl[2] (P.q₁ s)))
  let g := f (P.towerUnit s : ZMod (P.q₁ s))
  have hb₃ : 3 ^ (Nat.log 3 s + 4 + 1) ∣ 3 * l₀ s * P.q₀ := by
    rw [pow_succ, l₀_def, mul_comm _ 3]
    exact dvd_mul_right _ _
  have hq : 3 * l₀ s * P.q₀ ∣ P.q₁ s := ⟨_, P.q₁_eq_base_mul_two_pow s⟩
  have h₂ : ¬ 2 ∣ 3 ^ (Nat.log 3 s + 4 + 1) := fun h ↦
    (by decide : (2 : ℕ) ≠ 3) (Nat.prime_eq_prime_of_dvd_pow Nat.prime_two Nat.prime_three h)
  have hd := Nat.dvd_ordCompl_of_dvd_not_dvd (hb₃.trans hq) h₂
  have hg : ZMod.castHom hd (ZMod (3 ^ (Nat.log 3 s + 4 + 1))) g = 1 := by
    dsimp only [g, f]
    rw [← RingHom.comp_apply, ZMod.castHom_comp, ZMod.castHom_apply]
    have h := (P.unitsMap_towerUnit_eq_one_iff
      (hd.trans (Nat.ordCompl_dvd (P.q₁ s) 2))).mpr hb₃
    simpa only [ZMod.unitsMap_val, Units.val_one] using congrArg Units.val h
  exact ZMod.not_exists_signed_two_pow_relation hd hg hi (by simpa only [l₀_def] using hir)

/-- The negative tower-unit powers indexed by a set with no nontrivial short modular mean
are sparse for every prime cutoff satisfying the displayed dyadic bound. -/
theorem isSparse_neg_pow_towerUnit_image {s L : ℕ} {S : Set ℕ}
    (hsize : 2 * l₀ s * (L + 1) < 2 ^ s)
    (hmean : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ i j : ℕ, 0 < i → 0 < j → i + j ≤ 2 * l₀ s →
      (i + j) * b ≡ i * a + j * c [MOD 2 ^ s] → a = b) :
    P.IsSparse s L ((fun e ↦ -(P.towerUnit s ^ e)) '' S) := by
  rw [isSparse_iff]
  rintro p hp hpL i j hi hij hj _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    ⟨ε, ε', hab, hac⟩
  let f := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod (ordCompl[p] (P.q₁ s)))
  let g := f (P.towerUnit s : ZMod (P.q₁ s))
  have hε (u : ℤˣ) : ((u : ℤ) : ZMod (ordCompl[p] (P.q₁ s))) ^ 2 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, Int.cast_pow, Int.cast_one] using
      congrArg (fun x : ℤˣ ↦ ((x : ℤ) : ZMod (ordCompl[p] (P.q₁ s)))) (Int.units_sq u)
  have hlabel (e : ℕ) :
      (ZMod.unitsMap (Nat.ordCompl_dvd (P.q₁ s) p) (-(P.towerUnit s ^ e)) :
        ZMod (ordCompl[p] (P.q₁ s))) = -(g ^ e) := by
    rw [ZMod.unitsMap_val, ← ZMod.castHom_apply (h := Nat.ordCompl_dvd (P.q₁ s) p)]
    simp only [Units.val_neg, Units.val_pow_eq_pow_val, map_neg, map_pow, g, f]
  simp only [hlabel, mul_neg, neg_inj] at hab hac
  rcases eq_or_ne p 2 with rfl | hp₂
  · exact P.not_exists_signed_two_pow_towerUnit hi (by omega)
      ⟨(ε : ℤ), hε ε, by simpa only [g, f, ZMod.castHom_apply, Nat.cast_ofNat] using hab⟩
  · obtain ⟨m, hm⟩ := P.four_dvd_towerUnit_base s
    have hpos : 0 < 3 * l₀ s * P.q₀ := by have := P.q₀_pos; rw [l₀_def]; positivity
    have hm₀ : m ≠ 0 := by omega
    obtain ⟨v, u, hu, hmu⟩ := Nat.exists_eq_two_pow_mul_odd hm₀
    have hbase : 3 * l₀ s * P.q₀ = 2 ^ (v + 2) * u := by
      rw [hm, hmu, pow_add]
      norm_num only [Nat.reducePow]
      ac_rfl
    have hd : 2 ^ (s + (v + 2)) ∣ ordCompl[p] (P.q₁ s) := by
      apply Nat.dvd_ordCompl_of_dvd_not_dvd
      · rw [P.q₁_eq_base_mul_two_pow s, hbase, pow_add]
        exact ⟨u, by ac_rfl⟩
      · exact fun h ↦ hp₂ (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h)
    have hg : g = 1 + 2 ^ (v + 2) * u := by
      dsimp only [g]
      rw [coe_towerUnit, hbase, map_add, map_one, map_natCast]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    -- Squaring removes the signs and doubles both weights in the modular mean.
    have hmean' (h : 2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) : a = b := by
      apply hmean a ha b hb c hc (2 * (j - i)) (2 * i) (by omega) (by omega) (by omega)
      have hsum : 2 * (j - i) + 2 * i = 2 * j := by omega
      rwa [hsum]
    exact ZMod.not_exists_signed_pow_relations hu hd hp.one_lt hi hij.le
      ((Nat.mul_le_mul (by omega) (by omega)).trans_lt hsize) hmean'
      ⟨(ε : ℤ), (ε' : ℤ), hε ε, hε ε', hg ▸ hab, hg ▸ hac⟩

/-- For a Behrend digit box of dimension `n` and side length `H` fitting below `2 ^ s`,
there is a sparse family of labels of class `-1` modulo `q₀`, with at least
`H ^ n / (n * H ^ 2)` members. -/
theorem exists_large_sparse_place_labels {s L n H : ℕ} (hbox : (2 * l₀ s * H) ^ n ≤ 2 ^ s)
    (hsize : 2 * l₀ s * (L + 1) < 2 ^ s) :
    ∃ T : Finset (ZMod (P.q₁ s))ˣ, (H : ℝ) ^ n / (n * H ^ 2) ≤ #T ∧ P.IsSparse s L T ∧
      ∀ σ ∈ T, ZMod.unitsMap (P.q₀_dvd_q₁ s) σ = -1 := by
  have hbase : 0 < 2 * l₀ s := by rw [l₀_def]; positivity
  obtain ⟨S, hS, hcard, hmean⟩ := exists_eq_and_eq_of_add_mul_modEq hbase hbox
  classical
  let f := fun e : ℕ ↦ -(P.towerUnit s ^ e)
  have hinj : Set.InjOn f S := (P.injOn_neg_pow_towerUnit s).mono
    (fun e he ↦ Set.mem_Iio.mpr (hS e he))
  refine ⟨S.image f, ?_, ?_, ?_⟩
  · rw [card_image_of_injOn hinj]
    exact_mod_cast hcard
  · rw [coe_image]
    exact P.isSparse_neg_pow_towerUnit_image hsize
      (fun a ha b hb c hc i j hi hj hij h ↦ (hmean a ha b hb c hc i j hi hj hij h).1)
  · intro σ hσ
    obtain ⟨e, _, rfl⟩ := mem_image.mp hσ
    exact P.unitsMap_neg_pow_towerUnit (dvd_mul_left _ _) (P.q₀_dvd_q₁ s) e

end TauCeti.OneSidedBound.Parameters
