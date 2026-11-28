/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TowerUnits
import TauCeti.Combinatorics.Additive.NoRelation
import TauCeti.Data.ZMod.SignedPowers
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.SparseExponents

/-!
# Large sparse sets of cyclotomic place labels

Sparse sets of labels avoid two distinct short signed prime-power ratios from the same
label, even after removing the prime part of the modulus. The negative powers of a
cyclotomic tower unit transport a modular Behrend set to a sparse set in the class `-1`.
The cardinality estimate provides the place budget for the short cutoff in a two-cutoff
prime sum.

The construction follows the mathematical argument of `New.Parameters.exists_large_isSparse`
and `New.Parameters.exists_isSparse` in `grh/src/New/Reduction/Data/Existence.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Finset

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- A set of cyclotomic place labels is sparse up to `L` if, for each prime `p ≤ L`, there are
no two ratios from a common label in the set that are signed powers `p ^ i` and `p ^ j`, with
`0 < i < j < l₀ s`, modulo the prime-to-`p` part of the tower modulus. The three labels need not
be distinct. -/
def IsSparse (s L : ℕ) (B : Finset (ZMod (P.q₁ s))ˣ) : Prop :=
  ∀ p ≤ L, p.Prime → ∀ i j : ℕ, 0 < i → i < j → j < l₀ s →
    let M := ordCompl[p] (P.q₁ s)
    let red := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod M)
    ∀ σ ∈ B, ∀ τ ∈ B, ∀ ρ ∈ B,
      ¬ ∃ ε ε' : ZMod M, (ε = 1 ∨ ε = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧
        red τ = ε * (p : ZMod M) ^ i * red σ ∧
        red ρ = ε' * (p : ZMod M) ^ j * red σ

/-- The test for sparsity in terms of simultaneous signed power relations on reduced labels. -/
theorem isSparse_iff {s L : ℕ} {B : Finset (ZMod (P.q₁ s))ˣ} :
    P.IsSparse s L B ↔
      ∀ p ≤ L, p.Prime → ∀ i j : ℕ, 0 < i → i < j → j < l₀ s →
        let M := ordCompl[p] (P.q₁ s)
        let red := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod M)
        ∀ σ ∈ B, ∀ τ ∈ B, ∀ ρ ∈ B,
          ¬ ∃ ε ε' : ZMod M, (ε = 1 ∨ ε = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧
            red τ = ε * (p : ZMod M) ^ i * red σ ∧
            red ρ = ε' * (p : ZMod M) ^ j * red σ := (Iff.rfl)

private theorem not_exists_towerUnit_signed_powers {s p i j a b c : ℕ} (hp : p.Prime)
    (hi : 0 < i) (hij : i < j) (hj : j < l₀ s) (hsize : 2 * i * (p + 1) < 2 ^ s)
    (hmean : (2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) → a = b) :
    let M := ordCompl[p] (P.q₁ s)
    let g := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod M) (P.towerUnit s)
    ¬ ∃ ε ε' : ZMod M, ε ^ 2 = 1 ∧ ε' ^ 2 = 1 ∧
      g ^ b = ε * (p : ZMod M) ^ i * g ^ a ∧ g ^ c = ε' * (p : ZMod M) ^ j * g ^ a := by
  intro M g
  have hg : g = 1 + (3 * l₀ s * P.q₀ : ℕ) := by
    simp only [g, coe_towerUnit, map_add, map_one, map_natCast]
  rcases eq_or_ne p 2 with rfl | hp₂
  · let r := Nat.log 3 s + 4
    have h₃ : 3 ^ (r + 1) = 3 * l₀ s := by rw [l₀_def, ← pow_succ']
    have hd : 3 ^ (r + 1) ∣ M := Nat.dvd_ordCompl_of_dvd_not_dvd
      (by rw [q₁_def, towerDeg_def, h₃]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
      ((by decide : Odd (3 : ℕ)).pow.not_two_dvd_nat)
    have hz : ((3 * l₀ s * P.q₀ : ℕ) : ZMod (3 ^ (r + 1))) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (by rw [h₃]; exact dvd_mul_right _ _)
    have hred : ZMod.castHom hd (ZMod (3 ^ (r + 1))) g = 1 := by
      simp only [hg, map_add, map_one, map_natCast, hz, add_zero]
    rintro ⟨ε, _, hε, _, hb, _⟩
    have hir : i < 3 ^ r := (hij.trans hj).trans_le (by rw [l₀_def])
    exact ZMod.not_exists_signed_two_pow_relation hd hred hi hir ⟨ε, hε, hb⟩
  · have hbase : 0 < 3 * l₀ s * P.q₀ := by
      have := P.q₀_pos
      rw [l₀_def]
      positivity
    obtain ⟨v, u, hu, hbase_eq⟩ := Nat.exists_eq_two_pow_mul_odd hbase.ne'
    have hv : 2 ≤ v := by
      have h₄ : 4 ∣ 3 * l₀ s * P.q₀ :=
        dvd_mul_of_dvd_right ((by norm_num : 4 ∣ 18480).trans P.dvd_q₀) _
      rw [hbase_eq] at h₄
      have hc : Nat.Coprime (4 : ℕ) u := by
        simpa [show (4 : ℕ) = 2 ^ 2 by decide] using
          (Nat.prime_two.coprime_iff_not_dvd.mpr hu.not_two_dvd_nat).pow_left 2
      exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp (hc.dvd_of_dvd_mul_right h₄)
    have hv' : v - 2 + 2 = v := by omega
    have hd : 2 ^ (s + v) ∣ M := Nat.dvd_ordCompl_of_dvd_not_dvd (by
      have hvdvd : 2 ^ v ∣ 3 * l₀ s * P.q₀ := ⟨u, hbase_eq⟩
      rw [q₁_def, towerDeg_def, pow_add]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_dvd_mul_left (2 ^ s) hvdvd)
      (fun h ↦ hp₂ ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow h)).symm)
    have hg' : g = 1 + 2 ^ (v - 2 + 2) * u := by
      simp only [hg, hv', hbase_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hg']
    exact ZMod.not_exists_signed_pow_relations hu (by rwa [hv']) hp.one_lt hi hij.le hsize hmean

-- Transport the exponents without losing cardinality, and use the two residual moduli to
-- rule out the signed relations even when all three labels coincide.
private theorem exists_sparse_places_of_exponents {s L : ℕ} (S : Finset ℕ)
    (hS : ∀ e ∈ S, e < 2 ^ s) (hL : 2 * l₀ s * (L + 1) < 2 ^ s)
    (hmean : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ u v : ℕ, 0 < u → 0 < v → u + v ≤ 2 * l₀ s →
      (u + v) * b ≡ u * a + v * c [MOD 2 ^ s] → a = b) :
    ∃ B : Finset (ZMod (P.q₁ s))ˣ, #B = #S ∧
      (∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1) ∧ P.IsSparse s L B := by
  classical
  let B := S.image fun e ↦ -(P.towerUnit s ^ e)
  have hcard : #B = #S := card_image_of_injOn (fun e he f hf ↦
    P.injOn_neg_pow_towerUnit s (hS e he) (hS f hf))
  refine ⟨B, hcard, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨e, _, rfl⟩ := mem_image.mp hτ
    exact P.unitsMap_neg_pow_towerUnit (dvd_mul_left _ _) (P.q₀_dvd_q₁ s) e
  · rw [P.isSparse_iff]
    intro p hpL hp i j hi hij hj M red σ hσ τ hτ ρ hρ
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hσ
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hτ
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hρ
    rintro ⟨ε, ε', hε, hε', h₁, h₂⟩
    have sign_sq (e : ZMod M) (he : e = 1 ∨ e = -1) : e ^ 2 = 1 := by
      rcases he with rfl | rfl <;> simp
    have hs : 2 * i * (p + 1) < 2 ^ s :=
      lt_of_le_of_lt (by gcongr; omega) hL
    have hweights : 2 * (j - i) + 2 * i = 2 * j := by omega
    have hm (h : 2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) : a = b :=
      hmean a ha b hb c hc (2 * (j - i)) (2 * i) (by omega) (by omega) (by omega)
        (by rwa [hweights])
    apply P.not_exists_towerUnit_signed_powers hp hi hij hj hs hm
    refine ⟨ε, ε', sign_sq _ hε, sign_sq _ hε', ?_, ?_⟩
    · simpa only [red, Units.val_neg, Units.val_pow_eq_pow_val, map_neg, map_pow,
        mul_neg, neg_inj] using h₁
    · simpa only [red, Units.val_neg, Units.val_pow_eq_pow_val, map_neg, map_pow,
        mul_neg, neg_inj] using h₂

/-- A fitting Behrend digit box yields a sparse set of class `-1` with at least as many labels
as the largest sphere guaranteed by the box count. The inequality uses real cardinalities,
without truncating the lower bound. -/
theorem exists_sparse_places_of_digit_bound {s L n H : ℕ}
    (hfit : (2 * l₀ s * H) ^ n ≤ 2 ^ s) (hL : 2 * l₀ s * (L + 1) < 2 ^ s) :
    ∃ B : Finset (ZMod (P.q₁ s))ˣ, (H : ℝ) ^ n / (n * H ^ 2) ≤ #B ∧
      (∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1) ∧ P.IsSparse s L B := by
  have hℓ : 0 < 2 * l₀ s := by rw [l₀_def]; positivity
  obtain ⟨S, hS, hcard, hmean⟩ := exists_eq_and_eq_of_add_mul_modEq hℓ hfit
  obtain ⟨B, hB, hclass, hsparse⟩ := P.exists_sparse_places_of_exponents S hS hL
    fun a ha b hb c hc u v hu hv huv h ↦ (hmean a ha b hb c hc u v hu hv huv h).1
  exact ⟨B, by simpa only [hB, Nat.cast_mul, Nat.cast_pow] using hcard, hclass, hsparse⟩

/-- In the class `-1` of the cyclotomic tower there is a set sparse up to `L` whose size,
multiplied by the loss factor `W ^ 6`, covers the tower degree. -/
theorem exists_large_sparse_places {s L n : ℕ} {W : ℝ}
    (ho : (2 : ℝ) ^ s ≤ W ^ (n + 1)) (hbase : (2 * (l₀ s : ℝ)) ^ n ≤ W)
    (hL : 2 * l₀ s * (L + 1) < 2 ^ s) :
    ∃ B : Finset (ZMod (P.q₁ s))ˣ, (towerDeg s : ℝ) ≤ #B * W ^ 6 ∧
      (∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1) ∧ P.IsSparse s L B := by
  have hexps : ∃ k > 0, (2 : ℝ) ^ s ≤ W ^ (k + 1) ∧ (2 * (l₀ s : ℝ)) ^ k ≤ W := by
    by_cases hn : 0 < n
    · exact ⟨n, hn, ho, hbase⟩
    · have hW : 1 ≤ W := by simpa [Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hn)] using hbase
      have h₂ : (2 : ℝ) ^ s ≤ W := by
        simpa [Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hn)] using ho
      have hℓ : 2 * l₀ s ≤ 2 ^ s :=
        le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos L)) hL.le
      refine ⟨1, Nat.one_pos, h₂.trans (le_self_pow₀ hW (by decide)), ?_⟩
      rw [pow_one]
      exact (by exact_mod_cast hℓ : 2 * (l₀ s : ℝ) ≤ 2 ^ s).trans h₂
  obtain ⟨k, hk, ho', hbase'⟩ := hexps
  obtain ⟨S, hS, hcard, hmean⟩ := exists_large_sparse_exponents hk ho' hbase'
  obtain ⟨B, hB, hclass, hsparse⟩ := P.exists_sparse_places_of_exponents S hS hL
    fun a ha b hb c hc u v hu hv huv h ↦ (hmean a ha b hb c hc u v hu hv huv h).1
  exact ⟨B, hB ▸ hcard, hclass, hsparse⟩

end TauCeti.OneSidedBound.Parameters
