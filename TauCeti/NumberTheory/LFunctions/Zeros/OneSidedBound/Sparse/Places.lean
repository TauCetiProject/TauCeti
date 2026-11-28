/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Factorization.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TowerUnits
import TauCeti.Combinatorics.Additive.NoRelation
import TauCeti.Data.ZMod.SignedPowers
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Sparse.Exponents

/-!
# Sparse places in a cyclotomic tower

The infinite places are labelled by units modulo the cyclotomic order `q₁ s`. The negative
powers of the tower unit turn a modular Behrend set into place labels of base class `-1`.
Sparsity rules out two short signed powers of the same prime occurring as ratios from a
single label, after removing that prime's part of the modulus.

The construction follows the mathematical argument of `New.Parameters.exists_large_isSparse`
and `New.Parameters.exists_isSparse` in `grh/src/New/Reduction/Data/Existence.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Finset

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- A set of cyclotomic place labels is sparse up to `L` if, modulo the part of `q₁ s` prime
to each prime `p ≤ L`, two distinct signed powers of `p` with exponents in `(0, l₀ s)` cannot
occur as ratios from the same label. The three labels need not be distinct. -/
def IsSparse (s L : ℕ) (S : Set (ZMod (P.q₁ s))ˣ) : Prop :=
  ∀ ⦃p i j : ℕ⦄, p.Prime → p ≤ L → 0 < i → i < j → j < l₀ s →
    ∀ ⦃σ τ ρ : (ZMod (P.q₁ s))ˣ⦄, σ ∈ S → τ ∈ S → ρ ∈ S →
      let f := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod (ordCompl[p] (P.q₁ s)))
      ¬ ∃ ε ε' : ℤ, (ε = 1 ∨ ε = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧
        f τ = ε * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ i * f σ ∧
        f ρ = ε' * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ j * f σ

/-- Test sparsity by reducing the three labels and clearing the common denominator. -/
theorem isSparse_iff {s L : ℕ} {S : Set (ZMod (P.q₁ s))ˣ} :
    P.IsSparse s L S ↔
      ∀ ⦃p i j : ℕ⦄, p.Prime → p ≤ L → 0 < i → i < j → j < l₀ s →
        ∀ ⦃σ τ ρ : (ZMod (P.q₁ s))ˣ⦄, σ ∈ S → τ ∈ S → ρ ∈ S →
          let f := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod (ordCompl[p] (P.q₁ s)))
          ¬ ∃ ε ε' : ℤ, (ε = 1 ∨ ε = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧
            f τ = ε * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ i * f σ ∧
            f ρ = ε' * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ j * f σ := Iff.rfl

private theorem not_exists_signed_two_pow_towerUnit {s a b i : ℕ}
    (hi : 0 < i) (hil : i < l₀ s) :
    let m := ordCompl[2] (P.q₁ s)
    let f := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) 2) (ZMod m)
    let g := f (P.towerUnit s)
    ¬ ∃ ε : ZMod m, ε ^ 2 = 1 ∧ g ^ b = ε * (2 : ZMod m) ^ i * g ^ a := by
  intro m f g
  have hd₃ : 3 ^ (Nat.log 3 s + 4 + 1) ∣ 3 * l₀ s * P.q₀ := by
    rw [l₀_def, pow_succ']
    exact dvd_mul_right _ _
  have hm₃ : 3 ^ (Nat.log 3 s + 4 + 1) ∣ m := Nat.dvd_ordCompl_of_dvd_not_dvd
    (by rw [q₁_def, towerDeg_def]; exact hd₃.trans ⟨2 ^ s, by ac_rfl⟩)
    ((by decide : ¬ 2 ∣ 3).comp Nat.prime_two.dvd_of_dvd_pow)
  have hg₃ : ZMod.castHom hm₃ (ZMod (3 ^ (Nat.log 3 s + 4 + 1))) g = 1 := by
    dsimp only [g]
    rw [P.coe_towerUnit, map_add, map_one, map_natCast, map_add, map_one, map_natCast,
      (ZMod.natCast_eq_zero_iff _ _).2 hd₃, add_zero]
  exact ZMod.not_exists_signed_two_pow_relation (m := m) hm₃ hg₃ hi
    (by simpa only [l₀_def] using hil)

private theorem isSparse_image_neg_pow_towerUnit {s L : ℕ} {S : Finset ℕ}
    (hsize : 2 * l₀ s * (L + 1) ≤ 2 ^ s)
    (hmean : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ u v : ℕ, 0 < u → 0 < v → u + v ≤ 2 * l₀ s →
      (u + v) * b ≡ u * a + v * c [MOD 2 ^ s] → a = b) :
    P.IsSparse s L ((S.image fun e ↦ -(P.towerUnit s ^ e) : Finset _) : Set _) := by
  classical
  refine P.isSparse_iff.mpr fun p i j hp hpL hi hij hj σ τ ρ hσ hτ hρ ↦ ?_
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hσ
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hτ
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hρ
  let m := ordCompl[p] (P.q₁ s)
  let f := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod m)
  let g := f (P.towerUnit s)
  dsimp only
  rintro ⟨ε, ε', hε, hε', hb', hc'⟩
  have hrelation (e : ℕ) (z : ℤ) (k : ℕ)
      (h : f (-(P.towerUnit s ^ e) : (ZMod (P.q₁ s))ˣ) =
        z * (p : ZMod m) ^ k * f (-(P.towerUnit s ^ a) : (ZMod (P.q₁ s))ˣ)) :
      g ^ e = z * (p : ZMod m) ^ k * g ^ a := by
    simpa only [Units.val_neg, Units.val_pow_eq_pow_val, map_neg, map_pow, mul_neg, neg_inj, g]
      using h
  have hb'' := hrelation b ε i hb'
  have hc'' := hrelation c ε' j hc'
  have hsquare (z : ℤ) (hz : z = 1 ∨ z = -1) : (z : ZMod m) ^ 2 = 1 := by
    rcases hz with rfl | rfl <;> simp
  -- At two, the cubic part alone excludes the first signed power.
  by_cases hp₂ : p = 2
  · subst p
    exact P.not_exists_signed_two_pow_towerUnit hi (lt_trans hij hj)
      ⟨ε, hsquare ε hε, by simpa only [Nat.cast_ofNat] using hb''⟩
  -- At odd primes, the prime-to-`p` modulus retains the whole dyadic part.
  · obtain ⟨v, u, hu, heq⟩ := Nat.exists_eq_two_pow_mul_odd
      (show 3 * l₀ s * P.q₀ ≠ 0 by have := P.q₀_pos; rw [l₀_def]; positivity)
    have h₄ : 2 ^ 2 ∣ 2 ^ v * u := heq ▸
      dvd_mul_of_dvd_right ((by decide : 4 ∣ 18480).trans P.dvd_q₀) _
    have hv : 2 ≤ v := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mp
      ((hu.coprime_two_left.pow_left 2).dvd_of_dvd_mul_right h₄)
    have hm₂ : 2 ^ (s + v) ∣ m := Nat.dvd_ordCompl_of_dvd_not_dvd
      ⟨u, by rw [q₁_def, towerDeg_def, pow_add, ← mul_assoc, mul_comm P.q₀, heq]; ac_rfl⟩
      (fun h ↦ hp₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
    have hbudget : 2 * i * (p + 1) < 2 ^ s := calc
      2 * i * (p + 1) < 2 * l₀ s * (p + 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ 2 * l₀ s * (L + 1) := by gcongr
      _ ≤ 2 ^ s := hsize
    have hmean' (h : 2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) : a = b :=
      hmean a ha b hb c hc (2 * (j - i)) (2 * i) (by omega) (by omega) (by omega)
        (by simpa only [← Nat.mul_add, Nat.sub_add_cancel hij.le] using h)
    have hg₂ : g = 1 + 2 ^ ((v - 2) + 2) * u := by
      dsimp only [g]
      rw [P.coe_towerUnit, map_add, map_one, map_natCast, Nat.sub_add_cancel hv, heq,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hg₂] at hb'' hc''
    exact ZMod.not_exists_signed_pow_relations (m := m) (v := v - 2) hu
      (by rwa [Nat.sub_add_cancel hv]) hp.one_lt hi hij.le hbudget hmean'
      ⟨ε, ε', hsquare ε hε, hsquare ε' hε', hb'', hc''⟩

private theorem exists_sparse_places_of_exponents {s L : ℕ} {S : Finset ℕ}
    (hsize : 2 * l₀ s * (L + 1) ≤ 2 ^ s) (hS : ∀ e ∈ S, e < 2 ^ s)
    (hmean : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ u v : ℕ, 0 < u → 0 < v → u + v ≤ 2 * l₀ s →
      (u + v) * b ≡ u * a + v * c [MOD 2 ^ s] → a = b ∧ b = c) :
    ∃ T : Finset (ZMod (P.q₁ s))ˣ, #T = #S ∧ P.IsSparse s L T ∧
      ∀ τ ∈ T, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1 := by
  classical
  refine ⟨S.image (fun e ↦ -(P.towerUnit s ^ e)),
    card_image_of_injOn ((P.injOn_neg_pow_towerUnit s).mono fun e he ↦ hS e he),
    P.isSparse_image_neg_pow_towerUnit hsize
      (fun a ha b hb c hc u v hu hv huv h ↦ (hmean a ha b hb c hc u v hu hv huv h).1), ?_⟩
  intro τ hτ
  obtain ⟨e, _, rfl⟩ := mem_image.mp hτ
  exact P.unitsMap_neg_pow_towerUnit (dvd_mul_left _ _) (P.q₀_dvd_q₁ s) e

/-- A Behrend digit box fitting modulo `2 ^ s` supplies sparse place labels of base class `-1`
with the sphere-count lower bound. -/
theorem exists_large_sparse_places {s L n H : ℕ} (hfit : (2 * l₀ s * H) ^ n ≤ 2 ^ s)
    (hsize : 2 * l₀ s * (L + 1) ≤ 2 ^ s) :
    ∃ S : Finset (ZMod (P.q₁ s))ˣ, (H : ℝ) ^ n / (n * H ^ 2) ≤ #S ∧ P.IsSparse s L S ∧
      ∀ τ ∈ S, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1 := by
  have hL : 0 < 2 * l₀ s := by rw [l₀_def]; positivity
  obtain ⟨T, hT, hcard, hmean⟩ := exists_eq_and_eq_of_add_mul_modEq hL hfit
  obtain ⟨S, hS, hsparse, hclass⟩ := P.exists_sparse_places_of_exponents hsize hT hmean
  refine ⟨S, ?_, hsparse, hclass⟩
  push_cast at hcard
  simpa only [hS] using hcard

/-- Choose sparse place labels of base class `-1` with a cardinality loss of at most `W ^ 6`
relative to the tower degree. -/
theorem exists_sparse_places {s L n : ℕ} {W : ℝ}
    (ho : (2 : ℝ) ^ s ≤ W ^ (n + 1)) (hbase : (2 * (l₀ s : ℝ)) ^ n ≤ W)
    (hsize : 2 * l₀ s * (L + 1) ≤ 2 ^ s) :
    ∃ S : Finset (ZMod (P.q₁ s))ˣ, (towerDeg s : ℝ) ≤ #S * W ^ 6 ∧ P.IsSparse s L S ∧
      ∀ τ ∈ S, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1 := by
  have hdim : ∃ n' : ℕ, 0 < n' ∧ (2 : ℝ) ^ s ≤ W ^ (n' + 1) ∧
      (2 * (l₀ s : ℝ)) ^ n' ≤ W := by
    by_cases hn : 0 < n
    · exact ⟨n, hn, ho, hbase⟩
    · -- In dimension zero `W` already covers the dyadic order, so use dimension one.
      have hW : (2 : ℝ) ^ s ≤ W := by simpa [Nat.eq_zero_of_not_pos hn] using ho
      have hW₁ : 1 ≤ W := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hW
      have hL : 2 * l₀ s ≤ 2 ^ s := (Nat.le_mul_of_pos_right _ (Nat.succ_pos L)).trans hsize
      exact ⟨1, Nat.one_pos, hW.trans (le_self_pow₀ hW₁ (by decide)),
        by rw [pow_one]; exact (by exact_mod_cast hL : (2 : ℝ) * l₀ s ≤ (2 : ℝ) ^ s).trans hW⟩
  obtain ⟨n', hn', ho', hbase'⟩ := hdim
  obtain ⟨T, hT, hcard, hmean⟩ := exists_large_sparse_exponents hn' ho' hbase'
  obtain ⟨S, hS, hsparse, hclass⟩ := P.exists_sparse_places_of_exponents hsize hT hmean
  exact ⟨S, hS ▸ hcard, hsparse, hclass⟩

end TauCeti.OneSidedBound.Parameters
