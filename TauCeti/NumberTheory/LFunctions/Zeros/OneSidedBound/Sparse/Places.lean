/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.Combinatorics.Additive.NoRelation
import TauCeti.Data.ZMod.SignedPowers
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Sparse.Exponents
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TowerUnits

/-!
# Sparse cyclotomic place labels

A sparse set contains no two distinct short signed prime-power steps from the same starting
point, after reducing the place labels modulo the prime-to-`p` part of the conductor. Mapping a
modular Behrend set to negative powers of the tower unit gives many labels in the class `-1`.

The construction is the one in `New.Parameters.exists_large_isSparse` and
`New.Parameters.exists_isSparse` in `grh/src/New/Reduction/Data/Existence.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Nat
open scoped Finset

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- No two short steps by signed powers of a prime `p ≤ L` from a common label stay in `S`,
when all labels are reduced modulo the prime-to-`p` part of `q₁ s`. The three labels need not be
distinct. -/
structure IsSparse (s L : ℕ) (S : Set (ZMod (P.q₁ s))ˣ) : Prop where
  /-- If the first step stays in the set, the second step cannot stay in it. -/
  not_second_step {p i j : ℕ} (hp : p.Prime) (hpL : p ≤ L)
    (hi : 0 < i) (hij : i < j) (hj : j < l₀ s)
    {σ τ ρ : (ZMod (P.q₁ s))ˣ} (hσ : σ ∈ S) (hτ : τ ∈ S) (hρ : ρ ∈ S)
    {ε ε' : ZMod (ordCompl[p] (P.q₁ s))} (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1)
    (hτstep : ZMod.cast (τ : ZMod (P.q₁ s)) = ε * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ i *
      ZMod.cast (σ : ZMod (P.q₁ s))) :
    ZMod.cast (ρ : ZMod (P.q₁ s)) ≠ ε' * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ j *
      ZMod.cast (σ : ZMod (P.q₁ s))

-- A single short step at two is impossible, using the three-power part of the conductor.
private theorem not_towerUnit_two_step (s i a b : ℕ) (hi : 0 < i) (hi' : i < l₀ s)
    {ε : ZMod (ordCompl[2] (P.q₁ s))} (hε : ε ^ 2 = 1) :
    ZMod.cast ((P.towerUnit s ^ b : (ZMod (P.q₁ s))ˣ) : ZMod (P.q₁ s)) ≠
      ε * (2 : ZMod (ordCompl[2] (P.q₁ s))) ^ i *
        ZMod.cast ((P.towerUnit s ^ a : (ZMod (P.q₁ s))ˣ) : ZMod (P.q₁ s)) := by
  let r := Nat.log 3 s + 4
  have hr : 3 ^ r = l₀ s := l₀_def s |>.symm
  have hbase : 3 ^ (r + 1) ∣ 3 * l₀ s * P.q₀ := by
    rw [pow_succ', hr]
    exact dvd_mul_right ..
  have hdiv : 3 ^ (r + 1) ∣ P.q₁ s := by
    rw [q₁_def, towerDeg_def]
    exact hbase.trans (Dvd.intro (2 ^ s) (by ac_rfl))
  have hd := Nat.dvd_ordCompl_of_dvd_not_dvd hdiv
    (fun h ↦ (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow h))
  have hcast : ZMod.castHom hd (ZMod (3 ^ (r + 1)))
      (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s))) = 1 := by
    rw [← ZMod.castHom_apply (h := Nat.ordCompl_dvd _ _), ← RingHom.comp_apply,
      ZMod.castHom_comp, ZMod.castHom_apply, ← ZMod.unitsMap_val hdiv,
      (P.unitsMap_towerUnit_eq_one_iff hdiv).mpr hbase, Units.val_one]
  intro h
  refine ZMod.not_exists_signed_two_pow_relation (a := a) (b := b) hd hcast hi (hr.symm ▸ hi')
    ⟨ε, hε, ?_⟩
  simpa only [Units.val_pow_eq_pow_val, ZMod.cast_pow (Nat.ordCompl_dvd _ _)] using h

-- For odd primes reduction preserves the entire two-primary part of the conductor.
private theorem not_towerUnit_odd_steps {s p i j a b c : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    (hi : 0 < i) (hij : i ≤ j) (hsize : 2 * i * (p + 1) < 2 ^ s)
    (hmean : (2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) → a = b)
    {ε ε' : ZMod (ordCompl[p] (P.q₁ s))} (hε : ε ^ 2 = 1) (hε' : ε' ^ 2 = 1)
    (hb : ZMod.cast ((P.towerUnit s ^ b : (ZMod (P.q₁ s))ˣ) : ZMod (P.q₁ s)) =
      ε * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ i *
        ZMod.cast ((P.towerUnit s ^ a : (ZMod (P.q₁ s))ˣ) : ZMod (P.q₁ s)))
    (hc : ZMod.cast ((P.towerUnit s ^ c : (ZMod (P.q₁ s))ˣ) : ZMod (P.q₁ s)) =
      ε' * (p : ZMod (ordCompl[p] (P.q₁ s))) ^ j *
        ZMod.cast ((P.towerUnit s ^ a : (ZMod (P.q₁ s))ˣ) : ZMod (P.q₁ s))) : False := by
  let N := 3 * l₀ s * P.q₀
  let k := N.factorization 2
  have hN : N ≠ 0 := by dsimp [N]; rw [l₀_def]; have := P.q₀_pos; positivity
  have hk : 2 ≤ k := (Nat.prime_two.pow_dvd_iff_le_factorization hN).mp
    (dvd_mul_of_dvd_right ((by decide : 4 ∣ 18480).trans P.dvd_q₀) _)
  let v := k - 2
  let u := ordCompl[2] N
  have hk' : v + 2 = k := by omega
  have hu : Odd u := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact Nat.not_dvd_ordCompl Nat.prime_two hN
  have hNu : 2 ^ (v + 2) * u = 3 * l₀ s * P.q₀ := by
    rw [hk']
    exact Nat.ordProj_mul_ordCompl_eq_self N 2
  have hd : 2 ^ (s + (v + 2)) ∣ ordCompl[p] (P.q₁ s) := by
    apply Nat.dvd_ordCompl_of_dvd_not_dvd
    · have hq : P.q₁ s = 2 ^ s * (3 * l₀ s * P.q₀) := by
        rw [q₁_def, towerDeg_def]; ac_rfl
      rw [hq, ← hNu, pow_add]
      exact Nat.mul_dvd_mul_left _ (dvd_mul_right ..)
    · exact fun h ↦ hp₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hg : (ZMod.cast (P.towerUnit s : ZMod (P.q₁ s)) : ZMod (ordCompl[p] (P.q₁ s))) =
      1 + 2 ^ (v + 2) * u := by
    rw [P.coe_towerUnit, ZMod.cast_add (Nat.ordCompl_dvd _ _), ZMod.cast_one (Nat.ordCompl_dvd _ _),
      ZMod.cast_natCast (Nat.ordCompl_dvd _ _), ← hNu]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  refine ZMod.not_exists_signed_pow_relations hu hd hp.one_lt hi hij hsize hmean
    ⟨ε, ε', hε, hε', ?_, ?_⟩
  · simpa only [Units.val_pow_eq_pow_val, ZMod.cast_pow (Nat.ordCompl_dvd _ _), hg] using hb
  · simpa only [Units.val_pow_eq_pow_val, ZMod.cast_pow (Nat.ordCompl_dvd _ _), hg] using hc

private theorem isSparse_image_neg_pow_towerUnit {s L : ℕ} (S : Finset ℕ)
    (hL : 2 * l₀ s * (L + 1) ≤ 2 ^ s)
    (hmean : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ α β : ℕ, 0 < α → 0 < β → α + β ≤ 2 * l₀ s →
      (α + β) * b ≡ α * a + β * c [MOD 2 ^ s] → a = b) :
    P.IsSparse s L (S.image (fun e ↦ -(P.towerUnit s ^ e)) : Set (ZMod (P.q₁ s))ˣ) := by
  classical
  constructor
  intro p i j hp hpL hi hij hj σ τ ρ hσ hτ hρ ε ε' hε hε' hb hc
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hσ)
  obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hτ)
  obtain ⟨c, hcS, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
  simp only [Units.val_neg, ZMod.cast_neg (Nat.ordCompl_dvd _ _), mul_neg, neg_inj] at hb hc
  have hε₂ : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> simp
  have hε'₂ : ε' ^ 2 = 1 := by rcases hε' with rfl | rfl <;> simp
  by_cases hp₂ : p = 2
  · subst p
    exact P.not_towerUnit_two_step s i a b hi (hij.trans hj) hε₂
      (by simpa only [Nat.cast_ofNat] using hb)
  refine P.not_towerUnit_odd_steps hp hp₂ hi hij.le ?_ ?_ hε₂ hε'₂ hb hc
  · calc
      2 * i * (p + 1) < 2 * l₀ s * (p + 1) := by gcongr; omega
      _ ≤ 2 ^ s := (Nat.mul_le_mul_left _ (by omega)).trans hL
  · intro h
    have heq : 2 * (j - i) + 2 * i = 2 * j := by omega
    exact hmean a ha b hbS c hcS _ _ (by omega) (by omega) (by omega) (heq.symm ▸ h)

/-- A modular weighted-mean-free set of exponents yields equally many sparse place labels,
all reducing to `-1` modulo `q₀`. -/
theorem exists_sparse_places_of_exponents {s L : ℕ} (S : Finset ℕ)
    (hL : 2 * l₀ s * (L + 1) ≤ 2 ^ s)
    (hmean : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ α β : ℕ, 0 < α → 0 < β → α + β ≤ 2 * l₀ s →
      (α + β) * b ≡ α * a + β * c [MOD 2 ^ s] → a = b) :
    ∃ B : Finset (ZMod (P.q₁ s))ˣ, #B = #S ∧ P.IsSparse s L B ∧
      ∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1 := by
  classical
  refine ⟨S.image (fun e ↦ -(P.towerUnit s ^ e)), Finset.card_image_of_injOn ?_,
    P.isSparse_image_neg_pow_towerUnit S hL hmean, ?_⟩
  · intro a ha b hb hab
    have hmod := pow_eq_pow_iff_modEq.mp (neg_injective hab)
    rw [P.orderOf_towerUnit] at hmod
    have hl₀ : 0 < l₀ s := by rw [l₀_def]; positivity
    exact hmean a ha b hb a ha 1 1 (by decide) (by decide) (by omega) (by
      simpa only [one_mul, Nat.reduceAdd, two_mul] using hmod.symm.mul_left 2)
  · intro τ hτ
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hτ
    exact P.unitsMap_neg_pow_towerUnit (dvd_mul_left _ _) (P.q₀_dvd_q₁ s) e

/-- The explicit Behrend cardinality bound for sparse place labels in the class `-1`. -/
theorem exists_sparse_places_of_digit_box {s L n H : ℕ}
    (hfit : (2 * l₀ s * H) ^ n ≤ 2 ^ s) (hL : 2 * l₀ s * (L + 1) ≤ 2 ^ s) :
    ∃ B : Finset (ZMod (P.q₁ s))ˣ, (H : ℝ) ^ n / (n * H ^ 2) ≤ #B ∧ P.IsSparse s L B ∧
      ∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1 := by
  have hl₀ : 0 < l₀ s := by rw [l₀_def]; positivity
  obtain ⟨S, _, hcard, hmean⟩ := exists_eq_and_eq_of_add_mul_modEq (by omega) hfit
  obtain ⟨B, hB, hSparse, hclass⟩ := P.exists_sparse_places_of_exponents S hL
    fun a ha b hb c hc α β hα hβ hsum h ↦ (hmean a ha b hb c hc α β hα hβ hsum h).1
  exact ⟨B, by simpa only [hB, Nat.cast_pow, Nat.cast_mul] using hcard, hSparse, hclass⟩

/-- Sparse labels in the class `-1` fill at least a `W⁻⁶` share of that class. -/
theorem exists_large_sparse_places {s L n : ℕ} {W : ℝ} (hn : 0 < n)
    (horder : (2 : ℝ) ^ s ≤ W ^ (n + 1)) (hbase : (2 * (l₀ s : ℝ)) ^ n ≤ W)
    (hL : 2 * l₀ s * (L + 1) ≤ 2 ^ s) :
    ∃ B : Finset (ZMod (P.q₁ s))ˣ, (towerDeg s : ℝ) ≤ #B * W ^ 6 ∧ P.IsSparse s L B ∧
      ∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1 := by
  obtain ⟨S, _, hcard, hmean⟩ := exists_large_sparse_exponents hn horder hbase
  obtain ⟨B, hB, hSparse, hclass⟩ := P.exists_sparse_places_of_exponents S hL
    fun a ha b hb c hc α β hα hβ hsum h ↦ (hmean a ha b hb c hc α β hα hβ hsum h).1
  exact ⟨B, hB.symm ▸ hcard, hSparse, hclass⟩

end TauCeti.OneSidedBound.Parameters
