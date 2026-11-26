/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.Combinatorics.Additive.NoRelation
import TauCeti.Data.ZMod.SignedPowers

/-!
# Large sparse sets in a cyclotomic tower

A set of exponents avoiding short modular weighted means gives a large set of units in the
class `-1` at the base level. Two distinct short signed powers of the same small prime cannot
carry one selected unit to two selected units, even after removing the prime part of the level.
The units are the labels of cyclotomic places; the statement is independent of a choice of
embedding used to identify places with labels.

The construction is that of `New.Parameters.exists_large_isSparse` in
`grh/src/New/Reduction/Data/Existence.lean` of [grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
-/

public section

open scoped Nat

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters) (s : ℕ)

-- Isolate the odd factor of the generator increment and the full dyadic divisor of the level.
private theorem exists_sparseBase_dyadic : ∃ v u : ℕ,
    Odd u ∧ 3 * l₀ s * P.q₀ = 2 ^ (v + 2) * u ∧ 2 ^ (s + (v + 2)) ∣ P.q₁ s := by
  have hq := Nat.ordProj_mul_ordCompl_eq_self P.q₀ 2
  have hv : 2 ≤ P.q₀.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two P.q₀_ne_zero).mp
      ((by norm_num : 2 ^ 2 ∣ 18480).trans P.dvd_q₀)
  let v := P.q₀.factorization 2 - 2
  have he : v + 2 = P.q₀.factorization 2 := by dsimp [v]; omega
  have hu : Odd (ordCompl[2] P.q₀) := by
    rw [Nat.odd_iff]
    have h := Nat.not_dvd_ordCompl Nat.prime_two P.q₀_ne_zero
    omega
  have h₃ : Odd (3 : ℕ) := by decide
  have hl : Odd (l₀ s) := by rw [l₀_def]; exact h₃.pow
  refine ⟨v, 3 * l₀ s * ordCompl[2] P.q₀, (h₃.mul hl).mul hu, ?_, ?_⟩
  · rw [he]
    calc
      3 * l₀ s * P.q₀ = 3 * l₀ s * (2 ^ P.q₀.factorization 2 * ordCompl[2] P.q₀) :=
        congrArg (3 * l₀ s * ·) hq.symm
      _ = _ := by ac_rfl
  · rw [he, q₁_def, towerDeg_def, add_comm s, pow_add]
    have hd := mul_dvd_mul (Nat.ordProj_dvd P.q₀ 2) (dvd_refl (2 ^ s))
    exact (dvd_mul_of_dvd_left hd (3 * l₀ s)).trans (dvd_of_eq (by ac_rfl))

private theorem sparseBase_pow_injOn :
    Set.InjOn (fun e : ℕ ↦ (1 + (3 * l₀ s * P.q₀ : ℕ) : ZMod (P.q₁ s)) ^ e)
      (Set.Iio (2 ^ s)) := by
  obtain ⟨v, u, hu, he, hd⟩ := P.exists_sparseBase_dyadic s
  let f := ZMod.castHom hd (ZMod (2 ^ (s + (v + 2))))
  have hord : orderOf (f (1 + (3 * l₀ s * P.q₀ : ℕ))) = 2 ^ s := by
    have h := ZMod.orderOf_one_add_mul_prime_pow Nat.prime_two (v + 2) (by omega) (u : ℤ)
      (by exact_mod_cast hu.not_two_dvd_nat) s
    rw [map_add, map_one, map_natCast, he]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_natCast] using h
  intro a ha b hb hab
  exact pow_injOn_Iio_orderOf (hord ▸ ha) (hord ▸ hb)
    (by simpa only [map_pow] using congrArg f hab)

private theorem not_sparseBase_relations {p a b c i j : ℕ} (hp : p.Prime)
    (hi : 0 < i) (hij : i < j) (hj : j < l₀ s) (hsize : 2 * l₀ s * (p + 1) < 2 ^ s)
    (hmean : (2 * j * b ≡ 2 * (j - i) * a + 2 * i * c [MOD 2 ^ s]) → a = b) :
    let m := ordCompl[p] (P.q₁ s)
    let g : ZMod m := 1 + (3 * l₀ s * P.q₀ : ℕ)
    ¬ ∃ ε ε' : ZMod m, ε ^ 2 = 1 ∧ ε' ^ 2 = 1 ∧
      g ^ b = ε * (p : ZMod m) ^ i * g ^ a ∧ g ^ c = ε' * (p : ZMod m) ^ j * g ^ a := by
  rcases hp.eq_two_or_odd with rfl | hpodd
  · intro m g ⟨ε, _, hε, _, hb, _⟩
    have h₃ : 3 ^ (Nat.log 3 s + 4 + 1) ∣ 3 * l₀ s := by rw [pow_succ', l₀_def]
    have h₃q : 3 * l₀ s ∣ P.q₁ s := by
      rw [q₁_def, towerDeg_def]
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    have hd : 3 ^ (Nat.log 3 s + 4 + 1) ∣ m :=
      Nat.dvd_ordCompl_of_dvd_not_dvd (h₃.trans h₃q) fun h ↦
        (by decide : ¬2 ∣ (3 : ℕ)) (Nat.prime_two.dvd_of_dvd_pow h)
    have hg : ZMod.castHom hd (ZMod (3 ^ (Nat.log 3 s + 4 + 1))) g = 1 := by
      dsimp only [g]
      rw [map_add, map_one, map_natCast,
        (ZMod.natCast_eq_zero_iff _ _).2 (h₃.trans (dvd_mul_right _ _)), add_zero]
    exact ZMod.not_exists_signed_two_pow_relation hd hg hi
      (by simpa only [← l₀_def] using hij.trans hj)
      ⟨ε, hε, by simpa only [Nat.cast_ofNat] using hb⟩
  · obtain ⟨v, u, hu, he, hd⟩ := P.exists_sparseBase_dyadic s
    have hn : ¬p ∣ 2 ^ (s + (v + 2)) := fun h ↦
      (not_le_of_gt (show 2 < p by have := hp.two_le; omega))
        (Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow h))
    have hd' := Nat.dvd_ordCompl_of_dvd_not_dvd hd hn
    have hsmall : 2 * i * (p + 1) < 2 ^ s :=
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (hij.trans hj).le)).trans_lt hsize
    simpa only [he, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      ZMod.not_exists_signed_pow_relations hu hd' hp.one_lt hi hij.le hsmall hmean

/-- A cyclotomic tower has a large finite set of labels above `-1` at the base level whose
reductions modulo the prime-to-`p` part admit no two short signed transitions from a common
point. The three labels may coincide. Signs are allowed to be any square roots of `1` in the
reduced ring, in particular `±1`. -/
theorem exists_large_sparse_places {n H L : ℕ} (hbox : (2 * l₀ s * H) ^ n ≤ 2 ^ s)
    (hsize : 2 * l₀ s * (L + 1) < 2 ^ s) :
    ∃ S : Finset (ZMod (P.q₁ s))ˣ,
      ((H ^ n : ℕ) / (n * H ^ 2 : ℕ) : ℝ) ≤ S.card ∧
      (∀ a ∈ S, ZMod.castHom (P.q₀_dvd_q₁ s) (ZMod P.q₀) a = -1) ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ p ≤ L, p.Prime →
        ∀ i j : ℕ, 0 < i → i < j → j < l₀ s →
          let m := ordCompl[p] (P.q₁ s)
          let f := ZMod.castHom (Nat.ordCompl_dvd (P.q₁ s) p) (ZMod m)
          ¬ ∃ ε ε' : ZMod m, ε ^ 2 = 1 ∧ ε' ^ 2 = 1 ∧
            f b = ε * (p : ZMod m) ^ i * f a ∧ f c = ε' * (p : ZMod m) ^ j * f a := by
  classical
  obtain ⟨A, hA, hcard, hmean⟩ := exists_eq_and_eq_of_add_mul_modEq
    (show 0 < 2 * l₀ s by rw [l₀_def]; positivity) hbox
  have hcop : (1 + 3 * l₀ s * P.q₀).Coprime (P.q₁ s) := by
    by_contra h
    obtain ⟨p, hp, hg, hq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    exact hp.not_dvd_one ((Nat.dvd_add_left (dvd_mul_of_dvd_right
      (P.dvd_q₀_of_dvd_q₁ hp hq) _)).mp hg)
  let g : (ZMod (P.q₁ s))ˣ := ZMod.unitOfCoprime _ hcop
  let F (e : ℕ) := (-1 : (ZMod (P.q₁ s))ˣ) * g ^ e
  have hg : (g : ZMod (P.q₁ s)) = 1 + (3 * l₀ s * P.q₀ : ℕ) := by
    simp [g, ZMod.coe_unitOfCoprime]
  refine ⟨A.image F, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · exact hcard
    · intro a ha b hb hab
      have h := congrArg (fun u : (ZMod (P.q₁ s))ˣ ↦ (u : ZMod (P.q₁ s))) hab
      simp only [F, neg_one_mul, Units.val_neg, Units.val_pow_eq_pow_val, neg_inj, hg] at h
      exact P.sparseBase_pow_injOn s (hA a ha) (hA b hb) h
  · rintro _ hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    have hz : ((3 * l₀ s * P.q₀ : ℕ) : ZMod P.q₀) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_left _ _)
    simp only [F, neg_one_mul, Units.val_neg, Units.val_pow_eq_pow_val, hg, map_neg,
      map_pow, map_add, map_one, map_natCast, hz, add_zero, one_pow]
  · intro a ha b hb c hc p hpL hp i j hi hij hj m f
    obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨e₂, he₂, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨e₃, he₃, rfl⟩ := Finset.mem_image.mp hc
    have hm (h : 2 * j * e₂ ≡ 2 * (j - i) * e₁ + 2 * i * e₃ [MOD 2 ^ s]) : e₁ = e₂ := by
      have he : 2 * (j - i) + 2 * i = 2 * j := by omega
      exact (hmean e₁ he₁ e₂ he₂ e₃ he₃ _ _ (by omega) (by omega)
        (he ▸ Nat.mul_le_mul_left 2 hj.le) (he ▸ h)).1
    have hs : 2 * l₀ s * (p + 1) < 2 ^ s :=
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hpL 1)).trans_lt hsize
    simpa only [F, neg_one_mul, Units.val_neg, Units.val_pow_eq_pow_val, hg, map_neg, map_pow,
      map_add, map_one, map_natCast, mul_neg, neg_inj, f, m] using
      P.not_sparseBase_relations s hp hi hij hj hs hm

end TauCeti.OneSidedBound.Parameters
