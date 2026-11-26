/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Basic

import TauCeti.FieldTheory.IntermediateField.Quadratic
import TauCeti.NumberTheory.Cyclotomic.CoprimeCompositum
import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant

/-!
# Roots of unity in an even cyclotomic field and its quadratic composita

Over `ℚ`, a cyclotomic field of even order `n` has no roots of unity of order not dividing `n`.
Adjoining the square root of an odd prime discriminant of absolute value `p > 3` does not enlarge
this group of roots of unity. This identifies the possible torsion elements when testing whether a
character of a norm-one torus is trivial on global integral points.

The quadratic case follows the degree argument for `New.Parameters.exists_zeta_pow_eq` in
`New/Reduction/Data/FieldsAndPlaces.lean` of lsernau/grh-lean at `72fead1`. The cyclotomic field
facts are those of Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section

open IntermediateField Module Polynomial

namespace IsPrimitiveRoot

/-- Let `p` be prime with `np` even. If a field embeds in the `np`-th rational cyclotomic
extension but has degree less than `φ(np)`, then every root of unity in it has order dividing `n`,
provided it contains a primitive `n`-th root. -/
theorem dvd_of_finrank_lt_totient_mul_prime {E F : Type*} [Field E] [CharZero E] [Field F]
    [CharZero F] {n p m : ℕ} [IsCyclotomicExtension {n * p} ℚ F]
    {z ζ : E} (hz : IsPrimitiveRoot z m) (hm : m ≠ 0) (hζ : IsPrimitiveRoot ζ n)
    (f : E →ₐ[ℚ] F) (heven : Even (n * p)) (hp : p.Prime)
    (hdeg : finrank ℚ E < (n * p).totient) : m ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact dvd_zero m
  have : NeZero (n * p) := ⟨mul_ne_zero hn0 hp.ne_zero⟩
  have : NeZero m := ⟨hm⟩
  have : NumberField F := IsCyclotomicExtension.numberField {n * p} ℚ F
  have : FiniteDimensional ℚ E := FiniteDimensional.of_injective f.toLinearMap f.injective
  have hdiv : m ∣ n * p := by
    simpa only [IsCyclotomicExtension.Rat.torsionOrder_eq (n := n * p), ite_eq_left heven] using
      NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot (hz.map_of_injective f.injective)
  -- The only divisors of `np` that are multiples of `n` are `n` and `np`.
  obtain ⟨k, hk⟩ := dvd_lcm_left n m
  have hkdiv : k ∣ p := by
    apply Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hn0)
    rw [← hk]
    exact Nat.lcm_dvd (dvd_mul_right n p) hdiv
  rcases (Nat.dvd_prime hp).mp hkdiv with rfl | rfl
  · exact (dvd_lcm_right n m).trans (by simp [hk])
  · have hle := hζ.lcm_totient_le_finrank hz
      (cyclotomic.irreducible_rat (Nat.lcm_pos (Nat.pos_of_ne_zero hn0) (Nat.pos_of_ne_zero hm)))
    exact False.elim (hdeg.not_ge (hk ▸ hle))

open TauCeti.Cyclotomic TauCeti.Multiquadratic

/-- For an even positive `n` and a prime `p > 3`, the roots of unity in the compositum
`ℚ(ζ, √D)` are exactly the powers of `ζ`, where `ζ` is primitive of order `n` and `D` is the
odd prime discriminant of `p`. In particular, `D = -p` when `p ≡ 3 (mod 4)`. -/
theorem exists_pow_eq_of_mem_adjoin_oddPrimeDiscriminant {n p : ℕ} [NeZero n]
    {ζ x z : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : Even n) (hp : p.Prime) (hp3 : 3 < p)
    (hx : x ^ 2 = (oddPrimeDiscriminant p : ℂ)) (hz : IsOfFinOrder z)
    (hmem : z ∈ ℚ⟮ζ⟯ ⊔ ℚ⟮x⟯) : ∃ k < n, ζ ^ k = z := by
  have hζfield : ℚ⟮ζ⟯ = complexField n := by
    have : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯ :=
      (isCyclotomicExtension_singleton_iff_eq_adjoin n ℚ ℂ _ hζ).mpr rfl
    exact isCyclotomicExtension_eq (S := {n}) (K := ℚ) (L := ℂ) _ _
  have : NeZero p := ⟨hp.ne_zero⟩
  have hD := isPrimeDiscriminant_oddPrimeDiscriminant hp (hp.odd_of_ne_two (by omega))
  have hxfield {j : ℕ} [NeZero j] (hj : p ∣ j) : ℚ⟮x⟯ ≤ complexField j := by
    rw [adjoin_simple_le_iff]
    exact mem_of_sq_eq_of_isFundamentalDiscr (NeZero.pos j) isPrimitiveRoot_complexRoot
      (complexRoot_mem_complexField j) hD.isFundamentalDiscr (by simpa using hj) hx
  have : NeZero (orderOf z) := ⟨hz.orderOf_pos.ne'⟩
  refine hζ.eq_pow_of_pow_eq_one (orderOf_dvd_iff_pow_eq_one.mp ?_)
  by_cases hpn : p ∣ n
  · have hmem' : z ∈ complexField n := sup_le hζfield.le (hxfield hpn) hmem
    let z' : complexField n := ⟨z, hmem'⟩
    have hz' : IsPrimitiveRoot z' (orderOf z) :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp (IsPrimitiveRoot.orderOf z)
    simpa only [IsCyclotomicExtension.Rat.torsionOrder_eq (n := n), ite_eq_left hn] using
      NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot hz'
  · have hnp := (hp.coprime_iff_not_dvd.mpr hpn).symm
    let E : IntermediateField ℚ ℂ := ℚ⟮ζ⟯ ⊔ ℚ⟮x⟯
    have he : E ≤ complexField (n * p) := by
      rw [← complexField_sup_eq hnp]
      exact sup_le_sup hζfield.le (hxfield dvd_rfl)
    let z' : E := ⟨z, hmem⟩
    let ζ' : E := ⟨ζ, (le_sup_left : ℚ⟮ζ⟯ ≤ E) (mem_adjoin_simple_self ℚ ζ)⟩
    have hz' : IsPrimitiveRoot z' (orderOf z) :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp (IsPrimitiveRoot.orderOf z)
    have hζ' : IsPrimitiveRoot ζ' n := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
    refine hz'.dvd_of_finrank_lt_totient_mul_prime hz.orderOf_pos.ne' hζ' (inclusion he)
      (hn.mul_right p) hp ?_
    -- The quadratic compositum has degree at most `2φ(n)`, strictly smaller than `φ(np)`.
    have hquad : finrank ℚ ℚ⟮x⟯ ≤ 2 := by
      have hx2 : x ^ 2 ∈ (⊥ : IntermediateField ℚ ℂ) := by rw [hx]; exact intCast_mem _ _
      by_cases hxb : x ∈ (⊥ : IntermediateField ℚ ℂ)
      · rw [(adjoin_simple_le_iff.mpr hxb).antisymm bot_le, IntermediateField.finrank_bot]
        norm_num
      · have h := (⊥ : IntermediateField ℚ ℂ).finrank_sup_adjoin_simple_eq_mul_two hx2 hxb
        rw [bot_sup_eq, IntermediateField.finrank_bot, one_mul] at h
        exact h.le
    calc
      finrank ℚ E ≤ finrank ℚ ℚ⟮ζ⟯ * finrank ℚ ℚ⟮x⟯ := finrank_sup_le _ _
      _ ≤ n.totient * 2 := by rw [hζfield, IsCyclotomicExtension.Rat.finrank n]; gcongr
      _ < (n * p).totient := by
        rw [Nat.totient_mul hnp, Nat.totient_prime hp]
        exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.totient_pos.mpr (NeZero.pos n))

end IsPrimitiveRoot
