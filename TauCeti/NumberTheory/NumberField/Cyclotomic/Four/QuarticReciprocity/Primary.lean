/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.QuarticReciprocity.IntCast
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.RationalResidue
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.SupplementaryLaws
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The law of biquadratic (quartic) reciprocity

Let `K = ℚ(i)`, given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]`, and write `(α / β)_4` for the quartic power residue symbol
`Ideal.powerResidueSymbolIdeal (Ideal.span {β}) 4 (Ideal.Quotient.mk _ α)`. For primary elements
`π₁` and `π₂` of `ℤ[i]`, the law of biquadratic reciprocity relates `(π₂ / π₁)_4` and
`(π₁ / π₂)_4` up to a sign determined by their norms (or equivalently by their real parts):

`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N(π₂) - 1) / 4) * ((N(π₁) - 1) / 4))`.

If `π₁` and `π₂` are not coprime, both residue symbols vanish and the equality still holds.

Building on odd-integer reciprocity in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Four.QuarticReciprocity.IntCast`, the proof proceeds
in two stages:

1. **Primary elements with coprime coordinates**: for primary `π₁ = a + b i` and `π₂ = c + d i`
   with `gcd(a, b) = gcd(c, d) = 1`, setting `m = a c + b d` relates `(π₂ / π₁)_4` and
   `(π₁ / π₂)_4` to `(m / π₂)_4`, `(m / σ π₁)_4`, `(c / π₂)_4`, and `(a / σ π₁)_4`. Applying
   odd-integer reciprocity and `(i / n)_4 = (-1) ^ ((n² - 1) / 8)` reduces the sign to a parity
   congruence on primary coordinates.
2. **General primary elements** (`TauCeti.IsPrimaryGaussian.quartic_reciprocity`): writing each
   primary element as `r · π₀` with `r ≡ 1 (mod 4)` in `ℤ` and `π₀` primary with coprime
   coordinates (`TauCeti.IsPrimaryGaussian.exists_intCast_mul_add_mul_isCoprime`), the rational
   factors cancel by `(r / π)_4 = (π / r)_4` and `(r / s)_4 = 1`.

## Main results

* `TauCeti.IsPrimaryGaussian.quartic_reciprocity`: the law of biquadratic reciprocity in `𝓞 K`,
  with exponent `((N(π₂ 𝓞 K) - 1) / 4) * ((N(π₁ 𝓞 K) - 1) / 4)`.
* `TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity`: the law of biquadratic reciprocity read in
  `K`, with integer norm exponent `((N(π₂) - 1) / 4) * ((N(π₁) - 1) / 4)`.
* `TauCeti.IsPrimaryGaussian.coe_quartic_reciprocity_add_mul`: the coordinate form
  `(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((a - 1) / 2) * ((c - 1) / 2))` for primary `π₁ = a + b i`
  and `π₂ = c + d i`.

## References

* N. Xu, *Reciprocity Laws*, §5, Theorem 5.8 and Proposition 5.13.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 9, §§8–9.
* M. C. Relyea, *On finite fields and higher reciprocity*, §4.1, Theorem 4.4.
-/

public section

open NumberField

namespace TauCeti

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-! ### Primary elements with coprime coordinates -/

/-- For primary coordinates `(a, b)` and `(c, d)` and `m = a * c + b * d`, the combined sign
exponent from odd-integer reciprocity and `(i / ·)_4` is congruent modulo `2` to
`((a - 1) / 2) * ((c - 1) / 2)`. -/
private theorem sign_exponent_modEq {a b c d : ℤ}
    (hπ₁ : a ≡ 1 [ZMOD 4] ∧ b ≡ 0 [ZMOD 4] ∨ a ≡ 3 [ZMOD 4] ∧ b ≡ 2 [ZMOD 4])
    (hπ₂ : c ≡ 1 [ZMOD 4] ∧ d ≡ 0 [ZMOD 4] ∨ c ≡ 3 [ZMOD 4] ∧ d ≡ 2 [ZMOD 4]) :
    let m := a * c + b * d
    ((m ^ 2 - 1) / 8 + ((m - 1) / 2) * ((c - 1) / 2) + ((m - 1) / 2) * ((a - 1) / 2) +
      ((c ^ 2 - 1) / 8 + ((c - 1) / 2) * ((c - 1) / 2) +
        (a ^ 2 - 1) / 8 + ((a - 1) / 2) * ((a - 1) / 2))) ≡
      ((a - 1) / 2) * ((c - 1) / 2) [ZMOD 2] := by
  intro m
  simp only [Int.ModEq] at hπ₁ hπ₂
  obtain ⟨u, rfl⟩ : ∃ u, a = 2 * u + 1 := ⟨(a - 1) / 2, by omega⟩
  obtain ⟨β, rfl⟩ : ∃ β, b = 2 * β := ⟨b / 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c = 2 * v + 1 := ⟨(c - 1) / 2, by omega⟩
  obtain ⟨δ, rfl⟩ : ∃ δ, d = 2 * δ := ⟨d / 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, β = u + 2 * r := ⟨(β - u) / 2, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, δ = v + 2 * s := ⟨(δ - v) / 2, by omega⟩
  have hoddsq (z : ℤ) : ((2 * z + 1) ^ 2 - 1) / 8 = z * (z + 1) / 2 := by
    have hsq : (2 * z + 1) ^ 2 - 1 = 4 * (z * (z + 1)) := by ring
    rw [hsq]
    omega
  set t : ℤ := u * v + u * s + v * r + 2 * r * s
  have hm_eq : m = 2 * (u + v + 4 * t) + 1 := by simp only [m, t]; ring
  have hw : (m - 1) / 2 = u + v + 4 * t := by omega
  have hu2 : (2 * u + 1 - 1) / 2 = u := by omega
  have hv2 : (2 * v + 1 - 1) / 2 = v := by omega
  rw [hw, hm_eq, hoddsq (u + v + 4 * t), hoddsq u, hoddsq v, hu2, hv2]
  have hsum : (u + v + 4 * t) * (u + v + 4 * t + 1) / 2 =
      (u + v) * (u + v + 1) / 2 + 2 * (t * (2 * (u + v) + 4 * t + 1)) := by
    have h : (u + v + 4 * t) * (u + v + 4 * t + 1) =
        (u + v) * (u + v + 1) + 2 * (2 * (t * (2 * (u + v) + 4 * t + 1))) := by ring
    rw [h, Int.add_mul_ediv_left _ _ (by decide)]
  have huv_tri : (u + v) * (u + v + 1) / 2 = u * (u + 1) / 2 + v * (v + 1) / 2 + u * v := by
    obtain ⟨eu, heu⟩ := Int.two_dvd_mul_add_one u
    obtain ⟨ev, hev⟩ := Int.two_dvd_mul_add_one v
    have h : (u + v) * (u + v + 1) = 2 * (eu + ev + u * v) := by linear_combination heu + hev
    rw [h, heu, hev]
    omega
  rw [hsum, huv_tri]
  exact Int.modEq_iff_dvd.mpr
    ⟨-(u * (u + 1) / 2 + v * (v + 1) / 2 + t * (2 * (u + v) + 4 * t + 1) + u ^ 2 + u * v +
      v ^ 2 + 2 * t * (u + v)), by ring⟩

/-- For coprime Gaussian integers `π₁ = a + b i` and `π₂ = c + d i` and `m = a c + b d`, relates
`(π₂ / π₁)_4` and `(π₁ / π₂)_4` to residue symbols with rational integer numerators `m, c, a`. -/
private theorem mul_powerResidueSymbolIdeal_add_mul_eq {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} {τ : 𝓞 K ≃+* 𝓞 K} (hτ : ∀ z : 𝓞 K, z ^ 4 = 1 → τ z = z ^ 3)
    (hcop : IsCoprime (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger})
      (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})) :
    let i := hζ.toInteger
    let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * i
    let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * i
    let m : ℤ := a * c + b * d
    (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
        powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K))) *
        powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (c : 𝓞 K)) *
        powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K))) *
        powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) := by
  intro i π₁ π₂ m
  have hsq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hid1 : (c : 𝓞 K) * π₁ - (m : 𝓞 K) = ((b : 𝓞 K) * i) * π₂ := by
    simp only [π₁, π₂, m]; push_cast; linear_combination (-(b : 𝓞 K) * d) * hsq
  have hid2 : (a : 𝓞 K) * π₂ - (m : 𝓞 K) = ((d : 𝓞 K) * i) * π₁ := by
    simp only [π₁, π₂, m]; push_cast; linear_combination (-(b : 𝓞 K) * d) * hsq
  have heq1 : powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (c : 𝓞 K)) *
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) := by
    have hmk : Ideal.Quotient.mk (span {π₂}) ((c : 𝓞 K) * π₁) =
        Ideal.Quotient.mk (span {π₂}) (m : 𝓞 K) :=
      Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨b * i, by linear_combination hid1⟩)
    rw [← map_mul, ← map_mul, hmk]
  have heq2 : powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
      powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K)) := by
    have heq2_raw : powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (a : 𝓞 K)) *
        powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
        powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) := by
      have hmk : Ideal.Quotient.mk (span {π₁}) ((a : 𝓞 K) * π₂) =
          Ideal.Quotient.mk (span {π₁}) (m : 𝓞 K) :=
        Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨d * i, by linear_combination hid2⟩)
      rw [← map_mul, ← map_mul, hmk]
    have h4 : powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) ^ 4 = 1 :=
      powerResidueSymbolIdeal_pow_eq_one (n := 4)
        (Ideal.Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp hcop))
    have hmap : (span {π₁}).map τ = span {τ π₁} := by rw [map_span, Set.image_singleton]
    have hτ_int (z : ℤ) :
        τ (powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ (z : 𝓞 K))) =
          powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (z : 𝓞 K)) := by
      rw [map_powerResidueSymbolIdeal, hmap, map_intCast τ]
    have hτ2 := congrArg τ heq2_raw
    rw [map_mul, hτ_int a, hτ _ h4, hτ_int m] at hτ2
    simpa only [mul_assoc, ← pow_succ, h4, mul_one] using
      (congrArg (· * powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂)) hτ2).symm
  calc (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
        powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K))) *
        powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂)
      = (powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (c : 𝓞 K)) *
          powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁)) *
          (powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
            powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂)) := by
        rw [heq1, mul_assoc]
    _ = _ := by rw [heq2]; ring

/-- For an odd integer `n`, `x` divisible by `n`, and `y` coprime to `n`,
`((x + y i) / n)_4 = (-1) ^ ((n² - 1) / 8)`, read in `K`. -/
private theorem coe_powerResidueSymbolIdeal_span_intCast_add_mul_of_dvd {ζ : K}
    (hζ : IsPrimitiveRoot ζ 4) {n x y : ℤ} (hn : Odd n) (hxn : n ∣ x) (hyn : IsCoprime y n) :
    ((powerResidueSymbolIdeal (span {(n : 𝓞 K)}) 4
        (Ideal.Quotient.mk _ ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      (-1) ^ ((n ^ 2 - 1) / 8) := by
  obtain ⟨q, rfl⟩ := hxn
  have hmk : Ideal.Quotient.mk (span {(n : 𝓞 K)})
      (((n * q : ℤ) : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger) =
      Ideal.Quotient.mk (span {(n : 𝓞 K)}) ((y : 𝓞 K) * hζ.toInteger) :=
    Ideal.Quotient.eq.mpr (mem_span_singleton.mpr ⟨q, by push_cast; ring⟩)
  rw [hmk, map_mul, map_mul, map_intCast, powerResidueSymbolIdeal_intCast_four hyn, one_mul]
  exact hζ.powerResidueSymbolIdeal_span_intCast_mk_toInteger_of_odd hn

/-- For primary `π = c + d i` with coprime coordinates, `(c / π)_4` read in `K` equals
`(-1) ^ ((c² - 1) / 8 + ((c - 1) / 2)²)`. -/
private theorem coe_powerResidueSymbolIdeal_mk_re {ζ : K} {hζ : IsPrimitiveRoot ζ 4} {c d : ℤ}
    (hπ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) (hcd : IsCoprime c d) :
    ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ (c : 𝓞 K)) : 𝓞 K) : K) =
      (-1) ^ ((c ^ 2 - 1) / 8 + ((c - 1) / 2) * ((c - 1) / 2)) := by
  have hcoord := (hζ.isPrimaryGaussian_add_mul_iff (a := c) (b := d)).mp hπ
  have hc_odd : Odd c := by rw [Int.odd_iff]; simp only [Int.ModEq] at hcoord; omega
  rw [hπ.coe_quartic_reciprocity_intCast_add_mul_of_odd hc_odd,
    coe_powerResidueSymbolIdeal_span_intCast_add_mul_of_dvd hζ hc_odd dvd_rfl hcd.symm,
    ← zpow_add₀ (by norm_num)]

/-- For coprime primary elements `π₁ = a + b i` and `π₂ = c + d i` with coprime coordinates and
`m = a c + b d`, evaluates `(m / π₂)_4 * (m / τ π₁)_4` in `K`. -/
private theorem coe_mul_powerResidueSymbolIdeal_add_mul_eq_zpow {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} {τ : 𝓞 K ≃+* 𝓞 K} (hτ : ∀ z : 𝓞 K, z ^ 4 = 1 → τ z = z ^ 3)
    (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger))
    (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hcop : IsCoprime (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger})
      (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger})) :
    let i := hζ.toInteger
    let π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * i
    let π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * i
    let m : ℤ := a * c + b * d
    ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) : 𝓞 K) : K) *
      ((powerResidueSymbolIdeal (span {τ π₁}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) : 𝓞 K) : K) =
      (-1) ^ ((m ^ 2 - 1) / 8 + ((m - 1) / 2) * ((c - 1) / 2) +
        ((m - 1) / 2) * ((a - 1) / 2)) := by
  intro i π₁ π₂ m
  have hsq : i ^ 2 = -1 := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  have hπ₁_coord := (hζ.isPrimaryGaussian_add_mul_iff (a := a) (b := b)).mp hπ₁
  have hπ₂_coord := (hζ.isPrimaryGaussian_add_mul_iff (a := c) (b := d)).mp hπ₂
  have hm_odd : Odd m := by
    have ha_odd : Odd a := by rw [Int.odd_iff]; simp only [Int.ModEq] at hπ₁_coord; omega
    have hc_odd : Odd c := by rw [Int.odd_iff]; simp only [Int.ModEq] at hπ₂_coord; omega
    obtain ⟨u, ha_eq⟩ := ha_odd
    obtain ⟨v, hc_eq⟩ := hc_odd
    obtain ⟨w, hb_eq⟩ : ∃ w, b = 2 * w := ⟨b / 2, by simp only [Int.ModEq] at hπ₁_coord; omega⟩
    exact ⟨2 * u * v + u + v + w * d, by simp only [m, ha_eq, hc_eq, hb_eq]; ring⟩
  have hτπ₁ : τ π₁ = (a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * i := by
    rw [hζ.apply_intCast_add_intCast_mul_toInteger_of_four hτ a b]; push_cast; ring
  have hτπ₁_prim : IsPrimaryGaussian ((a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * i) :=
    hτπ₁ ▸ hπ₁.map τ.toRingHom
  have hprod : τ π₁ * π₂ = (m : 𝓞 K) + ((a * d - b * c : ℤ) : 𝓞 K) * i := by
    rw [hτπ₁]; simp only [π₂, m]; push_cast; linear_combination (-(b : 𝓞 K) * d) * hsq
  have hL_sym : ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) :
      K) * ((powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 4 (Ideal.Quotient.mk _ (τ π₁)) : 𝓞 K) :
      K) = (-1) ^ ((m ^ 2 - 1) / 8) := by
    have h := coe_powerResidueSymbolIdeal_span_intCast_add_mul_of_dvd hζ hm_odd dvd_rfl
      (hζ.isCoprime_mul_sub_mul_mul_add_mul_of_four hab hcd
        ((isCoprime_span_singleton_iff _ _).mp hcop).symm)
    rw [← hprod] at h
    simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap] at h
    rwa [mul_comm]
  rw [hπ₂.coe_quartic_reciprocity_intCast_add_mul_of_odd hm_odd, hτπ₁,
    hτπ₁_prim.coe_quartic_reciprocity_intCast_add_mul_of_odd hm_odd, ← hτπ₁,
    mul_mul_mul_comm, hL_sym, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num), ← add_assoc]

/-- Quartic reciprocity for primary elements `π₁ = a + b i` and `π₂ = c + d i` whose coordinates
are coprime (`IsCoprime a b` and `IsCoprime c d`). -/
private theorem coe_quartic_reciprocity_add_mul_of_isCoprime {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger))
    (hab : IsCoprime a b) (hcd : IsCoprime c d) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by
  set i := hζ.toInteger
  set π₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * i
  set π₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * i
  by_cases hcop : IsCoprime (span {π₂}) (span {π₁})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop)]
    simp
  have hπ₁_coord := (hζ.isPrimaryGaussian_add_mul_iff (a := a) (b := b)).mp hπ₁
  have hπ₂_coord := (hζ.isPrimaryGaussian_add_mul_iff (a := c) (b := d)).mp hπ₂
  set m : ℤ := a * c + b * d
  obtain ⟨σ, _, hτ⟩ := exists_gal_apply_eq_pow_three_of_four (K := K)
  let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
  have hτπ₁ : τ π₁ = (a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * i := by
    rw [hζ.apply_intCast_add_intCast_mul_toInteger_of_four hτ a b]; push_cast; ring
  have hτπ₁_prim : IsPrimaryGaussian ((a : 𝓞 K) + ((-b : ℤ) : 𝓞 K) * i) :=
    hτπ₁ ▸ hπ₁.map τ.toRingHom
  have hmasterK := congrArg (algebraMap (𝓞 K) K) (mul_powerResidueSymbolIdeal_add_mul_eq hτ hcop)
  simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap] at hmasterK
  rw [coe_mul_powerResidueSymbolIdeal_add_mul_eq_zpow hτ hπ₁ hπ₂ hab hcd hcop,
    coe_powerResidueSymbolIdeal_mk_re hπ₂ hcd, hτπ₁,
    coe_powerResidueSymbolIdeal_mk_re hτπ₁_prim hab.neg_right,
    ← zpow_add₀ (by norm_num)] at hmasterK
  set eL : ℤ := (m ^ 2 - 1) / 8 + ((m - 1) / 2) * ((c - 1) / 2) + ((m - 1) / 2) * ((a - 1) / 2)
  set eR : ℤ := ((c ^ 2 - 1) / 8 + ((c - 1) / 2) * ((c - 1) / 2)) +
    ((a ^ 2 - 1) / 8 + ((a - 1) / 2) * ((a - 1) / 2))
  have hsq_sign : (-1 : K) ^ eL * (-1 : K) ^ eL = 1 := by
    rw [← zpow_add₀ (by norm_num)]
    exact Even.neg_one_zpow ⟨eL, by ring⟩
  calc ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K)
      = ((-1 : K) ^ eL * (-1 : K) ^ eL) *
          ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K) := by
        rw [hsq_sign, one_mul]
    _ = (-1 : K) ^ eL * ((-1 : K) ^ eR *
          ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K)) := by
        rw [mul_assoc, hmasterK]
    _ = ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K) *
          (-1) ^ (eL + eR) := by
        rw [← mul_assoc, ← zpow_add₀ (by norm_num), mul_comm]
    _ = _ := by
        have heR : eL + eR = (m ^ 2 - 1) / 8 + ((m - 1) / 2) * ((c - 1) / 2) +
            ((m - 1) / 2) * ((a - 1) / 2) + ((c ^ 2 - 1) / 8 + ((c - 1) / 2) * ((c - 1) / 2) +
              (a ^ 2 - 1) / 8 + ((a - 1) / 2) * ((a - 1) / 2)) := by simp only [eL, eR]; ring
        rw [heR, zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
          (sign_exponent_modEq hπ₁_coord hπ₂_coord)]

/-! ### The general law of biquadratic reciprocity -/

/-- Multiplying a primary element `α = x + y i` by a rational integer `r ≡ 1 (mod 4)` leaves the
parity of `(N((r * α) 𝓞 K) - 1) / 4` equal to that of `(x - 1) / 2`. -/
private theorem absNorm_intCast_mul_sub_one_div_four_modEq {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {r x y : ℤ} (hr : r ≡ 1 [ZMOD 4])
    (hxy : IsPrimaryGaussian ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger)) :
    (((absNorm (span {(r : 𝓞 K) * ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger)}) - 1) / 4 : ℕ) : ℤ) ≡
      (x - 1) / 2 [ZMOD 2] := by
  have hmul : (r : 𝓞 K) * ((x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger) =
      ((r * x : ℤ) : 𝓞 K) + ((r * y : ℤ) : 𝓞 K) * hζ.toInteger := by push_cast; ring
  have hrxy : IsPrimaryGaussian (((r * x : ℤ) : 𝓞 K) + ((r * y : ℤ) : 𝓞 K) * hζ.toInteger) :=
    hmul ▸ (isPrimaryGaussian_intCast_iff.mpr hr).mul hxy
  rw [hmul, hrxy.natCast_absNorm_sub_one_div_four]
  refine hrxy.norm_sub_one_div_four.trans ?_
  obtain ⟨t, rfl⟩ : ∃ t, r = 4 * t + 1 := ⟨(r - 1) / 4, by simp only [Int.ModEq] at hr; omega⟩
  have hdiv : ((4 * t + 1) * x - 1) / 2 = (x - 1) / 2 + 2 * (t * x) := by
    rw [show (4 * t + 1) * x - 1 = (x - 1) + 2 * (2 * (t * x)) by ring,
      Int.add_mul_ediv_left _ _ (by decide)]
  rw [hdiv]
  exact Int.modEq_iff_dvd.mpr ⟨-(t * x), by ring⟩

/-- Expands `((n * α₂) / (m * α₁))_4` when `m ≡ 1 (mod 4)` and `gcd(n, m) = 1`. -/
private theorem powerResidueSymbolIdeal_span_intCast_mul_mk_intCast_mul {m n : ℤ} {α₁ α₂ : 𝓞 K}
    (hm : m ≡ 1 [ZMOD 4]) (hmn : IsCoprime n m) (hα₁ : IsPrimaryGaussian α₁)
    (hα₂ : IsPrimaryGaussian α₂) :
    powerResidueSymbolIdeal (span {(m : 𝓞 K) * α₁}) 4
        (Ideal.Quotient.mk _ ((n : 𝓞 K) * α₂)) =
      (powerResidueSymbolIdeal (span {α₂}) 4 (Ideal.Quotient.mk _ (m : 𝓞 K)) *
        powerResidueSymbolIdeal (span {α₁}) 4 (Ideal.Quotient.mk _ (n : 𝓞 K))) *
        powerResidueSymbolIdeal (span {α₁}) 4 (Ideal.Quotient.mk _ α₂) := by
  have hm0 : span {(m : 𝓞 K)} ≠ ⊥ := by
    have hm_ne : m ≠ 0 := by simp only [Int.ModEq] at hm; omega
    simpa using hm_ne
  have hα₁_0 : span {α₁} ≠ ⊥ := by simpa using hα₁.ne_zero
  rw [← span_singleton_mul_span_singleton, powerResidueSymbolIdeal_mul_right hm0 hα₁_0,
    map_mul, map_mul, map_mul, map_mul, map_intCast,
    powerResidueSymbolIdeal_intCast_four hmn, one_mul,
    ← hα₂.quartic_reciprocity_intCast hm, mul_assoc]

/-- **The law of biquadratic (quartic) reciprocity.** Let `K = ℚ(i)`, so that `𝓞 K = ℤ[i]`, and
let `π₁` and `π₂` be primary elements of `𝓞 K`. Then
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N(π₂ 𝓞 K) - 1) / 4) * ((N(π₁ 𝓞 K) - 1) / 4))`,
where the quartic power residue symbols are taken at the principal ideals `π₁ 𝓞 K` and `π₂ 𝓞 K`.
If `π₁` and `π₂` are not coprime, both symbols vanish and the equality still holds. -/
theorem IsPrimaryGaussian.quartic_reciprocity {π₁ π₂ : 𝓞 K} (hπ₁ : IsPrimaryGaussian π₁)
    (hπ₂ : IsPrimaryGaussian π₂) :
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) *
        (-1) ^ (((absNorm (span {π₂}) - 1) / 4) * ((absNorm (span {π₁}) - 1) / 4)) := by
  by_cases hcop : IsCoprime (span {π₂}) (span {π₁})
  swap
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hcop,
      powerResidueSymbolIdeal_mk_eq_zero_iff.mpr (mt IsCoprime.symm hcop), zero_mul]
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨m, a, b, hm, hab, hα₁, rfl⟩ := hπ₁.exists_intCast_mul_add_mul_isCoprime hζ
  obtain ⟨n, c, d, hn, hcd, hα₂, rfl⟩ := hπ₂.exists_intCast_mul_add_mul_isCoprime hζ
  set α₁ : 𝓞 K := (a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger
  set α₂ : 𝓞 K := (c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger
  have hmn : IsCoprime n m := by
    rw [← span_singleton_mul_span_singleton, ← span_singleton_mul_span_singleton] at hcop
    exact RingOfIntegers.isCoprime_intCast.mp
      ((isCoprime_span_singleton_iff _ _).mp hcop.of_mul_left_left.of_mul_right_left)
  rw [powerResidueSymbolIdeal_span_intCast_mul_mk_intCast_mul hm hmn hα₁ hα₂,
    powerResidueSymbolIdeal_span_intCast_mul_mk_intCast_mul hn hmn.symm hα₂ hα₁,
    mul_comm (powerResidueSymbolIdeal (span {α₁}) 4 _) (powerResidueSymbolIdeal (span {α₂}) 4 _)]
  simp only [mul_assoc]
  congr 1
  congr 1
  apply RingOfIntegers.coe_injective
  simp only [map_mul, ← RingOfIntegers.coe_eq_algebraMap]
  push_cast
  rw [coe_quartic_reciprocity_add_mul_of_isCoprime hα₁ hα₂ hab hcd, ← zpow_natCast, Nat.cast_mul]
  congr 1
  refine (zpow_eq_zpow_of_modEq (n := 2) (by norm_num) ?_).symm
  rw [mul_comm ((a - 1) / 2)]
  exact (absNorm_intCast_mul_sub_one_div_four_modEq hn hα₂).mul
    (absNorm_intCast_mul_sub_one_div_four_modEq hm hα₁)

/-- **The law of biquadratic (quartic) reciprocity, with integer norms.** Let `K = ℚ(i)` and let
`π₁` and `π₂` be primary elements of `𝓞 K = ℤ[i]`. Read in `K`,
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((N(π₂) - 1) / 4) * ((N(π₁) - 1) / 4))`,
where `N = Algebra.norm ℤ`. -/
theorem IsPrimaryGaussian.coe_quartic_reciprocity {π₁ π₂ : 𝓞 K} (hπ₁ : IsPrimaryGaussian π₁)
    (hπ₂ : IsPrimaryGaussian π₂) :
    ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K) *
        (-1) ^ (((Algebra.norm ℤ π₂ - 1) / 4) * ((Algebra.norm ℤ π₁ - 1) / 4)) := by
  rw [hπ₁.quartic_reciprocity hπ₂]
  push_cast
  rw [← zpow_natCast, Nat.cast_mul, hπ₂.natCast_absNorm_sub_one_div_four,
    hπ₁.natCast_absNorm_sub_one_div_four]

/-- **The law of biquadratic reciprocity in coordinates.** For any primary elements
`π₁ = a + b i` and `π₂ = c + d i` of `𝓞 K = ℤ[i]`,
`(π₂ / π₁)_4 = (π₁ / π₂)_4 · (-1) ^ (((a - 1) / 2) * ((c - 1) / 2))`, read in `K`. Neither
coprimality of `(a, b)` or `(c, d)` nor coprimality of `π₁` and `π₂` is required. -/
theorem IsPrimaryGaussian.coe_quartic_reciprocity_add_mul {ζ : K} {hζ : IsPrimitiveRoot ζ 4}
    {a b c d : ℤ} (hπ₁ : IsPrimaryGaussian ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger))
    (hπ₂ : IsPrimaryGaussian ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) :
    ((powerResidueSymbolIdeal (span {(a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) =
      ((powerResidueSymbolIdeal (span {(c : 𝓞 K) + (d : 𝓞 K) * hζ.toInteger}) 4
        (Ideal.Quotient.mk _ ((a : 𝓞 K) + (b : 𝓞 K) * hζ.toInteger)) : 𝓞 K) : K) *
        (-1) ^ (((a - 1) / 2) * ((c - 1) / 2)) := by
  rw [hπ₁.coe_quartic_reciprocity hπ₂]
  congr 1
  exact zpow_eq_zpow_of_modEq (n := 2) (by norm_num)
    (by simpa [mul_comm] using hπ₁.norm_sub_one_div_four.mul hπ₂.norm_sub_one_div_four)

/-! ### Examples -/

section Examples

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/- For `π₁ = -1 + 2i` (norm `5 ≡ 5 (mod 8)`) and `π₂ = 3 + 2i` (norm `13 ≡ 5 (mod 8)`), the
reciprocity sign is `-1`, so `(π₂ / π₁)_4 = -(π₁ / π₂)_4`. -/
example :
    let π₁ : 𝓞 K := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := ((3 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    ((powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) : 𝓞 K) : K) =
      -((powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) : 𝓞 K) : K) := by
  intro π₁ π₂
  have hπ₁ : IsPrimaryGaussian π₁ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hπ₂ : IsPrimaryGaussian π₂ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hsign : (-1 : K) ^ (((-1 - 1 : ℤ) / 2) * ((3 - 1) / 2)) = -1 := by norm_num
  rw [hπ₁.coe_quartic_reciprocity_add_mul hπ₂, hsign, mul_neg_one]

/- For `π₁ = -1 + 2i` (norm `5`) and `π₂ = -3` (norm `9`, where `gcd(-3, 0) = 3 ≠ 1`), the general
biquadratic reciprocity law gives `(π₂ / π₁)_4 = (π₁ / π₂)_4`. -/
example :
    let π₁ : 𝓞 K := ((-1 : ℤ) : 𝓞 K) + ((2 : ℤ) : 𝓞 K) * hζ.toInteger
    let π₂ : 𝓞 K := ((-3 : ℤ) : 𝓞 K)
    powerResidueSymbolIdeal (span {π₁}) 4 (Ideal.Quotient.mk _ π₂) =
      powerResidueSymbolIdeal (span {π₂}) 4 (Ideal.Quotient.mk _ π₁) := by
  intro π₁ π₂
  have hπ₁ : IsPrimaryGaussian π₁ := by rw [hζ.isPrimaryGaussian_add_mul_iff]; decide
  have hπ₂ : IsPrimaryGaussian π₂ := by rw [isPrimaryGaussian_intCast_iff]; decide
  have h3 : π₂ = -((3 : ℕ) : 𝓞 K) := by simp [π₂]
  have hNπ₂ : absNorm (span {π₂}) = 9 := by
    rw [h3, span_singleton_neg, absNorm_span_natCast_four]
    rfl
  rw [hπ₁.quartic_reciprocity hπ₂, hNπ₂]
  norm_num

end Examples

end TauCeti
