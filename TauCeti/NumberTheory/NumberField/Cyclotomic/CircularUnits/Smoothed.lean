/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.CircularUnits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import TauCeti.NumberTheory.NumberField.Cyclotomic.HasseUnitIndex

/-!
# Cyclotomic ratios and real smoothed circular units

For an `N`-th root of unity `ζ` in a field `K` and `b : ℤ`, the **cyclotomic ratio** is
`cyclotomicRatio ζ b = (ζ ^ b - 1) / (ζ - 1)`. When `ζ` is a primitive `N`-th root of unity
(`2 ≤ N`) and `b.gcd N = 1`, it lifts to `cyclotomicRatioUnit` in `(𝓞 K)ˣ`.

To obtain real circular units directly in `(𝓞 K⁺)ˣ`, we introduce two smoothings:
* `smoothedCyclotomicRatio ζ N b = ζ ^ (((N + 1) / 2 : ℕ) * (1 - b)) * cyclotomicRatio ζ b` for
  odd conductors `N`, lifting to `smoothedCyclotomicUnit`;
* `oddSmoothedCyclotomicRatio ζ b = ζ ^ ((1 - b) / 2) * cyclotomicRatio ζ b` for arbitrary
  conductors `N` (especially powers of `2`) and odd `b : ℤ`, lifting to `oddSmoothedCyclotomicUnit`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer (1997), Chapter 8.
* R. Sharifi, *Iwasawa Theory*, Chapter 4.
-/

public section

open NumberField NumberField.IsCMField Finset

open scoped NumberField

namespace TauCeti

/-! ### Private helpers -/

section Private

variable {K : Type*} [Field K]

local notation3 "K⁺" => maximalRealSubfield K

private theorem ne_zero_of_pow_eq_one {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hN0 : N ≠ 0) :
    ζ ≠ 0 :=
  fun h0 ↦ by simp [h0, zero_pow hN0] at hζN

private theorem zpow_eq_of_modeq {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    {a b : ℤ} (hab : a ≡ b [ZMOD N]) : ζ ^ a = ζ ^ b := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [show a = b by simpa [Int.ModEq] using hab]
  · have hζ0 := ne_zero_of_pow_eq_one hζN hN
    have huN : (Units.mk0 ζ hζ0) ^ N = 1 := Units.ext (by simp [hζN])
    have hmod : (Units.mk0 ζ hζ0) ^ a = (Units.mk0 ζ hζ0) ^ b := by
      rw [zpow_eq_zpow_emod' a huN, zpow_eq_zpow_emod' b huN, hab.eq]
    simpa using congrArg Units.val hmod

private theorem toNat_emod_coprime {b : ℤ} {N : ℕ} (hN : 0 < N) (hb : b.gcd N = 1) :
    (b % (N : ℤ)).toNat.Coprime N := by
  rw [Nat.Coprime, ← Int.gcd_natCast_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg b (by positivity)), Int.gcd_emod, hb]

private theorem not_dvd_of_gcd_eq_one {b : ℤ} {N : ℕ} (hN : 2 ≤ N) (hb : b.gcd N = 1) :
    ¬ (N : ℤ) ∣ b := fun hdvd ↦ by
  have := Nat.le_of_dvd (by omega) (hb ▸ Int.dvd_gcd hdvd dvd_rfl); omega

private theorem two_mul_half_eq {N : ℕ} (hodd : Odd N) :
    2 * (((N + 1) / 2 : ℕ) : ℤ) = (N : ℤ) + 1 := by
  obtain ⟨m, rfl⟩ := hodd; omega

private theorem mem_maximalRealSubfield_of_inv_eq {ζ x : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN0 : N ≠ 0) (g : ℂ → ℂ) (hmap : ∀ φ : K →+* ℂ, φ x = g (φ ζ))
    (hconj : ∀ z : ℂ, (starRingEnd ℂ) (g z) = g ((starRingEnd ℂ) z))
    (hinv : ∀ z : ℂ, z ^ N = 1 → g z⁻¹ = g z) : x ∈ K⁺ := fun φ ↦ by
  have hφN : (φ ζ) ^ N = 1 := by rw [← map_pow, hζN, map_one]
  rw [Complex.star_def, hmap, hconj,
    (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hφN hN0)).symm, hinv _ hφN]

private theorem realUnit_ext {u v : (𝓞 K⁺)ˣ}
    (h : (((u : 𝓞 K⁺) : K⁺) : K) = (((v : 𝓞 K⁺) : K⁺) : K)) : u = v :=
  Units.ext (RingOfIntegers.ext (Subtype.ext h))

private noncomputable def liftRealUnit (u : (𝓞 K)ˣ) (hu : ((u : 𝓞 K) : K) ∈ K⁺) : (𝓞 K⁺)ˣ :=
  Classical.choose <| (mem_realUnits_iff K u).mp <|
    (TauCeti.NumberField.mem_realUnits_iff_coe_mem_maximalRealSubfield u).mpr hu

private theorem coe_liftRealUnit (u : (𝓞 K)ˣ) (hu : ((u : 𝓞 K) : K) ∈ K⁺) :
    (((liftRealUnit u hu : 𝓞 K⁺) : K⁺) : K) = ((u : 𝓞 K) : K) :=
  congrArg (fun x : 𝓞 K ↦ (x : K)) <| Classical.choose_spec <| (mem_realUnits_iff K u).mp <|
    (TauCeti.NumberField.mem_realUnits_iff_coe_mem_maximalRealSubfield u).mpr hu

private theorem coe_zpow_toInteger_unit {ζ : K} {N : ℕ} [NeZero N] (hζ : IsPrimitiveRoot ζ N)
    (k : ℤ) :
    ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne N)).unit ^ k : (𝓞 K)ˣ) : 𝓞 K) : K) =
      ζ ^ k := by
  let uζ : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne N)).unit
  change ((Units.map (algebraMap (𝓞 K) K).toMonoidHom (uζ ^ k) : Kˣ) : K) = ζ ^ k
  rw [map_zpow, Units.val_zpow_eq_zpow_val]; rfl

end Private

/-! ### Cyclotomic ratios -/

/-- The cyclotomic ratio `(ζ ^ b - 1) / (ζ - 1)` for `b : ℤ`. -/
def cyclotomicRatio {K : Type*} [Field K] (ζ : K) (b : ℤ) : K :=
  (ζ ^ b - 1) / (ζ - 1)

theorem cyclotomicRatio_eq {K : Type*} [Field K] (ζ : K) (b : ℤ) :
    cyclotomicRatio ζ b = (ζ ^ b - 1) / (ζ - 1) := by rfl

section CyclotomicRatio

variable {K : Type*} [Field K]

local notation3 "K⁺" => maximalRealSubfield K

@[simp]
theorem cyclotomicRatio_zero (ζ : K) : cyclotomicRatio ζ 0 = 0 := by simp [cyclotomicRatio]

@[simp]
theorem cyclotomicRatio_one {ζ : K} (hζ1 : ζ ≠ 1) : cyclotomicRatio ζ 1 = 1 := by
  simp [cyclotomicRatio, div_self (sub_ne_zero.mpr hζ1)]

theorem cyclotomicRatio_neg_one {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) :
    cyclotomicRatio ζ (-1) = -ζ⁻¹ := by
  rw [cyclotomicRatio, zpow_neg_one, div_eq_iff (sub_ne_zero.mpr hζ1)]; field_simp; ring

theorem cyclotomicRatio_natCast {ζ : K} (hζ1 : ζ ≠ 1) (b : ℕ) :
    cyclotomicRatio ζ (b : ℤ) = ∑ i ∈ range b, ζ ^ i := by
  rw [cyclotomicRatio, zpow_natCast, div_eq_iff (sub_ne_zero.mpr hζ1), geom_sum_mul]

/-- Multiplicative cocycle law for cyclotomic ratios:
`r_ζ(b * c) = r_{ζ ^ c}(b) * r_ζ(c)`. -/
theorem cyclotomicRatio_mul {ζ : K} {b c : ℤ} (hζc : ζ ^ c ≠ 1) :
    cyclotomicRatio ζ (b * c) = cyclotomicRatio (ζ ^ c) b * cyclotomicRatio ζ c := by
  have : ζ - 1 ≠ 0 := sub_ne_zero.mpr fun h1 ↦ hζc (by rw [h1, one_zpow])
  have : ζ ^ c - 1 ≠ 0 := sub_ne_zero.mpr hζc
  rw [cyclotomicRatio, cyclotomicRatio, cyclotomicRatio, mul_comm b c, zpow_mul]; field_simp

theorem cyclotomicRatio_eq_of_modeq {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) {a b : ℤ}
    (hab : a ≡ b [ZMOD N]) : cyclotomicRatio ζ a = cyclotomicRatio ζ b := by
  rw [cyclotomicRatio, cyclotomicRatio, zpow_eq_of_modeq hζN hab]

theorem cyclotomicRatio_map {L : Type*} [Field L] (σ : K →+* L) (ζ : K) (b : ℤ) :
    σ (cyclotomicRatio ζ b) = cyclotomicRatio (σ ζ) b := by
  simp [cyclotomicRatio, map_div₀, map_sub, map_zpow₀]

theorem cyclotomicRatio_inv {ζ : K} (hζ0 : ζ ≠ 0) (b : ℤ) :
    cyclotomicRatio ζ⁻¹ b = ζ ^ (1 - b) * cyclotomicRatio ζ b := by
  by_cases hζ1 : ζ = 1
  · simp [cyclotomicRatio, hζ1]
  · have : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
    rw [cyclotomicRatio, cyclotomicRatio, inv_zpow, zpow_sub₀ hζ0, zpow_one]; field_simp; ring

theorem cyclotomicRatio_neg {ζ : K} (hζ0 : ζ ≠ 0) (b : ℤ) :
    cyclotomicRatio ζ (-b) = -ζ ^ (-b) * cyclotomicRatio ζ b := by
  by_cases hζ1 : ζ = 1
  · simp [cyclotomicRatio, hζ1]
  · have : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
    rw [cyclotomicRatio, cyclotomicRatio, zpow_neg]; field_simp; ring

theorem cyclotomicRatio_ne_zero {ζ : K} {b : ℤ} (hζ1 : ζ ≠ 1) (hζb : ζ ^ b ≠ 1) :
    cyclotomicRatio ζ b ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hζb) (sub_ne_zero.mpr hζ1)

theorem cyclotomicRatio_mem_cyclotomicNumbers {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN : 2 ≤ N) (hζ1 : ζ ≠ 1) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b) (hζb : ζ ^ b ≠ 1) :
    Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) ∈
      cyclotomicNumbers ζ N := by
  have h1 := zpow_sub_one_mem_cyclotomicNumbers hζN (by omega) hb (sub_ne_zero.mpr hζb)
  have h2 := pow_sub_one_mem_cyclotomicNumbers (ζ := ζ) (N := N) (b := 1) (by omega) (by omega)
    (u := Units.mk0 (ζ - 1) (sub_ne_zero.mpr hζ1)) (by simp)
  rw [show Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) =
    Units.mk0 (ζ ^ b - 1) (sub_ne_zero.mpr hζb) *
      (Units.mk0 (ζ - 1) (sub_ne_zero.mpr hζ1))⁻¹ by
      ext; simp [cyclotomicRatio, div_eq_mul_inv]]
  exact mul_mem h1 (inv_mem h2)

private theorem zpow_mul_cyclotomicRatio_mem_cyclotomicNumbers {ζ : K} {N : ℕ}
    (hζN : ζ ^ N = 1) (hN : 2 ≤ N) (hζ1 : ζ ≠ 1) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b)
    (hζb : ζ ^ b ≠ 1) (e : ℤ) (hne : ζ ^ e * cyclotomicRatio ζ b ≠ 0) :
    Units.mk0 (ζ ^ e * cyclotomicRatio ζ b) hne ∈ cyclotomicNumbers ζ N := by
  have hζ0 := ne_zero_of_pow_eq_one hζN (by omega)
  rw [show Units.mk0 (ζ ^ e * cyclotomicRatio ζ b) hne =
    Units.mk0 (ζ ^ e) (zpow_ne_zero e hζ0) *
      Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) by ext; simp]
  exact mul_mem (zpow_mem_cyclotomicNumbers hζ0 e)
    (cyclotomicRatio_mem_cyclotomicNumbers hζN hN hζ1 hb hζb)

section RatioUnit

variable {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 2 ≤ N)

/-- When `ζ` is a primitive `N`-th root of unity (`2 ≤ N`) and `b.gcd N = 1`, the ratio
`(ζ ^ b - 1) / (ζ - 1)` is an integral unit in `(𝓞 K)ˣ`. -/
noncomputable def cyclotomicRatioUnit {b : ℤ} (hb : b.gcd N = 1) : (𝓞 K)ˣ :=
  have : NeZero N := ⟨by omega⟩
  (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit hN (toNat_emod_coprime (by omega) hb)).unit

@[simp]
theorem coe_cyclotomicRatioUnit {b : ℤ} (hb : b.gcd N = 1) :
    ((cyclotomicRatioUnit hζ hN hb : 𝓞 K) : K) = cyclotomicRatio ζ b := by
  have : NeZero N := ⟨by omega⟩
  set r : ℕ := (b % (N : ℤ)).toNat
  have hmodeq : (r : ℤ) ≡ b [ZMOD N] := by
    rw [Int.ModEq, Int.toNat_of_nonneg (Int.emod_nonneg b (by positivity)), Int.emod_emod]
  have hcoe : (algebraMap (𝓞 K) K) (cyclotomicRatioUnit hζ hN hb : 𝓞 K) =
      ∑ i ∈ range r, ζ ^ i := by
    change (algebraMap (𝓞 K) K) (∑ i ∈ range r, hζ.toInteger ^ i) = _
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ ↦ by
      rw [map_pow]; exact congrArg (· ^ i) hζ.coe_toInteger
  exact hcoe.trans <| (cyclotomicRatio_natCast (hζ.ne_one (by omega)) r).symm.trans <|
    cyclotomicRatio_eq_of_modeq hζ.pow_eq_one hmodeq

theorem cyclotomicRatioUnit_mem_cyclotomicUnits {b : ℤ} (hb : b.gcd N = 1) :
    cyclotomicRatioUnit hζ hN hb ∈ cyclotomicUnits K ζ N := by
  rw [mem_cyclotomicUnits_iff]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hndvd := not_dvd_of_gcd_eq_one hN hb
  have hζb : ζ ^ b ≠ 1 := fun h1 ↦ hndvd ((hζ.zpow_eq_one_iff_dvd b).mp h1)
  rw [show Units.map (algebraMap (𝓞 K) K).toMonoidHom (cyclotomicRatioUnit hζ hN hb) =
    Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) by ext; simp]
  exact cyclotomicRatio_mem_cyclotomicNumbers hζ.pow_eq_one hN hζ1 hndvd hζb

private theorem coe_zpow_mul_ratioUnit {b : ℤ} (hb : b.gcd N = 1) (e : ℤ) :
    have : NeZero N := ⟨by omega⟩
    ((((hζ.toInteger_isPrimitiveRoot.isUnit (by omega)).unit ^ e *
        cyclotomicRatioUnit hζ hN hb : (𝓞 K)ˣ) : 𝓞 K) : K) =
      ζ ^ e * cyclotomicRatio ζ b :=
  have : NeZero N := ⟨by omega⟩
  (map_mul (algebraMap (𝓞 K) K) _ _).trans <|
    congrArg₂ (· * ·) (coe_zpow_toInteger_unit hζ e) (coe_cyclotomicRatioUnit hζ hN hb)

private noncomputable def liftRealZpowRatioUnit {b : ℤ} (hb : b.gcd N = 1) (e : ℤ)
    (hreal : ζ ^ e * cyclotomicRatio ζ b ∈ K⁺) : (𝓞 K⁺)ˣ :=
  have : NeZero N := ⟨by omega⟩
  liftRealUnit
    ((hζ.toInteger_isPrimitiveRoot.isUnit (by omega)).unit ^ e * cyclotomicRatioUnit hζ hN hb)
    ((coe_zpow_mul_ratioUnit hζ hN hb e).symm ▸ hreal)

private theorem coe_liftRealZpowRatioUnit {b : ℤ} (hb : b.gcd N = 1) (e : ℤ)
    (hreal : ζ ^ e * cyclotomicRatio ζ b ∈ K⁺) :
    (((liftRealZpowRatioUnit hζ hN hb e hreal : 𝓞 K⁺) : K⁺) : K) =
      ζ ^ e * cyclotomicRatio ζ b := by
  rw [liftRealZpowRatioUnit, coe_liftRealUnit]; exact coe_zpow_mul_ratioUnit hζ hN hb e

private theorem algebraMap_liftRealZpowRatioUnit_mem {b : ℤ} (hb : b.gcd N = 1) (e : ℤ)
    (hreal : ζ ^ e * cyclotomicRatio ζ b ∈ K⁺) :
    Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
      (liftRealZpowRatioUnit hζ hN hb e hreal) ∈ cyclotomicUnits K ζ N := by
  rw [mem_cyclotomicUnits_iff]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hndvd := not_dvd_of_gcd_eq_one hN hb
  have hζb : ζ ^ b ≠ 1 := fun h1 ↦ hndvd ((hζ.zpow_eq_one_iff_dvd b).mp h1)
  have hne : ζ ^ e * cyclotomicRatio ζ b ≠ 0 :=
    mul_ne_zero (zpow_ne_zero e (hζ.ne_zero (by omega))) (cyclotomicRatio_ne_zero hζ1 hζb)
  rw [show Units.map (algebraMap (𝓞 K) K).toMonoidHom
      (Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
        (liftRealZpowRatioUnit hζ hN hb e hreal)) =
      Units.mk0 (ζ ^ e * cyclotomicRatio ζ b) hne by
    ext; exact coe_liftRealZpowRatioUnit hζ hN hb e hreal]
  exact zpow_mul_cyclotomicRatio_mem_cyclotomicNumbers hζ.pow_eq_one hN hζ1 hndvd hζb e hne

end RatioUnit

end CyclotomicRatio

/-! ### Real smoothed cyclotomic ratios for odd conductors -/

/-- For odd conductor `N`, the real smoothed cyclotomic ratio
`ζ ^ (((N + 1) / 2 : ℕ) * (1 - b)) * (ζ ^ b - 1) / (ζ - 1)`.
Here `(N + 1) / 2` is the canonical inverse of `2` modulo `N`, making this ratio invariant under
`ζ ↦ ζ⁻¹` and hence real whenever `ζ ^ N = 1`. -/
def smoothedCyclotomicRatio {K : Type*} [Field K] (ζ : K) (N : ℕ) (b : ℤ) : K :=
  ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b)) * cyclotomicRatio ζ b

theorem smoothedCyclotomicRatio_eq {K : Type*} [Field K] (ζ : K) (N : ℕ) (b : ℤ) :
    smoothedCyclotomicRatio ζ N b =
      ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b)) * cyclotomicRatio ζ b := by rfl

section SmoothedCyclotomicRatio

variable {K : Type*} [Field K]

local notation3 "K⁺" => maximalRealSubfield K

/-- Any integer `h` with `2 * h ≡ 1 [ZMOD N]` gives the same smoothed cyclotomic ratio. -/
theorem smoothedCyclotomicRatio_eq_of_two_mul_modeq {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hodd : Odd N) {h : ℤ} (hh : 2 * h ≡ 1 [ZMOD N]) (b : ℤ) :
    smoothedCyclotomicRatio ζ N b = ζ ^ (h * (1 - b)) * cyclotomicRatio ζ b := by
  rw [smoothedCyclotomicRatio]; congr 1; apply zpow_eq_of_modeq hζN
  have h2 := two_mul_half_eq hodd
  have h2eq : 2 * (((N + 1) / 2 : ℕ) : ℤ) ≡ 2 * h [ZMOD N] :=
    (Int.modEq_iff_dvd.mpr ⟨-1, by linear_combination -h2⟩).trans hh.symm
  obtain ⟨m, rfl⟩ := hodd
  have hcop : IsCoprime ((2 * m + 1 : ℕ) : ℤ) (2 : ℤ) := ⟨1, -(m : ℤ), by push_cast; ring⟩
  exact (Int.modEq_iff_dvd.mpr <| hcop.dvd_of_dvd_mul_left <|
    by simpa [mul_sub] using Int.modEq_iff_dvd.mp h2eq).mul_right (1 - b)

@[simp]
theorem smoothedCyclotomicRatio_one {ζ : K} (N : ℕ) (hζ1 : ζ ≠ 1) :
    smoothedCyclotomicRatio ζ N 1 = 1 := by simp [smoothedCyclotomicRatio, hζ1]

theorem smoothedCyclotomicRatio_neg {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hodd : Odd N)
    (b : ℤ) : smoothedCyclotomicRatio ζ N (-b) = -smoothedCyclotomicRatio ζ N b := by
  have hζ0 := ne_zero_of_pow_eq_one hζN hodd.pos.ne'
  have h2 := two_mul_half_eq hodd
  rw [smoothedCyclotomicRatio, smoothedCyclotomicRatio, cyclotomicRatio_neg hζ0]
  have hexp : ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - -b)) * ζ ^ (-b) =
      ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b)) := by
    rw [← zpow_add₀ hζ0]
    exact zpow_eq_of_modeq hζN (Int.modEq_iff_dvd.mpr ⟨-b, by linear_combination -b * h2⟩)
  linear_combination -(cyclotomicRatio ζ b) * hexp

theorem smoothedCyclotomicRatio_neg_one {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hodd : Odd N)
    (hζ1 : ζ ≠ 1) : smoothedCyclotomicRatio ζ N (-1) = -1 := by
  rw [smoothedCyclotomicRatio_neg hζN hodd 1, smoothedCyclotomicRatio_one N hζ1]

theorem smoothedCyclotomicRatio_eq_of_modeq {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    {a b : ℤ} (hab : a ≡ b [ZMOD N]) :
    smoothedCyclotomicRatio ζ N a = smoothedCyclotomicRatio ζ N b := by
  rw [smoothedCyclotomicRatio, smoothedCyclotomicRatio, cyclotomicRatio_eq_of_modeq hζN hab,
    zpow_eq_of_modeq hζN (Int.ModEq.mul_left _ (Int.ModEq.sub_left 1 hab))]

theorem smoothedCyclotomicRatio_map {L : Type*} [Field L] (σ : K →+* L) (ζ : K) (N : ℕ)
    (b : ℤ) : σ (smoothedCyclotomicRatio ζ N b) = smoothedCyclotomicRatio (σ ζ) N b := by
  simp [smoothedCyclotomicRatio, cyclotomicRatio_map, map_zpow₀]

/-- For odd `N` and `ζ ^ N = 1`, `smoothedCyclotomicRatio ζ N b` is invariant under
`ζ ↦ ζ⁻¹`. -/
theorem smoothedCyclotomicRatio_inv {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hodd : Odd N)
    (b : ℤ) : smoothedCyclotomicRatio ζ⁻¹ N b = smoothedCyclotomicRatio ζ N b := by
  have hζ0 := ne_zero_of_pow_eq_one hζN hodd.pos.ne'
  have h2 := two_mul_half_eq hodd
  rw [smoothedCyclotomicRatio, smoothedCyclotomicRatio, inv_zpow, ← zpow_neg,
    cyclotomicRatio_inv hζ0, ← mul_assoc, ← zpow_add₀ hζ0]
  exact congrArg (· * cyclotomicRatio ζ b) <| zpow_eq_of_modeq hζN
    (Int.modEq_iff_dvd.mpr ⟨1 - b, by linear_combination (1 - b) * h2⟩)

/-- Multiplicative cocycle law for smoothed cyclotomic ratios:
`γ_ζ(b * c) = γ_{ζ ^ c}(b) * γ_ζ(c)`. -/
theorem smoothedCyclotomicRatio_mul {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hodd : Odd N)
    {b c : ℤ} (hζc : ζ ^ c ≠ 1) :
    smoothedCyclotomicRatio ζ N (b * c) =
      smoothedCyclotomicRatio (ζ ^ c) N b * smoothedCyclotomicRatio ζ N c := by
  have hζ0 := ne_zero_of_pow_eq_one hζN hodd.pos.ne'
  rw [smoothedCyclotomicRatio, smoothedCyclotomicRatio, smoothedCyclotomicRatio,
    cyclotomicRatio_mul hζc, ← zpow_mul]
  have hexp : ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b * c)) =
      ζ ^ (c * ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b))) *
        ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - c)) := by rw [← zpow_add₀ hζ0]; congr 1; ring
  rw [hexp]; ring

/-- For odd `N` and `ζ ^ N = 1`, `smoothedCyclotomicRatio ζ N b` lies in the maximal real
subfield `K⁺`. -/
theorem smoothedCyclotomicRatio_mem_maximalRealSubfield {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hodd : Odd N) (b : ℤ) : smoothedCyclotomicRatio ζ N b ∈ K⁺ :=
  mem_maximalRealSubfield_of_inv_eq hζN hodd.pos.ne' (smoothedCyclotomicRatio · N b)
    (fun φ ↦ smoothedCyclotomicRatio_map φ ζ N b)
    (fun z ↦ smoothedCyclotomicRatio_map (starRingEnd ℂ) z N b)
    (fun _ hz ↦ smoothedCyclotomicRatio_inv hz hodd b)

theorem smoothedCyclotomicRatio_ne_zero {ζ : K} {N : ℕ} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {b : ℤ} (hζb : ζ ^ b ≠ 1) : smoothedCyclotomicRatio ζ N b ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ hζ0) (cyclotomicRatio_ne_zero hζ1 hζb)

theorem smoothedCyclotomicRatio_mem_cyclotomicNumbers {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN : 2 ≤ N) (hζ1 : ζ ≠ 1) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b) (hζb : ζ ^ b ≠ 1)
    (hne : smoothedCyclotomicRatio ζ N b ≠ 0) :
    Units.mk0 (smoothedCyclotomicRatio ζ N b) hne ∈ cyclotomicNumbers ζ N :=
  zpow_mul_cyclotomicRatio_mem_cyclotomicNumbers hζN hN hζ1 hb hζb _ hne

section SmoothedUnit

variable {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hodd : Odd N) (hN : 2 ≤ N)

/-- For odd `N ≥ 2`, a primitive `N`-th root of unity `ζ`, and `b.gcd N = 1`, the smoothed
cyclotomic ratio defines a real integral unit in `(𝓞 K⁺)ˣ`. -/
noncomputable def smoothedCyclotomicUnit {b : ℤ} (hb : b.gcd N = 1) : (𝓞 K⁺)ˣ :=
  liftRealZpowRatioUnit hζ hN hb _
    (smoothedCyclotomicRatio_mem_maximalRealSubfield hζ.pow_eq_one hodd b)

@[simp]
theorem coe_smoothedCyclotomicUnit {b : ℤ} (hb : b.gcd N = 1) :
    (((smoothedCyclotomicUnit hζ hodd hN hb : 𝓞 K⁺) : K⁺) : K) =
      smoothedCyclotomicRatio ζ N b :=
  coe_liftRealZpowRatioUnit hζ hN hb _ _

theorem algebraMap_smoothedCyclotomicUnit_mem_cyclotomicUnits {b : ℤ} (hb : b.gcd N = 1) :
    Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
      (smoothedCyclotomicUnit hζ hodd hN hb) ∈ cyclotomicUnits K ζ N :=
  algebraMap_liftRealZpowRatioUnit_mem hζ hN hb _ _

theorem smoothedCyclotomicUnit_mem_realCyclotomicUnits {b : ℤ} (hb : b.gcd N = 1) :
    smoothedCyclotomicUnit hζ hodd hN hb ∈ realCyclotomicUnits K ζ N :=
  mem_realCyclotomicUnits_iff.mpr
    (algebraMap_smoothedCyclotomicUnit_mem_cyclotomicUnits hζ hodd hN hb)

theorem smoothedCyclotomicUnit_one :
    smoothedCyclotomicUnit hζ hodd hN (by simp : (1 : ℤ).gcd N = 1) = 1 :=
  realUnit_ext (by simpa using smoothedCyclotomicRatio_one N (hζ.ne_one (by omega)))

theorem smoothedCyclotomicUnit_neg {b : ℤ} (hb : b.gcd N = 1) :
    smoothedCyclotomicUnit hζ hodd hN (by simpa using hb : (-b).gcd N = 1) =
      -(smoothedCyclotomicUnit hζ hodd hN hb) :=
  realUnit_ext (by simpa using smoothedCyclotomicRatio_neg hζ.pow_eq_one hodd b)

theorem smoothedCyclotomicUnit_neg_one :
    smoothedCyclotomicUnit hζ hodd hN (by simp : (-1 : ℤ).gcd N = 1) = -1 :=
  realUnit_ext (by
    simpa using smoothedCyclotomicRatio_neg_one hζ.pow_eq_one hodd (hζ.ne_one (by omega)))

theorem smoothedCyclotomicUnit_eq_of_modeq {a b : ℤ} (ha : a.gcd N = 1) (hb : b.gcd N = 1)
    (hab : a ≡ b [ZMOD N]) :
    smoothedCyclotomicUnit hζ hodd hN ha = smoothedCyclotomicUnit hζ hodd hN hb :=
  realUnit_ext (by simpa using smoothedCyclotomicRatio_eq_of_modeq hζ.pow_eq_one hab)

/-- Multiplicative cocycle law for `smoothedCyclotomicUnit` in `(𝓞 K⁺)ˣ`. -/
theorem smoothedCyclotomicUnit_mul {b c : ℤ} (hb : b.gcd N = 1) (hc : c.gcd N = 1) :
    smoothedCyclotomicUnit hζ hodd hN
        (by rw [← Int.isCoprime_iff_gcd_eq_one] at hb hc ⊢; exact hb.mul_left hc :
          (b * c).gcd N = 1) =
      smoothedCyclotomicUnit (hζ.zpow_of_gcd_eq_one c hc) hodd hN hb *
        smoothedCyclotomicUnit hζ hodd hN hc :=
  realUnit_ext (by
    simpa using smoothedCyclotomicRatio_mul hζ.pow_eq_one hodd (b := b)
      ((hζ.zpow_of_gcd_eq_one c hc).ne_one (by omega)))

end SmoothedUnit

/-- Ring isomorphisms act on `smoothedCyclotomicUnit` by transporting the primitive root. -/
theorem realUnitsMapEquiv_smoothedCyclotomicUnit {L : Type*} [Field L] (e : K ≃+* L)
    {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hodd : Odd N) (hN : 2 ≤ N)
    {b : ℤ} (hb : b.gcd N = 1) :
    realUnitsMapEquiv e (smoothedCyclotomicUnit hζ hodd hN hb) =
      smoothedCyclotomicUnit (hζ.map_of_injective e.injective) hodd hN hb :=
  realUnit_ext (by simpa using smoothedCyclotomicRatio_map e.toRingHom ζ N b)

/-- Explicit evaluation at conductor `5` and `b = 2`:
`smoothedCyclotomicRatio ζ 5 2 = ζ ^ 2 + ζ ^ 3`. -/
theorem smoothedCyclotomicRatio_five_two {ζ : K} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) :
    smoothedCyclotomicRatio ζ 5 2 = ζ ^ 2 + ζ ^ 3 := by
  have h2 : cyclotomicRatio ζ 2 = 1 + ζ := by
    simpa [Finset.sum_range_succ] using cyclotomicRatio_natCast hζ1 2
  have hinv3 : ζ ^ (-3 : ℤ) = ζ ^ 2 := by
    rw [← zpow_natCast]; exact zpow_eq_of_modeq hζ5 (by decide : (-3 : ℤ) ≡ 2 [ZMOD (5 : ℕ)])
  rw [smoothedCyclotomicRatio, h2,
    show ((((5 + 1) / 2 : ℕ) : ℤ) * (1 - 2)) = -3 by decide, hinv3]; ring

end SmoothedCyclotomicRatio

/-! ### Real smoothed cyclotomic ratios for arbitrary conductors and odd exponents -/

/-- For an arbitrary conductor (in particular, powers of `2`) and odd `b : ℤ`, the real smoothed
cyclotomic ratio `ζ ^ ((1 - b) / 2) * (ζ ^ b - 1) / (ζ - 1)`. When `b` is odd, `2 ∣ 1 - b`, so
this expression is invariant under `ζ ↦ ζ⁻¹` without needing an inverse of `2` modulo `N`. -/
def oddSmoothedCyclotomicRatio {K : Type*} [Field K] (ζ : K) (b : ℤ) : K :=
  ζ ^ ((1 - b) / 2) * cyclotomicRatio ζ b

theorem oddSmoothedCyclotomicRatio_eq {K : Type*} [Field K] (ζ : K) (b : ℤ) :
    oddSmoothedCyclotomicRatio ζ b = ζ ^ ((1 - b) / 2) * cyclotomicRatio ζ b := by rfl

section OddSmoothedCyclotomicRatio

variable {K : Type*} [Field K]

local notation3 "K⁺" => maximalRealSubfield K

@[simp]
theorem oddSmoothedCyclotomicRatio_one {ζ : K} (hζ1 : ζ ≠ 1) :
    oddSmoothedCyclotomicRatio ζ 1 = 1 := by simp [oddSmoothedCyclotomicRatio, hζ1]

theorem oddSmoothedCyclotomicRatio_neg {ζ : K} (hζ0 : ζ ≠ 0) {b : ℤ} (hb : Odd b) :
    oddSmoothedCyclotomicRatio ζ (-b) = -oddSmoothedCyclotomicRatio ζ b := by
  obtain ⟨m, rfl⟩ := hb
  rw [oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio, cyclotomicRatio_neg hζ0,
    show (1 - -(2 * m + 1)) / 2 = m + 1 by omega, show (1 - (2 * m + 1)) / 2 = -m by omega]
  have hexp : ζ ^ (m + 1) * ζ ^ (-(2 * m + 1)) = ζ ^ (-m) := by rw [← zpow_add₀ hζ0]; congr 1; ring
  linear_combination -(cyclotomicRatio ζ (2 * m + 1)) * hexp

theorem oddSmoothedCyclotomicRatio_neg_one {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) :
    oddSmoothedCyclotomicRatio ζ (-1) = -1 := by
  rw [oddSmoothedCyclotomicRatio_neg hζ0 odd_one, oddSmoothedCyclotomicRatio_one hζ1]

theorem oddSmoothedCyclotomicRatio_map {L : Type*} [Field L] (σ : K →+* L) (ζ : K) (b : ℤ) :
    σ (oddSmoothedCyclotomicRatio ζ b) = oddSmoothedCyclotomicRatio (σ ζ) b := by
  simp [oddSmoothedCyclotomicRatio, cyclotomicRatio_map, map_zpow₀]

/-- For odd `b`, `oddSmoothedCyclotomicRatio ζ b` is invariant under `ζ ↦ ζ⁻¹`. -/
theorem oddSmoothedCyclotomicRatio_inv {ζ : K} (hζ0 : ζ ≠ 0) {b : ℤ} (hb : Odd b) :
    oddSmoothedCyclotomicRatio ζ⁻¹ b = oddSmoothedCyclotomicRatio ζ b := by
  obtain ⟨m, rfl⟩ := hb
  rw [oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio,
    show (1 - (2 * m + 1)) / 2 = -m by omega, inv_zpow, ← zpow_neg,
    cyclotomicRatio_inv hζ0, ← mul_assoc, ← zpow_add₀ hζ0]
  congr 2; ring

/-- Multiplicative cocycle law for `oddSmoothedCyclotomicRatio` on odd exponents. -/
theorem oddSmoothedCyclotomicRatio_mul {ζ : K} (hζ0 : ζ ≠ 0) {b c : ℤ}
    (hb : Odd b) (hc : Odd c) (hζc : ζ ^ c ≠ 1) :
    oddSmoothedCyclotomicRatio ζ (b * c) =
      oddSmoothedCyclotomicRatio (ζ ^ c) b * oddSmoothedCyclotomicRatio ζ c := by
  obtain ⟨m, rfl⟩ := hb; obtain ⟨n, rfl⟩ := hc
  rw [oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio,
    cyclotomicRatio_mul hζc, ← zpow_mul,
    show (1 - (2 * m + 1) * (2 * n + 1)) / 2 = -(2 * m * n + m + n) by
      rw [show 1 - (2 * m + 1) * (2 * n + 1) = 2 * -(2 * m * n + m + n) by ring,
        Int.mul_ediv_cancel_left _ (by decide)],
    show (1 - (2 * m + 1)) / 2 = -m by omega, show (1 - (2 * n + 1)) / 2 = -n by omega]
  have hexp : ζ ^ (-(2 * m * n + m + n)) = ζ ^ ((2 * n + 1) * -m) * ζ ^ (-n) := by
    rw [← zpow_add₀ hζ0]; congr 1; ring
  rw [hexp]; ring

/-- When `ζ ^ m = -1` (for instance `m = 2 ^ (a - 1)` for a primitive `2 ^ a`-th root of unity),
shifting `b` by `2 * m` negates `oddSmoothedCyclotomicRatio ζ b`. -/
theorem oddSmoothedCyclotomicRatio_add_two_mul {ζ : K} {m : ℕ} (hm : ζ ^ m = -1) (b : ℤ) :
    oddSmoothedCyclotomicRatio ζ (b + 2 * (m : ℤ)) = -oddSmoothedCyclotomicRatio ζ b := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp only [pow_zero] at hm
    simp [show ∀ x : K, -x = x from fun x ↦ by linear_combination -x * hm]
  · have hζ2m : ζ ^ (2 * m) = 1 := by rw [mul_comm, pow_mul, hm]; ring
    have hζ0 : ζ ≠ 0 := fun h0 ↦
      zero_ne_one (by rw [h0, zero_pow hm0] at hm; linear_combination -hm)
    have hratio : cyclotomicRatio ζ (b + 2 * (m : ℤ)) = cyclotomicRatio ζ b :=
      cyclotomicRatio_eq_of_modeq hζ2m (Int.modEq_iff_dvd.mpr ⟨-1, by push_cast; ring⟩)
    rw [oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio, hratio,
      show (1 - (b + 2 * (m : ℤ))) / 2 = (1 - b) / 2 + -(m : ℤ) by omega,
      zpow_add₀ hζ0, zpow_neg, zpow_natCast, hm, inv_neg, inv_one]; ring

/-- When both `N` and `b` are odd and `ζ ^ N = 1`, the two smoothings agree. -/
theorem smoothedCyclotomicRatio_eq_oddSmoothedCyclotomicRatio {ζ : K} {N : ℕ}
    (hζN : ζ ^ N = 1) (hN : Odd N) {b : ℤ} (hb : Odd b) :
    smoothedCyclotomicRatio ζ N b = oddSmoothedCyclotomicRatio ζ b := by
  rw [smoothedCyclotomicRatio, oddSmoothedCyclotomicRatio]; congr 1
  obtain ⟨m, rfl⟩ := hb; have h2 := two_mul_half_eq hN
  rw [show (1 - (2 * m + 1)) / 2 = -m by omega]
  exact zpow_eq_of_modeq hζN (Int.modEq_iff_dvd.mpr ⟨m, by linear_combination m * h2⟩)

/-- Whenever `ζ` is a root of unity (`ζ ^ N = 1`, `0 < N`) and `b` is odd,
`oddSmoothedCyclotomicRatio ζ b` lies in the maximal real subfield `K⁺`. -/
theorem oddSmoothedCyclotomicRatio_mem_maximalRealSubfield {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN : 0 < N) {b : ℤ} (hb : Odd b) : oddSmoothedCyclotomicRatio ζ b ∈ K⁺ :=
  mem_maximalRealSubfield_of_inv_eq hζN hN.ne' (oddSmoothedCyclotomicRatio · b)
    (fun φ ↦ oddSmoothedCyclotomicRatio_map φ ζ b)
    (fun z ↦ oddSmoothedCyclotomicRatio_map (starRingEnd ℂ) z b)
    (fun _ hz ↦ oddSmoothedCyclotomicRatio_inv (ne_zero_of_pow_eq_one hz hN.ne') hb)

theorem oddSmoothedCyclotomicRatio_ne_zero {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {b : ℤ} (hζb : ζ ^ b ≠ 1) : oddSmoothedCyclotomicRatio ζ b ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ hζ0) (cyclotomicRatio_ne_zero hζ1 hζb)

theorem oddSmoothedCyclotomicRatio_mem_cyclotomicNumbers {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN : 2 ≤ N) (hζ1 : ζ ≠ 1) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b) (hζb : ζ ^ b ≠ 1)
    (hne : oddSmoothedCyclotomicRatio ζ b ≠ 0) :
    Units.mk0 (oddSmoothedCyclotomicRatio ζ b) hne ∈ cyclotomicNumbers ζ N :=
  zpow_mul_cyclotomicRatio_mem_cyclotomicNumbers hζN hN hζ1 hb hζb _ hne

section OddSmoothedUnit

variable {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 2 ≤ N)

/-- For a primitive `N`-th root of unity `ζ` (`2 ≤ N`) and an odd integer `b` coprime to `N`,
`oddSmoothedCyclotomicRatio ζ b` defines a real integral unit in `(𝓞 K⁺)ˣ`. -/
noncomputable def oddSmoothedCyclotomicUnit {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    (𝓞 K⁺)ˣ :=
  liftRealZpowRatioUnit hζ hN hb _
    (oddSmoothedCyclotomicRatio_mem_maximalRealSubfield hζ.pow_eq_one (by omega) hodd)

@[simp]
theorem coe_oddSmoothedCyclotomicUnit {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    (((oddSmoothedCyclotomicUnit hζ hN hodd hb : 𝓞 K⁺) : K⁺) : K) =
      oddSmoothedCyclotomicRatio ζ b :=
  coe_liftRealZpowRatioUnit hζ hN hb _ _

theorem oddSmoothedCyclotomicUnit_mem_realCyclotomicUnits {b : ℤ} (hodd : Odd b)
    (hb : b.gcd N = 1) :
    oddSmoothedCyclotomicUnit hζ hN hodd hb ∈ realCyclotomicUnits K ζ N :=
  mem_realCyclotomicUnits_iff.mpr (algebraMap_liftRealZpowRatioUnit_mem hζ hN hb _ _)

theorem oddSmoothedCyclotomicUnit_neg {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    oddSmoothedCyclotomicUnit hζ hN hodd.neg (by simpa using hb : (-b).gcd N = 1) =
      -(oddSmoothedCyclotomicUnit hζ hN hodd hb) :=
  realUnit_ext (by simpa using oddSmoothedCyclotomicRatio_neg (hζ.ne_zero (by omega)) hodd)

theorem oddSmoothedCyclotomicUnit_one :
    oddSmoothedCyclotomicUnit hζ hN odd_one (by simp : (1 : ℤ).gcd N = 1) = 1 :=
  realUnit_ext (by simpa using oddSmoothedCyclotomicRatio_one (hζ.ne_one (by omega)))

theorem oddSmoothedCyclotomicUnit_neg_one :
    oddSmoothedCyclotomicUnit hζ hN odd_one.neg (by simp : (-1 : ℤ).gcd N = 1) = -1 := by
  rw [oddSmoothedCyclotomicUnit_neg hζ hN odd_one (by simp), oddSmoothedCyclotomicUnit_one hζ hN]

end OddSmoothedUnit

theorem smoothedCyclotomicUnit_eq_oddSmoothedCyclotomicUnit {ζ : K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ N) (hNodd : Odd N) (hN : 2 ≤ N) {b : ℤ} (hbodd : Odd b)
    (hb : b.gcd N = 1) :
    smoothedCyclotomicUnit hζ hNodd hN hb = oddSmoothedCyclotomicUnit hζ hN hbodd hb :=
  realUnit_ext (by
    simpa using smoothedCyclotomicRatio_eq_oddSmoothedCyclotomicRatio hζ.pow_eq_one hNodd hbodd)

theorem oddSmoothedCyclotomicUnit_add_two_mul {ζ : K} {m : ℕ} (hζ : IsPrimitiveRoot ζ (2 * m))
    (hm : 1 ≤ m) {b : ℤ} (hodd : Odd b) (hb : b.gcd (2 * m) = 1) :
    oddSmoothedCyclotomicUnit hζ (by omega)
        (by obtain ⟨k, rfl⟩ := hodd; exact ⟨k + m, by ring⟩ : Odd (b + 2 * (m : ℤ)))
        (by simpa [Nat.cast_mul] using hb : (b + 2 * (m : ℤ)).gcd (2 * m) = 1) =
      -(oddSmoothedCyclotomicUnit hζ (by omega) hodd hb) := by
  apply realUnit_ext
  have hζm : ζ ^ m = -1 := by
    have hsq : (ζ ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, hζ.pow_eq_one]
    have hne : ζ ^ m ≠ 1 := fun h1 ↦ by
      have := Nat.le_of_dvd (by omega) (hζ.dvd_of_pow_eq_one m h1); omega
    exact (sq_eq_one_iff.mp hsq).resolve_left hne
  simpa using oddSmoothedCyclotomicRatio_add_two_mul hζm b

/-- Ring isomorphisms act on `oddSmoothedCyclotomicUnit` by transporting the primitive root. -/
theorem realUnitsMapEquiv_oddSmoothedCyclotomicUnit {L : Type*} [Field L] (e : K ≃+* L)
    {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 2 ≤ N)
    {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    realUnitsMapEquiv e (oddSmoothedCyclotomicUnit hζ hN hodd hb) =
      oddSmoothedCyclotomicUnit (hζ.map_of_injective e.injective) hN hodd hb :=
  realUnit_ext (by simpa using oddSmoothedCyclotomicRatio_map e.toRingHom ζ b)

end OddSmoothedCyclotomicRatio

end TauCeti
