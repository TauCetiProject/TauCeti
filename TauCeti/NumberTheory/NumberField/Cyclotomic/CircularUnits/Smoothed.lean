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

For an `N`-th root of unity `ζ` in a field `K` and an integer `b : ℤ`, the **cyclotomic ratio** is
`cyclotomicRatio ζ b = (ζ ^ b - 1) / (ζ - 1)`. When `ζ` is a primitive `N`-th root of unity
(`2 ≤ N`) and `Int.gcd b N = 1`, `cyclotomicRatio ζ b` is an algebraic integer unit lying in
`cyclotomicUnits K ζ N` (`cyclotomicRatioUnit`).

To obtain real circular units directly in `(𝓞 K⁺)ˣ`, this file introduces two canonical smoothings:

* For odd conductor `N`,
  `smoothedCyclotomicRatio ζ N b = ζ ^ (((N + 1) / 2 : ℕ) * (1 - b)) * r_ζ(b)`
  uses the canonical inverse `(N + 1) / 2` of `2` modulo `N`, is invariant under `ζ ↦ ζ⁻¹`,
  depends only on `b mod N`, satisfies the cocycle law `γ(b * c) = γ_{ζ ^ c}(b) * γ_ζ(c)`, and
  defines a real circular unit `smoothedCyclotomicUnit` in `realCyclotomicUnits K ζ N`.
* For arbitrary conductor `N` (in particular, powers of `2`) and odd `b : ℤ`,
  `oddSmoothedCyclotomicRatio ζ b = ζ ^ ((1 - b) / 2) * r_ζ(b)` requires no inverse of `2` modulo
  `N`, is invariant under `ζ ↦ ζ⁻¹`, agrees with `smoothedCyclotomicRatio` whenever `N` and `b`
  are both odd, flips sign under `b ↦ b + 2m` when `ζ ^ m = -1`, satisfies the cocycle law for
  odd exponents, and defines `oddSmoothedCyclotomicUnit` in `realCyclotomicUnits K ζ N`.

## Main definitions

* `TauCeti.cyclotomicRatio`, `TauCeti.smoothedCyclotomicRatio`,
  `TauCeti.oddSmoothedCyclotomicRatio`: field-level cyclotomic ratios and their real smoothings.
* `TauCeti.cyclotomicRatioUnit`, `TauCeti.smoothedCyclotomicUnit`,
  `TauCeti.oddSmoothedCyclotomicUnit`: corresponding integral (real) circular units.

## Main results

* `TauCeti.smoothedCyclotomicRatio_mem_maximalRealSubfield` and
  `TauCeti.oddSmoothedCyclotomicRatio_mem_maximalRealSubfield`: reality of the smoothed ratios.
* `TauCeti.smoothedCyclotomicRatio_mul`, `TauCeti.oddSmoothedCyclotomicRatio_mul`, and
  `TauCeti.smoothedCyclotomicUnit_mul`: multiplicative cocycle identities.
* `TauCeti.smoothedCyclotomicUnit_mem_realCyclotomicUnits` and
  `TauCeti.oddSmoothedCyclotomicUnit_mem_realCyclotomicUnits`: membership in
  `realCyclotomicUnits K ζ N`.
* `TauCeti.realUnitsMapEquiv_smoothedCyclotomicUnit` and
  `TauCeti.realUnitsMapEquiv_oddSmoothedCyclotomicUnit`: functorial action of ring isomorphisms.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer (1997), Chapter 8.
* R. Sharifi, *Iwasawa Theory*, Chapter 4.
-/

public section

open NumberField NumberField.IsCMField Finset

open scoped NumberField

namespace TauCeti

/-! ### Private helpers -/

private theorem zpow_eq_of_modeq {K : Type*} [Field K] {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    {a b : ℤ} (hab : a ≡ b [ZMOD N]) : ζ ^ a = ζ ^ b := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [Nat.cast_zero, Int.modEq_zero_iff] at hab
    rw [hab]
  · have hζ0 : ζ ≠ 0 := fun h0 ↦ by simp [h0, zero_pow hN] at hζN
    have huN : (Units.mk0 ζ hζ0) ^ N = 1 := Units.ext (by simp [hζN])
    have hmod : (Units.mk0 ζ hζ0) ^ a = (Units.mk0 ζ hζ0) ^ b := by
      rw [zpow_eq_zpow_emod' a huN, zpow_eq_zpow_emod' b huN, hab.eq]
    simpa using congrArg Units.val hmod

private theorem toNat_emod_coprime {b : ℤ} {N : ℕ} (hN : 0 < N) (hb : b.gcd N = 1) :
    (b % (N : ℤ)).toNat.Coprime N := by
  have hnn : 0 ≤ b % (N : ℤ) := Int.emod_nonneg b (by positivity)
  have hcast : ((b % (N : ℤ)).toNat : ℤ) = b % (N : ℤ) := Int.toNat_of_nonneg hnn
  rw [Nat.Coprime]
  have hnat : ((b % (N : ℤ)).toNat).gcd N = (b % (N : ℤ)).gcd N := by
    rw [← hcast, Int.gcd_natCast_natCast]
    simp [max_eq_left hnn]
  rw [hnat, Int.gcd_emod, hb]

private noncomputable def liftRealUnit {K : Type*} [Field K] (u : (𝓞 K)ˣ)
    (hu : ((u : 𝓞 K) : K) ∈ maximalRealSubfield K) : (𝓞 (maximalRealSubfield K))ˣ :=
  Classical.choose <| (mem_realUnits_iff K u).mp <|
    (TauCeti.NumberField.mem_realUnits_iff_coe_mem_maximalRealSubfield u).mpr hu

private theorem coe_liftRealUnit {K : Type*} [Field K] (u : (𝓞 K)ˣ)
    (hu : ((u : 𝓞 K) : K) ∈ maximalRealSubfield K) :
    (((liftRealUnit u hu : 𝓞 (maximalRealSubfield K)) : maximalRealSubfield K) : K) =
      ((u : 𝓞 K) : K) :=
  congrArg (fun x : 𝓞 K ↦ (x : K)) <|
    Classical.choose_spec <| (mem_realUnits_iff K u).mp <|
      (TauCeti.NumberField.mem_realUnits_iff_coe_mem_maximalRealSubfield u).mpr hu

private theorem coe_zpow_toInteger_unit {K : Type*} [Field K] {ζ : K} {N : ℕ} [NeZero N]
    (hζ : IsPrimitiveRoot ζ N) (k : ℤ) :
    ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne N)).unit ^ k : (𝓞 K)ˣ) : 𝓞 K) : K) =
      ζ ^ k := by
  let uζ : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne N)).unit
  have hval : ((Units.map (algebraMap (𝓞 K) K).toMonoidHom uζ : Kˣ) : K) = ζ := rfl
  have hmap : (((uζ ^ k : (𝓞 K)ˣ) : 𝓞 K) : K) =
      ((Units.map (algebraMap (𝓞 K) K).toMonoidHom (uζ ^ k) : Kˣ) : K) := rfl
  rw [hmap, map_zpow, Units.val_zpow_eq_zpow_val, hval]

/-! ### Cyclotomic ratios -/

/-- The cyclotomic ratio `(ζ ^ b - 1) / (ζ - 1)` for `b : ℤ`. -/
def cyclotomicRatio {K : Type*} [Field K] (ζ : K) (b : ℤ) : K :=
  (ζ ^ b - 1) / (ζ - 1)

theorem cyclotomicRatio_eq {K : Type*} [Field K] (ζ : K) (b : ℤ) :
    cyclotomicRatio ζ b = (ζ ^ b - 1) / (ζ - 1) := by
  rfl

section CyclotomicRatio

variable {K : Type*} [Field K]

@[simp]
theorem cyclotomicRatio_zero (ζ : K) : cyclotomicRatio ζ 0 = 0 := by
  simp [cyclotomicRatio]

@[simp]
theorem cyclotomicRatio_one {ζ : K} (hζ1 : ζ ≠ 1) : cyclotomicRatio ζ 1 = 1 := by
  simp [cyclotomicRatio, div_self (sub_ne_zero.mpr hζ1)]

theorem cyclotomicRatio_neg_one {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) :
    cyclotomicRatio ζ (-1) = -ζ⁻¹ := by
  rw [cyclotomicRatio, zpow_neg_one, div_eq_iff (sub_ne_zero.mpr hζ1)]
  field_simp
  ring

theorem cyclotomicRatio_natCast {ζ : K} (hζ1 : ζ ≠ 1) (b : ℕ) :
    cyclotomicRatio ζ (b : ℤ) = ∑ i ∈ range b, ζ ^ i := by
  rw [cyclotomicRatio, zpow_natCast, div_eq_iff (sub_ne_zero.mpr hζ1), geom_sum_mul]

/-- Multiplicative cocycle law for cyclotomic ratios:
`r_ζ(b * c) = r_{ζ ^ c}(b) * r_ζ(c)`. -/
theorem cyclotomicRatio_mul {ζ : K} {b c : ℤ} (hζc : ζ ^ c ≠ 1) :
    cyclotomicRatio ζ (b * c) = cyclotomicRatio (ζ ^ c) b * cyclotomicRatio ζ c := by
  have hζ1 : ζ ≠ 1 := by
    intro h1
    apply hζc
    rw [h1, one_zpow]
  rw [cyclotomicRatio, cyclotomicRatio, cyclotomicRatio, mul_comm b c, zpow_mul]
  have hne : ζ ^ c - 1 ≠ 0 := sub_ne_zero.mpr hζc
  have hne1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  field_simp

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
  · have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
    rw [cyclotomicRatio, cyclotomicRatio, inv_zpow, zpow_sub₀ hζ0, zpow_one]
    field_simp
    ring

theorem cyclotomicRatio_neg {ζ : K} (hζ0 : ζ ≠ 0) (b : ℤ) :
    cyclotomicRatio ζ (-b) = -ζ ^ (-b) * cyclotomicRatio ζ b := by
  by_cases hζ1 : ζ = 1
  · simp [cyclotomicRatio, hζ1]
  · have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
    rw [cyclotomicRatio, cyclotomicRatio, zpow_neg]
    field_simp
    ring

theorem cyclotomicRatio_ne_zero {ζ : K} {b : ℤ} (hζ1 : ζ ≠ 1) (hζb : ζ ^ b ≠ 1) :
    cyclotomicRatio ζ b ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hζb) (sub_ne_zero.mpr hζ1)

theorem cyclotomicRatio_mem_cyclotomicNumbers {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN : 2 ≤ N) (hζ1 : ζ ≠ 1) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b) (hζb : ζ ^ b ≠ 1) :
    Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) ∈
      cyclotomicNumbers ζ N := by
  have hNpos : 0 < N := by omega
  have h1 : Units.mk0 (ζ ^ b - 1) (sub_ne_zero.mpr hζb) ∈ cyclotomicNumbers ζ N :=
    zpow_sub_one_mem_cyclotomicNumbers hζN hNpos hb (sub_ne_zero.mpr hζb)
  have h2 : Units.mk0 (ζ - 1) (sub_ne_zero.mpr hζ1) ∈ cyclotomicNumbers ζ N :=
    pow_sub_one_mem_cyclotomicNumbers (b := 1) (by omega) (by omega) (by simp)
  have hEq : Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) =
      Units.mk0 (ζ ^ b - 1) (sub_ne_zero.mpr hζb) *
        (Units.mk0 (ζ - 1) (sub_ne_zero.mpr hζ1))⁻¹ := by
    ext
    simp [cyclotomicRatio, div_eq_mul_inv]
  rw [hEq]
  exact mul_mem h1 (inv_mem h2)

/-- When `ζ` is a primitive `N`-th root of unity (`2 ≤ N`) and `b.gcd N = 1`, the cyclotomic ratio
`(ζ ^ b - 1) / (ζ - 1)` is an integral unit in `(𝓞 K)ˣ`. -/
noncomputable def cyclotomicRatioUnit {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) : (𝓞 K)ˣ :=
  have : NeZero N := ⟨by omega⟩
  (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit hN (toNat_emod_coprime (by omega) hb)).unit

@[simp]
theorem coe_cyclotomicRatioUnit {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    ((cyclotomicRatioUnit hζ hN hb : 𝓞 K) : K) = cyclotomicRatio ζ b := by
  have hNpos : 0 < N := by omega
  have : NeZero N := ⟨hNpos.ne'⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  set r : ℕ := (b % (N : ℤ)).toNat
  have hcast : (r : ℤ) = b % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg b (by positivity))
  have hmodeq : (r : ℤ) ≡ b [ZMOD N] := by
    rw [Int.ModEq, hcast, Int.emod_emod]
  have hcoe : (algebraMap (𝓞 K) K) (cyclotomicRatioUnit hζ hN hb : 𝓞 K) = ∑ i ∈ range r, ζ ^ i := by
    have hsum : (cyclotomicRatioUnit hζ hN hb : 𝓞 K) = ∑ i ∈ range r, hζ.toInteger ^ i := rfl
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_pow]
    exact congrArg (· ^ i) hζ.coe_toInteger
  exact hcoe.trans <| (cyclotomicRatio_natCast hζ1 r).symm.trans <|
    cyclotomicRatio_eq_of_modeq hζ.pow_eq_one hmodeq

theorem cyclotomicRatioUnit_mem_cyclotomicUnits {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    cyclotomicRatioUnit hζ hN hb ∈ cyclotomicUnits K ζ N := by
  rw [mem_cyclotomicUnits_iff]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hndvd : ¬ (N : ℤ) ∣ b := by
    intro hdvd
    have hgcd : N ∣ b.gcd N := Int.dvd_gcd hdvd dvd_rfl
    rw [hb] at hgcd
    have := Nat.le_of_dvd (by omega) hgcd
    omega
  have hζb : ζ ^ b ≠ 1 := fun h1 ↦ hndvd ((hζ.zpow_eq_one_iff_dvd b).mp h1)
  have hEq : Units.map (algebraMap (𝓞 K) K).toMonoidHom (cyclotomicRatioUnit hζ hN hb) =
      Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) := by
    ext
    simp
  rw [hEq]
  exact cyclotomicRatio_mem_cyclotomicNumbers hζ.pow_eq_one hN hζ1 hndvd hζb

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
      ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b)) * cyclotomicRatio ζ b := by
  rfl

section SmoothedCyclotomicRatio

variable {K : Type*} [Field K]

/-- Any integer `h` with `2 * h ≡ 1 [ZMOD N]` gives the same smoothed cyclotomic ratio. -/
theorem smoothedCyclotomicRatio_eq_of_two_mul_modeq {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hodd : Odd N) {h : ℤ} (hh : 2 * h ≡ 1 [ZMOD N]) (b : ℤ) :
    smoothedCyclotomicRatio ζ N b = ζ ^ (h * (1 - b)) * cyclotomicRatio ζ b := by
  rw [smoothedCyclotomicRatio]
  congr 1
  apply zpow_eq_of_modeq hζN
  obtain ⟨m, rfl⟩ := hodd
  have hhalf : (((2 * m + 1 + 1) / 2 : ℕ) : ℤ) = (m : ℤ) + 1 := by omega
  have h2half : 2 * (((2 * m + 1 + 1) / 2 : ℕ) : ℤ) ≡ 1 [ZMOD (2 * m + 1 : ℕ)] := by
    rw [Int.modEq_iff_dvd, hhalf]
    exact ⟨-1, by push_cast; ring⟩
  have h2eq : 2 * (((2 * m + 1 + 1) / 2 : ℕ) : ℤ) ≡ 2 * h [ZMOD (2 * m + 1 : ℕ)] :=
    h2half.trans hh.symm
  have hcop : IsCoprime ((2 * m + 1 : ℕ) : ℤ) (2 : ℤ) :=
    ⟨1, -(m : ℤ), by push_cast; ring⟩
  have hmod : (((2 * m + 1 + 1) / 2 : ℕ) : ℤ) ≡ h [ZMOD (2 * m + 1 : ℕ)] := by
    rw [Int.modEq_iff_dvd] at h2eq ⊢
    exact hcop.dvd_of_dvd_mul_left (by simpa [mul_sub] using h2eq)
  exact hmod.mul_right (1 - b)

@[simp]
theorem smoothedCyclotomicRatio_one {ζ : K} (N : ℕ) (hζ1 : ζ ≠ 1) :
    smoothedCyclotomicRatio ζ N 1 = 1 := by
  simp [smoothedCyclotomicRatio, hζ1]

theorem smoothedCyclotomicRatio_neg {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hodd : Odd N) (b : ℤ) :
    smoothedCyclotomicRatio ζ N (-b) = -smoothedCyclotomicRatio ζ N b := by
  have hN0 : N ≠ 0 := by rcases hodd with ⟨m, rfl⟩; omega
  have hζ0 : ζ ≠ 0 := fun h0 ↦ by simp [h0, zero_pow hN0] at hζN
  rw [smoothedCyclotomicRatio, smoothedCyclotomicRatio, cyclotomicRatio_neg hζ0]
  have hexp : ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - -b)) * ζ ^ (-b) =
      ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b)) := by
    rw [← zpow_add₀ hζ0]
    apply zpow_eq_of_modeq hζN
    rw [Int.modEq_iff_dvd]
    obtain ⟨m, rfl⟩ := hodd
    have hhalf : (((2 * m + 1 + 1) / 2 : ℕ) : ℤ) = (m : ℤ) + 1 := by omega
    rw [hhalf]
    exact ⟨-b, by push_cast; ring⟩
  calc ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - -b)) * (-ζ ^ (-b) * cyclotomicRatio ζ b)
      = -(ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - -b)) * ζ ^ (-b)) * cyclotomicRatio ζ b := by ring
    _ = -(ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b)) * cyclotomicRatio ζ b) := by rw [hexp]; ring

theorem smoothedCyclotomicRatio_neg_one {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hodd : Odd N)
    (hζ1 : ζ ≠ 1) : smoothedCyclotomicRatio ζ N (-1) = -1 := by
  rw [smoothedCyclotomicRatio_neg hζN hodd 1, smoothedCyclotomicRatio_one N hζ1]

theorem smoothedCyclotomicRatio_eq_of_modeq {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    {a b : ℤ} (hab : a ≡ b [ZMOD N]) :
    smoothedCyclotomicRatio ζ N a = smoothedCyclotomicRatio ζ N b := by
  rw [smoothedCyclotomicRatio, smoothedCyclotomicRatio, cyclotomicRatio_eq_of_modeq hζN hab]
  congr 1
  apply zpow_eq_of_modeq hζN
  exact Int.ModEq.mul_left _ (Int.ModEq.sub_left 1 hab)

theorem smoothedCyclotomicRatio_map {L : Type*} [Field L] (σ : K →+* L) (ζ : K) (N : ℕ) (b : ℤ) :
    σ (smoothedCyclotomicRatio ζ N b) = smoothedCyclotomicRatio (σ ζ) N b := by
  simp [smoothedCyclotomicRatio, cyclotomicRatio_map, map_zpow₀]

/-- For odd `N` and `ζ ^ N = 1`, `smoothedCyclotomicRatio ζ N b` is invariant under `ζ ↦ ζ⁻¹`. -/
theorem smoothedCyclotomicRatio_inv {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hodd : Odd N) (b : ℤ) :
    smoothedCyclotomicRatio ζ⁻¹ N b = smoothedCyclotomicRatio ζ N b := by
  have hN0 : N ≠ 0 := by rcases hodd with ⟨m, rfl⟩; omega
  have hζ0 : ζ ≠ 0 := fun h0 ↦ by simp [h0, zero_pow hN0] at hζN
  rw [smoothedCyclotomicRatio, smoothedCyclotomicRatio, inv_zpow, ← zpow_neg,
    cyclotomicRatio_inv hζ0, ← mul_assoc, ← zpow_add₀ hζ0]
  congr 1
  apply zpow_eq_of_modeq hζN
  rw [Int.modEq_iff_dvd]
  obtain ⟨m, rfl⟩ := hodd
  have hhalf : (((2 * m + 1 + 1) / 2 : ℕ) : ℤ) = (m : ℤ) + 1 := by omega
  rw [hhalf]
  exact ⟨1 - b, by push_cast; ring⟩

/-- Multiplicative cocycle law for smoothed cyclotomic ratios:
`γ_ζ(b * c) = γ_{ζ ^ c}(b) * γ_ζ(c)`. -/
theorem smoothedCyclotomicRatio_mul {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1) (hodd : Odd N)
    {b c : ℤ} (hζc : ζ ^ c ≠ 1) :
    smoothedCyclotomicRatio ζ N (b * c) =
      smoothedCyclotomicRatio (ζ ^ c) N b * smoothedCyclotomicRatio ζ N c := by
  have hN0 : N ≠ 0 := by rcases hodd with ⟨m, rfl⟩; omega
  have hζ0 : ζ ≠ 0 := fun h0 ↦ by simp [h0, zero_pow hN0] at hζN
  rw [smoothedCyclotomicRatio, smoothedCyclotomicRatio, smoothedCyclotomicRatio,
    cyclotomicRatio_mul hζc, ← zpow_mul]
  have hexp : ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b * c)) =
      ζ ^ (c * ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b))) *
        ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - c)) := by
    rw [← zpow_add₀ hζ0]
    congr 1
    ring
  rw [hexp]
  ring

/-- For odd `N` and `ζ ^ N = 1`, `smoothedCyclotomicRatio ζ N b` lies in the maximal real
subfield `K⁺`. -/
theorem smoothedCyclotomicRatio_mem_maximalRealSubfield {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hodd : Odd N) (b : ℤ) :
    smoothedCyclotomicRatio ζ N b ∈ maximalRealSubfield K := by
  have hN0 : N ≠ 0 := by rcases hodd with ⟨m, rfl⟩; omega
  intro φ
  have hφN : (φ ζ) ^ N = 1 := by rw [← map_pow, hζN, map_one]
  have hstar : (starRingEnd ℂ) (φ ζ) = (φ ζ)⁻¹ :=
    (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hφN hN0)).symm
  rw [Complex.star_def, smoothedCyclotomicRatio_map, smoothedCyclotomicRatio_map,
    hstar, smoothedCyclotomicRatio_inv hφN hodd]

theorem smoothedCyclotomicRatio_ne_zero {ζ : K} {N : ℕ} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {b : ℤ} (hζb : ζ ^ b ≠ 1) : smoothedCyclotomicRatio ζ N b ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ hζ0) (cyclotomicRatio_ne_zero hζ1 hζb)

theorem smoothedCyclotomicRatio_mem_cyclotomicNumbers {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN : 2 ≤ N) (hζ1 : ζ ≠ 1) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b) (hζb : ζ ^ b ≠ 1)
    (hne : smoothedCyclotomicRatio ζ N b ≠ 0) :
    Units.mk0 (smoothedCyclotomicRatio ζ N b) hne ∈ cyclotomicNumbers ζ N := by
  have hζ0 : ζ ≠ 0 := fun h0 ↦ by simp [h0, zero_pow (by omega : N ≠ 0)] at hζN
  have hEq : Units.mk0 (smoothedCyclotomicRatio ζ N b) hne =
      Units.mk0 (ζ ^ ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b))) (zpow_ne_zero _ hζ0) *
        Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) := by
    ext
    simp [smoothedCyclotomicRatio]
  rw [hEq]
  exact mul_mem (zpow_mem_cyclotomicNumbers hζ0 _)
    (cyclotomicRatio_mem_cyclotomicNumbers hζN hN hζ1 hb hζb)

private noncomputable def smoothedCyclotomicUnitAux {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) : (𝓞 K)ˣ :=
  have : NeZero N := ⟨by omega⟩
  (hζ.toInteger_isPrimitiveRoot.isUnit (by omega)).unit ^
      ((((N + 1) / 2 : ℕ) : ℤ) * (1 - b)) *
    cyclotomicRatioUnit hζ hN hb

private theorem coe_smoothedCyclotomicUnitAux {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    ((smoothedCyclotomicUnitAux hζ hN hb : 𝓞 K) : K) = smoothedCyclotomicRatio ζ N b := by
  have : NeZero N := ⟨by omega⟩
  exact (map_mul (algebraMap (𝓞 K) K) _ _).trans <|
    congrArg₂ (· * ·) (coe_zpow_toInteger_unit hζ _) (coe_cyclotomicRatioUnit hζ hN hb)

/-- For odd `N ≥ 2`, a primitive `N`-th root of unity `ζ`, and `b.gcd N = 1`, the smoothed
cyclotomic ratio defines a real integral unit in `(𝓞 K⁺)ˣ`. -/
noncomputable def smoothedCyclotomicUnit {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hodd : Odd N) (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    (𝓞 (maximalRealSubfield K))ˣ :=
  liftRealUnit (smoothedCyclotomicUnitAux hζ hN hb) (by
    rw [coe_smoothedCyclotomicUnitAux]
    exact smoothedCyclotomicRatio_mem_maximalRealSubfield hζ.pow_eq_one hodd b)

@[simp]
theorem coe_smoothedCyclotomicUnit {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hodd : Odd N) (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    (((smoothedCyclotomicUnit hζ hodd hN hb : 𝓞 (maximalRealSubfield K)) :
      maximalRealSubfield K) : K) = smoothedCyclotomicRatio ζ N b := by
  rw [smoothedCyclotomicUnit, coe_liftRealUnit, coe_smoothedCyclotomicUnitAux]

theorem algebraMap_smoothedCyclotomicUnit_mem_cyclotomicUnits {ζ : K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ N) (hodd : Odd N) (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)).toMonoidHom
      (smoothedCyclotomicUnit hζ hodd hN hb) ∈ cyclotomicUnits K ζ N := by
  rw [mem_cyclotomicUnits_iff]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hndvd : ¬ (N : ℤ) ∣ b := by
    intro hdvd
    have hgcd : N ∣ b.gcd N := Int.dvd_gcd hdvd dvd_rfl
    rw [hb] at hgcd
    have := Nat.le_of_dvd (by omega) hgcd
    omega
  have hζb : ζ ^ b ≠ 1 := fun h1 ↦ hndvd ((hζ.zpow_eq_one_iff_dvd b).mp h1)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hne := smoothedCyclotomicRatio_ne_zero (N := N) hζ0 hζ1 hζb
  have hEq : Units.map (algebraMap (𝓞 K) K).toMonoidHom
        (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)).toMonoidHom
          (smoothedCyclotomicUnit hζ hodd hN hb)) =
      Units.mk0 (smoothedCyclotomicRatio ζ N b) hne := by
    ext
    exact coe_smoothedCyclotomicUnit hζ hodd hN hb
  rw [hEq]
  exact smoothedCyclotomicRatio_mem_cyclotomicNumbers hζ.pow_eq_one hN hζ1 hndvd hζb hne

theorem smoothedCyclotomicUnit_mem_realCyclotomicUnits {ζ : K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ N) (hodd : Odd N) (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    smoothedCyclotomicUnit hζ hodd hN hb ∈ realCyclotomicUnits K ζ N :=
  mem_realCyclotomicUnits_iff.mpr
    (algebraMap_smoothedCyclotomicUnit_mem_cyclotomicUnits hζ hodd hN hb)

theorem smoothedCyclotomicUnit_one {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hodd : Odd N) (hN : 2 ≤ N) :
    smoothedCyclotomicUnit hζ hodd hN (by simp : (1 : ℤ).gcd N = 1) = 1 := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using smoothedCyclotomicRatio_one N (hζ.ne_one (by omega))

theorem smoothedCyclotomicUnit_neg {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hodd : Odd N) (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    smoothedCyclotomicUnit hζ hodd hN (by simpa using hb : (-b).gcd N = 1) =
      -(smoothedCyclotomicUnit hζ hodd hN hb) := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using smoothedCyclotomicRatio_neg hζ.pow_eq_one hodd b

theorem smoothedCyclotomicUnit_neg_one {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hodd : Odd N) (hN : 2 ≤ N) :
    smoothedCyclotomicUnit hζ hodd hN (by simp : (-1 : ℤ).gcd N = 1) = -1 := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using smoothedCyclotomicRatio_neg_one hζ.pow_eq_one hodd (hζ.ne_one (by omega))

theorem smoothedCyclotomicUnit_eq_of_modeq {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hodd : Odd N) (hN : 2 ≤ N) {a b : ℤ} (ha : a.gcd N = 1) (hb : b.gcd N = 1)
    (hab : a ≡ b [ZMOD N]) :
    smoothedCyclotomicUnit hζ hodd hN ha = smoothedCyclotomicUnit hζ hodd hN hb := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using smoothedCyclotomicRatio_eq_of_modeq hζ.pow_eq_one hab

/-- Multiplicative cocycle law for `smoothedCyclotomicUnit` in `(𝓞 K⁺)ˣ`. -/
theorem smoothedCyclotomicUnit_mul {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hodd : Odd N) (hN : 2 ≤ N) {b c : ℤ} (hb : b.gcd N = 1) (hc : c.gcd N = 1) :
    smoothedCyclotomicUnit hζ hodd hN
        (by
          rw [← Int.isCoprime_iff_gcd_eq_one] at hb hc ⊢
          exact hb.mul_left hc : (b * c).gcd N = 1) =
      smoothedCyclotomicUnit (hζ.zpow_of_gcd_eq_one c hc) hodd hN hb *
        smoothedCyclotomicUnit hζ hodd hN hc := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  have hζc : ζ ^ c ≠ 1 := (hζ.zpow_of_gcd_eq_one c hc).ne_one (by omega)
  simpa using smoothedCyclotomicRatio_mul hζ.pow_eq_one hodd (b := b) hζc

/-- Ring isomorphisms act on `smoothedCyclotomicUnit` by transporting the primitive root. -/
theorem realUnitsMapEquiv_smoothedCyclotomicUnit {L : Type*} [Field L] (e : K ≃+* L)
    {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hodd : Odd N) (hN : 2 ≤ N)
    {b : ℤ} (hb : b.gcd N = 1) :
    realUnitsMapEquiv e (smoothedCyclotomicUnit hζ hodd hN hb) =
      smoothedCyclotomicUnit (hζ.map_of_injective e.injective) hodd hN hb := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using smoothedCyclotomicRatio_map e.toRingHom ζ N b

/-- Explicit evaluation at conductor `5` and `b = 2`:
`smoothedCyclotomicRatio ζ 5 2 = ζ ^ 2 + ζ ^ 3`. -/
theorem smoothedCyclotomicRatio_five_two {ζ : K} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) :
    smoothedCyclotomicRatio ζ 5 2 = ζ ^ 2 + ζ ^ 3 := by
  have h2 : cyclotomicRatio ζ 2 = 1 + ζ := by
    simpa [Finset.sum_range_succ] using cyclotomicRatio_natCast hζ1 2
  rw [smoothedCyclotomicRatio, h2]
  have hexp : ((((5 + 1) / 2 : ℕ) : ℤ) * (1 - 2)) = (-3 : ℤ) := by decide
  rw [hexp]
  have hinv3 : ζ ^ (-3 : ℤ) = ζ ^ 2 := by
    rw [← zpow_natCast]
    exact zpow_eq_of_modeq hζ5 (by decide : (-3 : ℤ) ≡ 2 [ZMOD (5 : ℕ)])
  rw [hinv3]
  ring

end SmoothedCyclotomicRatio

/-! ### Real smoothed cyclotomic ratios for arbitrary conductors and odd exponents -/

/-- For an arbitrary conductor (in particular, powers of `2`) and odd `b : ℤ`, the real smoothed
cyclotomic ratio `ζ ^ ((1 - b) / 2) * (ζ ^ b - 1) / (ζ - 1)`. When `b` is odd, `2 ∣ 1 - b`, so
this expression is invariant under `ζ ↦ ζ⁻¹` without needing an inverse of `2` modulo `N`. -/
def oddSmoothedCyclotomicRatio {K : Type*} [Field K] (ζ : K) (b : ℤ) : K :=
  ζ ^ ((1 - b) / 2) * cyclotomicRatio ζ b

theorem oddSmoothedCyclotomicRatio_eq {K : Type*} [Field K] (ζ : K) (b : ℤ) :
    oddSmoothedCyclotomicRatio ζ b = ζ ^ ((1 - b) / 2) * cyclotomicRatio ζ b := by
  rfl

section OddSmoothedCyclotomicRatio

variable {K : Type*} [Field K]

@[simp]
theorem oddSmoothedCyclotomicRatio_one {ζ : K} (hζ1 : ζ ≠ 1) :
    oddSmoothedCyclotomicRatio ζ 1 = 1 := by
  simp [oddSmoothedCyclotomicRatio, hζ1]

theorem oddSmoothedCyclotomicRatio_neg {ζ : K} (hζ0 : ζ ≠ 0) {b : ℤ} (hb : Odd b) :
    oddSmoothedCyclotomicRatio ζ (-b) = -oddSmoothedCyclotomicRatio ζ b := by
  obtain ⟨m, rfl⟩ := hb
  rw [oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio, cyclotomicRatio_neg hζ0]
  have h1 : (1 - -(2 * m + 1)) / 2 = m + 1 := by omega
  have h2 : (1 - (2 * m + 1)) / 2 = -m := by omega
  rw [h1, h2]
  have hexp : ζ ^ (m + 1) * ζ ^ (-(2 * m + 1)) = ζ ^ (-m) := by
    rw [← zpow_add₀ hζ0]
    congr 1
    ring
  calc ζ ^ (m + 1) * (-ζ ^ (-(2 * m + 1)) * cyclotomicRatio ζ (2 * m + 1))
      = -(ζ ^ (m + 1) * ζ ^ (-(2 * m + 1))) * cyclotomicRatio ζ (2 * m + 1) := by ring
    _ = -(ζ ^ (-m) * cyclotomicRatio ζ (2 * m + 1)) := by rw [hexp]; ring

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
  have h1 : (1 - (2 * m + 1)) / 2 = -m := by omega
  rw [oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio, h1, inv_zpow, ← zpow_neg,
    cyclotomicRatio_inv hζ0, ← mul_assoc, ← zpow_add₀ hζ0]
  congr 2
  ring

/-- Multiplicative cocycle law for `oddSmoothedCyclotomicRatio` on odd exponents. -/
theorem oddSmoothedCyclotomicRatio_mul {ζ : K} (hζ0 : ζ ≠ 0) {b c : ℤ}
    (hb : Odd b) (hc : Odd c) (hζc : ζ ^ c ≠ 1) :
    oddSmoothedCyclotomicRatio ζ (b * c) =
      oddSmoothedCyclotomicRatio (ζ ^ c) b * oddSmoothedCyclotomicRatio ζ c := by
  obtain ⟨m, rfl⟩ := hb
  obtain ⟨n, rfl⟩ := hc
  rw [oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio,
    cyclotomicRatio_mul hζc, ← zpow_mul]
  have h1 : (1 - (2 * m + 1) * (2 * n + 1)) / 2 = -(2 * m * n + m + n) := by
    have hmul : 1 - (2 * m + 1) * (2 * n + 1) = 2 * -(2 * m * n + m + n) := by ring
    rw [hmul, Int.mul_ediv_cancel_left _ (by decide)]
  have h2 : (1 - (2 * m + 1)) / 2 = -m := by omega
  have h3 : (1 - (2 * n + 1)) / 2 = -n := by omega
  rw [h1, h2, h3]
  have hexp : ζ ^ (-(2 * m * n + m + n)) = ζ ^ ((2 * n + 1) * -m) * ζ ^ (-n) := by
    rw [← zpow_add₀ hζ0]
    congr 1
    ring
  rw [hexp]
  ring

/-- When `ζ ^ m = -1` (for instance `m = 2 ^ (a - 1)` for a primitive `2 ^ a`-th root of unity),
shifting `b` by `2 * m` negates `oddSmoothedCyclotomicRatio ζ b`. -/
theorem oddSmoothedCyclotomicRatio_add_two_mul {ζ : K} {m : ℕ} (hm : ζ ^ m = -1) (b : ℤ) :
    oddSmoothedCyclotomicRatio ζ (b + 2 * (m : ℤ)) = -oddSmoothedCyclotomicRatio ζ b := by
  by_cases hm0 : m = 0
  · subst hm0
    simp only [pow_zero] at hm
    have hneg : ∀ x : K, -x = x := fun x ↦ by
      calc -x = (-1 : K) * x := by ring
        _ = 1 * x := by rw [← hm]
        _ = x := one_mul x
    simp [hneg]
  · have hζ2m : ζ ^ (2 * m) = 1 := by
      rw [mul_comm, pow_mul, hm]
      ring
    have hζ0 : ζ ≠ 0 := by
      intro h0
      rw [h0, zero_pow hm0] at hm
      exact zero_ne_one (by linear_combination -hm)
    rw [oddSmoothedCyclotomicRatio, oddSmoothedCyclotomicRatio]
    have hratio : cyclotomicRatio ζ (b + 2 * (m : ℤ)) = cyclotomicRatio ζ b := by
      apply cyclotomicRatio_eq_of_modeq hζ2m
      rw [Int.modEq_iff_dvd]
      exact ⟨-1, by push_cast; ring⟩
    have hdiv : (1 - (b + 2 * (m : ℤ))) / 2 = (1 - b) / 2 + -(m : ℤ) := by omega
    rw [hratio, hdiv, zpow_add₀ hζ0, zpow_neg, zpow_natCast, hm, inv_neg, inv_one]
    ring

/-- When both `N` and `b` are odd and `ζ ^ N = 1`, the two smoothings agree. -/
theorem smoothedCyclotomicRatio_eq_oddSmoothedCyclotomicRatio {ζ : K} {N : ℕ}
    (hζN : ζ ^ N = 1) (hN : Odd N) {b : ℤ} (hb : Odd b) :
    smoothedCyclotomicRatio ζ N b = oddSmoothedCyclotomicRatio ζ b := by
  rw [smoothedCyclotomicRatio, oddSmoothedCyclotomicRatio]
  congr 1
  apply zpow_eq_of_modeq hζN
  rw [Int.modEq_iff_dvd]
  obtain ⟨k, rfl⟩ := hN
  obtain ⟨m, rfl⟩ := hb
  have hhalf : (((2 * k + 1 + 1) / 2 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
  have hbdiv : (1 - (2 * m + 1)) / 2 = -m := by omega
  rw [hhalf, hbdiv]
  exact ⟨m, by push_cast; ring⟩

/-- Whenever `ζ` is a root of unity (`ζ ^ N = 1`, `0 < N`) and `b` is odd,
`oddSmoothedCyclotomicRatio ζ b` lies in the maximal real subfield `K⁺`. -/
theorem oddSmoothedCyclotomicRatio_mem_maximalRealSubfield {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN : 0 < N) {b : ℤ} (hb : Odd b) :
    oddSmoothedCyclotomicRatio ζ b ∈ maximalRealSubfield K := by
  intro φ
  have hφN : (φ ζ) ^ N = 1 := by rw [← map_pow, hζN, map_one]
  have hφ0 : φ ζ ≠ 0 := fun h0 ↦ by simp [h0, zero_pow hN.ne'] at hφN
  have hstar : (starRingEnd ℂ) (φ ζ) = (φ ζ)⁻¹ :=
    (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hφN hN.ne')).symm
  rw [Complex.star_def, oddSmoothedCyclotomicRatio_map, oddSmoothedCyclotomicRatio_map,
    hstar, oddSmoothedCyclotomicRatio_inv hφ0 hb]

theorem oddSmoothedCyclotomicRatio_ne_zero {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    {b : ℤ} (hζb : ζ ^ b ≠ 1) : oddSmoothedCyclotomicRatio ζ b ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ hζ0) (cyclotomicRatio_ne_zero hζ1 hζb)

theorem oddSmoothedCyclotomicRatio_mem_cyclotomicNumbers {ζ : K} {N : ℕ} (hζN : ζ ^ N = 1)
    (hN : 2 ≤ N) (hζ1 : ζ ≠ 1) {b : ℤ} (hb : ¬ (N : ℤ) ∣ b) (hζb : ζ ^ b ≠ 1)
    (hne : oddSmoothedCyclotomicRatio ζ b ≠ 0) :
    Units.mk0 (oddSmoothedCyclotomicRatio ζ b) hne ∈ cyclotomicNumbers ζ N := by
  have hζ0 : ζ ≠ 0 := fun h0 ↦ by simp [h0, zero_pow (by omega : N ≠ 0)] at hζN
  have hEq : Units.mk0 (oddSmoothedCyclotomicRatio ζ b) hne =
      Units.mk0 (ζ ^ ((1 - b) / 2)) (zpow_ne_zero _ hζ0) *
        Units.mk0 (cyclotomicRatio ζ b) (cyclotomicRatio_ne_zero hζ1 hζb) := by
    ext
    simp [oddSmoothedCyclotomicRatio]
  rw [hEq]
  exact mul_mem (zpow_mem_cyclotomicNumbers hζ0 _)
    (cyclotomicRatio_mem_cyclotomicNumbers hζN hN hζ1 hb hζb)

private noncomputable def oddSmoothedCyclotomicUnitAux {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) : (𝓞 K)ˣ :=
  have : NeZero N := ⟨by omega⟩
  (hζ.toInteger_isPrimitiveRoot.isUnit (by omega)).unit ^ ((1 - b) / 2) *
    cyclotomicRatioUnit hζ hN hb

private theorem coe_oddSmoothedCyclotomicUnitAux {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hb : b.gcd N = 1) :
    ((oddSmoothedCyclotomicUnitAux hζ hN hb : 𝓞 K) : K) = oddSmoothedCyclotomicRatio ζ b := by
  have : NeZero N := ⟨by omega⟩
  exact (map_mul (algebraMap (𝓞 K) K) _ _).trans <|
    congrArg₂ (· * ·) (coe_zpow_toInteger_unit hζ _) (coe_cyclotomicRatioUnit hζ hN hb)

/-- For a primitive `N`-th root of unity `ζ` (`2 ≤ N`) and an odd integer `b` coprime to `N`,
`oddSmoothedCyclotomicRatio ζ b` defines a real integral unit in `(𝓞 K⁺)ˣ`. -/
noncomputable def oddSmoothedCyclotomicUnit {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    (𝓞 (maximalRealSubfield K))ˣ :=
  liftRealUnit (oddSmoothedCyclotomicUnitAux hζ hN hb) (by
    rw [coe_oddSmoothedCyclotomicUnitAux]
    exact oddSmoothedCyclotomicRatio_mem_maximalRealSubfield hζ.pow_eq_one (by omega) hodd)

@[simp]
theorem coe_oddSmoothedCyclotomicUnit {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    (((oddSmoothedCyclotomicUnit hζ hN hodd hb : 𝓞 (maximalRealSubfield K)) :
      maximalRealSubfield K) : K) = oddSmoothedCyclotomicRatio ζ b := by
  rw [oddSmoothedCyclotomicUnit, coe_liftRealUnit, coe_oddSmoothedCyclotomicUnitAux]

theorem oddSmoothedCyclotomicUnit_mem_realCyclotomicUnits {ζ : K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ N) (hN : 2 ≤ N) {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    oddSmoothedCyclotomicUnit hζ hN hodd hb ∈ realCyclotomicUnits K ζ N := by
  rw [mem_realCyclotomicUnits_iff, mem_cyclotomicUnits_iff]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hndvd : ¬ (N : ℤ) ∣ b := by
    intro hdvd
    have hgcd : N ∣ b.gcd N := Int.dvd_gcd hdvd dvd_rfl
    rw [hb] at hgcd
    have := Nat.le_of_dvd (by omega) hgcd
    omega
  have hζb : ζ ^ b ≠ 1 := fun h1 ↦ hndvd ((hζ.zpow_eq_one_iff_dvd b).mp h1)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hne := oddSmoothedCyclotomicRatio_ne_zero hζ0 hζ1 hζb
  have hEq : Units.map (algebraMap (𝓞 K) K).toMonoidHom
        (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)).toMonoidHom
          (oddSmoothedCyclotomicUnit hζ hN hodd hb)) =
      Units.mk0 (oddSmoothedCyclotomicRatio ζ b) hne := by
    ext
    exact coe_oddSmoothedCyclotomicUnit hζ hN hodd hb
  rw [hEq]
  exact oddSmoothedCyclotomicRatio_mem_cyclotomicNumbers hζ.pow_eq_one hN hζ1 hndvd hζb hne

theorem smoothedCyclotomicUnit_eq_oddSmoothedCyclotomicUnit {ζ : K} {N : ℕ}
    (hζ : IsPrimitiveRoot ζ N) (hNodd : Odd N) (hN : 2 ≤ N) {b : ℤ} (hbodd : Odd b)
    (hb : b.gcd N = 1) :
    smoothedCyclotomicUnit hζ hNodd hN hb = oddSmoothedCyclotomicUnit hζ hN hbodd hb := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using smoothedCyclotomicRatio_eq_oddSmoothedCyclotomicRatio hζ.pow_eq_one hNodd hbodd

theorem oddSmoothedCyclotomicUnit_neg {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    oddSmoothedCyclotomicUnit hζ hN hodd.neg (by simpa using hb : (-b).gcd N = 1) =
      -(oddSmoothedCyclotomicUnit hζ hN hodd hb) := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using oddSmoothedCyclotomicRatio_neg (hζ.ne_zero (by omega)) hodd

theorem oddSmoothedCyclotomicUnit_one {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 2 ≤ N) :
    oddSmoothedCyclotomicUnit hζ hN odd_one (by simp : (1 : ℤ).gcd N = 1) = 1 := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using oddSmoothedCyclotomicRatio_one (hζ.ne_one (by omega))

theorem oddSmoothedCyclotomicUnit_neg_one {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 2 ≤ N) :
    oddSmoothedCyclotomicUnit hζ hN odd_one.neg (by simp : (-1 : ℤ).gcd N = 1) = -1 := by
  rw [oddSmoothedCyclotomicUnit_neg hζ hN odd_one (by simp), oddSmoothedCyclotomicUnit_one hζ hN]

theorem oddSmoothedCyclotomicUnit_add_two_mul {ζ : K} {m : ℕ} (hζ : IsPrimitiveRoot ζ (2 * m))
    (hm : 1 ≤ m) {b : ℤ} (hodd : Odd b) (hb : b.gcd (2 * m) = 1) :
    oddSmoothedCyclotomicUnit hζ (by omega)
        (by obtain ⟨k, rfl⟩ := hodd; exact ⟨k + m, by ring⟩ : Odd (b + 2 * (m : ℤ)))
        (by simpa [Nat.cast_mul] using hb : (b + 2 * (m : ℤ)).gcd (2 * m) = 1) =
      -(oddSmoothedCyclotomicUnit hζ (by omega) hodd hb) := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  have hζm : ζ ^ m = -1 := by
    have hsq : (ζ ^ m) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, hζ.pow_eq_one]
    have hne : ζ ^ m ≠ 1 := by
      intro h1
      have hdvd := hζ.dvd_of_pow_eq_one m h1
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    exact (sq_eq_one_iff.mp hsq).resolve_left hne
  simpa using oddSmoothedCyclotomicRatio_add_two_mul hζm b

/-- Ring isomorphisms act on `oddSmoothedCyclotomicUnit` by transporting the primitive root. -/
theorem realUnitsMapEquiv_oddSmoothedCyclotomicUnit {L : Type*} [Field L] (e : K ≃+* L)
    {ζ : K} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 2 ≤ N)
    {b : ℤ} (hodd : Odd b) (hb : b.gcd N = 1) :
    realUnitsMapEquiv e (oddSmoothedCyclotomicUnit hζ hN hodd hb) =
      oddSmoothedCyclotomicUnit (hζ.map_of_injective e.injective) hN hodd hb := by
  apply Units.ext
  apply RingOfIntegers.ext
  apply Subtype.ext
  simpa using oddSmoothedCyclotomicRatio_map e.toRingHom ζ b

end OddSmoothedCyclotomicRatio

end TauCeti
