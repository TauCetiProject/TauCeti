/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The valuation of `x ^ n - 1` in a local field

Let `K` be a nonarchimedean local field and write `v_K` for its normalized additive valuation,
read on all of `K` as `WithZero.log ∘ normalizedValuationWithZero K` (so that the junk value at
`0` is `0`). This file computes `v_K(x ^ n - 1)` for deep principal units and deduces the
one-factor estimate for `v_K(α ^ b - 1)` in a local field of characteristic zero, that is, in a
finite extension of `ℚ_[p]`.

For `x ∈ U(K,i)` at a depth `i` with `v_K(ℓ) < (ℓ - 1) * i` for every prime `ℓ ∣ n`, the `n`-th
power map carries `U(K,j)` onto `U(K, j + v_K(n))` for every `j ≥ i` and is injective on
`U(K,i)`, so it moves the exact depth of `x` by `v_K(n)`:

`v_K(x ^ n - 1) = v_K(x - 1) + v_K(n)` for `x ≠ 1`.

This plays the role of the isometry of the `p`-adic logarithm on deep units, without any
logarithm in the statement.

In characteristic zero, with residue characteristic `p` and `e = v_K(p)`, every unit `α` has a
power `γ = α ^ M` in `U(K, e + 1)`, where the formula applies at every exponent. If `γ ≠ 1` this
gives `v_K(α ^ b - 1) ≤ v_K(γ - 1) + e v_p(b)`. Separating nonunits (where
`v_K(α ^ b - 1) ≤ 0`) and roots of unity (where `α ^ b` takes only finitely many values) gives,
for every fixed `α`, a constant `C` with

`v_K(α ^ b - 1) ≤ C (1 + log max(1, |b|))` whenever `α ^ b ≠ 1`.

## Main results

* `TauCeti.log_normalizedValuationWithZero_pow_sub_one`: the exact formula
  `v_K(x ^ n - 1) = v_K(x - 1) + v_K(n)` for a deep unit `x ≠ 1`.
* `TauCeti.log_normalizedValuationWithZero_zpow_sub_one_le`: if `x ^ M ≠ 1` lies in a deep
  step, then `v_K(x ^ b - 1) ≤ v_K(x ^ M - 1) + v_K(|b|)`.
* `TauCeti.exists_log_normalizedValuationWithZero_zpow_sub_one_le`: in characteristic zero, the
  one-factor estimate `v_K(α ^ b - 1) ≤ C (1 + log max(1, |b|))` for every fixed `α ∈ K`.

## References

* Kunrui Yu, *Linear forms in p-adic logarithms II*, Compositio Math. 74 (1990), 15–113, §1.
* Kunrui Yu, *Linear forms in p-adic logarithms III*, Compositio Math. 91 (1994), 241–276, §1.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter XIV, §4, Proposition 9.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The valuation of `x ^ n - 1` for a deep unit.** For `(n : K) ≠ 0`, a depth `i` with
`v_K(p) < (p - 1) * i` for every prime `p ∣ n`, and `x ∈ U(K,i)` with `x ≠ 1`,

`v_K(x ^ n - 1) = v_K(x - 1) + v_K(n)`. -/
theorem log_normalizedValuationWithZero_pow_sub_one {n : ℕ} (hn : (n : K) ≠ 0) {i : ℕ}
    (hi : ∀ p : ℕ, p.Prime → ∀ hpK : (p : K) ≠ 0, p ∣ n →
      natCastValuation K p hpK < (p - 1) * i)
    {x : Kˣ} (hx : x ∈ unitFiltration K i) (hx1 : x ≠ 1) :
    WithZero.log (normalizedValuationWithZero K ((x : K) ^ n - 1)) =
      WithZero.log (normalizedValuationWithZero K ((x : K) - 1)) + natCastValuation K n hn := by
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  -- Some prime divides `n`, so the depth condition forces `i ≠ 0`.
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd hn1
  have hℓK : (ℓ : K) ≠ 0 := fun h ↦ hn (by
    obtain ⟨c, rfl⟩ := hℓn
    rw [Nat.cast_mul, h, zero_mul])
  have hi0 : i ≠ 0 := by
    rintro rfl
    simpa using hi ℓ hℓ hℓK hℓn
  have hxn1 : x ^ n ≠ 1 := fun h ↦ hx1 (Subgroup.disjoint_def.mp
    (disjoint_rootsOfUnity_unitFiltration hn hi) ((mem_rootsOfUnity n x).mpr h) hx)
  set d := WithZero.log (normalizedValuationWithZero K ((x : K) - 1))
  have hid : (i : ℤ) ≤ d :=
    (mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one hi0 hx1).mp hx
  -- Write `d = m` with `m ≥ i`: then `x ∈ U(K,m) \ U(K,m+1)`, and the power map moves this
  -- exact depth by `v_K(n)`.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d = m := ⟨d.toNat, by omega⟩
  have him : i ≤ m := by omega
  have hm0 : m ≠ 0 := by omega
  have hxm : x ∈ unitFiltration K m :=
    (mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one hm0 hx1).mpr hm.ge
  have hxm1 : x ∉ unitFiltration K (m + 1) := fun h ↦ by
    have := (mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one
      m.succ_ne_zero hx1).mp h
    omega
  have h1 := (pow_mem_unitFiltration_add_natCastValuation_iff hn hi him hx).mpr hxm
  have h2 := (pow_mem_unitFiltration_add_natCastValuation_iff hn hi (him.trans m.le_succ)
    hx).not.mpr hxm1
  rw [mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one (by omega) hxn1,
    Units.val_pow_eq_pow_val] at h1 h2
  push_cast at h1 h2
  omega

/-- **The one-factor estimate, explicit form.** Let `x ∈ Kˣ` have a power `x ^ M ≠ 1` in a
positive-depth step `U(K,i)`, and let `b` be an integer with `(|b| : K) ≠ 0` such that
`v_K(ℓ) < (ℓ - 1) * i` for every prime `ℓ ∣ b`. Then

`v_K(x ^ b - 1) ≤ v_K(x ^ M - 1) + v_K(|b|)`. -/
theorem log_normalizedValuationWithZero_zpow_sub_one_le {x : Kˣ} {M i : ℕ} (hi0 : i ≠ 0)
    (hM : x ^ M ∈ unitFiltration K i) (hM1 : x ^ M ≠ 1) {b : ℤ} (hb : (b.natAbs : K) ≠ 0)
    (hi : ∀ ℓ : ℕ, ℓ.Prime → ∀ hℓK : (ℓ : K) ≠ 0, ℓ ∣ b.natAbs →
      natCastValuation K ℓ hℓK < (ℓ - 1) * i) :
    WithZero.log (normalizedValuationWithZero K ((x : K) ^ b - 1)) ≤
      WithZero.log (normalizedValuationWithZero K ((x : K) ^ M - 1)) +
        natCastValuation K b.natAbs hb := by
  rw [← Units.val_pow_eq_pow_val, ← Units.val_zpow_eq_zpow_val]
  set γ := x ^ M
  set d := WithZero.log (normalizedValuationWithZero K ((γ : K) - 1))
  have hid : (i : ℤ) ≤ d :=
    (mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one hi0 hM1).mp hM
  by_cases hb1 : x ^ b = 1
  · simp only [hb1, Units.val_one, sub_self, map_zero, WithZero.log_zero]
    omega
  -- The exact formula at `γ`: `v_K(γ ^ |b| - 1) = d + v_K(|b|)`.
  have hγn := log_normalizedValuationWithZero_pow_sub_one hb hi hM hM1
  have hγn1 : γ ^ b.natAbs ≠ 1 := fun h ↦ by
    simp [← Units.val_pow_eq_pow_val, h] at hγn
    omega
  -- If `x ^ b` were deeper than `d + v_K(|b|)`, so would be `γ ^ |b| = (x ^ b) ^ (± M)`.
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ : ∃ j : ℕ, d + natCastValuation K b.natAbs hb + 1 = j :=
    ⟨(d + natCastValuation K b.natAbs hb + 1).toNat, by omega⟩
  have hj0 : j ≠ 0 := by omega
  have hxb : x ^ b ∈ unitFiltration K j :=
    (mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one hj0 hb1).mpr (by omega)
  have hγb : γ ^ b.natAbs ∈ unitFiltration K j := by
    have h := zpow_mem hxb (M : ℤ)
    rw [← zpow_mul, mul_comm, zpow_mul, zpow_natCast] at h
    rcases Int.natAbs_eq b with hb' | hb'
    · rwa [hb', zpow_natCast] at h
    · rwa [hb', zpow_neg, zpow_natCast, inv_mem_iff] at h
  have := (mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one hj0 hγn1).mp hγb
  rw [Units.val_pow_eq_pow_val, hγn] at this
  omega

/-- **Nonunits.** If `x` is not a unit of `𝒪[K]` and `b ≠ 0`, then `v_K(x ^ b - 1) ≤ 0`: a positive
valuation would make `x ^ b`, hence `x`, a unit. -/
theorem log_normalizedValuationWithZero_zpow_sub_one_nonpos {x : Kˣ}
    (hx : x ∉ unitFiltration K 0) {b : ℤ} (hb : b ≠ 0) :
    WithZero.log (normalizedValuationWithZero K ((x : K) ^ b - 1)) ≤ 0 := by
  by_contra! hpos
  have hb1 : x ^ b ≠ 1 := fun h ↦ by
    simp [← Units.val_zpow_eq_zpow_val, h] at hpos
  have hmem : x ^ b ∈ unitFiltration K 1 :=
    (mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one one_ne_zero hb1).mpr
      (by rw [Units.val_zpow_eq_zpow_val]; exact_mod_cast hpos)
  have hval := (mem_unitFiltration_zero _).mp (unitFiltration_antitone (Nat.zero_le 1) hmem)
  rw [← normalizedValuation_eq_one_iff, map_zpow] at hval
  exact hx <| (mem_unitFiltration_zero x).mpr <|
    (normalizedValuation_eq_one_iff x).mp (by simpa [hb] using hval)

/-- The values `v_K(α ^ b - 1)` of a root of unity `α` are bounded above: `α ^ b` takes only the
finitely many values `α ^ r` with `0 ≤ r < M`. -/
private theorem bddAbove_range_log_normalizedValuationWithZero_zpow_sub_one {α : K} {M : ℕ}
    (hM0 : M ≠ 0) (hαM : α ^ M = 1) :
    BddAbove (Set.range fun b : ℤ ↦ WithZero.log (normalizedValuationWithZero K (α ^ b - 1))) := by
  have hα : α ≠ 0 := by
    rintro rfl
    simp [zero_pow hM0] at hαM
  have hu : IsOfFinOrder (Units.mk0 α hα) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨M, Nat.pos_of_ne_zero hM0, Units.ext (by simpa using hαM)⟩
  refine ((hu.powers_eq_zpowers ▸ hu.finite_powers).image fun u : Kˣ ↦
    WithZero.log (normalizedValuationWithZero K (u - 1))).bddAbove.mono ?_
  rintro _ ⟨b, rfl⟩
  exact ⟨_, Subgroup.zpow_mem_zpowers _ b, by simp⟩

/-- **The one-factor estimate.** Let `K` be a nonarchimedean local field of characteristic zero,
that is, a finite extension of `ℚ_[p]`. For every fixed `α ∈ K` there is a constant `C`,
depending on `α` and `K`, such that

`v_K(α ^ b - 1) ≤ C (1 + log max(1, |b|))` for every integer `b` with `α ^ b ≠ 1`. -/
theorem exists_log_normalizedValuationWithZero_zpow_sub_one_le [CharZero K] (α : K) :
    ∃ C : ℝ, ∀ b : ℤ, α ^ b ≠ 1 →
      ((WithZero.log (normalizedValuationWithZero K (α ^ b - 1)) : ℤ) : ℝ) ≤
        C * (1 + Real.log (max 1 |(b : ℝ)|)) := by
  have hL : ∀ b : ℤ, 0 ≤ Real.log (max 1 |(b : ℝ)|) := fun b ↦
    Real.log_nonneg (le_max_left _ _)
  -- The case `α = 0`: `α ^ b - 1 = -1` for `b ≠ 0`.
  rcases eq_or_ne α 0 with rfl | hα
  · refine ⟨0, fun b hb ↦ ?_⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    rw [zero_zpow b hb0, zero_sub, ← Units.val_one, ← Units.val_neg,
      normalizedValuationWithZero_coe, normalizedValuation_neg, map_one]
    simp
  set a := Units.mk0 α hα
  have ha : (a : K) = α := Units.val_mk0 hα
  by_cases ha0 : a ∈ unitFiltration K 0
  swap
  · refine ⟨0, fun b hb ↦ ?_⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hb (zpow_zero α)
    rw [zero_mul, Int.cast_nonpos, ← ha]
    exact log_normalizedValuationWithZero_zpow_sub_one_nonpos ha0 hb0
  -- A unit: some power `a ^ M` with `M > 0` lies in `U(K, e + 1)`, where `e = v_K(p)`.
  have hpK : (ringChar 𝓀[K] : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (CharP.char_is_prime 𝓀[K] _).ne_zero
  set e := natCastValuation K (ringChar 𝓀[K]) hpK
  obtain ⟨M, hM0, -, hM, -⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    (Subgroup.relIndex_ne_zero (H := unitFiltration K (e + 1))) ha0
  by_cases hM1 : a ^ M = 1
  · -- A root of unity.
    obtain ⟨C₀, hC₀⟩ := bddAbove_range_log_normalizedValuationWithZero_zpow_sub_one
      (α := α) hM0.ne' (by rw [← ha, ← Units.val_pow_eq_pow_val, hM1, Units.val_one])
    refine ⟨((max C₀ 0 : ℤ) : ℝ), fun b _ ↦ ?_⟩
    calc ((WithZero.log (normalizedValuationWithZero K (α ^ b - 1)) : ℤ) : ℝ)
        ≤ ((max C₀ 0 : ℤ) : ℝ) := by exact_mod_cast (hC₀ ⟨b, rfl⟩).trans (le_max_left _ _)
      _ ≤ ((max C₀ 0 : ℤ) : ℝ) * (1 + Real.log (max 1 |(b : ℝ)|)) :=
        le_mul_of_one_le_right (by exact_mod_cast le_max_right _ _) (by linarith [hL b])
  -- A non-torsion unit: the explicit form, with `v_K(|b|) ≤ (e / log p) log |b|`.
  have hd : ((e + 1 : ℕ) : ℤ) ≤ WithZero.log (normalizedValuationWithZero K (α ^ M - 1)) := by
    rw [← ha, ← Units.val_pow_eq_pow_val]
    exact (mem_unitFiltration_iff_le_log_normalizedValuationWithZero_sub_one
      (Nat.succ_ne_zero e) hM1).mp hM
  set d := WithZero.log (normalizedValuationWithZero K (α ^ M - 1))
  refine ⟨d + e / Real.log (ringChar 𝓀[K]), fun b hb ↦ ?_⟩
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (zpow_zero α)
  have hbK : (b.natAbs : K) ≠ 0 := Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb0)
  have h := log_normalizedValuationWithZero_zpow_sub_one_le (Nat.succ_ne_zero e) hM hM1 hbK
    fun ℓ hℓ hℓK _ ↦ natCastValuation_lt_sub_one_mul_natCastValuation_ringChar_add_one hpK hℓ hℓK
  have hv := natCastValuation_le_div_log_mul_log hbK hpK
  have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hb0
  rw [Nat.cast_natAbs, Int.cast_abs, ← max_eq_right hb1] at hv
  have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast (Int.natCast_nonneg _).trans hd
  have he0 : (0 : ℝ) ≤ e / Real.log (ringChar 𝓀[K]) := by positivity
  have h' : ((WithZero.log (normalizedValuationWithZero K (α ^ b - 1)) : ℤ) : ℝ) ≤
      d + natCastValuation K b.natAbs hbK := by
    rw [ha] at h
    exact_mod_cast h
  nlinarith [hL b]

end TauCeti
