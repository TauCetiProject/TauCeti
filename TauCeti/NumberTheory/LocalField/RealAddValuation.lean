/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import TauCeti.NumberTheory.LocalField.IntegerRing.Basic
public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.RingTheory.Valuation.ToAdditive
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic

/-!
# The real-valued normalized additive valuation of a nonarchimedean local field

This file constructs `TauCeti.realAddValuation K : AddValuation K (WithTop ℝ)` on a nonarchimedean
local field `K`, sending `0` to `⊤` and nonzero `x` to
`((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ)`, so uniformizers have valuation `1` and
units of `𝒪[K]` have valuation `0`.

## Main definitions

* `TauCeti.realAddValuation`: the normalized additive valuation `K → WithTop ℝ`.

## Main results

* `TauCeti.realAddValuation_of_ne_zero`, `TauCeti.untop₀_realAddValuation`,
  `TauCeti.realAddValuation_zpow_of_ne_zero` and `TauCeti.eq_realAddValuation`: values on nonzero
  elements, `untop₀` decoding, integer powers, and uniqueness.
* `TauCeti.realAddValuation_irreducible`, `TauCeti.realAddValuation_coe_integer`,
  `TauCeti.realAddValuation_natCast` and `TauCeti.realAddValuation_natCast_eq_nsmul`: values at
  uniformizers, integers and natural-number casts.
* `TauCeti.realAddValuation_algebraMap`, `AlgHom.normalizedValuationWithZero_apply` and
  `AlgHom.realAddValuation_apply`: ramification-index scaling along `algebraMap` and `K`-embeddings.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §§1–4, and Chapter II, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§3–6.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField
open scoped WithZero

namespace TauCeti

section SingleField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- The real-valued normalized additive valuation of a nonarchimedean local field `K`: zero maps to
`⊤` and nonzero `x` maps to `((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ)`. -/
def realAddValuation : AddValuation K (WithTop ℝ) :=
  (((valuation K).map
    (valueGroupWithZeroIsoInt K : ValueGroupWithZero K →*₀o ℤᵐ⁰)).addVal).map
    { (Int.castAddHom ℝ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr fun _ _ h ↦ Int.cast_le.mpr h } rfl

/-- Evaluating `realAddValuation` transports `valuation` via `WithZero.negLog` and casts to `ℝ`. -/
theorem realAddValuation_apply (x : K) :
    realAddValuation K x =
      (WithZero.negLog (valueGroupWithZeroIsoInt K (valuation K x))).map ((↑) : ℤ → ℝ) := by
  change WithTop.map (Int.castAddHom ℝ) (((valuation K).map
      (valueGroupWithZeroIsoInt K : ValueGroupWithZero K →*₀o ℤᵐ⁰)).addVal x) = _
  rw [Valuation.addVal_apply]; rfl

/-- Only zero has infinite `realAddValuation`. -/
theorem realAddValuation_eq_top_iff {x : K} : realAddValuation K x = ⊤ ↔ x = 0 :=
  (realAddValuation K).top_iff

/-- On a unit `x : Kˣ`, `realAddValuation` is the integer normalized valuation cast to `ℝ`. -/
@[simp]
theorem realAddValuation_coe_unit (x : Kˣ) :
    realAddValuation K (x : K) = (((normalizedValuation K x).toAdd : ℝ) : WithTop ℝ) := by
  rw [realAddValuation_apply, valueGroupWithZeroIsoInt_valuation, WithZero.negLog_exp, neg_neg,
    WithTop.map_coe]

/-- On nonzero `x : K`, `realAddValuation` is `WithZero.log (normalizedValuationWithZero K x)`. -/
theorem realAddValuation_of_ne_zero {x : K} (hx : x ≠ 0) :
    realAddValuation K x =
      (((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) : WithTop ℝ) := by
  have hcoe : normalizedValuationWithZero K x = ↑(normalizedValuation K (Units.mk0 x hx)) :=
    normalizedValuationWithZero_coe (Units.mk0 x hx)
  rw [hcoe, ← WithZero.toAdd_unzero_eq_log WithZero.coe_ne_zero, WithZero.unzero_coe]
  exact realAddValuation_coe_unit (Units.mk0 x hx)

/-- Decoding `realAddValuation K x` via `WithTop.untop₀` gives `WithZero.log` cast to `ℝ`. -/
@[simp]
theorem untop₀_realAddValuation (x : K) :
    (realAddValuation K x).untop₀ = ((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [realAddValuation_of_ne_zero hx, WithTop.untop₀_coe]

/-- Every nonzero element of `K` has an integer value under `realAddValuation`. -/
theorem exists_int_realAddValuation {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, realAddValuation K x = ((n : ℝ) : WithTop ℝ) :=
  ⟨WithZero.log (normalizedValuationWithZero K x), realAddValuation_of_ne_zero hx⟩

/-- `realAddValuation K` is the unique real additive valuation matching `WithZero.log` off `0`. -/
theorem eq_realAddValuation {v : AddValuation K (WithTop ℝ)}
    (hv : ∀ x : K, x ≠ 0 →
      v x = (((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) : WithTop ℝ)) :
    v = realAddValuation K := by
  ext x; rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [hv x hx, realAddValuation_of_ne_zero hx]

/-- A uniformizer of `𝒪[K]` has `realAddValuation` equal to `1`. -/
@[simp]
theorem realAddValuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    realAddValuation K (π : K) = 1 := by
  simpa [normalizedValuation_irreducible hπ] using
    realAddValuation_coe_unit (Units.mk0 (π : K) fun h ↦ hπ.ne_zero (Subtype.ext h))

/-- A unit of `𝒪[K]` has `realAddValuation` equal to `0`. -/
@[simp]
theorem realAddValuation_coe_integer_unit (u : 𝒪[K]ˣ) :
    realAddValuation K ((u : 𝒪[K]) : K) = 0 := by
  rw [realAddValuation_of_ne_zero fun h ↦ u.ne_zero (Subtype.ext h),
    (isUnit_iff_normalizedValuationWithZero_eq_one (u := (u : 𝒪[K]))).mp u.isUnit,
    WithZero.log_one, Int.cast_zero, WithTop.coe_zero]

/-- An element of `K` lies in `𝒪[K]` if and only if its `realAddValuation` is nonnegative. -/
theorem mem_integer_iff_realAddValuation_nonneg {x : K} :
    x ∈ 𝒪[K] ↔ 0 ≤ realAddValuation K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h := mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 x hx)
    have hval := realAddValuation_coe_unit (Units.mk0 x hx)
    simp only [Units.val_mk0] at h hval
    rw [h, hval, ← WithTop.coe_zero, WithTop.coe_le_coe]; exact_mod_cast Iff.rfl

/-- On `𝒪[K]`, `realAddValuation` agrees with `IsDiscreteValuationRing.addVal` cast to `ℝ`. -/
theorem realAddValuation_coe_integer (a : 𝒪[K]) :
    realAddValuation K (a : K) =
      (IsDiscreteValuationRing.addVal 𝒪[K] a).recTopCoe ⊤ fun n : ℕ ↦ ((n : ℝ) : WithTop ℝ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    simp [IsDiscreteValuationRing.addVal_def' u hπ n, (realAddValuation K).map_mul,
      (realAddValuation K).map_pow, realAddValuation_irreducible hπ]

/-- An element of `𝒪[K]` lies in `𝓂[K]` if and only if its `realAddValuation` is at least `1`. -/
theorem mem_maximalIdeal_iff_one_le_realAddValuation {a : 𝒪[K]} :
    a ∈ 𝓂[K] ↔ 1 ≤ realAddValuation K (a : K) := by
  rw [show a ∈ 𝓂[K] ↔ 1 ≤ IsDiscreteValuationRing.addVal 𝒪[K] a by
    simpa using IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal (x := a) (n := 1),
    realAddValuation_coe_integer]
  cases IsDiscreteValuationRing.addVal 𝒪[K] a using ENat.recTopCoe with
  | top => simp
  | coe n =>
    simp only [ENat.recTopCoe_natCast, ← ENat.natCast_one, ENat.natCast_le_natCast,
      ← WithTop.coe_one, WithTop.coe_le_coe, Nat.one_le_cast]

/-- An element of `𝒪[K]` lies in `𝓂[K]` if and only if its `realAddValuation` is positive. -/
theorem mem_maximalIdeal_iff_realAddValuation_pos {a : 𝒪[K]} :
    a ∈ 𝓂[K] ↔ 0 < realAddValuation K (a : K) := by
  rw [mem_maximalIdeal_iff_one_le_realAddValuation, realAddValuation_coe_integer]
  cases IsDiscreteValuationRing.addVal 𝒪[K] a using ENat.recTopCoe with
  | top => simp [← WithTop.coe_zero]
  | coe n =>
    simp only [ENat.recTopCoe_natCast, ← WithTop.coe_one, ← WithTop.coe_zero, WithTop.coe_le_coe,
      WithTop.coe_lt_coe, Nat.cast_pos, Nat.one_le_cast]; omega

/-- At a nonzero natural-number cast in `K`, `realAddValuation` equals `natCastValuation`. -/
theorem realAddValuation_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    realAddValuation K (n : K) = ((natCastValuation K n hn : ℝ) : WithTop ℝ) := by
  rw [realAddValuation_of_ne_zero hn, normalizedValuationWithZero_natCast K n hn,
    WithZero.log_exp, Int.cast_natCast]

/-- A natural-number cast in `K` has `realAddValuation` at least `1` iff `ringChar 𝓀[K] ∣ n`. -/
theorem one_le_realAddValuation_natCast_iff_dvd {n : ℕ} :
    1 ≤ realAddValuation K (n : K) ↔ ringChar 𝓀[K] ∣ n := by
  rw [← Subring.coe_natCast, ← mem_maximalIdeal_iff_one_le_realAddValuation,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsLocalRing.isUnit_natCast_iff_not_dvd, not_not]

/-- A natural-number cast in `K` has `realAddValuation` equal to `0` iff `¬ ringChar 𝓀[K] ∣ n`. -/
theorem realAddValuation_natCast_eq_zero_iff_not_dvd {n : ℕ} :
    realAddValuation K (n : K) = 0 ↔ ¬ ringChar 𝓀[K] ∣ n := by
  refine ⟨fun h0 hdvd ↦ absurd (h0 ▸ one_le_realAddValuation_natCast_iff_dvd (K := K).mpr hdvd)
    (by simp), fun hndvd ↦ ?_⟩
  obtain ⟨u, hu⟩ := (IsLocalRing.isUnit_natCast_iff_not_dvd (R := 𝒪[K])).mpr hndvd
  rw [show (n : K) = ((u : 𝒪[K]) : K) from congrArg Subtype.val hu.symm,
    realAddValuation_coe_integer_unit]

/-- For nonzero `n : ℕ`, `realAddValuation K n` scales `v_K(ringChar 𝓀[K])` by `n.factorization`. -/
theorem realAddValuation_natCast_eq_nsmul {n : ℕ} (hn : n ≠ 0) :
    realAddValuation K (n : K) =
      (n.factorization (ringChar 𝓀[K])) • realAddValuation K (ringChar 𝓀[K] : K) := by
  set p := ringChar 𝓀[K]
  have hcast : (n : K) = (p : K) ^ n.factorization p * ((n / p ^ n.factorization p : ℕ) : K) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [hcast, (realAddValuation K).map_mul, (realAddValuation K).map_pow,
    realAddValuation_natCast_eq_zero_iff_not_dvd.mpr
      (Nat.not_dvd_ordCompl (CharP.char_is_prime 𝓀[K] p) hn), add_zero]

/-- At nonzero `x : K` and `n : ℤ`, `realAddValuation K (x ^ n) = n * (realAddValuation K x)`. -/
theorem realAddValuation_zpow_of_ne_zero {x : K} (hx : x ≠ 0) (n : ℤ) :
    realAddValuation K (x ^ n) = ((n * (realAddValuation K x).untop₀ : ℝ) : WithTop ℝ) := by
  rw [realAddValuation_of_ne_zero (zpow_ne_zero n hx), untop₀_realAddValuation, map_zpow₀,
    WithZero.log_zpow, zsmul_eq_mul]; push_cast; rfl

end SingleField

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- In a compatible extension `L/K`, `algebraMap K L` scales `realAddValuation` by `e(L/K)`. -/
theorem realAddValuation_algebraMap (x : K) :
    realAddValuation L (algebraMap K L x) =
      (realAddValuation K x).map ((ramificationIndex K L : ℝ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [realAddValuation_of_ne_zero ((map_ne_zero (algebraMap K L)).mpr hx),
      realAddValuation_of_ne_zero hx, normalizedValuationWithZero_algebraMap (K := K) (L := L),
      WithTop.map_coe, WithZero.log_pow, nsmul_eq_mul]; push_cast; rfl

end Extension

end TauCeti

namespace AlgHom

open TauCeti

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

private theorem normalizedValuationWithZero_apply_of_mul_eq (σ : L →ₐ[K] M) {e : ℕ}
    (he : ramificationIndex K L * e = ramificationIndex K M) (x : L) :
    normalizedValuationWithZero M (σ x) = normalizedValuationWithZero L x ^ e := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  let _ : Algebra L M := σ.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' σ.comp_algebraMap.symm
  have : ValuativeExtension L M := σ.valuativeExtension
  rw [← Nat.eq_of_mul_eq_mul_left (ramificationIndex_pos (K := K) (L := L))
    ((ramificationIndex_tower (K := K) (L := L) M).symm.trans he.symm)]
  exact normalizedValuationWithZero_algebraMap (K := L) (L := M) x

/-- Every `K`-embedding `σ : L →ₐ[K] M` raises `normalizedValuationWithZero L x` to `e(M/L)`. -/
theorem normalizedValuationWithZero_apply [Algebra L M] [IsScalarTower K L M]
    (σ : L →ₐ[K] M) (x : L) :
    normalizedValuationWithZero M (σ x) =
      normalizedValuationWithZero L x ^ ramificationIndex L M := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have : ValuativeExtension L M := ValuativeExtension.of_isScalarTower (K := K) (M := L) (N := M)
  exact σ.normalizedValuationWithZero_apply_of_mul_eq
    (ramificationIndex_tower (K := K) (L := L) M).symm x

/-- In a tower `M/L/K`, `σ : L →ₐ[K] M` agrees with `algebraMap L M` under `|·|_M`. -/
theorem normalizedValuationWithZero_apply_eq_algebraMap [Algebra L M] [IsScalarTower K L M]
    (σ : L →ₐ[K] M) (x : L) :
    normalizedValuationWithZero M (σ x) = normalizedValuationWithZero M (algebraMap L M x) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have : ValuativeExtension L M := ValuativeExtension.of_isScalarTower (K := K) (M := L) (N := M)
  rw [σ.normalizedValuationWithZero_apply, normalizedValuationWithZero_algebraMap]

/-- In a tower `M/L/K`, any `K`-embedding `σ : L →ₐ[K] M` scales `realAddValuation` by `e(M/L)`. -/
theorem realAddValuation_apply [Algebra L M] [IsScalarTower K L M] (σ : L →ₐ[K] M) (x : L) :
    realAddValuation M (σ x) = (realAddValuation L x).map ((ramificationIndex L M : ℝ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [realAddValuation_of_ne_zero ((map_ne_zero σ).mpr hx), realAddValuation_of_ne_zero hx,
      σ.normalizedValuationWithZero_apply, WithTop.map_coe, WithZero.log_pow, nsmul_eq_mul]
    push_cast; rfl

end AlgHom

namespace AlgEquiv

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- Every `K`-automorphism of `L` preserves `realAddValuation L`. -/
@[simp]
theorem realAddValuation_apply (σ : L ≃ₐ[K] L) (x : L) :
    realAddValuation L (σ x) = realAddValuation L x := by
  have h := σ.toAlgHom.realAddValuation_apply (M := L) x
  have he : ramificationIndex L L = 1 := ramificationIndex_eq_iff.mpr fun _ ↦ by simp
  cases hx : realAddValuation L x <;> simpa [hx, he] using h

end AlgEquiv
