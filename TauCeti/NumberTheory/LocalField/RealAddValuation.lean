/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import TauCeti.NumberTheory.LocalField.IntegerRing.Basic
public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.RingTheory.Valuation.Discrete.AddVal
public import TauCeti.RingTheory.Valuation.ToAdditive
import TauCeti.Algebra.Order.Monoid.Unbundled.WithTop
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
import TauCeti.NumberTheory.LocalField.DiscreteValuation
import TauCeti.RingTheory.Valuation.Discrete.Extension

/-!
# The real-valued normalized additive valuation of a nonarchimedean local field

This file develops the local-field API for `(ValuativeRel.valuation K).realAddVal`, sending `0` to
`⊤` and nonzero `x` to `((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ)`, so
uniformizers have valuation `1` and units of `𝒪[K]` have valuation `0`.

## Main results

* `TauCeti.realAddVal_valuation_of_ne_zero`, `TauCeti.untop₀_realAddVal_valuation`,
  `TauCeti.realAddVal_valuation_zpow_of_ne_zero`, and `TauCeti.eq_realAddVal_valuation`: values on
  nonzero elements, `untop₀` decoding, integer powers, and uniqueness.
* `TauCeti.realAddVal_valuation_irreducible`, `TauCeti.realAddVal_valuation_coe_integer`,
  `TauCeti.realAddVal_valuation_natCast`, and `TauCeti.realAddVal_valuation_natCast_eq_nsmul`:
  values at uniformizers, integers, and natural-number casts.
* `TauCeti.realAddVal_valuation_algebraMap`, `AlgHom.realAddVal_valuation_apply`, and
  `AlgEquiv.realAddVal_valuation_apply`: ramification-index scaling along `algebraMap`,
  `K`-embeddings, and invariance under `K`-isomorphisms.

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

/-- Evaluating `(valuation K).realAddVal` transports `valuation` via `WithZero.negLog` and casts
to `ℝ`. -/
theorem realAddVal_valuation_apply (x : K) :
    (valuation K).realAddVal x =
      (WithZero.negLog (valueGroupWithZeroIsoInt K (valuation K x))).map ((↑) : ℤ → ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Valuation.realAddVal_eq_map, (valuation K).intAddVal_of_ne_zero hx, ← Units.val_mk0 hx,
      ← toAdd_normalizedValuation_eq_ord, valueGroupWithZeroIsoInt_valuation,
      WithZero.negLog_exp, neg_neg, WithTop.map_coe]

/-- On a unit `x : Kˣ`, `(valuation K).realAddVal` is the integer normalized valuation cast to `ℝ`.
-/
@[simp]
theorem realAddVal_valuation_coe (x : Kˣ) :
    (valuation K).realAddVal (x : K) = (((normalizedValuation K x).toAdd : ℝ) : WithTop ℝ) := by
  rw [realAddVal_valuation_apply, valueGroupWithZeroIsoInt_valuation, WithZero.negLog_exp, neg_neg,
    WithTop.map_coe]

/-- On nonzero `x : K`, `(valuation K).realAddVal` is
`WithZero.log (normalizedValuationWithZero K x)`. -/
theorem realAddVal_valuation_of_ne_zero {x : K} (hx : x ≠ 0) :
    (valuation K).realAddVal x =
      (((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) : WithTop ℝ) := by
  have hcoe : normalizedValuationWithZero K x = ↑(normalizedValuation K (Units.mk0 x hx)) :=
    normalizedValuationWithZero_coe (Units.mk0 x hx)
  rw [hcoe, ← WithZero.toAdd_unzero_eq_log WithZero.coe_ne_zero, WithZero.unzero_coe]
  exact realAddVal_valuation_coe (Units.mk0 x hx)

/-- Decoding `(valuation K).realAddVal x` via `WithTop.untop₀` gives `WithZero.log` cast to `ℝ`.
-/
@[simp]
theorem untop₀_realAddVal_valuation (x : K) :
    ((valuation K).realAddVal x).untop₀ =
      ((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [realAddVal_valuation_of_ne_zero hx, WithTop.untop₀_coe]

/-- `(valuation K).realAddVal` is the unique real additive valuation matching `WithZero.log` off
`0`. -/
theorem eq_realAddVal_valuation {v : AddValuation K (WithTop ℝ)}
    (hv : ∀ x : K, x ≠ 0 →
      v x = (((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) : WithTop ℝ)) :
    v = (valuation K).realAddVal := by
  ext x; rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [hv x hx, realAddVal_valuation_of_ne_zero hx]

/-- A uniformizer of `𝒪[K]` has `(valuation K).realAddVal` equal to `1`. -/
@[simp]
theorem realAddVal_valuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    (valuation K).realAddVal (π : K) = 1 :=
  ((Valuation.integer.integers (valuation K)).isUniformizer_algebraMap_of_irreducible
    hπ).realAddVal_eq_one

/-- An element of `𝒪[K]` is a unit if and only if its `(valuation K).realAddVal` is `0`. -/
theorem isUnit_iff_realAddVal_valuation_eq_zero {a : 𝒪[K]} :
    IsUnit a ↔ (valuation K).realAddVal (a : K) = 0 :=
  (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation K))).trans (valuation K).realAddVal_eq_zero_iff.symm

/-- A unit of `𝒪[K]` has `(valuation K).realAddVal` equal to `0`. -/
@[simp]
theorem realAddVal_valuation_coe_integer_unit (u : 𝒪[K]ˣ) :
    (valuation K).realAddVal ((u : 𝒪[K]) : K) = 0 :=
  isUnit_iff_realAddVal_valuation_eq_zero.mp u.isUnit

/-- An element of `K` lies in `𝒪[K]` if and only if its `(valuation K).realAddVal` is nonnegative.
-/
theorem mem_integer_iff_realAddVal_valuation_nonneg {x : K} :
    x ∈ 𝒪[K] ↔ 0 ≤ (valuation K).realAddVal x :=
  (Valuation.mem_integer_iff (valuation K) x).trans (valuation K).realAddVal_nonneg_iff.symm

/-- On `𝒪[K]`, `(valuation K).realAddVal` agrees with `IsDiscreteValuationRing.addVal` cast to
`ℝ`. -/
theorem realAddVal_valuation_coe_integer (a : 𝒪[K]) :
    (valuation K).realAddVal (a : K) =
      (IsDiscreteValuationRing.addVal 𝒪[K] a).map ((↑) : ℕ → ℝ) := by
  rw [Valuation.realAddVal_eq_map]
  change ((valuation K).intAddVal (algebraMap 𝒪[K] K a)).map ((↑) : ℤ → ℝ) = _
  rw [(Valuation.integer.integers (valuation K)).intAddVal_algebraMap_eq_map_addVal a]
  cases IsDiscreteValuationRing.addVal 𝒪[K] a <;> simp

/-- An element of `𝒪[K]` lies in `𝓂[K]` if and only if its `(valuation K).realAddVal` is at
least `1`. -/
theorem mem_maximalIdeal_iff_one_le_realAddVal_valuation {a : 𝒪[K]} :
    a ∈ 𝓂[K] ↔ 1 ≤ (valuation K).realAddVal (a : K) := by
  have hmem : a ∈ 𝓂[K] ↔ 1 ≤ IsDiscreteValuationRing.addVal 𝒪[K] a := by
    simpa using IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal (x := a) (n := 1)
  rw [hmem, realAddVal_valuation_coe_integer]
  cases IsDiscreteValuationRing.addVal 𝒪[K] a using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- An element of `𝒪[K]` lies in `𝓂[K]` if and only if its `(valuation K).realAddVal` is positive.
-/
theorem mem_maximalIdeal_iff_realAddVal_valuation_pos {a : 𝒪[K]} :
    a ∈ 𝓂[K] ↔ 0 < (valuation K).realAddVal (a : K) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_realAddVal_valuation_eq_zero,
    lt_iff_le_and_ne, and_iff_right (mem_integer_iff_realAddVal_valuation_nonneg.mp a.property),
    ne_comm]

/-- At a nonzero natural-number cast in `K`, `(valuation K).realAddVal` equals `natCastValuation`.
-/
theorem realAddVal_valuation_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    (valuation K).realAddVal (n : K) = ((natCastValuation K n hn : ℝ) : WithTop ℝ) := by
  rw [realAddVal_valuation_of_ne_zero hn, normalizedValuationWithZero_natCast K n hn,
    WithZero.log_exp, Int.cast_natCast]

/-- A natural-number cast in `K` has `(valuation K).realAddVal` at least `1` iff
`ringChar 𝓀[K] ∣ n`. -/
theorem one_le_realAddVal_valuation_natCast_iff_dvd {n : ℕ} :
    1 ≤ (valuation K).realAddVal (n : K) ↔ ringChar 𝓀[K] ∣ n := by
  rw [← Subring.coe_natCast, ← mem_maximalIdeal_iff_one_le_realAddVal_valuation,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsLocalRing.isUnit_natCast_iff_not_dvd, not_not]

/-- A natural-number cast in `K` has `(valuation K).realAddVal` equal to `0` iff
`¬ ringChar 𝓀[K] ∣ n`. -/
theorem realAddVal_valuation_natCast_eq_zero_iff_not_dvd {n : ℕ} :
    (valuation K).realAddVal (n : K) = 0 ↔ ¬ ringChar 𝓀[K] ∣ n := by
  rw [← Subring.coe_natCast, ← isUnit_iff_realAddVal_valuation_eq_zero,
    IsLocalRing.isUnit_natCast_iff_not_dvd]

/-- For nonzero `n : ℕ`, `(valuation K).realAddVal n` scales `v_K(ringChar 𝓀[K])` by
`n.factorization`. -/
theorem realAddVal_valuation_natCast_eq_nsmul {n : ℕ} (hn : n ≠ 0) :
    (valuation K).realAddVal (n : K) =
      (n.factorization (ringChar 𝓀[K])) • (valuation K).realAddVal (ringChar 𝓀[K] : K) := by
  set p := ringChar 𝓀[K]
  have hcast : (n : K) = (p : K) ^ n.factorization p * ((n / p ^ n.factorization p : ℕ) : K) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [hcast, (valuation K).realAddVal.map_mul, (valuation K).realAddVal.map_pow,
    realAddVal_valuation_natCast_eq_zero_iff_not_dvd.mpr
      (Nat.not_dvd_ordCompl (CharP.char_is_prime 𝓀[K] p) hn), add_zero]

/-- At nonzero `x : K` and `n : ℤ`, `(valuation K).realAddVal (x ^ n) = n * v_K(x)`. -/
theorem realAddVal_valuation_zpow_of_ne_zero {x : K} (hx : x ≠ 0) (n : ℤ) :
    (valuation K).realAddVal (x ^ n) =
      ((n * ((valuation K).realAddVal x).untop₀ : ℝ) : WithTop ℝ) := by
  rw [realAddVal_valuation_of_ne_zero (zpow_ne_zero n hx), untop₀_realAddVal_valuation, map_zpow₀,
    WithZero.log_zpow, zsmul_eq_mul]; push_cast; rfl

end SingleField

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- In a compatible extension `L/K`, `algebraMap K L` scales `(valuation _).realAddVal` by
`e(L/K)`. -/
theorem realAddVal_valuation_algebraMap (x : K) :
    (valuation L).realAddVal (algebraMap K L x) =
      ((valuation K).realAddVal x).map ((ramificationIndex K L : ℝ) * ·) := by
  rw [Valuation.realAddVal_algebraMap (valuation K) (valuation L),
    ramificationIdx_valuation_eq_ramificationIndex,
    WithTop.nsmul_eq_map_of_ne_zero (ramificationIndex_pos (K := K) (L := L)).ne']
  simp only [nsmul_eq_mul]

end Extension

end TauCeti

namespace AlgHom

open TauCeti

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

/-- In a tower `M/L/K`, any `K`-embedding `σ : L →ₐ[K] M` scales `(valuation _).realAddVal` by
`e(M/L)`. -/
theorem realAddVal_valuation_apply [Algebra L M] [IsScalarTower K L M] (σ : L →ₐ[K] M) (x : L) :
    (valuation M).realAddVal (σ x) =
      ((valuation L).realAddVal x).map ((ramificationIndex L M : ℝ) * ·) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have : ValuativeExtension L M := ValuativeExtension.of_isScalarTower (K := K) (M := L) (N := M)
  have he := ramificationIndex_tower (K := K) (L := L) M
  let _ : Algebra L M := σ.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' σ.comp_algebraMap.symm
  have : ValuativeExtension L M := σ.valuativeExtension
  rw [← Nat.eq_of_mul_eq_mul_left (ramificationIndex_pos (K := K) (L := L))
    ((ramificationIndex_tower (K := K) (L := L) M).symm.trans he)]
  exact realAddVal_valuation_algebraMap (K := L) (L := M) x

end AlgHom

namespace AlgEquiv

open TauCeti

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

/-- Every `K`-isomorphism `σ : L ≃ₐ[K] M` preserves `(valuation _).realAddVal`. -/
@[simp]
theorem realAddVal_valuation_apply (σ : L ≃ₐ[K] M) (x : L) :
    (valuation M).realAddVal (σ x) = (valuation L).realAddVal x := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  let _ : Algebra L M := σ.toAlgHom.toAlgebra
  have : ValuativeExtension L M := σ.toAlgHom.valuativeExtension
  have halg : algebraMap L M = σ.toAlgHom.toRingHom := RingHom.algebraMap_toAlgebra _
  have hsurj : Function.Surjective (Units.map (algebraMap L M : L →* M)) := fun m ↦
    ⟨Units.map σ.symm.toMonoidHom m, by ext; simp [halg]⟩
  have hrange :
      ((normalizedValuation M).comp (Units.map (algebraMap L M : L →* M))).range = ⊤ :=
    MonoidHom.range_eq_top.mpr ((normalizedValuation_surjective (K := M)).comp hsurj)
  have he : ramificationIndex L M = 1 := by
    rw [ramificationIndex_def, hrange, Subgroup.index_top]
  have hmap := realAddVal_valuation_algebraMap (K := L) (L := M) x
  rw [halg, he] at hmap
  simpa [← Function.id_def] using hmap

end AlgEquiv
