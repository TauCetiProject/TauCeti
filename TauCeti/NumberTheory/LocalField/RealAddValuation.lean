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

The Newton-polygon library (`Polynomial.newtonPolygon`, `Polynomial.newtonSlopes`) takes a
real-valued additive valuation `AddValuation K (WithTop ℝ)`, whereas a nonarchimedean local field
`K` carries the multiplicative valuation `ValuativeRel.valuation K` together with its integer
normalizations `TauCeti.normalizedValuation` and `TauCeti.normalizedValuationWithZero`. This file
constructs the corresponding real additive valuation

`TauCeti.realAddValuation K : AddValuation K (WithTop ℝ)`,

which sends `0` to `⊤` and a nonzero element `x` to
`((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ)`, so that uniformizers have valuation
`1` and units of `𝒪[K]` have valuation `0`.

## Main definitions

* `TauCeti.realAddValuation`: the normalized additive valuation `K → WithTop ℝ` of a
  nonarchimedean local field `K`.

## Main results

* `TauCeti.realAddValuation_of_ne_zero`, `TauCeti.untop₀_realAddValuation` and
  `TauCeti.realAddValuation_zpow_of_ne_zero`: on nonzero elements, `realAddValuation K x` is
  `WithZero.log (normalizedValuationWithZero K x)` cast to `ℝ`, `untop₀` recovers this value on all
  of `K`, and integer powers scale it linearly.
* `TauCeti.eq_realAddValuation`: `realAddValuation K` is the unique real additive valuation on `K`
  taking the value `WithZero.log (normalizedValuationWithZero K x)` on every nonzero `x`.
* `TauCeti.realAddValuation_irreducible`, `TauCeti.realAddValuation_coe_integer`,
  `TauCeti.realAddValuation_natCast`, `TauCeti.realAddValuation_natCast_eq_zero_iff_not_dvd`,
  `TauCeti.one_le_realAddValuation_natCast_iff_dvd` and `TauCeti.realAddValuation_natCast_eq_nsmul`:
  explicit values at uniformizers, integers and natural-number casts.
* `TauCeti.realAddValuation_algebraMap`: in a compatible extension `L/K`, the algebra map scales
  `realAddValuation` by `ramificationIndex K L`.
* `AlgHom.normalizedValuationWithZero_apply` and `AlgHom.realAddValuation_apply`: every
  `K`-embedding `L →ₐ[K] M` into a compatible local-field extension `M` scales valuations by
  `ramificationIndex L M`, and in particular agrees in valuation with `algebraMap L M`.

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

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (K) in
/-- The real-valued normalized additive valuation of a nonarchimedean local field `K`: zero has
valuation `⊤`, and a nonzero element `x` has valuation
`((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ)`, so a uniformizer has valuation
`1`. -/
def realAddValuation : AddValuation K (WithTop ℝ) :=
  (((valuation K).map
    (valueGroupWithZeroIsoInt K : ValueGroupWithZero K →*₀o ℤᵐ⁰)).addVal).map
    { (Int.castAddHom ℝ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr fun _ _ h ↦ Int.cast_le.mpr h }
    rfl

/-- Evaluating `realAddValuation` transports `ValuativeRel.valuation` through `WithZero.negLog`
and casts from `ℤ` to `ℝ`. -/
theorem realAddValuation_apply (x : K) :
    realAddValuation K x =
      (WithZero.negLog (valueGroupWithZeroIsoInt K (valuation K x))).map ((↑) : ℤ → ℝ) := by
  -- Unfold `realAddValuation` to expose `AddValuation.map` followed by `Valuation.addVal`.
  change WithTop.map (Int.castAddHom ℝ)
      (((valuation K).map (valueGroupWithZeroIsoInt K : ValueGroupWithZero K →*₀o ℤᵐ⁰)).addVal x) =
    (WithZero.negLog (valueGroupWithZeroIsoInt K (valuation K x))).map ((↑) : ℤ → ℝ)
  rw [Valuation.addVal_apply]
  rfl

/-- Only zero has infinite `realAddValuation`. -/
theorem realAddValuation_eq_top_iff {x : K} :
    realAddValuation K x = ⊤ ↔ x = 0 :=
  (realAddValuation K).top_iff

/-- On a unit `x : Kˣ`, `realAddValuation` is the integer normalized valuation cast to `ℝ`. -/
@[simp]
theorem realAddValuation_coe_unit (x : Kˣ) :
    realAddValuation K (x : K) = (((normalizedValuation K x).toAdd : ℝ) : WithTop ℝ) := by
  rw [realAddValuation_apply, valueGroupWithZeroIsoInt_valuation, WithZero.negLog_exp, neg_neg,
    WithTop.map_coe]

/-- On a nonzero element `x : K`, `realAddValuation` is
`WithZero.log (normalizedValuationWithZero K x)` cast to `ℝ`. -/
theorem realAddValuation_of_ne_zero {x : K} (hx : x ≠ 0) :
    realAddValuation K x =
      (((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) : WithTop ℝ) := by
  have hcoe := normalizedValuationWithZero_coe (Units.mk0 x hx)
  simp only [Units.val_mk0] at hcoe
  rw [hcoe, ← WithZero.toAdd_unzero_eq_log WithZero.coe_ne_zero, WithZero.unzero_coe]
  exact realAddValuation_coe_unit (Units.mk0 x hx)

/-- Decoding `realAddValuation K x` via `WithTop.untop₀` gives
`((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ)` for every `x : K`, including
`x = 0`. -/
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

/-- `realAddValuation K` is the unique real additive valuation on `K` taking the value
`WithZero.log (normalizedValuationWithZero K x)` at every nonzero `x : K`. -/
theorem eq_realAddValuation {v : AddValuation K (WithTop ℝ)}
    (hv : ∀ x : K, x ≠ 0 →
      v x = (((WithZero.log (normalizedValuationWithZero K x) : ℤ) : ℝ) : WithTop ℝ)) :
    v = realAddValuation K := by
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [hv x hx, realAddValuation_of_ne_zero hx]

/-- A uniformizer of `𝒪[K]` has `realAddValuation` equal to `1`. -/
@[simp]
theorem realAddValuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    realAddValuation K (π : K) = 1 := by
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have h := realAddValuation_coe_unit (Units.mk0 (π : K) hπ0)
  rw [Units.val_mk0, normalizedValuation_irreducible hπ, toAdd_ofAdd, Int.cast_one,
    WithTop.coe_one] at h
  exact h

/-- A unit of `𝒪[K]` has `realAddValuation` equal to `0`. -/
@[simp]
theorem realAddValuation_coe_integer_unit (u : 𝒪[K]ˣ) :
    realAddValuation K ((u : 𝒪[K]) : K) = 0 := by
  have hu0 : ((u : 𝒪[K]) : K) ≠ 0 := fun h ↦ u.ne_zero (Subtype.ext h)
  rw [realAddValuation_of_ne_zero hu0,
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
    rw [h, hval, ← WithTop.coe_zero, WithTop.coe_le_coe]
    exact_mod_cast Iff.rfl

/-- On `𝒪[K]`, `realAddValuation` agrees with `IsDiscreteValuationRing.addVal` cast from `ℕ∞` to
`WithTop ℝ`. -/
theorem realAddValuation_coe_integer (a : 𝒪[K]) :
    realAddValuation K (a : K) =
      (IsDiscreteValuationRing.addVal 𝒪[K] a).recTopCoe ⊤ fun n : ℕ ↦ ((n : ℝ) : WithTop ℝ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [IsDiscreteValuationRing.addVal_def' u hπ n, Subring.coe_mul, Subring.coe_pow,
      (realAddValuation K).map_mul, (realAddValuation K).map_pow,
      realAddValuation_coe_integer_unit u, realAddValuation_irreducible hπ, zero_add, nsmul_one]
    simp

/-- An element of `𝒪[K]` lies in `𝓂[K]` if and only if its `realAddValuation` is at least `1`. -/
theorem mem_maximalIdeal_iff_one_le_realAddValuation {a : 𝒪[K]} :
    a ∈ 𝓂[K] ↔ 1 ≤ realAddValuation K (a : K) := by
  have hmem : a ∈ 𝓂[K] ↔ 1 ≤ IsDiscreteValuationRing.addVal 𝒪[K] a := by
    simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
      (x := a) (n := 1))
  rw [hmem, realAddValuation_coe_integer]
  cases IsDiscreteValuationRing.addVal 𝒪[K] a using ENat.recTopCoe with
  | top => simp
  | coe n =>
    simp only [ENat.recTopCoe_natCast, ← ENat.natCast_one, ENat.natCast_le_natCast,
      ← WithTop.coe_one, WithTop.coe_le_coe]
    exact_mod_cast Iff.rfl

/-- An element of `𝒪[K]` lies in `𝓂[K]` if and only if its `realAddValuation` is positive. -/
theorem mem_maximalIdeal_iff_realAddValuation_pos {a : 𝒪[K]} :
    a ∈ 𝓂[K] ↔ 0 < realAddValuation K (a : K) := by
  rw [mem_maximalIdeal_iff_one_le_realAddValuation, realAddValuation_coe_integer]
  cases IsDiscreteValuationRing.addVal 𝒪[K] a using ENat.recTopCoe with
  | top =>
    simp only [ENat.recTopCoe_top, le_top, ← WithTop.coe_zero, WithTop.coe_lt_top]
  | coe n =>
    simp only [ENat.recTopCoe_natCast, ← WithTop.coe_one, ← WithTop.coe_zero, WithTop.coe_le_coe,
      WithTop.coe_lt_coe, Nat.cast_pos, Nat.one_le_cast]
    omega

/-- At a nonzero natural-number cast in `K`, `realAddValuation` equals `natCastValuation`. -/
theorem realAddValuation_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    realAddValuation K (n : K) = ((natCastValuation K n hn : ℝ) : WithTop ℝ) := by
  rw [realAddValuation_of_ne_zero hn, normalizedValuationWithZero_natCast K n hn,
    WithZero.log_exp, Int.cast_natCast]

/-- A natural-number cast in `K` has `realAddValuation` at least `1` if and only if it is divisible
by `ringChar 𝓀[K]`. -/
theorem one_le_realAddValuation_natCast_iff_dvd {n : ℕ} :
    1 ≤ realAddValuation K (n : K) ↔ ringChar 𝓀[K] ∣ n := by
  have hmem : (n : 𝒪[K]) ∈ 𝓂[K] ↔ ringChar 𝓀[K] ∣ n := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsLocalRing.isUnit_natCast_iff_not_dvd,
      not_not]
  rw [← hmem, mem_maximalIdeal_iff_one_le_realAddValuation, Subring.coe_natCast]

/-- A natural-number cast in `K` has `realAddValuation` equal to `0` if and only if it is not
divisible by the residue characteristic `ringChar 𝓀[K]`. Both mixed and equal characteristic are
covered. -/
theorem realAddValuation_natCast_eq_zero_iff_not_dvd {n : ℕ} :
    realAddValuation K (n : K) = 0 ↔ ¬ ringChar 𝓀[K] ∣ n := by
  constructor
  · intro h0 hdvd
    have h1 := one_le_realAddValuation_natCast_iff_dvd (K := K).mpr hdvd
    rw [h0] at h1
    exact absurd h1 (by simp)
  · intro hndvd
    obtain ⟨u, hu⟩ := (IsLocalRing.isUnit_natCast_iff_not_dvd (R := 𝒪[K])).mpr hndvd
    have hcoe : (n : K) = ((u : 𝒪[K]) : K) := by
      simpa using congrArg (Subtype.val : 𝒪[K] → K) hu.symm
    rw [hcoe, realAddValuation_coe_integer_unit]

/-- For every nonzero natural number `n`, `realAddValuation K (n : K)` is
`(n.factorization (ringChar 𝓀[K])) • realAddValuation K (ringChar 𝓀[K] : K)`, in both mixed and
equal characteristic. -/
theorem realAddValuation_natCast_eq_nsmul {n : ℕ} (hn : n ≠ 0) :
    realAddValuation K (n : K) =
      (n.factorization (ringChar 𝓀[K])) • realAddValuation K (ringChar 𝓀[K] : K) := by
  set p := ringChar 𝓀[K]
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] p
  set w := n.factorization p
  set q := n / p ^ w
  have hnq : p ^ w * q = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hqp : ¬ p ∣ q := Nat.not_dvd_ordCompl hp hn
  have hcast : (n : K) = (p : K) ^ w * (q : K) := by
    rw [← hnq, Nat.cast_mul, Nat.cast_pow]
  rw [hcast, (realAddValuation K).map_mul, (realAddValuation K).map_pow,
    realAddValuation_natCast_eq_zero_iff_not_dvd.mpr hqp, add_zero]

/-- At a nonzero element `x : K` and integer exponent `n : ℤ`, `realAddValuation K (x ^ n)` is
`n` times `(realAddValuation K x).untop₀`. -/
theorem realAddValuation_zpow_of_ne_zero {x : K} (hx : x ≠ 0) (n : ℤ) :
    realAddValuation K (x ^ n) = ((n * (realAddValuation K x).untop₀ : ℝ) : WithTop ℝ) := by
  rw [realAddValuation_of_ne_zero (zpow_ne_zero n hx), untop₀_realAddValuation, map_zpow₀,
    WithZero.log_zpow, zsmul_eq_mul]
  push_cast
  rfl

end SingleField

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- In a compatible extension `L/K` of nonarchimedean local fields, `algebraMap K L` scales
`realAddValuation` by `ramificationIndex K L`. -/
theorem realAddValuation_algebraMap (x : K) :
    realAddValuation L (algebraMap K L x) =
      (realAddValuation K x).map ((ramificationIndex K L : ℝ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
    rw [realAddValuation_of_ne_zero hxL, realAddValuation_of_ne_zero hx,
      normalizedValuationWithZero_algebraMap (K := K) (L := L), WithTop.map_coe,
      WithZero.log_pow, nsmul_eq_mul]
    push_cast
    rfl

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
  have heq : ramificationIndex L M = e :=
    Nat.eq_of_mul_eq_mul_left (ramificationIndex_pos (K := K) (L := L))
      ((ramificationIndex_tower (K := K) (L := L) M).symm.trans he.symm)
  rw [← heq]
  exact normalizedValuationWithZero_algebraMap (K := L) (L := M) x

/-- Every `K`-embedding `σ : L →ₐ[K] M` of compatible nonarchimedean local-field extensions raises
`normalizedValuationWithZero L x` to the power `ramificationIndex L M`. -/
theorem normalizedValuationWithZero_apply [Algebra L M] [IsScalarTower K L M]
    (σ : L →ₐ[K] M) (x : L) :
    normalizedValuationWithZero M (σ x) =
      normalizedValuationWithZero L x ^ ramificationIndex L M := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have : ValuativeExtension L M := ValuativeExtension.of_isScalarTower (K := K) (M := L) (N := M)
  exact σ.normalizedValuationWithZero_apply_of_mul_eq
    (ramificationIndex_tower (K := K) (L := L) M).symm x

/-- In a compatible tower `M/L/K` of nonarchimedean local fields, every `K`-embedding
`σ : L →ₐ[K] M` agrees with `algebraMap L M` under `normalizedValuationWithZero M`. -/
theorem normalizedValuationWithZero_apply_eq_algebraMap [Algebra L M] [IsScalarTower K L M]
    (σ : L →ₐ[K] M) (x : L) :
    normalizedValuationWithZero M (σ x) = normalizedValuationWithZero M (algebraMap L M x) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have : ValuativeExtension L M := ValuativeExtension.of_isScalarTower (K := K) (M := L) (N := M)
  rw [σ.normalizedValuationWithZero_apply, normalizedValuationWithZero_algebraMap]

/-- In a compatible tower `M/L/K` of nonarchimedean local fields, every `K`-embedding
`σ : L →ₐ[K] M` scales `realAddValuation` by `ramificationIndex L M`. -/
theorem realAddValuation_apply [Algebra L M] [IsScalarTower K L M]
    (σ : L →ₐ[K] M) (x : L) :
    realAddValuation M (σ x) =
      (realAddValuation L x).map ((ramificationIndex L M : ℝ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
    rw [realAddValuation_of_ne_zero hσx, realAddValuation_of_ne_zero hx,
      σ.normalizedValuationWithZero_apply, WithTop.map_coe, WithZero.log_pow, nsmul_eq_mul]
    push_cast
    rfl

end AlgHom

namespace AlgEquiv

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- Every `K`-automorphism of a compatible local-field extension `L/K` preserves
`realAddValuation L`. -/
@[simp]
theorem realAddValuation_apply (σ : L ≃ₐ[K] L) (x : L) :
    realAddValuation L (σ x) = realAddValuation L x := by
  have h := σ.toAlgHom.realAddValuation_apply (M := L) x
  have he : ramificationIndex L L = 1 :=
    ramificationIndex_eq_iff.mpr fun u ↦ by simp
  cases hx : realAddValuation L x <;> simpa [hx, he] using h

end AlgEquiv
