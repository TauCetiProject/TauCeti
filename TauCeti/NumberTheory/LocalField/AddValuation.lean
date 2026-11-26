/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.RingTheory.Valuation.ToAdditive
import TauCeti.NumberTheory.LocalField.IntegerRing.Basic

/-!
# Integer-valued normalized additive valuations on nonarchimedean local fields

`TauCeti.normalizedValuation M` expresses the normalized valuation of a nonarchimedean local field
`M` as a multiplicative homomorphism `Mˣ →* Multiplicative ℤ`, `normalizedValuationWithZero M`
extends it across zero to `M →*₀ ℤᵐ⁰`, and `Valuation.ord (intValuation M)` reads the valuation
additively on `M` with values in `ℤ` (taking junk value `0` at `0`). This file packages the bundled
additive valuation `TauCeti.normalizedIntAddValuation M : AddValuation M (WithTop ℤ)` (sending `0`
to `⊤`) and proves the bridges between `Valuation.ord (intValuation M)`,
`normalizedIntAddValuation M`, `IsDiscreteValuationRing.addVal 𝒪[M]`, and `ramificationIndex`. The
real-valued counterpart `TauCeti.realAddValuation` into `WithTop ℝ` lives in
`TauCeti.NumberTheory.LocalField.RealAddValuation`.

## Main definitions

* `TauCeti.normalizedIntAddValuation M`: the bundled `AddValuation M (WithTop ℤ)` sending a
  nonzero `x` to `Valuation.ord (intValuation M) x` and `0` to `⊤`.

## Main results

* `TauCeti.ord_intValuation_eq_log_normalizedValuationWithZero`,
  `TauCeti.mem_integer_iff_ord_intValuation_nonneg`,
  `TauCeti.mem_integer_iff_normalizedIntAddValuation_nonneg`, and
  `TauCeti.mem_maximalIdeal_iff_normalizedIntAddValuation_pos`: agreement with `WithZero.log` of
  `normalizedValuationWithZero` and characterizations of `𝒪[M]` and `𝓂[M]`.
* `TauCeti.ord_intValuation_irreducible`, `TauCeti.ord_intValuation_eq_zero_of_isUnit_integer`,
  `TauCeti.addVal_eq_natCast_toNat_ord_intValuation`,
  `TauCeti.ord_intValuation_of_addVal_eq_natCast`, and
  `TauCeti.normalizedIntAddValuation_coe_integer`: values at uniformizers and units of `𝒪[M]`,
  and comparison with `IsDiscreteValuationRing.addVal 𝒪[M]` via `ENat.map`.
* `TauCeti.ord_intValuation_algebraMap` and `TauCeti.normalizedIntAddValuation_algebraMap`: scaling
  by `ramificationIndex` in compatible extensions.
* `TauCeti.normalizedIntAddValuation_of_ne_zero` and `TauCeti.eq_normalizedIntAddValuation`:
  uniqueness of `normalizedIntAddValuation M` from agreement with `Valuation.ord (intValuation M)`
  away from zero.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §§1–4.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField IsLocalRing
open scoped WithZero

namespace TauCeti

section SingleField

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]

/-- The normalized additive valuation of a nonarchimedean local field `M` with values in
`WithTop ℤ`, sending `0` to `⊤` and a uniformizer to `1`. -/
def normalizedIntAddValuation : AddValuation M (WithTop ℤ) :=
  (intValuation M).addVal

/-- The defining formula of `normalizedIntAddValuation`. -/
theorem normalizedIntAddValuation_def :
    normalizedIntAddValuation M = (intValuation M).addVal :=
  (rfl)

variable {M}

/-- On all of `M` (including `0`), `Valuation.ord (intValuation M)` agrees with `WithZero.log` of
`normalizedValuationWithZero M`. -/
theorem ord_intValuation_eq_log_normalizedValuationWithZero (x : M) :
    Valuation.ord (intValuation M) x = WithZero.log (normalizedValuationWithZero M x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h := normalizedValuationWithZero_coe (Units.mk0 x hx)
    rw [Units.val_mk0, ← ofAdd_toAdd (normalizedValuation M (Units.mk0 x hx)),
      ← WithZero.exp_eq_coe_ofAdd, toAdd_normalizedValuation_eq_ord, Units.val_mk0] at h
    rw [h, WithZero.log_exp]

/-- An element of `M` lies in the ring of integers `𝒪[M]` if and only if
`Valuation.ord (intValuation M) x` is nonnegative; this holds at `x = 0` as well as away from
zero. -/
theorem mem_integer_iff_ord_intValuation_nonneg (x : M) :
    x ∈ 𝒪[M] ↔ 0 ≤ Valuation.ord (intValuation M) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simpa [toAdd_normalizedValuation_eq_ord] using
      mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 x hx)

/-- An irreducible element of `𝒪[M]` (a uniformizer of `M`) has `Valuation.ord (intValuation M)`
equal to `1`. -/
@[simp]
theorem ord_intValuation_irreducible {π : 𝒪[M]} (hπ : Irreducible π) :
    Valuation.ord (intValuation M) (π : M) = 1 := by
  have hπ0 : (π : M) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have h := toAdd_normalizedValuation_eq_ord (Units.mk0 (π : M) hπ0)
  rwa [Units.val_mk0, normalizedValuation_irreducible hπ, toAdd_ofAdd, eq_comm] at h

/-- A unit of `𝒪[M]` has `Valuation.ord (intValuation M)` equal to `0`. -/
theorem ord_intValuation_eq_zero_of_isUnit_integer {u : 𝒪[M]} (hu : IsUnit u) :
    Valuation.ord (intValuation M) (u : M) = 0 := by
  rw [ord_intValuation_eq_log_normalizedValuationWithZero,
    isUnit_iff_normalizedValuationWithZero_eq_one.mp hu, WithZero.log_one]

/-- A unit in `𝒪[M]ˣ` coerced to `M` has `Valuation.ord (intValuation M)` equal to `0`. -/
@[simp]
theorem ord_intValuation_coe_integer_units (u : 𝒪[M]ˣ) :
    Valuation.ord (intValuation M) ((u : 𝒪[M]) : M) = 0 :=
  ord_intValuation_eq_zero_of_isUnit_integer u.isUnit

/-- On nonzero elements of `𝒪[M]`, `IsDiscreteValuationRing.addVal 𝒪[M]` agrees with
`Valuation.ord (intValuation M)`. -/
theorem addVal_eq_natCast_toNat_ord_intValuation {a : 𝒪[M]} (ha : a ≠ 0) :
    IsDiscreteValuationRing.addVal 𝒪[M] a =
      ((Valuation.ord (intValuation M) (a : M)).toNat : ℕ∞) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[M]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hu0 : intValuation M ((u : 𝒪[M]) : M) ≠ 0 :=
    (intValuation M).ne_zero_iff.mpr fun h ↦ u.ne_zero (Subtype.ext h)
  have hπ0 : intValuation M ((π : M) ^ n) ≠ 0 :=
    (intValuation M).ne_zero_iff.mpr (pow_ne_zero n fun h ↦ hπ.ne_zero (Subtype.ext h))
  rw [IsDiscreteValuationRing.addVal_def' u hπ n, Subring.coe_mul, Subring.coe_pow,
    Valuation.ord_mul (intValuation M) hu0 hπ0, ord_intValuation_coe_integer_units,
    Valuation.ord_pow, ord_intValuation_irreducible hπ, mul_one, zero_add, Int.toNat_natCast]

/-- If `a : 𝒪[M]` has finite DVR valuation `k : ℕ`, then
`Valuation.ord (intValuation M) (a : M) = k`. -/
theorem ord_intValuation_of_addVal_eq_natCast {a : 𝒪[M]} {k : ℕ}
    (ha : IsDiscreteValuationRing.addVal 𝒪[M] a = (k : ℕ∞)) :
    Valuation.ord (intValuation M) (a : M) = k := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hnn : 0 ≤ Valuation.ord (intValuation M) (a : M) :=
    (mem_integer_iff_ord_intValuation_nonneg (a : M)).mp a.property
  have hk : (Valuation.ord (intValuation M) (a : M)).toNat = k :=
    ENat.natCast_inj.mp ((addVal_eq_natCast_toNat_ord_intValuation ha0).symm.trans ha)
  omega

/-- On a nonzero natural-number cast, `Valuation.ord (intValuation M)` agrees with
`natCastValuation`. -/
@[simp]
theorem ord_intValuation_natCast (n : ℕ) (hn : (n : M) ≠ 0) :
    Valuation.ord (intValuation M) (n : M) = natCastValuation M n hn := by
  rw [ord_intValuation_eq_log_normalizedValuationWithZero, normalizedValuationWithZero_natCast,
    WithZero.log_exp]

/-- Away from zero, `normalizedIntAddValuation M x` is
`(Valuation.ord (intValuation M) x : WithTop ℤ)`. -/
theorem normalizedIntAddValuation_of_ne_zero {x : M} (hx : x ≠ 0) :
    normalizedIntAddValuation M x = (Valuation.ord (intValuation M) x : WithTop ℤ) := by
  have hv : intValuation M x ≠ 0 := (intValuation M).ne_zero_iff.mpr hx
  rw [normalizedIntAddValuation_def, Valuation.addVal_eq_coe]
  exact Valuation.valuation_eq_exp_neg_ord (intValuation M) hv

/-- An element of `M` lies in `𝒪[M]` if and only if its `normalizedIntAddValuation` is
nonnegative. -/
theorem mem_integer_iff_normalizedIntAddValuation_nonneg (x : M) :
    x ∈ 𝒪[M] ↔ 0 ≤ normalizedIntAddValuation M x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [mem_integer_iff_ord_intValuation_nonneg, normalizedIntAddValuation_of_ne_zero hx,
      ← WithTop.coe_zero, WithTop.coe_le_coe]

/-- A unit of `𝒪[M]` has `normalizedIntAddValuation` equal to `0`. -/
theorem normalizedIntAddValuation_eq_zero_of_isUnit_integer {u : 𝒪[M]} (hu : IsUnit u) :
    normalizedIntAddValuation M (u : M) = 0 := by
  have hu0 : (u : M) ≠ 0 := fun h ↦ hu.ne_zero (Subtype.ext h)
  rw [normalizedIntAddValuation_of_ne_zero hu0, ord_intValuation_eq_zero_of_isUnit_integer hu,
    WithTop.coe_zero]

/-- A unit in `𝒪[M]ˣ` coerced to `M` has `normalizedIntAddValuation` equal to `0`. -/
@[simp]
theorem normalizedIntAddValuation_coe_integer_units (u : 𝒪[M]ˣ) :
    normalizedIntAddValuation M ((u : 𝒪[M]) : M) = 0 :=
  normalizedIntAddValuation_eq_zero_of_isUnit_integer u.isUnit

/-- A uniformizer of `M` has `normalizedIntAddValuation` equal to `1`. -/
@[simp]
theorem normalizedIntAddValuation_irreducible {π : 𝒪[M]} (hπ : Irreducible π) :
    normalizedIntAddValuation M (π : M) = 1 := by
  have hπ0 : (π : M) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  rw [normalizedIntAddValuation_of_ne_zero hπ0, ord_intValuation_irreducible hπ, WithTop.coe_one]

/-- `normalizedIntAddValuation M` is the unique `AddValuation M (WithTop ℤ)` agreeing with
`Valuation.ord (intValuation M)` on all nonzero elements of `M`. -/
theorem eq_normalizedIntAddValuation {v : AddValuation M (WithTop ℤ)}
    (hv : ∀ x : M, x ≠ 0 → v x = (Valuation.ord (intValuation M) x : WithTop ℤ)) :
    v = normalizedIntAddValuation M := by
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [hv x hx, normalizedIntAddValuation_of_ne_zero hx]

/-- On `𝒪[M]`, `normalizedIntAddValuation M` agrees with `IsDiscreteValuationRing.addVal 𝒪[M]`. -/
theorem normalizedIntAddValuation_coe_integer (a : 𝒪[M]) :
    normalizedIntAddValuation M (a : M) =
      (IsDiscreteValuationRing.addVal 𝒪[M] a).map ((↑) : ℕ → ℤ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have haM : (a : M) ≠ 0 := fun h ↦ ha (Subtype.ext h)
    have hnn : 0 ≤ Valuation.ord (intValuation M) (a : M) :=
      (mem_integer_iff_ord_intValuation_nonneg (a : M)).mp a.property
    rw [normalizedIntAddValuation_of_ne_zero haM, addVal_eq_natCast_toNat_ord_intValuation ha,
      ENat.map_natCast, Int.toNat_of_nonneg hnn]

/-- An element of `𝒪[M]` lies in `𝓂[M]` if and only if its `normalizedIntAddValuation` is strictly
positive. -/
theorem mem_maximalIdeal_iff_normalizedIntAddValuation_pos (x : 𝒪[M]) :
    x ∈ 𝓂[M] ↔ 0 < normalizedIntAddValuation M (x : M) := by
  have hunit : IsUnit x ↔ IsDiscreteValuationRing.addVal 𝒪[M] x = 0 := by
    rw [isUnit_iff_dvd_one, ← IsDiscreteValuationRing.addVal_le_iff_dvd,
      IsDiscreteValuationRing.addVal_one, nonpos_iff_eq_zero]
  have hmono : StrictMono (ENat.map ((↑) : ℕ → ℤ)) :=
    ENat.strictMono_map_iff.mpr fun _ _ h ↦ Int.ofNat_lt.mpr h
  have h0 : (0 : WithTop ℤ) = ENat.map ((↑) : ℕ → ℤ) 0 := by simp
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, ← ne_eq, ← pos_iff_ne_zero,
    normalizedIntAddValuation_coe_integer, h0, hmono.lt_iff_lt]

end SingleField

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- In a compatible extension `L/K` of nonarchimedean local fields,
`Valuation.ord (intValuation _)` scales by `ramificationIndex K L` on all of `K` (including `0`). -/
@[simp]
theorem ord_intValuation_algebraMap (x : K) :
    Valuation.ord (intValuation L) (algebraMap K L x) =
      ramificationIndex K L * Valuation.ord (intValuation K) x := by
  rw [ord_intValuation_eq_log_normalizedValuationWithZero,
    ord_intValuation_eq_log_normalizedValuationWithZero,
    normalizedValuationWithZero_algebraMap (K := K) (L := L), WithZero.log_pow, nsmul_eq_mul]

/-- In a compatible extension `L/K`, `normalizedIntAddValuation L` on `K` multiplies
`normalizedIntAddValuation K` by `ramificationIndex K L`. -/
theorem normalizedIntAddValuation_algebraMap (x : K) :
    normalizedIntAddValuation L (algebraMap K L x) =
      (normalizedIntAddValuation K x).map ((ramificationIndex K L : ℤ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
    rw [normalizedIntAddValuation_of_ne_zero hxL, normalizedIntAddValuation_of_ne_zero hx,
      WithTop.map_coe, ord_intValuation_algebraMap]

end Extension

end TauCeti
