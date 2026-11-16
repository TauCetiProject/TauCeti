/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.RingTheory.Valuation.ToAdditive

/-!
# Additive normalized valuations on nonarchimedean local fields

`TauCeti.normalizedValuation M` expresses the normalized valuation of a nonarchimedean local field
`M` as a multiplicative homomorphism `Mˣ →* Multiplicative ℤ`, and `normalizedValuationWithZero M`
extends it across zero to `M →*₀ ℤᵐ⁰`. Computations with Newton polygons, ramification polygons,
and valuation bounds on field elements instead read valuations additively on all of `M`, either as
integers (with junk value `0` at `0`) or as bundled `AddValuation` maps into `WithTop ℤ` and
`WithTop ℝ` (sending `0` to `⊤`).

This file provides those three presentations and the bridges between them,
`IsDiscreteValuationRing.addVal 𝒪[M]`, and extensions of local fields.

## Main definitions

* `TauCeti.addValInt M x`: the integer-valued normalized valuation `v_M(x) ∈ ℤ` for `x : M`,
  equal to `(normalizedValuation M (Units.mk0 x hx)).toAdd` for `x ≠ 0` and `0` at `x = 0`.
* `TauCeti.normalizedIntAddValuation M`: the bundled `AddValuation M (WithTop ℤ)` sending a
  nonzero `x` to `addValInt M x` and `0` to `⊤`.
* `TauCeti.normalizedAddValuation M`: the real-valued `AddValuation M (WithTop ℝ)` obtained by
  casting `normalizedIntAddValuation M` along `ℤ → ℝ`, in the convention consumed by
  `Polynomial.newtonPolygon`.

## Main results

* `TauCeti.addValInt_of_ne_zero`, `TauCeti.addValInt_eq_dite`, `TauCeti.addValInt_mul`,
  `TauCeti.min_addValInt_le_addValInt_add`, `TauCeti.addValInt_add_eq_min_of_ne`: arithmetic and
  ultrametric laws for `addValInt`.
* `TauCeti.mem_integer_iff_addValInt_nonneg`,
  `TauCeti.mem_integer_iff_normalizedIntAddValuation_nonneg`,
  `TauCeti.mem_integer_iff_normalizedAddValuation_nonneg`,
  `TauCeti.mem_maximalIdeal_iff_normalizedIntAddValuation_pos`, and
  `TauCeti.mem_maximalIdeal_iff_normalizedAddValuation_pos`: characterizations of `𝒪[M]` and `𝓂[M]`.
* `TauCeti.addVal_eq_natCast_toNat_addValInt`, `TauCeti.addValInt_of_addVal_eq_natCast`,
  `TauCeti.normalizedIntAddValuation_coe_integer`, and
  `TauCeti.normalizedAddValuation_coe_integer`: comparison with
  `IsDiscreteValuationRing.addVal 𝒪[M]` via `ENat.map`.
* `TauCeti.addValInt_algebraMap`, `TauCeti.normalizedIntAddValuation_algebraMap`,
  `TauCeti.normalizedAddValuation_algebraMap`: scaling by `ramificationIndex K L` in a compatible
  extension `L/K`.
* `TauCeti.normalizedIntAddValuation_of_ne_zero`, `TauCeti.eq_normalizedIntAddValuation`,
  `TauCeti.normalizedAddValuation_of_ne_zero`, and `TauCeti.eq_normalizedAddValuation`:
  uniqueness of `normalizedIntAddValuation M` and `normalizedAddValuation M` from agreement with
  `addValInt M` away from zero.

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

/-- The additive normalized valuation `v_M(x) ∈ ℤ` of an element `x` of a nonarchimedean local
field `M`, taking the junk value `0` at `x = 0`. At a uniformizer of `M` its value is `1`. -/
def addValInt (x : M) : ℤ :=
  WithZero.log (normalizedValuationWithZero M x)

/-- The defining formula of `addValInt` as the `WithZero.log` of `normalizedValuationWithZero`. -/
theorem addValInt_def (x : M) :
    addValInt M x = WithZero.log (normalizedValuationWithZero M x) := (rfl)

/-- The normalized additive valuation of a nonarchimedean local field `M` with values in
`WithTop ℤ`, sending `0` to `⊤` and a uniformizer to `1`. -/
def normalizedIntAddValuation : AddValuation M (WithTop ℤ) :=
  (intValuation M).addVal

/-- The defining formula of `normalizedIntAddValuation`. -/
theorem normalizedIntAddValuation_def :
    normalizedIntAddValuation M = (intValuation M).addVal :=
  (rfl)

/-- The normalized real-valued additive valuation of a nonarchimedean local field `M`, sending `0`
to `⊤` and a nonzero `x` to `(addValInt M x : ℝ)`. This is the valuation consumed by
`Polynomial.newtonPolygon`. -/
def normalizedAddValuation : AddValuation M (WithTop ℝ) :=
  (normalizedIntAddValuation M).map
    (OrderAddMonoidHom.mk (Int.castAddHom ℝ).withTopMap
      (WithTop.monotone_map_iff.mpr (by
        rw [Int.coe_castAddHom]
        exact fun _ _ h ↦ Int.cast_le.mpr h)))
    rfl

/-- The defining formula of `normalizedAddValuation`. -/
theorem normalizedAddValuation_def :
    normalizedAddValuation M =
      (normalizedIntAddValuation M).map
        (OrderAddMonoidHom.mk (Int.castAddHom ℝ).withTopMap
          (WithTop.monotone_map_iff.mpr (by
            rw [Int.coe_castAddHom]
            exact fun _ _ h ↦ Int.cast_le.mpr h)))
        rfl := (rfl)

variable {M}

/-- At a nonzero element, `addValInt` decodes `normalizedValuation`. -/
theorem addValInt_of_ne_zero {x : M} (hx : x ≠ 0) :
    addValInt M x = (normalizedValuation M (Units.mk0 x hx)).toAdd := by
  have h := normalizedValuationWithZero_coe (Units.mk0 x hx)
  rw [Units.val_mk0, ← ofAdd_toAdd (normalizedValuation M (Units.mk0 x hx)),
    ← WithZero.exp_eq_coe_ofAdd] at h
  rw [addValInt, h, WithZero.log_exp]

/-- `addValInt M` agrees on all of `M` with `Valuation.ord (intValuation M)`. -/
theorem addValInt_eq_ord (x : M) : addValInt M x = Valuation.ord (intValuation M) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [addValInt]
  · rw [addValInt_of_ne_zero hx, toAdd_normalizedValuation_eq_ord, Units.val_mk0]

/-- On `Mˣ`, `addValInt` is `Multiplicative.toAdd` of `normalizedValuation`. -/
@[simp]
theorem addValInt_coe_units (u : Mˣ) :
    addValInt M (u : M) = (normalizedValuation M u).toAdd := by
  simpa using addValInt_of_ne_zero u.ne_zero

/-- The `dite` presentation of `addValInt`: `0` at `0`, and `toAdd` of `normalizedValuation`
away from `0`. -/
theorem addValInt_eq_dite (x : M) [Decidable (x = 0)] :
    addValInt M x = if hx : x = 0 then 0 else (normalizedValuation M (Units.mk0 x hx)).toAdd := by
  split_ifs with hx
  · simp [addValInt, hx]
  · exact addValInt_of_ne_zero hx

/-- At `0`, `addValInt` takes its junk value `0`. -/
@[simp]
theorem addValInt_zero : addValInt M 0 = 0 := by
  rw [addValInt_eq_ord, Valuation.ord_zero]

/-- At `1`, `addValInt` is `0`. -/
@[simp]
theorem addValInt_one : addValInt M 1 = 0 := by
  rw [addValInt_eq_ord, Valuation.ord_one]

/-- Negation preserves `addValInt`. -/
@[simp]
theorem addValInt_neg (x : M) : addValInt M (-x) = addValInt M x := by
  rw [addValInt_eq_ord, addValInt_eq_ord, Valuation.ord_neg]

/-- On nonzero elements, `addValInt` converts multiplication to addition. -/
theorem addValInt_mul {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) :
    addValInt M (x * y) = addValInt M x + addValInt M y := by
  rw [addValInt_eq_ord, addValInt_eq_ord, addValInt_eq_ord]
  exact Valuation.ord_mul (intValuation M) ((intValuation M).ne_zero_iff.mpr hx)
    ((intValuation M).ne_zero_iff.mpr hy)

/-- On finite products of nonzero elements, `addValInt` equals the sum of valuations. -/
theorem addValInt_prod {ι : Type*} (s : Finset ι) {f : ι → M} (hf : ∀ i ∈ s, f i ≠ 0) :
    addValInt M (∏ i ∈ s, f i) = ∑ i ∈ s, addValInt M (f i) := by
  simp_rw [addValInt_eq_ord]
  exact Valuation.ord_prod (intValuation M) s fun i hi ↦ (intValuation M).ne_zero_iff.mpr (hf i hi)

/-- Inversion negates `addValInt` (including at `0`, where both sides vanish). -/
@[simp]
theorem addValInt_inv (x : M) : addValInt M x⁻¹ = -addValInt M x := by
  rw [addValInt_eq_ord, addValInt_eq_ord, Valuation.ord_inv]

/-- On nonzero elements, `addValInt` converts division to subtraction. -/
theorem addValInt_div {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) :
    addValInt M (x / y) = addValInt M x - addValInt M y := by
  rw [addValInt_eq_ord, addValInt_eq_ord, addValInt_eq_ord,
    Valuation.ord_div (intValuation M) hx hy]

/-- Natural-number powers multiply `addValInt` by the exponent. -/
@[simp]
theorem addValInt_pow (x : M) (n : ℕ) : addValInt M (x ^ n) = n * addValInt M x := by
  rw [addValInt_eq_ord, addValInt_eq_ord, Valuation.ord_pow]

/-- Integer powers multiply `addValInt` by the exponent. -/
@[simp]
theorem addValInt_zpow (x : M) (n : ℤ) : addValInt M (x ^ n) = n * addValInt M x := by
  rw [addValInt_eq_ord, addValInt_eq_ord, Valuation.ord_zpow]

/-- Every integer is the normalized additive valuation of an element of `M`. -/
theorem addValInt_surjective : Function.Surjective (addValInt M) := by
  intro n
  obtain ⟨x, hx⟩ := Valuation.ord_surjective (intValuation M) intValuation_surjective n
  exact ⟨x, (addValInt_eq_ord x).trans hx⟩

/-- The ultrametric inequality for `addValInt` when the sum is nonzero. -/
theorem min_addValInt_le_addValInt_add {x y : M} (hxy : x + y ≠ 0) :
    min (addValInt M x) (addValInt M y) ≤ addValInt M (x + y) := by
  simp_rw [addValInt_eq_ord]
  exact Valuation.min_ord_le_ord_add (intValuation M) ((intValuation M).ne_zero_iff.mpr hxy)

/-- Strict ultrametric equality for `addValInt` on nonzero elements of distinct valuation. -/
theorem addValInt_add_eq_min_of_ne {x y : M} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : addValInt M x ≠ addValInt M y) :
    addValInt M (x + y) = min (addValInt M x) (addValInt M y) := by
  simp_rw [addValInt_eq_ord] at hne ⊢
  exact Valuation.ord_add_eq_min_of_ord_ne (intValuation M)
    ((intValuation M).ne_zero_iff.mpr hx) ((intValuation M).ne_zero_iff.mpr hy) hne

/-- An element of `M` lies in the ring of integers `𝒪[M]` if and only if its integer normalized
valuation `addValInt M x` is nonnegative; this holds at `x = 0` as well as away from zero. -/
theorem mem_integer_iff_addValInt_nonneg (x : M) : x ∈ 𝒪[M] ↔ 0 ≤ addValInt M x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [addValInt_of_ne_zero hx, ← mem_integer_iff_toAdd_normalizedValuation_nonneg, Units.val_mk0]

/-- An irreducible element of `𝒪[M]` (a uniformizer of `M`) has `addValInt` equal to `1`. -/
@[simp]
theorem addValInt_irreducible {π : 𝒪[M]} (hπ : Irreducible π) : addValInt M (π : M) = 1 := by
  have hπ0 : (π : M) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  rw [addValInt_of_ne_zero hπ0, normalizedValuation_irreducible hπ, toAdd_ofAdd]

/-- A unit of `𝒪[M]` has `addValInt` equal to `0`. -/
theorem addValInt_eq_zero_of_isUnit_integer {u : 𝒪[M]} (hu : IsUnit u) :
    addValInt M (u : M) = 0 := by
  have h1 : normalizedValuationWithZero M (u : M) = 1 :=
    isUnit_iff_normalizedValuationWithZero_eq_one.mp hu
  rw [addValInt, h1, WithZero.log_one]

/-- A unit in `𝒪[M]ˣ` coerced to `M` has `addValInt` equal to `0`. -/
@[simp]
theorem addValInt_coe_integer_units (u : 𝒪[M]ˣ) : addValInt M ((u : 𝒪[M]) : M) = 0 :=
  addValInt_eq_zero_of_isUnit_integer u.isUnit

/-- On nonzero elements of `𝒪[M]`, `IsDiscreteValuationRing.addVal 𝒪[M]` agrees with `addValInt`. -/
theorem addVal_eq_natCast_toNat_addValInt {a : 𝒪[M]} (ha : a ≠ 0) :
    IsDiscreteValuationRing.addVal 𝒪[M] a = ((addValInt M (a : M)).toNat : ℕ∞) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[M]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hu0 : ((u : 𝒪[M]) : M) ≠ 0 := fun h ↦ u.ne_zero (Subtype.ext h)
  have hπ0 : (π : M) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  rw [IsDiscreteValuationRing.addVal_def' u hπ n, Subring.coe_mul, Subring.coe_pow,
    addValInt_mul hu0 (pow_ne_zero n hπ0), addValInt_coe_integer_units, addValInt_pow,
    addValInt_irreducible hπ, mul_one, zero_add, Int.toNat_natCast]

/-- If `a : 𝒪[M]` has finite DVR valuation `k : ℕ`, then `addValInt M (a : M) = k`. -/
theorem addValInt_of_addVal_eq_natCast {a : 𝒪[M]} {k : ℕ}
    (ha : IsDiscreteValuationRing.addVal 𝒪[M] a = (k : ℕ∞)) :
    addValInt M (a : M) = k := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hnn : 0 ≤ addValInt M (a : M) := (mem_integer_iff_addValInt_nonneg (a : M)).mp a.2
  have hk : (addValInt M (a : M)).toNat = k :=
    ENat.natCast_inj.mp ((addVal_eq_natCast_toNat_addValInt ha0).symm.trans ha)
  omega

/-- On a nonzero natural-number cast, `addValInt` agrees with `natCastValuation`. -/
@[simp]
theorem addValInt_natCast (n : ℕ) (hn : (n : M) ≠ 0) :
    addValInt M (n : M) = natCastValuation M n hn := by
  rw [addValInt_of_ne_zero hn, toAdd_normalizedValuation_natCast]

/-- Away from zero, `normalizedIntAddValuation M x` is `(addValInt M x : WithTop ℤ)`. -/
theorem normalizedIntAddValuation_of_ne_zero {x : M} (hx : x ≠ 0) :
    normalizedIntAddValuation M x = (addValInt M x : WithTop ℤ) := by
  have hv : intValuation M x ≠ 0 := (intValuation M).ne_zero_iff.mpr hx
  rw [normalizedIntAddValuation_def, Valuation.addVal_eq_coe, addValInt_eq_ord]
  exact Valuation.valuation_eq_exp_neg_ord (intValuation M) hv

/-- `normalizedAddValuation M` is `normalizedIntAddValuation M` cast from `WithTop ℤ` to
`WithTop ℝ`. -/
theorem normalizedAddValuation_apply (x : M) :
    normalizedAddValuation M x = (normalizedIntAddValuation M x).map ((↑) : ℤ → ℝ) := by
  refine (congrFun (congrArg DFunLike.coe (normalizedAddValuation_def M)) x).trans ?_
  refine (AddValuation.map_apply _ _ (normalizedIntAddValuation M) x).trans ?_
  refine (congrFun (OrderAddMonoidHom.coe_mk _ _) _).trans ?_
  simp

/-- Away from zero, `normalizedAddValuation M x` is `(addValInt M x : ℝ)`. -/
theorem normalizedAddValuation_of_ne_zero {x : M} (hx : x ≠ 0) :
    normalizedAddValuation M x = ((addValInt M x : ℝ) : WithTop ℝ) := by
  rw [normalizedAddValuation_apply, normalizedIntAddValuation_of_ne_zero hx, WithTop.map_coe]

/-- An element of `M` lies in `𝒪[M]` if and only if its `normalizedIntAddValuation` is
nonnegative. -/
theorem mem_integer_iff_normalizedIntAddValuation_nonneg (x : M) :
    x ∈ 𝒪[M] ↔ 0 ≤ normalizedIntAddValuation M x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [mem_integer_iff_addValInt_nonneg, normalizedIntAddValuation_of_ne_zero hx,
      ← WithTop.coe_zero, WithTop.coe_le_coe]

/-- An element of `M` lies in `𝒪[M]` if and only if its `normalizedAddValuation` is nonnegative. -/
theorem mem_integer_iff_normalizedAddValuation_nonneg (x : M) :
    x ∈ 𝒪[M] ↔ 0 ≤ normalizedAddValuation M x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [mem_integer_iff_addValInt_nonneg, normalizedAddValuation_of_ne_zero hx,
      ← WithTop.coe_zero, WithTop.coe_le_coe, Int.cast_nonneg_iff]

/-- A unit of `𝒪[M]` has `normalizedIntAddValuation` equal to `0`. -/
theorem normalizedIntAddValuation_eq_zero_of_isUnit_integer {u : 𝒪[M]} (hu : IsUnit u) :
    normalizedIntAddValuation M (u : M) = 0 := by
  have hu0 : (u : M) ≠ 0 := fun h ↦ hu.ne_zero (Subtype.ext h)
  rw [normalizedIntAddValuation_of_ne_zero hu0, addValInt_eq_zero_of_isUnit_integer hu,
    WithTop.coe_zero]

/-- A unit in `𝒪[M]ˣ` coerced to `M` has `normalizedIntAddValuation` equal to `0`. -/
@[simp]
theorem normalizedIntAddValuation_coe_integer_units (u : 𝒪[M]ˣ) :
    normalizedIntAddValuation M ((u : 𝒪[M]) : M) = 0 :=
  normalizedIntAddValuation_eq_zero_of_isUnit_integer u.isUnit

/-- A unit of `𝒪[M]` has `normalizedAddValuation` equal to `0`. -/
theorem normalizedAddValuation_eq_zero_of_isUnit_integer {u : 𝒪[M]} (hu : IsUnit u) :
    normalizedAddValuation M (u : M) = 0 := by
  rw [normalizedAddValuation_apply, normalizedIntAddValuation_eq_zero_of_isUnit_integer hu]
  simp

/-- A unit in `𝒪[M]ˣ` coerced to `M` has `normalizedAddValuation` equal to `0`. -/
@[simp]
theorem normalizedAddValuation_coe_integer_units (u : 𝒪[M]ˣ) :
    normalizedAddValuation M ((u : 𝒪[M]) : M) = 0 :=
  normalizedAddValuation_eq_zero_of_isUnit_integer u.isUnit

/-- A uniformizer of `M` has `normalizedIntAddValuation` equal to `1`. -/
@[simp]
theorem normalizedIntAddValuation_irreducible {π : 𝒪[M]} (hπ : Irreducible π) :
    normalizedIntAddValuation M (π : M) = 1 := by
  have hπ0 : (π : M) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  rw [normalizedIntAddValuation_of_ne_zero hπ0, addValInt_irreducible hπ, WithTop.coe_one]

/-- A uniformizer of `M` has `normalizedAddValuation` equal to `1`. -/
@[simp]
theorem normalizedAddValuation_irreducible {π : 𝒪[M]} (hπ : Irreducible π) :
    normalizedAddValuation M (π : M) = 1 := by
  have hπ0 : (π : M) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  rw [normalizedAddValuation_of_ne_zero hπ0, addValInt_irreducible hπ, Int.cast_one,
    WithTop.coe_one]

/-- `normalizedIntAddValuation M` is the unique `AddValuation M (WithTop ℤ)` agreeing with
`addValInt M` on all nonzero elements of `M`. -/
theorem eq_normalizedIntAddValuation {v : AddValuation M (WithTop ℤ)}
    (hv : ∀ x : M, x ≠ 0 → v x = (addValInt M x : WithTop ℤ)) :
    v = normalizedIntAddValuation M := by
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [hv x hx, normalizedIntAddValuation_of_ne_zero hx]

/-- `normalizedAddValuation M` is the unique `AddValuation M (WithTop ℝ)` agreeing with
`addValInt M` on all nonzero elements of `M`. -/
theorem eq_normalizedAddValuation {v : AddValuation M (WithTop ℝ)}
    (hv : ∀ x : M, x ≠ 0 → v x = ((addValInt M x : ℝ) : WithTop ℝ)) :
    v = normalizedAddValuation M := by
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [hv x hx, normalizedAddValuation_of_ne_zero hx]

/-- On `𝒪[M]`, `normalizedIntAddValuation M` agrees with `IsDiscreteValuationRing.addVal 𝒪[M]`. -/
theorem normalizedIntAddValuation_coe_integer (a : 𝒪[M]) :
    normalizedIntAddValuation M (a : M) =
      (IsDiscreteValuationRing.addVal 𝒪[M] a).map ((↑) : ℕ → ℤ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have haM : (a : M) ≠ 0 := fun h ↦ ha (Subtype.ext h)
    have hnn : 0 ≤ addValInt M (a : M) := (mem_integer_iff_addValInt_nonneg (a : M)).mp a.2
    rw [normalizedIntAddValuation_of_ne_zero haM, addVal_eq_natCast_toNat_addValInt ha,
      ENat.map_natCast, Int.toNat_of_nonneg hnn]

/-- On `𝒪[M]`, `normalizedAddValuation M` agrees with `IsDiscreteValuationRing.addVal 𝒪[M]`. -/
theorem normalizedAddValuation_coe_integer (a : 𝒪[M]) :
    normalizedAddValuation M (a : M) =
      (IsDiscreteValuationRing.addVal 𝒪[M] a).map ((↑) : ℕ → ℝ) := by
  rw [normalizedAddValuation_apply, normalizedIntAddValuation_coe_integer]
  generalize IsDiscreteValuationRing.addVal 𝒪[M] a = v
  induction v using ENat.recTopCoe with
  | top => simp
  | coe k => simp [ENat.map_natCast]

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

/-- An element of `𝒪[M]` lies in `𝓂[M]` if and only if its `normalizedAddValuation` is strictly
positive. -/
theorem mem_maximalIdeal_iff_normalizedAddValuation_pos (x : 𝒪[M]) :
    x ∈ 𝓂[M] ↔ 0 < normalizedAddValuation M (x : M) := by
  have hunit : IsUnit x ↔ IsDiscreteValuationRing.addVal 𝒪[M] x = 0 := by
    rw [isUnit_iff_dvd_one, ← IsDiscreteValuationRing.addVal_le_iff_dvd,
      IsDiscreteValuationRing.addVal_one, nonpos_iff_eq_zero]
  have hmono : StrictMono (ENat.map ((↑) : ℕ → ℝ)) :=
    ENat.strictMono_map_iff.mpr fun _ _ h ↦ Nat.cast_lt.mpr h
  have h0 : (0 : WithTop ℝ) = ENat.map ((↑) : ℕ → ℝ) 0 := by simp
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, ← ne_eq, ← pos_iff_ne_zero,
    normalizedAddValuation_coe_integer, h0, hmono.lt_iff_lt]

end SingleField

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- In a compatible extension `L/K` of nonarchimedean local fields, `addValInt` scales by
`ramificationIndex K L` on all of `K` (including `0`). -/
@[simp]
theorem addValInt_algebraMap (x : K) :
    addValInt L (algebraMap K L x) = ramificationIndex K L * addValInt K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
    have hu : Units.mk0 (algebraMap K L x) hxL =
        Units.map (algebraMap K L : K →* L) (Units.mk0 x hx) := by
      ext
      simp
    rw [addValInt_of_ne_zero hxL, hu, toAdd_normalizedValuation_algebraMap,
      addValInt_of_ne_zero hx]

/-- In a compatible extension `L/K`, `normalizedIntAddValuation L` on `K` multiplies
`normalizedIntAddValuation K` by `ramificationIndex K L`. -/
theorem normalizedIntAddValuation_algebraMap (x : K) :
    normalizedIntAddValuation L (algebraMap K L x) =
      (normalizedIntAddValuation K x).map ((ramificationIndex K L : ℤ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
    rw [normalizedIntAddValuation_of_ne_zero hxL, normalizedIntAddValuation_of_ne_zero hx,
      WithTop.map_coe, addValInt_algebraMap]

/-- In a compatible extension `L/K`, `normalizedAddValuation L` on `K` multiplies
`normalizedAddValuation K` by `(ramificationIndex K L : ℝ)`. -/
theorem normalizedAddValuation_algebraMap (x : K) :
    normalizedAddValuation L (algebraMap K L x) =
      (normalizedAddValuation K x).map ((ramificationIndex K L : ℝ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
    rw [normalizedAddValuation_of_ne_zero hxL, normalizedAddValuation_of_ne_zero hx,
      WithTop.map_coe, addValInt_algebraMap, Int.cast_mul, Int.cast_natCast]

end Extension

end TauCeti
