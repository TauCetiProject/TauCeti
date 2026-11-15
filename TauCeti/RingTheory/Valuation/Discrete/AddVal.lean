/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import TauCeti.RingTheory.Valuation.Discrete.Order
public import TauCeti.RingTheory.Valuation.ToAdditive

/-!
# Normalized `ℤᵐ⁰`-valued, `ℤ`-valued, and `ℝ`-valued valuations of a discrete valuation

Let `v : Valuation R Γ` be a rank-one discrete valuation (`v.IsRankOneDiscrete`), with generator
`γ = IsRankOneDiscrete.generator v < 1` of `v.valueGroup`. Transporting `v.restrict` along
`IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v` produces a `ℤᵐ⁰`-valued valuation
`v.intValuation` equivalent to `v` that sends `γ ^ m` to `WithZero.exp (-m)` and `0` to `0`.
Converting `v.intValuation` to additive notation via `Valuation.addVal` gives the normalized
integer additive valuation

`v.intAddVal : AddValuation R (WithTop ℤ)`,

characterized by `v.intAddVal x = m ↔ v x = γ ^ m` and `v.intAddVal x = ⊤ ↔ v x = 0`, so every
uniformizer has additive valuation `1`. Pushing forward along `ℤ →+ ℝ` gives the real additive
valuation

`v.realAddVal : AddValuation R (WithTop ℝ)`,

which agrees with `(v.intAddVal ·).map ((↑) : ℤ → ℝ)` and feeds directly into real-valued APIs such
as Newton polygons.

On a division ring, `v.intValuation` is surjective onto `ℤᵐ⁰`, so equivalent rank-one discrete
valuations have literally equal `intValuation`, `intAddVal`, and `realAddVal`. On a field `K`, for
any discrete valuation ring `R` with `v.Integers R` (in particular `v.valuationSubring`),
`v.intAddVal` restricts on `R` to `IsDiscreteValuationRing.addVal R` cast from `ℕ∞` to `WithTop ℤ`.

## Main definitions

* `Valuation.intValuation`: the normalized `ℤᵐ⁰`-valued valuation attached to a rank-one discrete
  valuation `v`.
* `Valuation.intAddVal`: the normalized additive valuation `AddValuation R (WithTop ℤ)` with value
  `1` at every uniformizer of `v`.
* `Valuation.realAddVal`: the normalized real additive valuation `AddValuation R (WithTop ℝ)`
  obtained by casting `v.intAddVal` to `ℝ`.

## Main results

* `Valuation.intValuation_eq_exp_neg_iff`, `Valuation.intAddVal_eq_coe_iff`, and
  `Valuation.realAddVal_eq_intCast_iff`: characterization of values by powers of the generator of
  `v.valueGroup`.
* `Valuation.IsUniformizer.intAddVal_eq_one`, `Valuation.isUniformizer_iff_intAddVal_eq_one`, and
  `Valuation.IsUniformizer.realAddVal_eq_one`: uniformizers are precisely the elements of normalized
  additive valuation `1`.
* `Valuation.intValuation_surjective` and `Valuation.IsEquiv.intValuation_eq`: on a division ring,
  `v.intValuation` is surjective and depends only on the equivalence class of `v`.
* `Valuation.Integers.intAddVal_algebraMap_eq_map_addVal` and
  `Valuation.intAddVal_coe_valuationSubring`: compatibility with `IsDiscreteValuationRing.addVal` on
  any discrete valuation ring of integers.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter I, §1.
* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §3.
-/

public section

open scoped WithZero
open MonoidWithZeroHom

namespace Valuation

section Ring

variable {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation R Γ) [hv : v.IsRankOneDiscrete]

/-- The normalized `ℤᵐ⁰`-valued valuation attached to a rank-one discrete valuation `v`: it sends
an element of value `(IsRankOneDiscrete.generator v) ^ m` to `WithZero.exp (-m)`. -/
noncomputable def intValuation : Valuation R ℤᵐ⁰ :=
  v.restrict.map (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v)

/-- The normalized integer additive valuation attached to a rank-one discrete valuation `v`, with
values in `WithTop ℤ` and value `1` at every uniformizer. -/
noncomputable def intAddVal : AddValuation R (WithTop ℤ) :=
  v.intValuation.addVal

/-- The normalized real additive valuation attached to a rank-one discrete valuation `v`, obtained
by pushing `v.intAddVal` forward along `ℤ →+ ℝ`. -/
noncomputable def realAddVal : AddValuation R (WithTop ℝ) :=
  v.intAddVal.map
    { (Int.castAddHom ℝ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr fun _ _ h ↦ Int.cast_le.mpr h }
    rfl

/-- The defining formula of `Valuation.intValuation`. -/
theorem intValuation_def :
    v.intValuation = v.restrict.map (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v) :=
  (rfl)

/-- Pointwise evaluation of `Valuation.intValuation`. -/
theorem intValuation_apply (x : R) :
    v.intValuation x = IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v (v.restrict x) :=
  (rfl)

/-- The defining formula of `Valuation.intAddVal`. -/
theorem intAddVal_def : v.intAddVal = v.intValuation.addVal := (rfl)

/-- Pointwise evaluation of `Valuation.intAddVal` as the negative logarithm of `v.intValuation`. -/
theorem intAddVal_apply (x : R) : v.intAddVal x = WithZero.negLog (v.intValuation x) :=
  v.intValuation.addVal_apply x

/-- `v.realAddVal` agrees pointwise with `v.intAddVal` cast from `ℤ` to `ℝ`. -/
theorem realAddVal_eq_map (x : R) :
    v.realAddVal x = (v.intAddVal x).map ((↑) : ℤ → ℝ) :=
  (rfl)

/-- The normalized `ℤᵐ⁰`-valued valuation is equivalent to `v`. -/
theorem isEquiv_intValuation : v.intValuation.IsEquiv v := by
  rw [intValuation_def]
  exact (isEquiv_map_self_of_strictMono _
    (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono v).injective).trans
    v.isEquiv_restrict.symm

/-- `v.intValuation` vanishes on the same elements as `v`. -/
@[simp]
theorem intValuation_eq_zero_iff {x : R} : v.intValuation x = 0 ↔ v x = 0 :=
  v.isEquiv_intValuation.eq_zero

/-- `v.intValuation` induces the same preorder as `v`. -/
theorem intValuation_le_intValuation_iff {x y : R} :
    v.intValuation x ≤ v.intValuation y ↔ v x ≤ v y :=
  v.isEquiv_intValuation x y

/-- `v.intValuation` induces the same strict order as `v`. -/
theorem intValuation_lt_intValuation_iff {x y : R} :
    v.intValuation x < v.intValuation y ↔ v x < v y :=
  v.isEquiv_intValuation.lt_iff_lt

/-- `v.intValuation x ≤ 1` is equivalent to `v x ≤ 1`. -/
@[simp]
theorem intValuation_le_one_iff {x : R} : v.intValuation x ≤ 1 ↔ v x ≤ 1 :=
  v.isEquiv_intValuation.le_one_iff_le_one

/-- `v.intValuation x < 1` is equivalent to `v x < 1`. -/
@[simp]
theorem intValuation_lt_one_iff {x : R} : v.intValuation x < 1 ↔ v x < 1 :=
  v.isEquiv_intValuation.lt_one_iff_lt_one

/-- `v.intValuation x = 1` is equivalent to `v x = 1`. -/
@[simp]
theorem intValuation_eq_one_iff {x : R} : v.intValuation x = 1 ↔ v x = 1 :=
  v.isEquiv_intValuation.eq_one_iff_eq_one

/-- `v.intValuation` takes the value `WithZero.exp (-m)` exactly on the elements of value
`γ ^ m`, where `γ < 1` generates `v.valueGroup`. -/
theorem intValuation_eq_exp_neg_iff {x : R} {m : ℤ} :
    v.intValuation x = WithZero.exp (-m) ↔ v x = (hv.generator : Γ) ^ m := by
  rw [intValuation_apply,
    ← IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply_zpow v m,
    (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono v).injective.eq_iff,
    ← ValueGroup₀.embedding_inj, v.embedding_restrict, map_zpow₀,
    IsRankOneDiscrete.embedding_generator']

/-- Outside the valuation support, `ord v.intValuation x = m` means `v x = γ ^ m`. -/
theorem ord_intValuation_eq_iff {x : R} (hx : v x ≠ 0) {m : ℤ} :
    ord v.intValuation x = m ↔ v x = (hv.generator : Γ) ^ m := by
  rw [ord_eq_iff_valuation_eq_exp_neg v.intValuation (v.intValuation_eq_zero_iff.not.mpr hx),
    intValuation_eq_exp_neg_iff]

/-- `v.intAddVal` takes the value `⊤` exactly on the valuation support of `v`. -/
@[simp]
theorem intAddVal_eq_top_iff {x : R} : v.intAddVal x = ⊤ ↔ v x = 0 := by
  rw [intAddVal_apply, WithZero.negLog_eq_top, intValuation_eq_zero_iff]

/-- **Characteristic equation of `v.intAddVal`**: `v.intAddVal x = m` if and only if
`v x = γ ^ m`, where `γ < 1` generates `v.valueGroup`. -/
theorem intAddVal_eq_coe_iff {x : R} {m : ℤ} :
    v.intAddVal x = (m : WithTop ℤ) ↔ v x = (hv.generator : Γ) ^ m := by
  rw [intAddVal_def, addVal_eq_coe, intValuation_eq_exp_neg_iff]

/-- Outside the valuation support, `v.intAddVal x` is `ord v.intValuation x`. -/
theorem intAddVal_of_map_ne_zero {x : R} (hx : v x ≠ 0) :
    v.intAddVal x = (ord v.intValuation x : WithTop ℤ) := by
  rw [intAddVal_eq_coe_iff]
  exact (v.ord_intValuation_eq_iff hx).mp rfl

/-- Outside the valuation support, `v.intAddVal` takes an integer value. -/
theorem exists_int_intAddVal {x : R} (hx : v x ≠ 0) :
    ∃ m : ℤ, v.intAddVal x = (m : WithTop ℤ) :=
  ⟨ord v.intValuation x, v.intAddVal_of_map_ne_zero hx⟩

/-- `v.intAddVal` vanishes exactly on the elements of valuation `1`. -/
@[simp]
theorem intAddVal_eq_zero_iff {x : R} : v.intAddVal x = 0 ↔ v x = 1 := by
  simpa using v.intAddVal_eq_coe_iff (x := x) (m := 0)

/-- `v.intAddVal x` is nonnegative exactly when `v x ≤ 1`. -/
@[simp]
theorem nonneg_intAddVal_iff {x : R} : 0 ≤ v.intAddVal x ↔ v x ≤ 1 := by
  rcases eq_or_ne (v x) 0 with hx | hx
  · simp [v.intAddVal_eq_top_iff.mpr hx, hx]
  · rw [v.intAddVal_of_map_ne_zero hx, ← WithTop.coe_zero, WithTop.coe_le_coe, ord_def, neg_nonneg,
      WithZero.log_le_iff_le_exp (v.intValuation_eq_zero_iff.not.mpr hx), WithZero.exp_zero,
      intValuation_le_one_iff]

/-- `v.intAddVal x` is positive exactly when `v x < 1`. -/
@[simp]
theorem pos_intAddVal_iff {x : R} : 0 < v.intAddVal x ↔ v x < 1 := by
  rcases eq_or_ne (v x) 0 with hx | hx
  · simp [v.intAddVal_eq_top_iff.mpr hx, hx]
  · rw [v.intAddVal_of_map_ne_zero hx, ← WithTop.coe_zero, WithTop.coe_lt_coe, ord_def, neg_pos,
      ← WithZero.exp_lt_exp, WithZero.exp_log (v.intValuation_eq_zero_iff.not.mpr hx),
      WithZero.exp_zero, intValuation_lt_one_iff]

/-- `v.realAddVal` takes the value `⊤` exactly on the valuation support of `v`. -/
@[simp]
theorem realAddVal_eq_top_iff {x : R} : v.realAddVal x = ⊤ ↔ v x = 0 := by
  rw [realAddVal_eq_map, WithTop.map_eq_top_iff, intAddVal_eq_top_iff]

/-- **Characteristic equation of `v.realAddVal`** on integer values. -/
theorem realAddVal_eq_intCast_iff {x : R} {m : ℤ} :
    v.realAddVal x = ((m : ℝ) : WithTop ℝ) ↔ v x = (hv.generator : Γ) ^ m := by
  rw [realAddVal_eq_map, ← v.intAddVal_eq_coe_iff]
  cases h : v.intAddVal x with
  | top => simp
  | coe k => simp

/-- Outside the valuation support, `v.realAddVal x` is `(ord v.intValuation x : ℝ)`. -/
theorem realAddVal_of_map_ne_zero {x : R} (hx : v x ≠ 0) :
    v.realAddVal x = ((ord v.intValuation x : ℝ) : WithTop ℝ) := by
  rw [realAddVal_eq_map, v.intAddVal_of_map_ne_zero hx, WithTop.map_coe]

/-- Outside the valuation support, `v.realAddVal` takes an integer value. -/
theorem exists_int_realAddVal {x : R} (hx : v x ≠ 0) :
    ∃ m : ℤ, v.realAddVal x = ((m : ℝ) : WithTop ℝ) :=
  ⟨ord v.intValuation x, v.realAddVal_of_map_ne_zero hx⟩

/-- `v.realAddVal` vanishes exactly on the elements of valuation `1`. -/
@[simp]
theorem realAddVal_eq_zero_iff {x : R} : v.realAddVal x = 0 ↔ v x = 1 := by
  simpa using v.realAddVal_eq_intCast_iff (x := x) (m := 0)

/-- `v.realAddVal x` is nonnegative exactly when `v x ≤ 1`. -/
@[simp]
theorem nonneg_realAddVal_iff {x : R} : 0 ≤ v.realAddVal x ↔ v x ≤ 1 := by
  rcases eq_or_ne (v x) 0 with hx | hx
  · simp [v.realAddVal_eq_top_iff.mpr hx, hx]
  · rw [v.realAddVal_of_map_ne_zero hx, ← WithTop.coe_zero, WithTop.coe_le_coe,
      Int.cast_nonneg_iff, ← WithTop.coe_le_coe (α := ℤ), WithTop.coe_zero,
      ← v.intAddVal_of_map_ne_zero hx, nonneg_intAddVal_iff]

/-- `v.realAddVal x` is positive exactly when `v x < 1`. -/
@[simp]
theorem pos_realAddVal_iff {x : R} : 0 < v.realAddVal x ↔ v x < 1 := by
  rcases eq_or_ne (v x) 0 with hx | hx
  · simp [v.realAddVal_eq_top_iff.mpr hx, hx]
  · rw [v.realAddVal_of_map_ne_zero hx, ← WithTop.coe_zero, WithTop.coe_lt_coe, Int.cast_pos,
      ← WithTop.coe_lt_coe (α := ℤ), WithTop.coe_zero, ← v.intAddVal_of_map_ne_zero hx,
      pos_intAddVal_iff]

section Uniformizer

variable {v} {π : R}

/-- A uniformizer of `v` has normalized `ℤᵐ⁰`-valuation `WithZero.exp (-1)`. -/
theorem IsUniformizer.intValuation_eq (hπ : v.IsUniformizer π) :
    v.intValuation π = WithZero.exp (-1) := by
  rw [v.intValuation_eq_exp_neg_iff, zpow_one, hπ.val]

/-- Uniformizers of `v` are precisely the elements of normalized `ℤᵐ⁰`-valuation
`WithZero.exp (-1)`. -/
theorem isUniformizer_iff_intValuation_eq :
    v.IsUniformizer π ↔ v.intValuation π = WithZero.exp (-1) := by
  rw [IsUniformizer.iff, v.intValuation_eq_exp_neg_iff, zpow_one]

/-- A uniformizer of `v` has order `1` for `v.intValuation`. -/
@[simp]
theorem IsUniformizer.ord_intValuation (hπ : v.IsUniformizer π) :
    ord v.intValuation π = 1 := by
  rw [ord_def, hπ.intValuation_eq, WithZero.log_exp, neg_neg]

/-- A uniformizer of `v` has normalized integer additive valuation `1`. -/
@[simp]
theorem IsUniformizer.intAddVal_eq_one (hπ : v.IsUniformizer π) :
    v.intAddVal π = 1 := by
  simpa using (v.intAddVal_eq_coe_iff (x := π) (m := 1)).mpr (by simpa using hπ.val)

/-- Uniformizers of `v` are precisely the elements of normalized integer additive valuation `1`. -/
theorem isUniformizer_iff_intAddVal_eq_one :
    v.IsUniformizer π ↔ v.intAddVal π = 1 :=
  ⟨fun h ↦ h.intAddVal_eq_one,
    fun h ↦ IsUniformizer.iff.mpr (by simpa using (v.intAddVal_eq_coe_iff (x := π) (m := 1)).mp h)⟩

/-- Measured against a uniformizer `π`, `v.intAddVal x = m` means `v x = v π ^ m`. -/
theorem IsUniformizer.intAddVal_eq_coe_iff (hπ : v.IsUniformizer π) {x : R} {m : ℤ} :
    v.intAddVal x = (m : WithTop ℤ) ↔ v x = v π ^ m := by
  rw [v.intAddVal_eq_coe_iff, hπ.val]

/-- A uniformizer of `v` has normalized real additive valuation `1`. -/
@[simp]
theorem IsUniformizer.realAddVal_eq_one (hπ : v.IsUniformizer π) :
    v.realAddVal π = 1 := by
  simp [realAddVal_eq_map, hπ.intAddVal_eq_one]

/-- Uniformizers of `v` are precisely the elements of normalized real additive valuation `1`. -/
theorem isUniformizer_iff_realAddVal_eq_one :
    v.IsUniformizer π ↔ v.realAddVal π = 1 :=
  ⟨fun h ↦ h.realAddVal_eq_one, fun h ↦ IsUniformizer.iff.mpr
    (by simpa using (v.realAddVal_eq_intCast_iff (x := π) (m := 1)).mp (by simpa using h))⟩

end Uniformizer

section SurjectiveWithZeroMulInt

/-- A surjective `ℤᵐ⁰`-valued discrete valuation equals its own `intValuation`. -/
@[simp]
theorem intValuation_eq_self_of_surjective {u : Valuation R ℤᵐ⁰} [u.IsRankOneDiscrete]
    (hu : Function.Surjective u) : u.intValuation = u :=
  Valuation.ext fun x ↦
    IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hu x

/-- The normalized integer additive valuation of a surjective `ℤᵐ⁰`-valued valuation `u` is
`u.addVal`. -/
@[simp]
theorem intAddVal_eq_addVal_of_surjective {u : Valuation R ℤᵐ⁰} [u.IsRankOneDiscrete]
    (hu : Function.Surjective u) : u.intAddVal = u.addVal := by
  rw [intAddVal_def, intValuation_eq_self_of_surjective hu]

end SurjectiveWithZeroMulInt

end Ring

section DivisionRing

variable {F Γ₁ Γ₂ : Type*} [DivisionRing F]
  [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
  (v : Valuation F Γ₁) [v.IsRankOneDiscrete]

/-- On a division ring, `v.intValuation` is surjective onto `ℤᵐ⁰`. -/
theorem intValuation_surjective : Function.Surjective v.intValuation :=
  (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v).surjective.comp
    (ValueGroup₀.restrict₀_surjective (f := (v : F →*₀ Γ₁)))

/-- On a division ring, `v.intValuation` is rank-one discrete. -/
instance isRankOneDiscrete_intValuation : v.intValuation.IsRankOneDiscrete :=
  .of_isEquiv v.isEquiv_intValuation.symm

/-- On a division ring, `v.intAddVal` is surjective onto `WithTop ℤ`. -/
theorem intAddVal_surjective : Function.Surjective v.intAddVal := by
  rintro (_ | m)
  · exact ⟨0, v.intAddVal.map_zero⟩
  · obtain ⟨x, hx⟩ := v.intValuation_surjective (WithZero.exp (-m))
    exact ⟨x, v.intValuation.addVal_eq_coe.mpr hx⟩

/-- On a division ring, `v.intAddVal x` equals `ord v.intValuation x` for every nonzero `x`. -/
theorem intAddVal_of_ne_zero {x : F} (hx : x ≠ 0) :
    v.intAddVal x = (ord v.intValuation x : WithTop ℤ) :=
  v.intAddVal_of_map_ne_zero (v.ne_zero_iff.mpr hx)

/-- On a division ring, `v.realAddVal x` equals `(ord v.intValuation x : ℝ)` for every nonzero
`x`. -/
theorem realAddVal_of_ne_zero {x : F} (hx : x ≠ 0) :
    v.realAddVal x = ((ord v.intValuation x : ℝ) : WithTop ℝ) :=
  v.realAddVal_of_map_ne_zero (v.ne_zero_iff.mpr hx)

/-- On a division ring, `v.realAddVal` takes integer values on all nonzero elements. -/
theorem exists_int_realAddVal_of_ne_zero {x : F} (hx : x ≠ 0) :
    ∃ m : ℤ, v.realAddVal x = ((m : ℝ) : WithTop ℝ) :=
  v.exists_int_realAddVal (v.ne_zero_iff.mpr hx)

/-- **Equivalent rank-one discrete valuations on a division ring have equal `intValuation`.** -/
theorem IsEquiv.intValuation_eq {v₁ : Valuation F Γ₁} {v₂ : Valuation F Γ₂}
    [v₁.IsRankOneDiscrete] [v₂.IsRankOneDiscrete] (h : v₁.IsEquiv v₂) :
    v₁.intValuation = v₂.intValuation :=
  eq_of_isEquiv_of_surjective v₁.intValuation_surjective v₂.intValuation_surjective
    (v₁.isEquiv_intValuation.trans (h.trans v₂.isEquiv_intValuation.symm))

/-- **Equivalent rank-one discrete valuations on a division ring have equal `intAddVal`.** -/
theorem IsEquiv.intAddVal_eq {v₁ : Valuation F Γ₁} {v₂ : Valuation F Γ₂}
    [v₁.IsRankOneDiscrete] [v₂.IsRankOneDiscrete] (h : v₁.IsEquiv v₂) :
    v₁.intAddVal = v₂.intAddVal := by
  rw [intAddVal_def, intAddVal_def, h.intValuation_eq]

/-- **Equivalent rank-one discrete valuations on a division ring have equal `realAddVal`.** -/
theorem IsEquiv.realAddVal_eq {v₁ : Valuation F Γ₁} {v₂ : Valuation F Γ₂}
    [v₁.IsRankOneDiscrete] [v₂.IsRankOneDiscrete] (h : v₁.IsEquiv v₂) :
    v₁.realAddVal = v₂.realAddVal := by
  rw [realAddVal, realAddVal, h.intAddVal_eq]

end DivisionRing

section Field

variable {K R Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) [hv : v.IsRankOneDiscrete]

/-- `v.intValuation` has the same valuation subring as `v`. -/
@[simp]
theorem valuationSubring_intValuation : v.intValuation.valuationSubring = v.valuationSubring :=
  (isEquiv_iff_valuationSubring _ _).mp v.isEquiv_intValuation

/-- If `R` is a discrete valuation ring of integers for `v`, every irreducible element of `R` maps
to a uniformizer of `v` in `K`. -/
theorem Integers.isUniformizer_algebraMap_of_irreducible [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R K] {v : Valuation K Γ} [hv : v.IsRankOneDiscrete]
    (hvR : v.Integers R) {ϖ : R} (hϖ : Irreducible ϖ) :
    v.IsUniformizer (algebraMap R K ϖ) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨t, ht⟩ := hvR.exists_of_le_one π.2
  have ht_nonunit : ¬ IsUnit t := fun hu ↦
    hπ.val_lt_one.ne (ht ▸ hvR.one_of_isUnit hu)
  have hϖ_dvd_t : ϖ ∣ t := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact (IsLocalRing.mem_maximalIdeal t).mpr ht_nonunit
  have hle₁ : (hv.generator : Γ) ≤ v (algebraMap R K ϖ) := by
    rw [← hπ.val, ← ht]
    exact hvR.dvd_iff_le.mp hϖ_dvd_t
  have hϖ_ne : v (algebraMap R K ϖ) ≠ 0 :=
    v.ne_zero_iff.mpr ((map_ne_zero_iff _ hvR.hom_inj).mpr hϖ.ne_zero)
  have hϖ_lt_one : v (algebraMap R K ϖ) < 1 :=
    lt_of_le_of_ne (hvR.map_le_one ϖ) fun h1 ↦ hϖ.not_isUnit (hvR.isUnit_of_one
      (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hvR.hom_inj).mpr hϖ.ne_zero)) h1)
  have hmem : Units.mk0 (v (algebraMap R K ϖ)) hϖ_ne ∈ Subgroup.zpowers hv.generator := by
    rw [hv.generator_zpowers_eq_valueGroup]
    exact mem_valueGroup _ ⟨algebraMap R K ϖ, rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hm_eq : v (algebraMap R K ϖ) = (hv.generator : Γ) ^ m := by
    simpa using congrArg Units.val hm.symm
  have hm_pos : 1 ≤ m := by
    have hlt : (hv.generator : Γ) ^ m < 1 := hm_eq ▸ hϖ_lt_one
    have h0 : 0 < m :=
      (zpow_lt_one_iff_right_of_lt_one₀ (Units.zero_lt hv.generator) hv.generator_lt_one).mp hlt
    omega
  have hle₂ : v (algebraMap R K ϖ) ≤ (hv.generator : Γ) := by
    rw [hm_eq]
    simpa using zpow_le_zpow_right_of_le_one₀ (Units.zero_lt hv.generator)
      hv.generator_lt_one.le hm_pos
  exact IsUniformizer.iff.mpr (le_antisymm hle₂ hle₁)

/-- **Compatibility with `IsDiscreteValuationRing.addVal`.** For any discrete valuation ring `R` of
integers for `v` on `K`, `v.intAddVal` on `algebraMap R K r` agrees with
`IsDiscreteValuationRing.addVal R r` cast from `ℕ` to `ℤ`. -/
theorem Integers.intAddVal_algebraMap_eq_map_addVal [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R K] {v : Valuation K Γ} [v.IsRankOneDiscrete]
    (hvR : v.Integers R) (r : R) :
    v.intAddVal (algebraMap R K r) = (IsDiscreteValuationRing.addVal R r).map ((↑) : ℕ → ℤ) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨n, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    have hϖu : v.IsUniformizer (algebraMap R K ϖ) :=
      hvR.isUniformizer_algebraMap_of_irreducible hϖ
    have hu0 : v.intAddVal (algebraMap R K (u : R)) = 0 :=
      v.intAddVal_eq_zero_iff.mpr (hvR.one_of_isUnit u.isUnit)
    rw [hru, map_mul, map_pow, AddValuation.map_mul, AddValuation.map_pow, hu0, zero_add,
      hϖu.intAddVal_eq_one, IsDiscreteValuationRing.addVal_def' u hϖ n]
    simp

/-- On `v.valuationSubring`, `v.intAddVal` agrees with `IsDiscreteValuationRing.addVal` cast from
`ℕ` to `ℤ`. -/
@[simp]
theorem intAddVal_coe_valuationSubring (x : v.valuationSubring) :
    v.intAddVal (x : K) =
      (IsDiscreteValuationRing.addVal v.valuationSubring x).map ((↑) : ℕ → ℤ) :=
  (Valuation.valuationSubring.integers v).intAddVal_algebraMap_eq_map_addVal x

/-- On `v.valuationSubring`, `v.realAddVal` agrees with `IsDiscreteValuationRing.addVal` cast from
`ℕ` to `ℝ`. -/
theorem realAddVal_coe_valuationSubring (x : v.valuationSubring) :
    v.realAddVal (x : K) =
      (IsDiscreteValuationRing.addVal v.valuationSubring x).map ((↑) : ℕ → ℝ) := by
  rw [realAddVal_eq_map, intAddVal_coe_valuationSubring]
  cases IsDiscreteValuationRing.addVal v.valuationSubring x <;> simp

end Field

end Valuation
