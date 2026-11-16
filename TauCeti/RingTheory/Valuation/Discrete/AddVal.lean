/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import TauCeti.RingTheory.Valuation.Discrete.Order
public import TauCeti.RingTheory.Valuation.ToAdditive

/-!
# Normalized `ℤᵐ⁰`-valued, `ℤ`-valued, and `ℝ`-valued valuations of a discrete valuation

For a rank-one discrete valuation `v : Valuation R Γ` with value-group generator
`γ = IsRankOneDiscrete.generator v < 1`, transporting `v.restrict` along
`IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v` gives a `ℤᵐ⁰`-valued valuation
`v.intValuation` equivalent to `v` sending `γ ^ m` to `WithZero.exp (-m)`. Passing to additive
notation yields `v.intAddVal : AddValuation R (WithTop ℤ)` (value `1` on uniformizers) and
`v.realAddVal : AddValuation R (WithTop ℝ)`.

## Main definitions

* `Valuation.intValuation`: the normalized `ℤᵐ⁰`-valued valuation attached to `v`.
* `Valuation.intAddVal`: the normalized additive valuation `AddValuation R (WithTop ℤ)`.
* `Valuation.realAddVal`: the normalized real additive valuation `AddValuation R (WithTop ℝ)`.

## Main results

* `Valuation.isRankOneDiscrete_intValuation`, `Valuation.compatible_intValuation`, and
  `Valuation.IsEquiv.{intValuation_eq, intAddVal_eq, realAddVal_eq}`: discreteness, `ValuativeRel`
  compatibility, and equivalence invariance on any ring.
* `Valuation.intValuation_eq_exp_neg_iff`, `Valuation.intAddVal_eq_coe_iff`,
  `Valuation.realAddVal_eq_intCast_iff`, and `Valuation.isUniformizer_iff_{int,real}AddVal_eq_one`:
  characterizations by generator powers and uniformizers.
* `Valuation.intValuation_surjective` and `Valuation.intAddVal_surjective`: surjectivity on
  division rings.
* `Valuation.Integers.intAddVal_algebraMap_eq_map_addVal` and
  `Valuation.intAddVal_coe_valuationSubring`: compatibility with `IsDiscreteValuationRing.addVal`.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter I, §1.
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

/-- The normalized integer additive valuation attached to `v`, with value `1` on uniformizers. -/
noncomputable def intAddVal : AddValuation R (WithTop ℤ) := v.intValuation.addVal

/-- The normalized real additive valuation attached to `v`, obtained by casting `v.intAddVal`. -/
noncomputable def realAddVal : AddValuation R (WithTop ℝ) :=
  v.intAddVal.map
    { (Int.castAddHom ℝ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr fun _ _ h ↦ Int.cast_le.mpr h }
    rfl

/-- The defining formula of `Valuation.intValuation`. -/
theorem intValuation_def :
    v.intValuation = v.restrict.map (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v) := (rfl)

/-- Pointwise evaluation of `Valuation.intValuation`. -/
theorem intValuation_apply (x : R) :
    v.intValuation x = IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v (v.restrict x) := (rfl)

/-- The defining formula of `Valuation.intAddVal`. -/
theorem intAddVal_def : v.intAddVal = v.intValuation.addVal := (rfl)

/-- Pointwise evaluation of `Valuation.intAddVal` as the negative logarithm of `v.intValuation`. -/
theorem intAddVal_apply (x : R) : v.intAddVal x = WithZero.negLog (v.intValuation x) :=
  v.intValuation.addVal_apply x

/-- `v.realAddVal` agrees pointwise with `v.intAddVal` cast from `ℤ` to `ℝ`. -/
theorem realAddVal_eq_map (x : R) : v.realAddVal x = (v.intAddVal x).map ((↑) : ℤ → ℝ) := (rfl)

/-- The normalized `ℤᵐ⁰`-valued valuation is equivalent to `v`. -/
theorem isEquiv_intValuation : v.intValuation.IsEquiv v :=
  (isEquiv_map_self_of_strictMono _
    (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_strictMono v).injective).trans
    v.isEquiv_restrict.symm

/-- `v.intValuation` is rank-one discrete. -/
instance isRankOneDiscrete_intValuation : v.intValuation.IsRankOneDiscrete :=
  .of_isEquiv v.isEquiv_intValuation.symm

/-- Compatibility with `ValuativeRel R` passes from `v` to `v.intValuation`. -/
instance compatible_intValuation [ValuativeRel R] [v.Compatible] : v.intValuation.Compatible :=
  v.isEquiv_intValuation.symm.compatible

/-- `v.intValuation` vanishes on the same elements as `v`. -/
@[simp]
theorem intValuation_eq_zero_iff {x : R} : v.intValuation x = 0 ↔ v x = 0 :=
  v.isEquiv_intValuation.eq_zero

/-- `v.intValuation` induces the same preorder as `v`. -/
theorem intValuation_le_intValuation_iff {x y : R} :
    v.intValuation x ≤ v.intValuation y ↔ v x ≤ v y := v.isEquiv_intValuation x y

/-- `v.intValuation` induces the same strict order as `v`. -/
theorem intValuation_lt_intValuation_iff {x y : R} :
    v.intValuation x < v.intValuation y ↔ v x < v y := v.isEquiv_intValuation.lt_iff_lt

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
    v.intAddVal x = (ord v.intValuation x : WithTop ℤ) :=
  v.intAddVal_eq_coe_iff.mpr ((v.ord_intValuation_eq_iff hx).mp rfl)

/-- Outside the valuation support, `v.intAddVal` takes an integer value. -/
theorem exists_int_intAddVal {x : R} (hx : v x ≠ 0) :
    ∃ m : ℤ, v.intAddVal x = (m : WithTop ℤ) :=
  ⟨ord v.intValuation x, v.intAddVal_of_map_ne_zero hx⟩

/-- `v.intAddVal` reverses the preorder of `v`. -/
theorem intAddVal_le_intAddVal_iff {x y : R} : v.intAddVal x ≤ v.intAddVal y ↔ v y ≤ v x := by
  rw [intAddVal_apply, intAddVal_apply, WithZero.negLog_le_negLog, intValuation_le_intValuation_iff]

/-- `v.intAddVal` reverses the strict order of `v`. -/
theorem intAddVal_lt_intAddVal_iff {x y : R} : v.intAddVal x < v.intAddVal y ↔ v y < v x := by
  rw [← not_le, intAddVal_le_intAddVal_iff, not_le]

/-- `v.intAddVal` vanishes exactly on the elements of valuation `1`. -/
@[simp]
theorem intAddVal_eq_zero_iff {x : R} : v.intAddVal x = 0 ↔ v x = 1 := by
  simpa using v.intAddVal_eq_coe_iff (x := x) (m := 0)

/-- `v.intAddVal x` is nonnegative exactly when `v x ≤ 1`. -/
@[simp]
theorem intAddVal_nonneg_iff {x : R} : 0 ≤ v.intAddVal x ↔ v x ≤ 1 := by
  rw [← AddValuation.map_one v.intAddVal, intAddVal_le_intAddVal_iff, v.map_one]

/-- `v.intAddVal x` is positive exactly when `v x < 1`. -/
@[simp]
theorem intAddVal_pos_iff {x : R} : 0 < v.intAddVal x ↔ v x < 1 := by
  rw [← AddValuation.map_one v.intAddVal, intAddVal_lt_intAddVal_iff, v.map_one]

/-- `v.realAddVal` takes the value `⊤` exactly on the valuation support of `v`. -/
@[simp]
theorem realAddVal_eq_top_iff {x : R} : v.realAddVal x = ⊤ ↔ v x = 0 := by
  rw [realAddVal_eq_map, WithTop.map_eq_top_iff, intAddVal_eq_top_iff]

/-- **Characteristic equation of `v.realAddVal`** on integer values. -/
theorem realAddVal_eq_intCast_iff {x : R} {m : ℤ} :
    v.realAddVal x = ((m : ℝ) : WithTop ℝ) ↔ v x = (hv.generator : Γ) ^ m := by
  rw [realAddVal_eq_map, ← v.intAddVal_eq_coe_iff]
  cases v.intAddVal x <;> simp

/-- Outside the valuation support, `v.realAddVal x` is `(ord v.intValuation x : ℝ)`. -/
theorem realAddVal_of_map_ne_zero {x : R} (hx : v x ≠ 0) :
    v.realAddVal x = ((ord v.intValuation x : ℝ) : WithTop ℝ) := by
  rw [realAddVal_eq_map, v.intAddVal_of_map_ne_zero hx, WithTop.map_coe]

/-- Outside the valuation support, `v.realAddVal` takes an integer value. -/
theorem exists_int_realAddVal {x : R} (hx : v x ≠ 0) :
    ∃ m : ℤ, v.realAddVal x = ((m : ℝ) : WithTop ℝ) :=
  ⟨ord v.intValuation x, v.realAddVal_of_map_ne_zero hx⟩

/-- `v.realAddVal` reverses the preorder of `v`. -/
theorem realAddVal_le_realAddVal_iff {x y : R} : v.realAddVal x ≤ v.realAddVal y ↔ v y ≤ v x := by
  rw [realAddVal_eq_map, realAddVal_eq_map,
    (Int.cast_strictMono (R := ℝ)).withTop_map.le_iff_le, intAddVal_le_intAddVal_iff]

/-- `v.realAddVal` reverses the strict order of `v`. -/
theorem realAddVal_lt_realAddVal_iff {x y : R} : v.realAddVal x < v.realAddVal y ↔ v y < v x := by
  rw [← not_le, realAddVal_le_realAddVal_iff, not_le]

/-- `v.realAddVal` vanishes exactly on the elements of valuation `1`. -/
@[simp]
theorem realAddVal_eq_zero_iff {x : R} : v.realAddVal x = 0 ↔ v x = 1 := by
  simpa using v.realAddVal_eq_intCast_iff (x := x) (m := 0)

/-- `v.realAddVal x` is nonnegative exactly when `v x ≤ 1`. -/
@[simp]
theorem realAddVal_nonneg_iff {x : R} : 0 ≤ v.realAddVal x ↔ v x ≤ 1 := by
  rw [← AddValuation.map_one v.realAddVal, realAddVal_le_realAddVal_iff, v.map_one]

/-- `v.realAddVal x` is positive exactly when `v x < 1`. -/
@[simp]
theorem realAddVal_pos_iff {x : R} : 0 < v.realAddVal x ↔ v x < 1 := by
  rw [← AddValuation.map_one v.realAddVal, realAddVal_lt_realAddVal_iff, v.map_one]

section Uniformizer

variable {v} {π : R}

/-- Uniformizers of `v` are precisely the elements of normalized `ℤᵐ⁰`-valuation
`WithZero.exp (-1)`. -/
theorem isUniformizer_iff_intValuation_eq_exp_neg_one :
    v.IsUniformizer π ↔ v.intValuation π = WithZero.exp (-1) := by
  rw [IsUniformizer.iff, v.intValuation_eq_exp_neg_iff, zpow_one]

/-- A uniformizer of `v` has normalized `ℤᵐ⁰`-valuation `WithZero.exp (-1)`. -/
theorem IsUniformizer.intValuation_eq_exp_neg_one (hπ : v.IsUniformizer π) :
    v.intValuation π = WithZero.exp (-1) :=
  isUniformizer_iff_intValuation_eq_exp_neg_one.mp hπ

/-- A uniformizer of `v` has order `1` for `v.intValuation`. -/
@[simp]
theorem IsUniformizer.ord_intValuation (hπ : v.IsUniformizer π) : ord v.intValuation π = 1 := by
  rw [ord_def, hπ.intValuation_eq_exp_neg_one, WithZero.log_exp, neg_neg]

/-- Uniformizers of `v` are precisely the elements of normalized integer additive valuation `1`. -/
theorem isUniformizer_iff_intAddVal_eq_one : v.IsUniformizer π ↔ v.intAddVal π = 1 := by
  simpa [IsUniformizer.iff] using (v.intAddVal_eq_coe_iff (x := π) (m := 1)).symm

/-- A uniformizer of `v` has normalized integer additive valuation `1`. -/
@[simp]
theorem IsUniformizer.intAddVal_eq_one (hπ : v.IsUniformizer π) : v.intAddVal π = 1 :=
  isUniformizer_iff_intAddVal_eq_one.mp hπ

/-- Measured against a uniformizer `π`, `v.intAddVal x = m` means `v x = v π ^ m`. -/
theorem IsUniformizer.intAddVal_eq_coe_iff (hπ : v.IsUniformizer π) {x : R} {m : ℤ} :
    v.intAddVal x = (m : WithTop ℤ) ↔ v x = v π ^ m := by
  rw [v.intAddVal_eq_coe_iff, hπ.val]

/-- Uniformizers of `v` are precisely the elements of normalized real additive valuation `1`. -/
theorem isUniformizer_iff_realAddVal_eq_one : v.IsUniformizer π ↔ v.realAddVal π = 1 := by
  simpa [IsUniformizer.iff] using (v.realAddVal_eq_intCast_iff (x := π) (m := 1)).symm

/-- A uniformizer of `v` has normalized real additive valuation `1`. -/
@[simp]
theorem IsUniformizer.realAddVal_eq_one (hπ : v.IsUniformizer π) : v.realAddVal π = 1 :=
  isUniformizer_iff_realAddVal_eq_one.mp hπ

end Uniformizer

section IsEquiv

variable {Γ₁ Γ₂ : Type*}
  [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]

/-- **Equivalent rank-one discrete valuations on a ring have equal `intValuation`.** -/
theorem IsEquiv.intValuation_eq {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
    [hv₁ : v₁.IsRankOneDiscrete] [hv₂ : v₂.IsRankOneDiscrete] (h : v₁.IsEquiv v₂) :
    v₁.intValuation = v₂.intValuation := by
  have hgen : h.orderMonoidIso hv₁.generator' = hv₂.generator' := by
    rw [LinearOrderedCommGroup.genLTOne_unique _ hv₁.generator'_lt_one
      hv₁.generator'_zpowers_eq_top, LinearOrderedCommGroup.genLTOne_unique _
      hv₂.generator'_lt_one hv₂.generator'_zpowers_eq_top]
    exact h.orderMonoidIso.map_genLTOne'
  ext x
  rcases eq_or_ne (v₁ x) 0 with hx | hx
  · rw [v₁.intValuation_eq_zero_iff.mpr hx, v₂.intValuation_eq_zero_iff.mpr (h.eq_zero.mp hx)]
  · obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp (v₁.restrict_eq_zero_iff.not.mpr hx)
    obtain ⟨m, rfl⟩ : g ∈ Subgroup.zpowers hv₁.generator' := hv₁.generator'_zpowers_eq_top ▸ trivial
    have h1 : v₁.restrict x = (hv₁.generator' : v₁.ValueGroup₀) ^ m := by
      rw [← hg, WithZero.coe_zpow]
    have h2 : v₂.restrict x = (hv₂.generator' : v₂.ValueGroup₀) ^ m := by
      rw [← h.orderMonoidIso₀_spec x, h1, map_zpow₀, h.orderMonoidIso₀_coe, hgen]
    rw [intValuation_apply, intValuation_apply, h1, h2,
      IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply_zpow,
      IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply_zpow]

/-- **Equivalent rank-one discrete valuations on a ring have equal `intAddVal`.** -/
theorem IsEquiv.intAddVal_eq {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
    [v₁.IsRankOneDiscrete] [v₂.IsRankOneDiscrete] (h : v₁.IsEquiv v₂) :
    v₁.intAddVal = v₂.intAddVal := by
  rw [intAddVal_def, intAddVal_def, h.intValuation_eq]

/-- **Equivalent rank-one discrete valuations on a ring have equal `realAddVal`.** -/
theorem IsEquiv.realAddVal_eq {v₁ : Valuation R Γ₁} {v₂ : Valuation R Γ₂}
    [v₁.IsRankOneDiscrete] [v₂.IsRankOneDiscrete] (h : v₁.IsEquiv v₂) :
    v₁.realAddVal = v₂.realAddVal := by
  rw [realAddVal, realAddVal, h.intAddVal_eq]

end IsEquiv

section SurjectiveWithZeroMulInt

/-- A surjective `ℤᵐ⁰`-valued discrete valuation equals its own `intValuation`. -/
@[simp]
theorem intValuation_eq_self_of_surjective {u : Valuation R ℤᵐ⁰} [u.IsRankOneDiscrete]
    (hu : Function.Surjective u) : u.intValuation = u :=
  Valuation.ext fun x ↦
    IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hu x

/-- The normalized integer additive valuation of a surjective `ℤᵐ⁰`-valued valuation is `u.addVal`.
-/
@[simp]
theorem intAddVal_eq_addVal_of_surjective {u : Valuation R ℤᵐ⁰} [u.IsRankOneDiscrete]
    (hu : Function.Surjective u) : u.intAddVal = u.addVal := by
  rw [intAddVal_def, intValuation_eq_self_of_surjective hu]

end SurjectiveWithZeroMulInt

end Ring

section DivisionRing

variable {F Γ : Type*} [DivisionRing F] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation F Γ) [v.IsRankOneDiscrete]

/-- On a division ring, `v.intValuation` is surjective onto `ℤᵐ⁰`. -/
theorem intValuation_surjective : Function.Surjective v.intValuation :=
  (IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v).surjective.comp
    (ValueGroup₀.restrict₀_surjective (f := (v : F →*₀ Γ)))

/-- On a division ring, `v.intAddVal` is surjective onto `WithTop ℤ`. -/
theorem intAddVal_surjective : Function.Surjective v.intAddVal := by
  rintro (_ | m)
  · exact ⟨0, v.intAddVal.map_zero⟩
  · exact (v.intValuation_surjective _).imp fun _ hx ↦ v.intValuation.addVal_eq_coe.mpr hx

/-- On a division ring, `v.intAddVal x` equals `ord v.intValuation x` for every nonzero `x`. -/
theorem intAddVal_of_ne_zero {x : F} (hx : x ≠ 0) :
    v.intAddVal x = (ord v.intValuation x : WithTop ℤ) :=
  v.intAddVal_of_map_ne_zero (v.ne_zero_iff.mpr hx)

/-- On a division ring, `v.realAddVal x` equals `(ord v.intValuation x : ℝ)` for `x ≠ 0`. -/
theorem realAddVal_of_ne_zero {x : F} (hx : x ≠ 0) :
    v.realAddVal x = ((ord v.intValuation x : ℝ) : WithTop ℝ) :=
  v.realAddVal_of_map_ne_zero (v.ne_zero_iff.mpr hx)

/-- On a division ring, `v.realAddVal` takes integer values on all nonzero elements. -/
theorem exists_int_realAddVal_of_ne_zero {x : F} (hx : x ≠ 0) :
    ∃ m : ℤ, v.realAddVal x = ((m : ℝ) : WithTop ℝ) :=
  v.exists_int_realAddVal (v.ne_zero_iff.mpr hx)

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
    [IsDiscreteValuationRing R] [Algebra R K] {v : Valuation K Γ} [v.IsRankOneDiscrete]
    (hvR : v.Integers R) {ϖ : R} (hϖ : Irreducible ϖ) :
    v.IsUniformizer (algebraMap R K ϖ) := by
  refine isUniformizer_of_maximalIdeal_eq_span v (r := ⟨algebraMap R K ϖ, hvR.map_le_one ϖ⟩) ?_
  ext x
  obtain ⟨r, hr⟩ := hvR.exists_of_le_one x.2
  rw [Valuation.mem_maximalIdeal_iff, Ideal.mem_span_singleton,
    (Valuation.valuationSubring.integers v).dvd_iff_le,
    ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply, ← hr]
  refine ⟨fun hlt ↦ hvR.dvd_iff_le.mp ?_,
    fun hle ↦ hle.trans_lt (hvR.valuation_irreducible_lt_one hϖ)⟩
  rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal]
  exact fun hu ↦ hlt.ne (hvR.one_of_isUnit hu)

/-- **Compatibility with `IsDiscreteValuationRing.addVal`.** For any discrete valuation ring `R` of
integers for `v` on `K`, `v.intAddVal` on `algebraMap R K r` agrees with
`IsDiscreteValuationRing.addVal R r` cast from `ℕ` to `ℤ`. -/
theorem Integers.intAddVal_algebraMap_eq_map_addVal [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R K] {v : Valuation K Γ} [v.IsRankOneDiscrete]
    (hvR : v.Integers R) (r : R) :
    v.intAddVal (algebraMap R K r) = (IsDiscreteValuationRing.addVal R r).map ((↑) : ℕ → ℤ) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  simp [IsDiscreteValuationRing.addVal_def' u hϖ n,
    (hvR.isUniformizer_algebraMap_of_irreducible hϖ).intAddVal_eq_one, hvR.one_of_isUnit u.isUnit]

/-- On `v.valuationSubring`, `v.intAddVal` is `IsDiscreteValuationRing.addVal` cast to `ℤ`. -/
theorem intAddVal_coe_valuationSubring (x : v.valuationSubring) :
    v.intAddVal (x : K) =
      (IsDiscreteValuationRing.addVal v.valuationSubring x).map ((↑) : ℕ → ℤ) :=
  (Valuation.valuationSubring.integers v).intAddVal_algebraMap_eq_map_addVal x

/-- On `v.valuationSubring`, `v.realAddVal` is `IsDiscreteValuationRing.addVal` cast to `ℝ`. -/
theorem realAddVal_coe_valuationSubring (x : v.valuationSubring) :
    v.realAddVal (x : K) =
      (IsDiscreteValuationRing.addVal v.valuationSubring x).map ((↑) : ℕ → ℝ) := by
  rw [realAddVal_eq_map, intAddVal_coe_valuationSubring]
  cases IsDiscreteValuationRing.addVal v.valuationSubring x <;> simp

end Field

end Valuation
