/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import TauCeti.Data.Int.WithZero
public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# The normalized valuation of a nonarchimedean local field

Mathlib equips a nonarchimedean local field `K` with a valuation `ValuativeRel.valuation K`
taking values in an abstract value group `ValueGroupWithZero K`, together with an order
isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` of that group with `ℤᵐ⁰`.
This file assembles them into the additively normalized valuation of a local field, the monoid
homomorphism

`normalizedValuation K : Kˣ →* Multiplicative ℤ`,

whose value at a uniformizer is `Multiplicative.ofAdd 1`, and its zero-preserving extension
`normalizedValuationWithZero K : K →*₀ ℤᵐ⁰`. An integer is recovered from a nonzero value by
decoding with `Multiplicative.toAdd`. The associated rational-valued absolute value is

`normalizedAbsoluteValue K : AbsoluteValue K ℚ≥0`.

Its value at a nonzero `x` is `q ^ (-v_K(x))`, where `q` is the cardinality of the residue field.

## Main definitions

* `TauCeti.normalizedValuation`: the normalized valuation `v_K^×` of a nonarchimedean local
  field, as a homomorphism from the unit group to `Multiplicative ℤ`.
* `TauCeti.normalizedValuationWithZero`: its zero-preserving extension to all of the field.
* `TauCeti.normalizedAbsoluteValue`: the normalized `ℚ≥0`-valued absolute value associated to
  `normalizedValuation`.

## Main results

* `TauCeti.toAdd_normalizedValuation_eq_neg_log`: the translation between the multiplicative
  convention of `ValuativeRel.valuation` and the additive normalization.
* `TauCeti.normalizedValuation_surjective`: the normalized value group is all of `ℤ`.
* `TauCeti.normalizedValuation_irreducible`: an irreducible element of `𝒪[K]` has normalized
  valuation `1`; that is, uniformizers are exactly where the normalization is pinned.
* `TauCeti.normalizedValuationWithZero_eq_ordFrac`: the zero-preserving normalized valuation is
  Mathlib's order-of-vanishing map `Ring.ordFrac 𝒪[K]`, which is where the discrete-valuation-ring
  API for it comes from.
* `TauCeti.normalizedValuation_eq_one_of_isOfFinOrder`: the normalized valuation vanishes on the
  roots of unity of `K`.
* `TauCeti.normalizedAbsoluteValue_apply_ne_zero`: the formula `|x|_K = q ^ (-v_K(x))`.
* `TauCeti.isNonarchimedean_normalizedAbsoluteValue`: the normalized absolute value satisfies the
  strong triangle inequality.
* `TauCeti.eq_normalizedValuation`: the kernel condition together with the uniformizer equation
  characterizes the normalized valuation among homomorphisms `Kˣ →* Multiplicative ℤ`.
* `TauCeti.isUnit_iff_normalizedValuationWithZero_eq_one`,
  `TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg` and
  `TauCeti.dvd_iff_toAdd_normalizedValuation_le`: the normalized valuation reads off the units,
  the elements and the divisibility relation of the ring of integers.

## Implementation notes

Mathlib's convention is multiplicative and decreasing: `valuation K π < 1` at a uniformizer `π`,
and the integers of `K` are the elements of valuation at most `1`. The additive normalization
therefore carries a minus sign, and that sign is confined to the single translation lemma
`toAdd_normalizedValuation_eq_neg_log`; every statement mixing the two conventions is derived
from it.

The group-valued normalized valuation is defined on `Kˣ` because `Multiplicative ℤ` has no room
for the value at `0`; `normalizedValuationWithZero` supplies the corresponding map on all of `K`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §§1–2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§3–4.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

open scoped WithZero

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- The declaration sequence follows the human-authored specification in
-- `TauCetiRoadmap/LocalFieldsRamification/Suggested.lean`.
variable (K) in
/-- The normalized valuation `v_K^×` of a nonarchimedean local field `K`: the composite of
`ValuativeRel.valuation K` with the order isomorphism `valueGroupWithZeroIsoInt` of the value
group with `ℤᵐ⁰`, read additively and with the sign chosen so that a uniformizer has value
`Multiplicative.ofAdd 1`. -/
def normalizedValuation : Kˣ →* Multiplicative ℤ :=
  invMonoidHom.comp
    ((((Units.mapEquiv (valueGroupWithZeroIsoInt K).toMulEquiv).trans
      WithZero.unitsWithZeroEquiv).toMonoidHom).comp
        (Units.map (valuation K).toMonoidWithZeroHom.toMonoidHom))

variable (K) in
/-- The normalized valuation extended across zero, as a zero-preserving monoid homomorphism
from `K` to `ℤᵐ⁰`. -/
def normalizedValuationWithZero : K →*₀ ℤᵐ⁰ :=
  invMonoidWithZeroHom.comp
    ((valueGroupWithZeroIsoInt K).toMonoidWithZeroHom.comp
      (valuation K).toMonoidWithZeroHom)

private noncomputable def intValuation : Valuation K ℤᵐ⁰ :=
  (valuation K).map (valueGroupWithZeroIsoInt K).toMonoidWithZeroHom
    (valueGroupWithZeroIsoInt K).toOrderIso.monotone

private theorem intValuation_surjective : Function.Surjective (intValuation (K := K)) := by
  intro z
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective ((valueGroupWithZeroIsoInt K).symm z)
  refine ⟨x, ?_⟩
  simp [intValuation, hx]

private theorem intValuation_valuationSubring :
    (intValuation (K := K)).valuationSubring.toSubring = 𝒪[K] := by
  ext x
  -- Unfold mapped-valuation membership to expose the comparison transported by the order
  -- isomorphism; the valuation-subring API has no lemma stating this composite equality.
  change valueGroupWithZeroIsoInt K (valuation K x) ≤ 1 ↔ valuation K x ≤ 1
  simpa only [map_one] using
    (OrderIsoClass.map_le_map_iff (valueGroupWithZeroIsoInt K)
      (a := valuation K x) (b := 1))

private theorem intValuation_eq_maximalIdeal_valuation :
    intValuation (K := K) = (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation K := by
  have hv : Function.Surjective (intValuation (K := K)) := intValuation_surjective
  have : IsDiscreteValuationRing (intValuation (K := K)).valuationSubring :=
    Valuation.valuationSubring_isDiscreteValuationRing_of_surjective _ hv
  -- Both valuations are surjective and normalized, so it is enough to see that they have the
  -- same valuation subring, namely `𝒪[K]`.
  refine Valuation.eq_of_isEquiv_of_surjective hv
    (IsDedekindDomain.HeightOneSpectrum.valuation_surjective K _)
    ((Valuation.isEquiv_iff_valuationSubring ..).mpr ?_)
  refine ValuationSubring.eq_of_le_of_ne_top
    (A := (intValuation (K := K)).valuationSubring) ?_ ?_
  · intro x hx
    have hx' : x ∈ 𝒪[K] := by rwa [← intValuation_valuationSubring]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]) (K := K) (⟨x, hx'⟩ : 𝒪[K])
  · simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance

/-- The zero-preserving normalized valuation vanishes exactly at zero. -/
theorem normalizedValuationWithZero_eq_zero_iff (x : K) :
    normalizedValuationWithZero K x = 0 ↔ x = 0 := by
  simp [normalizedValuationWithZero]

/-- The zero-preserving normalized valuation restricts to `normalizedValuation` on `Kˣ`. -/
@[simp]
theorem normalizedValuationWithZero_coe (x : Kˣ) :
    normalizedValuationWithZero K (x : K) = (normalizedValuation K x : ℤᵐ⁰) := by
  simp [normalizedValuationWithZero, normalizedValuation, invMonoidWithZeroHom]

/-- The normalized valuation of a local field is the order of vanishing along `𝒪[K]`: it agrees
with Mathlib's `Ring.ordFrac`, the canonical `ℤᵐ⁰`-valued order map of a discrete valuation ring
on its fraction field. The `Ring.ordFrac` API therefore applies to `normalizedValuationWithZero`.
-/
theorem normalizedValuationWithZero_eq_ordFrac :
    normalizedValuationWithZero K = Ring.ordFrac 𝒪[K] := by
  ext x
  rw [Ring.ordFrac_eq_valuation_inv, ← intValuation_eq_maximalIdeal_valuation]
  simp [normalizedValuationWithZero, intValuation, invMonoidWithZeroHom]

/-- The translation between Mathlib's multiplicative valuation and the additive normalization:
the normalized valuation is minus the logarithm of `ValuativeRel.valuation`, transported to
`ℤᵐ⁰`. Every comparison of the two conventions goes through this lemma. -/
theorem toAdd_normalizedValuation_eq_neg_log (x : Kˣ) :
    (normalizedValuation K x).toAdd
      = -WithZero.log (valueGroupWithZeroIsoInt K (valuation K (x : K))) := by
  simp [normalizedValuation, ← WithZero.toAdd_unzero_eq_log]

private theorem toAdd_normalizedValuation_eq_ord (x : Kˣ) :
    (normalizedValuation K x).toAdd = Valuation.ord (intValuation (K := K)) (x : K) := by
  rw [toAdd_normalizedValuation_eq_neg_log, Valuation.ord_def]
  -- Both sides now unfold to the logarithm of the transported valuation; there is no named
  -- bridge between these two nested homomorphism presentations.
  rfl

private theorem valueGroupWithZeroIsoInt_valuation_ne_zero (x : Kˣ) :
    valueGroupWithZeroIsoInt K (valuation K (x : K)) ≠ 0 := by
  simp

/-- The translation of `toAdd_normalizedValuation_eq_neg_log` read in the other direction: Mathlib's
valuation of a unit is recovered from the normalized valuation by exponentiating its negative. -/
theorem valueGroupWithZeroIsoInt_valuation (x : Kˣ) :
    valueGroupWithZeroIsoInt K (valuation K (x : K))
      = WithZero.exp (-(normalizedValuation K x).toAdd) := by
  rw [toAdd_normalizedValuation_eq_ord]
  exact Valuation.valuation_eq_exp_neg_ord (intValuation (K := K)) x.ne_zero

/-- The normalized valuation vanishes exactly on the elements of valuation `1`. -/
@[simp]
theorem normalizedValuation_eq_one_iff (x : Kˣ) :
    normalizedValuation K x = 1 ↔ valuation K (x : K) = 1 := by
  rw [← toAdd_eq_zero, toAdd_normalizedValuation_eq_ord,
    Valuation.ord_eq_iff_valuation_eq_exp_neg (intValuation (K := K)) x.ne_zero]
  simp [intValuation]

/-- The normalized valuation vanishes on every root of unity: `Multiplicative ℤ` is torsion
free, so a unit of finite order has normalized valuation `1`. -/
theorem normalizedValuation_eq_one_of_isOfFinOrder {x : Kˣ} (hx : IsOfFinOrder x) :
    normalizedValuation K x = 1 :=
  ((normalizedValuation K).isOfFinOrder hx).eq_one'

/-- The normalized valuation reverses the order of Mathlib's valuation. -/
theorem toAdd_normalizedValuation_le_iff_valuation_le (x y : Kˣ) :
    (normalizedValuation K x).toAdd ≤ (normalizedValuation K y).toAdd
      ↔ valuation K (y : K) ≤ valuation K (x : K) := by
  rw [toAdd_normalizedValuation_eq_neg_log, toAdd_normalizedValuation_eq_neg_log,
    neg_le_neg_iff,
    WithZero.log_le_log (valueGroupWithZeroIsoInt_valuation_ne_zero y)
      (valueGroupWithZeroIsoInt_valuation_ne_zero x),
    OrderIsoClass.map_le_map_iff]

/-- A unit of `K` lies in the ring of integers exactly when its normalized valuation is
nonnegative. -/
theorem mem_integer_iff_toAdd_normalizedValuation_nonneg (x : Kˣ) :
    (x : K) ∈ 𝒪[K] ↔ 0 ≤ (normalizedValuation K x).toAdd := by
  rw [Valuation.mem_integer_iff, toAdd_normalizedValuation_eq_ord]
  -- Transport the valuation comparison through the order isomorphism before identifying the
  -- mapped valuation below.
  rw [show valuation K (x : K) ≤ 1 ↔
      valueGroupWithZeroIsoInt K (valuation K (x : K)) ≤ valueGroupWithZeroIsoInt K 1 from
    (OrderIsoClass.map_le_map_iff (valueGroupWithZeroIsoInt K) :
      valueGroupWithZeroIsoInt K (valuation K (x : K)) ≤ valueGroupWithZeroIsoInt K 1 ↔
        valuation K (x : K) ≤ 1).symm]
  simp only [map_one]
  -- Unfold the mapped valuation and its valuation-subring membership so that the generic
  -- order characterization applies; the API does not expose this as a rewrite lemma.
  change intValuation (K := K) (x : K) ≤ 1 ↔
    0 ≤ Valuation.ord (intValuation (K := K)) (x : K)
  exact Valuation.mem_valuationSubring_iff_ord_nonneg (intValuation (K := K))

/-- The normalized value group of a nonarchimedean local field is all of `ℤ`. -/
theorem normalizedValuation_surjective : Function.Surjective (normalizedValuation K) := by
  intro n
  obtain ⟨x, hx⟩ := Valuation.ord_surjective (intValuation (K := K))
    intValuation_surjective n.toAdd
  rcases eq_or_ne x 0 with rfl | hx0
  · have hn : n = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using hx.symm
    exact ⟨1, by simp [hn]⟩
  · refine ⟨Units.mk0 x hx0, ?_⟩
    apply Multiplicative.toAdd.injective
    simpa [toAdd_normalizedValuation_eq_ord] using hx

/-- An element of the ring of integers is a unit there exactly when its zero-preserving
normalized valuation is one. -/
theorem isUnit_iff_normalizedValuationWithZero_eq_one {u : 𝒪[K]} :
    IsUnit u ↔ normalizedValuationWithZero K (u : K) = 1 := by
  rw [normalizedValuationWithZero_eq_ordFrac]
  exact Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := K)

/-- Divisibility in the ring of integers is monotonicity of the normalized valuation. -/
theorem dvd_iff_toAdd_normalizedValuation_le {a b : 𝒪[K]} (ha : (a : K) ≠ 0) (hb : (b : K) ≠ 0) :
    a ∣ b ↔ (normalizedValuation K (Units.mk0 (a : K) ha)).toAdd
      ≤ (normalizedValuation K (Units.mk0 (b : K) hb)).toAdd := by
  rw [toAdd_normalizedValuation_le_iff_valuation_le]
  exact Valuation.Integers.dvd_iff_le (Valuation.integer.integers (valuation K))

/-- Every unit of `K` is a unit of `𝒪[K]` times an integer power of a fixed irreducible element
of `𝒪[K]`. -/
theorem exists_eq_mul_zpow_of_irreducible {π : 𝒪[K]} (hπ : Irreducible π) (x : Kˣ) :
    ∃ (u : Kˣ) (n : ℤ), valuation K (u : K) = 1 ∧
      x = u * Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h)) ^ n := by
  let hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  obtain ⟨n, u, hx⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (R := 𝒪[K]) hπ x.ne_zero
  let uK : Kˣ := Units.map (algebraMap 𝒪[K] K).toMonoidHom u
  refine ⟨uK, n, ?_, ?_⟩
  · exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp u.isUnit
  · apply Units.ext
    -- The algebra map from the valuation subring is definitionally its subtype coercion; expose
    -- that equality before applying the DVR decomposition equation.
    rw [show algebraMap 𝒪[K] K π = (π : K) by rfl] at hx
    simpa [uK, Units.smul_def, Algebra.smul_def] using hx

/-- The normalized valuation of an irreducible element of `𝒪[K]`, that is of a uniformizer of
`K`, is `Multiplicative.ofAdd 1`. -/
@[simp]
theorem normalizedValuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    normalizedValuation K
      (Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h))) = Multiplicative.ofAdd 1 := by
  have h : normalizedValuationWithZero K (π : K) = WithZero.exp 1 := by
    rw [normalizedValuationWithZero_eq_ordFrac]
    exact Ring.ordFrac_irreducible (K := K) hπ
  -- Read the equation on `Kˣ`: the algebra map out of `𝒪[K]` is the subtype coercion, so `π` is
  -- the underlying element of the unit displayed in the statement.
  rw [show (π : K) = ((Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h)) : Kˣ) : K) from rfl,
    normalizedValuationWithZero_coe, WithZero.exp_eq_coe_ofAdd] at h
  exact_mod_cast h

/-- The normalized valuation is the unique homomorphism `Kˣ →* Multiplicative ℤ` that vanishes
on the elements of valuation `1` and takes the value `Multiplicative.ofAdd 1` at a uniformizer. -/
theorem eq_normalizedValuation (w : Kˣ →* Multiplicative ℤ)
    (hw : ∀ x : Kˣ, valuation K (x : K) = 1 → w x = 1)
    {π : 𝒪[K]} (hπ : Irreducible π)
    (hwπ : w (Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h))) =
      Multiplicative.ofAdd 1) :
    w = normalizedValuation K := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨u, n, hu, rfl⟩ := exists_eq_mul_zpow_of_irreducible hπ x
  rw [map_mul, map_mul, hw u hu, (normalizedValuation_eq_one_iff u).2 hu, one_mul, one_mul,
    map_zpow, map_zpow, hwπ, normalizedValuation_irreducible hπ]

/-- The valuation of an irreducible element of `𝒪[K]` generates the value group: every nonzero
value is an integer power of it. -/
theorem exists_eq_valuation_zpow_of_irreducible {π : 𝒪[K]} (hπ : Irreducible π)
    (γ : (ValueGroupWithZero K)ˣ) :
    ∃ n : ℤ, (γ : ValueGroupWithZero K) = valuation K (π : K) ^ n := by
  have huni : (valuation K).IsUniformizer (π : K) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span (valuation K) hπ.maximalIdeal_eq
  have hγ : γ ∈ MonoidWithZeroHom.valueGroup (.ofClass (valuation K)) := by
    apply MonoidWithZeroHom.mem_valueGroup
    exact ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
  rw [huni.zpowers_eq_valueGroup] at hγ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hγ
  refine ⟨n, ?_⟩
  simpa using congrArg Units.val hn.symm

section NormalizedAbsoluteValue

open scoped NNRat

private theorem one_lt_residueFieldCard :
    (1 : ℚ≥0) < Nat.card 𝓀[K] := by
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])

private noncomputable def normalizedAbsoluteValueHom : K →*₀ ℚ≥0 :=
  (WithZeroMulInt.toNNRat (one_lt_residueFieldCard (K := K)).ne_zero).comp
    (intValuation (K := K)).toMonoidWithZeroHom

private theorem normalizedAbsoluteValueHom_apply (x : K) :
    normalizedAbsoluteValueHom (K := K) x =
      WithZeroMulInt.toNNRat (one_lt_residueFieldCard (K := K)).ne_zero
        (intValuation (K := K) x) :=
  rfl

private theorem isNonarchimedean_normalizedAbsoluteValueHom :
    IsNonarchimedean (normalizedAbsoluteValueHom (K := K)) := by
  intro x y
  rw [normalizedAbsoluteValueHom_apply, normalizedAbsoluteValueHom_apply,
    normalizedAbsoluteValueHom_apply,
    ← (WithZeroMulInt.toNNRat_strictMono (one_lt_residueFieldCard (K := K))).monotone.map_max]
  exact (WithZeroMulInt.toNNRat_strictMono (one_lt_residueFieldCard (K := K))).monotone
    ((intValuation (K := K)).map_add x y)

variable (K) in
/-- The normalized absolute value of a nonarchimedean local field, with values in `ℚ≥0`.
For a nonzero element `x`, its value is `q ^ (-v_K(x))`, where
`q = Nat.card 𝓀[K]` is the cardinality of the residue field. -/
noncomputable def normalizedAbsoluteValue : AbsoluteValue K ℚ≥0 where
  toFun := normalizedAbsoluteValueHom (K := K)
  map_mul' := map_mul (normalizedAbsoluteValueHom (K := K))
  nonneg' _ := bot_le
  eq_zero' x := by
    simp [normalizedAbsoluteValueHom, intValuation]
  add_le' x y := IsNonarchimedean.add_le (fun _ ↦ bot_le)
    isNonarchimedean_normalizedAbsoluteValueHom

private theorem normalizedAbsoluteValue_apply (x : K) :
    normalizedAbsoluteValue K x = normalizedAbsoluteValueHom (K := K) x :=
  rfl

/-- The normalized absolute value is the rational power `q ^ (-v_K(x))` at every nonzero
element, where `q` is the cardinality of the residue field. -/
theorem normalizedAbsoluteValue_apply_ne_zero (x : K) (hx : x ≠ 0) :
    normalizedAbsoluteValue K x =
      (Nat.card 𝓀[K] : ℚ≥0) ^
        (-(normalizedValuation K (Units.mk0 x hx)).toAdd) := by
  rw [normalizedAbsoluteValue_apply, normalizedAbsoluteValueHom_apply,
    WithZeroMulInt.toNNRat_apply_of_ne_zero]
  · rw [toAdd_normalizedValuation_eq_ord, Valuation.ord_def, neg_neg,
      WithZero.toAdd_unzero_eq_log]
    rfl
  · simp [intValuation, hx]

/-- The normalized absolute value on `Kˣ` is the rational power `q ^ (-v_K(x))`. -/
theorem normalizedAbsoluteValue_coe (x : Kˣ) :
    normalizedAbsoluteValue K (x : K) =
      (Nat.card 𝓀[K] : ℚ≥0) ^ (-(normalizedValuation K x).toAdd) := by
  simpa using normalizedAbsoluteValue_apply_ne_zero (x : K) x.ne_zero

/-- The normalized absolute value satisfies the strong triangle inequality. -/
theorem isNonarchimedean_normalizedAbsoluteValue :
    IsNonarchimedean (normalizedAbsoluteValue K) :=
  isNonarchimedean_normalizedAbsoluteValueHom

/-- The normalized absolute value takes the value one exactly on the elements of valuation one,
that is, on the units of the ring of integers. -/
@[simp]
theorem normalizedAbsoluteValue_eq_one_iff (x : K) :
    normalizedAbsoluteValue K x = 1 ↔ valuation K x = 1 := by
  rw [normalizedAbsoluteValue_apply, normalizedAbsoluteValueHom_apply,
    WithZeroMulInt.toNNRat_eq_one_iff]
  · change valueGroupWithZeroIsoInt K (valuation K x) = 1 ↔ valuation K x = 1
    simp
  · exact (one_lt_residueFieldCard (K := K)).ne'

/-- An element belongs to the ring of integers exactly when its normalized absolute value is at
most one. -/
theorem mem_integer_iff_normalizedAbsoluteValue_le_one (x : K) :
    x ∈ 𝒪[K] ↔ normalizedAbsoluteValue K x ≤ 1 := by
  rw [Valuation.mem_integer_iff, normalizedAbsoluteValue_apply, normalizedAbsoluteValueHom_apply,
    WithZeroMulInt.toNNRat_le_one_iff]
  · change valuation K x ≤ 1 ↔ valueGroupWithZeroIsoInt K (valuation K x) ≤ 1
    simpa only [map_one] using
      (OrderIsoClass.map_le_map_iff (valueGroupWithZeroIsoInt K)
        (a := valuation K x) (b := 1)).symm
  · exact one_lt_residueFieldCard (K := K)

/-- The normalized absolute value is one on every root of unity. -/
theorem normalizedAbsoluteValue_eq_one_of_isOfFinOrder {x : Kˣ} (hx : IsOfFinOrder x) :
    normalizedAbsoluteValue K (x : K) = 1 := by
  rw [normalizedAbsoluteValue_eq_one_iff]
  exact (normalizedValuation_eq_one_iff x).1
    (normalizedValuation_eq_one_of_isOfFinOrder hx)

end NormalizedAbsoluteValue

end TauCeti
