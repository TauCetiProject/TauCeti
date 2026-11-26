/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.RingTheory.Valuation.NormNormalization
public import TauCeti.RingTheory.Valuation.RealEquiv

/-!
# The real additive valuation of a rank-one valuation

A valuation `v : Valuation R Γ₀` of rank at most one (`Valuation.RankLeOne`) comes with a strictly
monotone embedding `RankLeOne.hom' v` of its value group into `ℝ≥0`, and so with the real-valued
function `Valuation.norm v x`, the image of `v x` under this embedding. This file attaches to it
the real additive valuation

  `Valuation.realAddVal v x = -Real.log (Valuation.norm v x)`, with `x ↦ ⊤` when `v x = 0`,

which is the form in which valuations enter the Newton polygon and other additive constructions.
It reverses the order of `v` (`Valuation.realAddVal_le_realAddVal_iff`), so its multiplicative
form is equivalent to `v` (`Valuation.isEquiv_toValuation_realAddVal`), and it recovers the norm
from its finite values: for `t : ℝ`, `realAddVal v x = t ↔ Valuation.norm v x = Real.exp (-t)`
(`Valuation.realAddVal_eq_coe_iff`), while `realAddVal v x = ⊤` exactly when `v x = 0`
(`Valuation.realAddVal_eq_top_iff`). On a normed ring whose norm is `Valuation.norm v` it is the
base-`e` valuation `AddValuation.ofNorm` of the norm (`Valuation.realAddVal_eq_ofNorm`); this
applies to the normed field `Valued.toNormedField` that a rank-one valued field carries
(`Valued.realAddVal_eq_ofNorm`) and to the valuation `NormedField.valuation` of an ultrametric
normed field (`NormedField.realAddVal_valuation`).

The embedding into `ℝ≥0` is part of the rank-one structure, and it fixes the scale of
`Valuation.realAddVal`: the real additive valuations inducing the same order as `v` are exactly the
positive real multiples of `Valuation.realAddVal v`
(`Valuation.isEquiv_toValuation_iff_exists_map_mul_realAddVal_eq`).

## Main definitions

* `Valuation.realAddVal`: the real additive valuation `-log (Valuation.norm v x)` of a valuation
  of rank at most one.

## Main results

* `Valuation.realAddVal_eq_top_iff`, `Valuation.realAddVal_of_ne_zero` and
  `Valuation.untop₀_realAddVal`: the values of `Valuation.realAddVal`.
* `Valuation.realAddVal_eq_coe_iff`: norm recovery from finite values, `realAddVal v x = t ↔
  v.norm x = exp (-t)` for `t : ℝ`.
* `Valuation.realAddVal_le_realAddVal_iff` and `Valuation.isEquiv_toValuation_realAddVal`:
  `Valuation.realAddVal v` induces the order of `v`.
* `Valuation.realAddVal_eq_ofNorm`, `Valued.realAddVal_eq_ofNorm` and
  `NormedField.realAddVal_valuation`: comparison with `AddValuation.ofNorm (Real.exp 1)`.
* `Valuation.isEquiv_toValuation_iff_exists_map_mul_realAddVal_eq`: the real additive
  valuations equivalent to `v` are the positive multiples of `Valuation.realAddVal v`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§3–4.
-/

public section

open scoped NNReal

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

section RankLeOne

variable (v : Valuation R Γ₀) [RankLeOne v]

/-- The norm attached to a valuation of rank at most one reflects the order of the valuation. -/
theorem norm_le_norm_iff {x y : R} : v.norm x ≤ v.norm y ↔ v x ≤ v y := by
  rw [norm_def, norm_def, NNReal.coe_le_coe, (RankLeOne.strictMono' (v := v)).le_iff_le,
    restrict_le_iff]

/-- The norm attached to a valuation of rank at most one is multiplicative. -/
@[simp]
theorem norm_mul (x y : R) : v.norm (x * y) = v.norm x * v.norm y := by
  simp [norm_def]

/-- The norm attached to a valuation of rank at most one takes the value one at one. -/
@[simp]
theorem norm_one : v.norm 1 = 1 := by
  simp [norm_def]

/-- The norm attached to a valuation of rank at most one is positive exactly where the valuation
is nonzero. -/
theorem norm_pos_iff {x : R} : 0 < v.norm x ↔ v x ≠ 0 :=
  v.norm_pos_iff_valuation_pos.trans pos_iff_ne_zero

/-- The norm attached to a valuation of rank at most one vanishes exactly where the valuation
does. -/
@[simp]
theorem norm_eq_zero_iff {x : R} : v.norm x = 0 ↔ v x = 0 := by
  rw [← not_iff_not, ← ne_eq, ← ne_eq, ← v.norm_pos_iff, (v.norm_nonneg x).lt_iff_ne']

open scoped Classical in
/-- The function `x ↦ -log (v.norm x)`, with `⊤` where `v` vanishes, underlying
`Valuation.realAddVal`. -/
private noncomputable def negLogNorm (x : R) : WithTop ℝ :=
  if v x = 0 then ⊤ else ((-Real.log (v.norm x) : ℝ) : WithTop ℝ)

private theorem negLogNorm_of_eq_zero {x : R} (hx : v x = 0) : negLogNorm v x = ⊤ := by
  simp [negLogNorm, hx]

private theorem negLogNorm_of_ne_zero {x : R} (hx : v x ≠ 0) :
    negLogNorm v x = ((-Real.log (v.norm x) : ℝ) : WithTop ℝ) := by
  simp [negLogNorm, hx]

private theorem negLogNorm_antitone {x y : R} (h : v x ≤ v y) :
    negLogNorm v y ≤ negLogNorm v x := by
  by_cases hx : v x = 0
  · rw [negLogNorm_of_eq_zero v hx]
    exact le_top
  have hy : v y ≠ 0 := fun hy ↦ hx (le_antisymm (hy ▸ h) zero_le)
  rw [negLogNorm_of_ne_zero v hx, negLogNorm_of_ne_zero v hy, WithTop.coe_le_coe, neg_le_neg_iff]
  exact Real.log_le_log ((v.norm_pos_iff).2 hx) ((v.norm_le_norm_iff).2 h)

private theorem negLogNorm_mul (x y : R) :
    negLogNorm v (x * y) = negLogNorm v x + negLogNorm v y := by
  by_cases hx : v x = 0
  · rw [negLogNorm_of_eq_zero v hx, WithTop.top_add,
      negLogNorm_of_eq_zero v (by rw [v.map_mul, hx, zero_mul])]
  by_cases hy : v y = 0
  · rw [negLogNorm_of_eq_zero v hy, WithTop.add_top,
      negLogNorm_of_eq_zero v (by rw [v.map_mul, hy, mul_zero])]
  rw [negLogNorm_of_ne_zero v hx, negLogNorm_of_ne_zero v hy,
    negLogNorm_of_ne_zero v (by rw [v.map_mul]; exact mul_ne_zero hx hy), norm_mul,
    Real.log_mul ((v.norm_pos_iff).2 hx).ne' ((v.norm_pos_iff).2 hy).ne', neg_add,
    WithTop.coe_add]

/-- The **real additive valuation** of a valuation `v` of rank at most one: it sends `x` to
`-Real.log (v.norm x)`, the negated natural logarithm of the image of `v x` under the embedding
`RankLeOne.hom' v` of the value group into `ℝ≥0`, and sends the elements with `v x = 0` to `⊤`. -/
noncomputable def realAddVal : AddValuation R (WithTop ℝ) :=
  AddValuation.of (negLogNorm v) (negLogNorm_of_eq_zero v v.map_zero)
    (by rw [negLogNorm_of_ne_zero v (by simp), norm_one, Real.log_one, neg_zero,
      WithTop.coe_zero])
    (fun x y ↦ (le_max_iff.1 (v.map_add x y)).elim
      (fun h ↦ min_le_of_left_le (negLogNorm_antitone v h))
      (fun h ↦ min_le_of_right_le (negLogNorm_antitone v h)))
    (negLogNorm_mul v)

/-- `Valuation.realAddVal` is `⊤` exactly where the valuation vanishes. -/
@[simp]
theorem realAddVal_eq_top_iff {x : R} : v.realAddVal x = ⊤ ↔ v x = 0 := by
  by_cases hx : v x = 0
  · simp only [realAddVal, AddValuation.of_apply, negLogNorm_of_eq_zero v hx, hx]
  · simp only [realAddVal, AddValuation.of_apply, negLogNorm_of_ne_zero v hx, hx,
      WithTop.coe_ne_top]

/-- Where the valuation does not vanish, `Valuation.realAddVal` is `-Real.log (v.norm x)`. -/
theorem realAddVal_of_ne_zero {x : R} (hx : v x ≠ 0) :
    v.realAddVal x = ((-Real.log (v.norm x) : ℝ) : WithTop ℝ) :=
  negLogNorm_of_ne_zero v hx

/-- `WithTop.untop₀` of `Valuation.realAddVal` is `-Real.log (v.norm x)` for every `x`, including
the elements where `v` vanishes and both sides are zero. -/
@[simp]
theorem untop₀_realAddVal (x : R) : (v.realAddVal x).untop₀ = -Real.log (v.norm x) := by
  by_cases hx : v x = 0
  · rw [(v.realAddVal_eq_top_iff).2 hx, (v.norm_eq_zero_iff).2 hx, Real.log_zero, neg_zero,
      WithTop.untop₀_top]
  · rw [v.realAddVal_of_ne_zero hx, WithTop.untop₀_coe]

/-- **Norm recovery**: `Valuation.realAddVal v x` is the finite value `t` exactly when
`v.norm x = Real.exp (-t)`. -/
theorem realAddVal_eq_coe_iff {x : R} {t : ℝ} :
    v.realAddVal x = t ↔ v.norm x = Real.exp (-t) := by
  by_cases hx : v x = 0
  · rw [(v.realAddVal_eq_top_iff).2 hx, (v.norm_eq_zero_iff).2 hx]
    exact iff_of_false WithTop.top_ne_coe (Real.exp_pos _).ne
  rw [v.realAddVal_of_ne_zero hx, WithTop.coe_eq_coe, neg_eq_iff_eq_neg]
  constructor
  · intro h
    rw [← h, Real.exp_log ((v.norm_pos_iff).2 hx)]
  · intro h
    rw [h, Real.log_exp]

/-- `Valuation.realAddVal v` reverses the order of `v`. -/
@[simp]
theorem realAddVal_le_realAddVal_iff {x y : R} :
    v.realAddVal x ≤ v.realAddVal y ↔ v y ≤ v x := by
  refine ⟨fun h ↦ ?_, negLogNorm_antitone v⟩
  by_contra hlt
  rw [not_le] at hlt
  have hy : v y ≠ 0 := pos_iff_ne_zero.1 (zero_le.trans_lt hlt)
  by_cases hx : v x = 0
  · rw [(v.realAddVal_eq_top_iff).2 hx, top_le_iff, v.realAddVal_eq_top_iff] at h
    exact hy h
  rw [v.realAddVal_of_ne_zero hx, v.realAddVal_of_ne_zero hy, WithTop.coe_le_coe,
    neg_le_neg_iff, Real.log_le_log_iff ((v.norm_pos_iff).2 hy) ((v.norm_pos_iff).2 hx),
    v.norm_le_norm_iff] at h
  exact hlt.not_ge h

/-- The multiplicative form of `Valuation.realAddVal v` is equivalent to `v`. -/
theorem isEquiv_toValuation_realAddVal :
    (AddValuation.toValuation v.realAddVal).IsEquiv v := fun x y ↦ by
  rw [AddValuation.toValuation_apply, AddValuation.toValuation_apply, Multiplicative.ofAdd_le,
    OrderDual.toDual_le_toDual, realAddVal_le_realAddVal_iff]

/-- **Class and scale for rank-one valuations.** The real additive valuations whose multiplicative
forms are equivalent to `v` are exactly the positive real multiples of `Valuation.realAddVal v`. -/
theorem isEquiv_toValuation_iff_exists_map_mul_realAddVal_eq (w : AddValuation R (WithTop ℝ)) :
    (AddValuation.toValuation w).IsEquiv v ↔
      ∃ c : ℝ, 0 < c ∧ ∀ x, WithTop.map (c * ·) (v.realAddVal x) = w x := by
  rw [← AddValuation.isEquiv_iff_exists_map_mul_eq, AddValuation.isEquiv_iff_val_le_val]
  refine ⟨fun h x y ↦ ?_, fun h x y ↦ ?_⟩
  · rw [realAddVal_le_realAddVal_iff, ← h y x, AddValuation.toValuation_apply,
      AddValuation.toValuation_apply, Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]
  · rw [AddValuation.toValuation_apply, AddValuation.toValuation_apply, Multiplicative.ofAdd_le,
      OrderDual.toDual_le_toDual, ← h, realAddVal_le_realAddVal_iff]

end RankLeOne

section Norm

variable {S : Type*} [SeminormedRing S] [IsUltrametricDist S] [NormMulClass S] [NormOneClass S]

/-- If a valuation `v` of rank at most one on a normed ring has `Valuation.norm v` as its norm, then
`Valuation.realAddVal v` is the base-`e` valuation `AddValuation.ofNorm (Real.exp 1)` of the
norm. -/
theorem realAddVal_eq_ofNorm (v : Valuation S Γ₀) [RankLeOne v] (hv : ∀ x, v.norm x = ‖x‖) :
    v.realAddVal = AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 one_pos) := by
  ext x
  by_cases hx : v x = 0
  · rw [(v.realAddVal_eq_top_iff).2 hx, eq_comm, AddValuation.ofNorm_eq_top_iff, ← hv,
      v.norm_eq_zero_iff]
    exact hx
  rw [v.realAddVal_of_ne_zero hx, hv,
    AddValuation.ofNorm_exp_one_of_norm_ne_zero (hv x ▸ (v.norm_pos_iff.2 hx).ne')]

end Norm

end Valuation

namespace Valued

open scoped Valued

/-- On a field with a rank-one valuation, the real additive valuation `Valuation.realAddVal` of the
valuation is `-Real.log ‖x‖` for the norm `Valued.toNormedField` that the rank-one structure
defines. -/
theorem realAddVal_eq_ofNorm {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued L Γ₀] [Valuation.RankOne (Valued.v : Valuation L Γ₀)] :
    (Valued.v : Valuation L Γ₀).realAddVal =
      AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 one_pos) :=
  Valuation.realAddVal_eq_ofNorm _ fun _ ↦ by
    rw [Valuation.norm_def, Valued.toNormedField.norm_def]

end Valued

namespace NormedField

/-- On an ultrametric normed field, the real additive valuation of the valuation
`NormedField.valuation` is the base-`e` valuation `AddValuation.ofNorm (Real.exp 1)` of the
norm. -/
theorem realAddVal_valuation {K : Type*} [NormedField K] [IsUltrametricDist K] :
    (valuation : Valuation K ℝ≥0).realAddVal =
      AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 one_pos) :=
  Valuation.realAddVal_eq_ofNorm _ fun x ↦ by
    rw [Valuation.norm_def, ← coe_nnNorm, ← valuation_apply]
    -- The rank-one embedding of `NormedField.valuation` is `ValueGroup₀.embedding`.
    exact congrArg ((↑) : ℝ≥0 → ℝ) (valuation.embedding_restrict x)

end NormedField
