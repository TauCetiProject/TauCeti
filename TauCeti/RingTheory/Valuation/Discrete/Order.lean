/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic
public import TauCeti.RingTheory.Valuation.Surjective

/-!
# Additive orders of discrete valuations

This file packages the additive order attached to a `ℤᵐ⁰`-valued valuation and develops the
facts that do not depend on a choice of constant field. The convention is
`ord_v f = -log (v f)`, so a uniformizer of a surjective valuation has order one.
The definition, characteristic lemmas, multiplication and addition laws apply to valuations on
rings, using nonzero valuation values to exclude the support where necessary. Finite products
require commutativity. Equivalence comparisons and the characterization of uniformizers also
apply to rings: a uniformizer is an element whose order is that of the generator below `1` of the
value group, and one exists exactly when the valuation attains that generator. Inverse and
quotient laws are stated on division rings; valuation-subring results are stated on fields. Facts
about surjective valuations that do not involve the order are in
`TauCeti.RingTheory.Valuation.Surjective`, under the conditions on the value group each needs: the
value group is full with no condition (and for a valuation from a division ring into an ordered
group with zero, full value group means surjectivity), the valuation is nontrivial exactly when
its target has an element other than `0` and `1`, equivalent surjective valuations into a
linearly ordered commutative group with zero are equal when its units form a cyclic group, and
for a surjective valuation from a field into a linearly ordered commutative group with zero whose
units form a nontrivial cyclic group, the valuation ring is a discrete valuation ring.
As `WithZero.log 0 = 0`, the order has the junk value `ord_v f = 0` whenever `v f = 0`.
On a division ring, `v f = 0` is equivalent to `f = 0`; hypotheses excluding zero are
included where necessary.

-/

public section

open scoped WithZero

open MonoidWithZeroHom

namespace Valuation

section Ring

variable {F : Type*} [Ring F]

/-- The additive order attached to a `ℤᵐ⁰`-valued valuation, given by its negative logarithm.
A uniformizer of a surjective valuation has order one. The order has the junk value zero
whenever the valuation vanishes, in particular at zero. -/
noncomputable def ord (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ℤ :=
  -WithZero.log (v f)

theorem ord_def (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ord v f = -WithZero.log (v f) :=
  (rfl)

/-- The order function commutes with restriction along a ring homomorphism. -/
@[simp]
theorem ord_comap {K : Type*} [Ring K] (v : _root_.Valuation F ℤᵐ⁰) (f : K →+* F)
    (x : K) : ord (v.comap f) x = ord v (f x) := by
  rw [ord_def, ord_def, _root_.Valuation.comap_apply]

/-- The order has its junk value zero on the valuation support. -/
theorem ord_eq_zero_of_map_eq_zero (v : _root_.Valuation F ℤᵐ⁰) {f : F} (hf : v f = 0) :
    ord v f = 0 := by
  simp [ord_def, hf]

/-- Nonzero order excludes the valuation support. -/
theorem valuation_ne_zero_of_ord_ne_zero (v : _root_.Valuation F ℤᵐ⁰) {f : F}
    (hf : ord v f ≠ 0) : v f ≠ 0 :=
  fun h ↦ hf (ord_eq_zero_of_map_eq_zero v h)

/-- Subtracting an element in the valuation support does not change the order. -/
theorem ord_sub_of_map_right_eq_zero (v : _root_.Valuation F ℤᵐ⁰) {f g : F}
    (hg : v g = 0) : ord v (f - g) = ord v f := by
  rw [ord_def, v.map_sub_of_right_eq_zero hg, ← ord_def]

@[simp]
theorem ord_zero (v : _root_.Valuation F ℤᵐ⁰) : ord v 0 = 0 :=
  ord_eq_zero_of_map_eq_zero v (map_zero v)

@[simp]
theorem ord_one (v : _root_.Valuation F ℤᵐ⁰) : ord v 1 = 0 := by
  simp [ord_def]

@[simp]
theorem ord_pow (v : _root_.Valuation F ℤᵐ⁰) (f : F) (n : ℕ) :
    ord v (f ^ n) = n * ord v f := by
  simp [ord_def, map_pow, WithZero.log_pow, mul_neg]

@[simp]
theorem ord_neg (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ord v (-f) = ord v f := by
  simp [ord_def, _root_.Valuation.map_neg]

/-- Outside the valuation support, the valuation is recovered from the order as
`exp (-ord v f)`. -/
theorem valuation_eq_exp_neg_ord (v : _root_.Valuation F ℤᵐ⁰) {f : F} (hf : v f ≠ 0) :
    v f = WithZero.exp (-ord v f) := by
  rw [ord_def, neg_neg, WithZero.exp_log hf]

/-- Outside the valuation support, `ord v f = n` exactly when `v f = exp (-n)`. -/
theorem ord_eq_iff_valuation_eq_exp_neg (v : _root_.Valuation F ℤᵐ⁰) {f : F}
    (hf : v f ≠ 0) {n : ℤ} : ord v f = n ↔ v f = WithZero.exp (-n) := by
  rw [valuation_eq_exp_neg_ord v hf, WithZero.exp_inj, neg_inj]

/-- `exp (-1)` lies below `1`. -/
private theorem mk0_exp_neg_one_lt_one :
    Units.mk0 (WithZero.exp (-1) : ℤᵐ⁰) WithZero.exp_ne_zero < 1 :=
  Units.val_lt_val.mp <| by simp

/-- `exp (-1)` generates the units of `ℤᵐ⁰`: its inverse corresponds to `1` under
`WithZero.unitsWithZeroEquiv`. -/
private theorem zpowers_mk0_exp_neg_one :
    Subgroup.zpowers (Units.mk0 (WithZero.exp (-1) : ℤᵐ⁰) WithZero.exp_ne_zero) = ⊤ := by
  rw [← Subgroup.zpowers_inv]
  exact WithZero.unitsWithZeroEquiv.zpowers_eq_top_of_apply_eq_ofAdd_one
    (WithZero.coe_injective <| by simp [← WithZero.exp_eq_coe_ofAdd])

theorem ord_surjective (v : _root_.Valuation F ℤᵐ⁰) (hv : Function.Surjective v) :
    Function.Surjective (ord v) := fun n => by
  obtain ⟨f, hf⟩ := hv (WithZero.exp (-n))
  exact ⟨f, by simp [ord_def, hf]⟩

/-- **A discrete valuation on a ring has a uniformizer exactly when it attains the generator below
`1` of its value group.** On a field it always does, by
`Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`. On a ring it need not: the `t`-adic
valuation on `k[t², t³]` has value group generated by `exp (-1)`, but takes neither this value nor
any other value of order one. -/
theorem exists_isUniformizer_iff_generator_mem_range {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : _root_.Valuation F Γ₀) [v.IsRankOneDiscrete] :
    (∃ t : F, v.IsUniformizer t) ↔ (IsRankOneDiscrete.generator v : Γ₀) ∈ Set.range v :=
  Iff.rfl

/-- **Uniformizers are the elements whose order is that of the generator below `1`** of the value
group of a discrete `ℤᵐ⁰`-valuation. Elements of the valuation support do not qualify, as the
generator is not `1`. -/
theorem isUniformizer_iff_ord_eq_neg_log_generator (v : _root_.Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] {t : F} :
    v.IsUniformizer t ↔ ord v t = -WithZero.log (IsRankOneDiscrete.generator v : ℤᵐ⁰) := by
  refine ⟨fun ht ↦ by rw [ord_def, ht], fun ht ↦ ?_⟩
  have hg := IsRankOneDiscrete.generator_ne_zero v
  have ht0 : v t ≠ 0 := fun h0 ↦ IsRankOneDiscrete.generator_ne_one v <| Units.val_eq_one.mp <| by
    rw [ord_eq_zero_of_map_eq_zero v h0, eq_comm, neg_eq_zero] at ht
    rw [← WithZero.exp_log hg, ht, WithZero.exp_zero]
  rwa [ord_eq_iff_valuation_eq_exp_neg v ht0, neg_neg, WithZero.exp_log hg] at ht

/-- **Uniformizers are the elements of order one** for a discrete `ℤᵐ⁰`-valuation with full value
group: the generator below `1` of its value group is then `exp (-1)`. The valuation need not attain
`exp (-1)`; on a ring it may not, and then neither side holds for any element. -/
theorem isUniformizer_iff_ord_eq_one_of_valueGroup_eq_top (v : _root_.Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] (hv : v.valueGroup = ⊤) {t : F} :
    v.IsUniformizer t ↔ ord v t = 1 := by
  rw [isUniformizer_iff_ord_eq_neg_log_generator,
    ← IsRankOneDiscrete.valueGroup_genLTOne_eq_generator,
    ← LinearOrderedCommGroup.Subgroup.genLTOne_unique _ mk0_exp_neg_one_lt_one
      (zpowers_mk0_exp_neg_one.trans hv.symm),
    Units.val_mk0, WithZero.log_exp, neg_neg]

theorem ord_mul (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : v f ≠ 0) (hg : v g ≠ 0) :
    ord v (f * g) = ord v f + ord v g := by
  rw [ord_def, ord_def, ord_def, map_mul, WithZero.log_mul hf hg]
  ring

/-- The order is additive on products of units, which lie outside the valuation support. -/
@[simp]
theorem ord_units_mul (v : _root_.Valuation F ℤᵐ⁰) (f g : Fˣ) :
    ord v ((f : F) * (g : F)) = ord v (f : F) + ord v (g : F) :=
  ord_mul v (f.isUnit.map v.toMonoidHom).ne_zero (g.isUnit.map v.toMonoidHom).ne_zero

/-- The ultrametric inequality in additive form. The sum must lie outside the valuation
support, where the order has its junk value. -/
theorem min_ord_le_ord_add (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (h : v (f + g) ≠ 0) :
    min (ord v f) (ord v g) ≤ ord v (f + g) := by
  rcases eq_or_ne (v f) 0 with hf | hf
  · simp only [ord_def, v.map_add_of_left_eq_zero hf, hf, WithZero.log_zero, neg_zero]
    exact min_le_right _ _
  rcases eq_or_ne (v g) 0 with hg | hg
  · simp only [ord_def, v.map_add_of_right_eq_zero hg, hg, WithZero.log_zero, neg_zero]
    exact min_le_left _ _
  simpa only [ord_def, min_le_iff, neg_le_neg_iff, WithZero.log_le_log h hf,
    WithZero.log_le_log h hg] using le_max_iff.mp (v.map_add f g)

/-- The order reverses the valuation: an element of larger order has smaller valuation.  The
hypotheses exclude the valuation support, where the order has its junk value. -/
theorem ord_lt_ord_iff_valuation_gt (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : v f ≠ 0)
    (hg : v g ≠ 0) : ord v f < ord v g ↔ v g < v f := by
  rw [ord_def, ord_def, neg_lt_neg_iff, WithZero.log_lt_log hg hf]

/-- **The order of a sum of summands of distinct orders.** If both summands lie outside the
valuation support and have distinct orders, the order of their sum is the smaller order. -/
theorem ord_add_eq_min_of_ord_ne (v : _root_.Valuation F ℤᵐ⁰) {f g : F}
    (hf : v f ≠ 0) (hg : v g ≠ 0) (h : ord v f ≠ ord v g) :
    ord v (f + g) = min (ord v f) (ord v g) := by
  -- Distinct orders mean distinct valuations, so the sum takes the larger valuation, whose
  -- order is the smaller one, as `-log` is antitone away from `0`.
  have hanti : AntitoneOn (fun γ : ℤᵐ⁰ ↦ -WithZero.log γ) {0}ᶜ := fun a ha b hb hab ↦
    neg_le_neg ((WithZero.log_le_log ha hb).mpr hab)
  rw [ord_def, v.map_add_of_distinct_val fun hfg ↦ h (by rw [ord_def, ord_def, hfg])]
  exact hanti.map_max hf hg

/-- The valuation of a finite sum with a strict minimum of orders: the summand of least order
dominates.  It is stated on the valuation because both
`Valuation.map_sum_ne_zero_of_forall_ord_lt` and
`Valuation.ord_sum_eq_of_forall_lt` read off from it. -/
private theorem valuation_sum_eq_of_forall_ord_lt (v : _root_.Valuation F ℤᵐ⁰) {ι : Type*}
    {s : Finset ι} {f : ι → F} {j : ι} (hj : j ∈ s) (hfj : v (f j) ≠ 0)
    (hlt : ∀ i ∈ s, i ≠ j → v (f i) ≠ 0 → ord v (f j) < ord v (f i)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  classical
  refine v.map_sum_eq_of_lt hj fun i hi ↦ ?_
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
  rcases eq_or_ne (v (f i)) 0 with h0 | h0
  · rw [h0]
    exact pos_iff_ne_zero.mpr hfj
  · exact (ord_lt_ord_iff_valuation_gt v hfj h0).mp (hlt i hi.1 hi.2 h0)

/-- A finite sum whose distinguished summand has nonzero valuation and strictly least order
among the summands with nonzero valuation lies outside the valuation support. -/
theorem map_sum_ne_zero_of_forall_ord_lt (v : _root_.Valuation F ℤᵐ⁰) {ι : Type*} {s : Finset ι}
    {f : ι → F} {j : ι} (hj : j ∈ s) (hfj : v (f j) ≠ 0)
    (hlt : ∀ i ∈ s, i ≠ j → v (f i) ≠ 0 → ord v (f j) < ord v (f i)) :
    v (∑ i ∈ s, f i) ≠ 0 := by
  rw [valuation_sum_eq_of_forall_ord_lt v hj hfj hlt]
  exact hfj

/-- **The order of a finite sum with a strict minimum**: if one summand has strictly smaller
order than each other summand with nonzero valuation, the sum has that order. This is the
`Finset.sum` form of `Valuation.ord_add_eq_min_of_ord_ne`; only the distinguished summand
must have nonzero valuation. Summands in the valuation support impose no order condition. -/
theorem ord_sum_eq_of_forall_lt (v : _root_.Valuation F ℤᵐ⁰) {ι : Type*} {s : Finset ι}
    {f : ι → F} {j : ι} (hj : j ∈ s) (hfj : v (f j) ≠ 0)
    (hlt : ∀ i ∈ s, i ≠ j → v (f i) ≠ 0 → ord v (f j) < ord v (f i)) :
    ord v (∑ i ∈ s, f i) = ord v (f j) := by
  rw [ord_def, ord_def, valuation_sum_eq_of_forall_ord_lt v hj hfj hlt]

/-- **Equivalent valuations agree on which elements have nonnegative order.** Equivalence
identifies the valuation support and preserves comparison with `1` away from the support.

Only equivalence is needed; neither valuation has to be surjective. -/
theorem IsEquiv.ord_nonneg_iff {v w : _root_.Valuation F ℤᵐ⁰} (h : v.IsEquiv w)
    (f : F) : 0 ≤ ord v f ↔ 0 ≤ ord w f := by
  rcases eq_or_ne (v f) 0 with hf | hf
  · simp [ord_def, hf, h.eq_zero.mp hf]
  have hw : w f ≠ 0 := h.eq_zero.ne.mp hf
  simp only [ord_def, neg_nonneg, WithZero.log_le_iff_le_exp hf,
    WithZero.log_le_iff_le_exp hw, WithZero.exp_zero]
  exact h.le_one_iff_le_one

/-- **Equivalent valuations agree on which elements have order zero.** Outside their common
support, order zero says the valuation is `1`; within the support, both orders have junk value
zero.

Only equivalence is needed; neither valuation has to be surjective. -/
theorem IsEquiv.ord_eq_zero_iff {v w : _root_.Valuation F ℤᵐ⁰} (h : v.IsEquiv w)
    (f : F) : ord v f = 0 ↔ ord w f = 0 := by
  rcases eq_or_ne (v f) 0 with hf | hf
  · simp [ord_def, hf, h.eq_zero.mp hf]
  have hw : w f ≠ 0 := h.eq_zero.ne.mp hf
  simpa only [ord_eq_iff_valuation_eq_exp_neg v hf,
    ord_eq_iff_valuation_eq_exp_neg w hw, neg_zero, WithZero.exp_zero]
    using h.eq_one_iff_eq_one

end Ring

section CommRing

variable {F : Type*} [CommRing F]

theorem ord_prod (v : _root_.Valuation F ℤᵐ⁰) {ι : Type*} (s : Finset ι) {f : ι → F}
    (hf : ∀ i ∈ s, v (f i) ≠ 0) : ord v (∏ i ∈ s, f i) = ∑ i ∈ s, ord v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul v (hf a (Finset.mem_insert_self a s))
        (by simpa only [map_prod] using
          Finset.prod_ne_zero_iff.mpr fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

end CommRing

section DivisionRing

variable {F : Type*} [DivisionRing F]

@[simp]
theorem ord_inv (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ord v f⁻¹ = -ord v f := by
  simp [ord_def, map_inv₀, WithZero.log_inv]

@[simp]
theorem ord_zpow (v : _root_.Valuation F ℤᵐ⁰) (f : F) (n : ℤ) :
    ord v (f ^ n) = n * ord v f := by
  simp [ord_def, map_zpow₀, WithZero.log_zpow, mul_neg]

theorem ord_div (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord v (f / g) = ord v f - ord v g := by
  rw [div_eq_mul_inv, ord_mul v (v.ne_zero_iff.mpr hf) (v.ne_zero_iff.mpr (inv_ne_zero hg)),
    ord_inv, sub_eq_add_neg]

/-- The order of a quotient by an integral power. -/
theorem ord_div_zpow (v : _root_.Valuation F ℤᵐ⁰) {f t : F} (hf : f ≠ 0) (ht : t ≠ 0)
    (n : ℤ) : ord v (f / t ^ n) = ord v f - n * ord v t := by
  rw [ord_div v hf (zpow_ne_zero _ ht), ord_zpow]

/-- **A valuation that takes the value `exp (-1)` is surjective onto `ℤᵐ⁰`**: `exp (-1)` generates
the units of `ℤᵐ⁰`, and on a division ring a valuation attaining a generator is surjective. -/
theorem surjective_of_map_eq_exp_neg_one (v : _root_.Valuation F ℤᵐ⁰) {t : F}
    (ht : v t = WithZero.exp (-1)) : Function.Surjective v :=
  (v : F →*₀ ℤᵐ⁰).surjective_of_mem_range_of_zpowers_eq_top ⟨t, ht⟩ zpowers_mk0_exp_neg_one

end DivisionRing

section Field

variable {F : Type*} [Field F]

theorem mem_valuationSubring_iff_ord_nonneg (v : _root_.Valuation F ℤᵐ⁰) {f : F} :
    f ∈ v.valuationSubring ↔ 0 ≤ ord v f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [_root_.Valuation.mem_valuationSubring_iff,
      valuation_eq_exp_neg_ord v (v.ne_zero_iff.mpr hf), ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

/-- For a `ℤᵐ⁰`-valued valuation, any integer of valuation `exp (-1)` generates the maximal ideal
of the valuation ring. -/
theorem maximalIdeal_eq_span_of_map_eq_exp_neg_one (v : _root_.Valuation F ℤᵐ⁰)
    {π : v.valuationSubring} (hπ : v π = WithZero.exp (-1)) :
    IsLocalRing.maximalIdeal v.valuationSubring = Ideal.span {π} := by
  have : v.IsNontrivial := (isNontrivial_iff_exists_lt_one v).mpr
    ⟨π, by simp [← v.ne_zero_iff, hπ], by simp [hπ]⟩
  refine IsUniformizer.is_generator ?_
  rw [IsUniformizer.iff,
    IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range (v := v) ⟨(π : F), hπ⟩,
    Units.val_mk0, hπ]

theorem isUnit_iff_ord_eq_zero (v : _root_.Valuation F ℤᵐ⁰) {x : v.valuationSubring}
    (hx : (x : F) ≠ 0) : IsUnit x ↔ ord v (x : F) = 0 := by
  rw [_root_.Valuation.Integers.isUnit_iff_valuation_eq_one
      (_root_.Valuation.valuationSubring.integers v),
    Algebra.algebraMap_ofSubsemiring_apply,
    ord_eq_iff_valuation_eq_exp_neg v (v.ne_zero_iff.mpr hx),
    neg_zero, WithZero.exp_zero]

/-- A field unit belongs to the valuation-ring unit subgroup exactly when its order is zero. -/
theorem mem_unitGroup_iff_ord_eq_zero (v : _root_.Valuation F ℤᵐ⁰) (f : Fˣ) :
    f ∈ v.valuationSubring.unitGroup ↔ v.ord (f : F) = 0 := by
  rw [mem_unitGroup_iff, ord_eq_iff_valuation_eq_exp_neg v (v.ne_zero_iff.mpr f.ne_zero)]
  simp

/-- Multiplication by a valuation-ring unit does not change the order. -/
@[simp]
theorem ord_mul_coe_unitGroup (v : _root_.Valuation F ℤᵐ⁰) (f : F)
    (u : v.valuationSubring.unitGroup) : ord v (f * (u : Fˣ)) = ord v f := by
  have hu : v (u : Fˣ) = 1 := (mem_unitGroup_iff F v (u : Fˣ)).mp u.property
  simp [ord_def, map_mul, hu]

theorem mem_maximalIdeal_iff_ord_pos (v : _root_.Valuation F ℤᵐ⁰)
    {f : v.valuationSubring} (hf : (f : F) ≠ 0) :
    f ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ 0 < ord v (f : F) := by
  rw [_root_.Valuation.mem_maximalIdeal_iff, valuation_eq_exp_neg_ord v (v.ne_zero_iff.mpr hf),
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

end Field

end Valuation
