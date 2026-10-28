/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Additive orders of discrete valuations

This file packages the additive order attached to a `ℤᵐ⁰`-valued valuation and develops the
facts that do not depend on a choice of constant field. The convention is
`ord_v f = -log (v f)`, so a uniformizer of a surjective valuation has order one.
The definition, characteristic lemmas, multiplication and addition laws apply to valuations on
rings, using nonzero valuation values to exclude the support where necessary. Finite products
require commutativity. Equivalence comparisons also apply to rings. Inverse and quotient laws and
equality of equivalent normalized valuations are stated on division rings; valuation-subring and
discrete-valuation-ring results are stated on fields.
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

/-- **A surjective valuation onto `ℤᵐ⁰` is nontrivial.** Surjectivity is the form the hypothesis
usually arrives in — a `Place` carries it by definition — while the results about order and
normalization are stated for a nontrivial valuation, and this converts one to the other. -/
theorem isNontrivial_of_surjective {R : Type*} [Ring R] {v : _root_.Valuation R ℤᵐ⁰}
    (hv : Function.Surjective v) : v.IsNontrivial where
  exists_val_nontrivial := by
    obtain ⟨x, hx⟩ := hv (WithZero.exp (-1))
    exact ⟨x, by simp [hx], by simp [hx]⟩

theorem ord_surjective (v : _root_.Valuation F ℤᵐ⁰) (hv : Function.Surjective v) :
    Function.Surjective (ord v) := fun n => by
  obtain ⟨f, hf⟩ := hv (WithZero.exp (-n))
  exact ⟨f, by simp [ord_def, hf]⟩

/-- Surjectivity of `v` makes its value group the whole of `ℤᵐ⁰`. -/
theorem valueGroup_eq_top_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : v.valueGroup = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun γ => mem_valueGroup _ (hv γ)

/-- A surjective `ℤᵐ⁰`-valued valuation has nontrivial value group. -/
theorem nontrivial_valueGroup_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : Nontrivial v.valueGroup := by
  rw [valueGroup_eq_top_of_surjective v hv]
  exact (Subgroup.topEquiv (G := ℤᵐ⁰ˣ)).toEquiv.nontrivial

/-- Uniformizers of a surjective `ℤᵐ⁰`-valuation are exactly the elements of order one. -/
theorem isUniformizer_iff_ord_eq_one_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    [Nontrivial v.valueGroup] (hv : Function.Surjective v) {t : F} :
    v.IsUniformizer t ↔ ord v t = 1 := by
  rw [_root_.Valuation.IsUniformizer,
    _root_.Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective hv, Units.val_mk0]
  constructor
  · intro ht
    simp [ord_def, ht]
  · intro ht
    have ht0 : v t ≠ 0 := fun h => by simp [ord_def, h] at ht
    rw [ord_def, neg_eq_iff_eq_neg] at ht
    rw [← WithZero.exp_log ht0, ht]

theorem exists_isUniformizer_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    [Nontrivial v.valueGroup] (hv : Function.Surjective v) :
    ∃ t : F, v.IsUniformizer t := by
  obtain ⟨t, ht⟩ := ord_surjective v hv 1
  exact ⟨t, (isUniformizer_iff_ord_eq_one_of_surjective v hv).mpr ht⟩

/-- Translation between the multiplicative valuation and its additive order. -/
theorem valuation_eq_exp_neg_ord (v : _root_.Valuation F ℤᵐ⁰) {f : F} (hf : v f ≠ 0) :
    v f = WithZero.exp (-ord v f) := by
  rw [ord_def, neg_neg, WithZero.exp_log hf]

theorem ord_eq_iff_valuation_eq_exp_neg (v : _root_.Valuation F ℤᵐ⁰) {f : F}
    (hf : v f ≠ 0) {n : ℤ} : ord v f = n ↔ v f = WithZero.exp (-n) := by
  rw [valuation_eq_exp_neg_ord v hf, WithZero.exp_inj, neg_inj]

theorem ord_mul (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : v f ≠ 0) (hg : v g ≠ 0) :
    ord v (f * g) = ord v f + ord v g := by
  rw [ord_def, ord_def, ord_def, map_mul, WithZero.log_mul hf hg]
  ring

private theorem exp_max (a b : ℤ) :
    max (WithZero.exp a) (WithZero.exp b) = WithZero.exp (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (WithZero.exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (WithZero.exp_le_exp.mpr h)]

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
  have hadd := v.map_add f g
  rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord v hg,
    valuation_eq_exp_neg_ord v h, exp_max, WithZero.exp_le_exp] at hadd
  omega

/-- The strict triangle inequality for an additive order. -/
theorem ord_add_eq_min_of_ord_ne (v : _root_.Valuation F ℤᵐ⁰) {f g : F}
    (hf : v f ≠ 0) (hg : v g ≠ 0) (h : ord v f ≠ ord v g) :
    ord v (f + g) = min (ord v f) (ord v g) := by
  have hne : v f ≠ v g := by
    rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord v hg]
    simpa using h
  have hsum := v.map_add_of_distinct_val hne
  have hfg : v (f + g) ≠ 0 := by
    rw [hsum]
    exact ne_of_gt (lt_max_of_lt_left (zero_lt_iff.mpr hf))
  rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord v hg,
    valuation_eq_exp_neg_ord v hfg, exp_max, WithZero.exp_inj] at hsum
  omega

/-- The order reverses the valuation: an element of larger order has smaller valuation.  The
hypotheses exclude the valuation support, where the order has its junk value. -/
theorem ord_lt_ord_iff_valuation_gt (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : v f ≠ 0)
    (hg : v g ≠ 0) : ord v f < ord v g ↔ v g < v f := by
  rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord v hg, WithZero.exp_lt_exp]
  omega

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
    exact zero_lt_iff.mpr hfj
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

/-- **A valuation that takes the value `exp (-1)` is surjective onto `ℤᵐ⁰`**: the integer powers
of an element of value `exp (-1)` take every nonzero value. -/
theorem surjective_of_map_eq_exp_neg_one (v : _root_.Valuation F ℤᵐ⁰) {t : F}
    (ht : v t = WithZero.exp (-1)) : Function.Surjective v := by
  intro x
  induction x using WithZero.expRecOn with
  | zero => exact ⟨0, map_zero v⟩
  | exp n => exact ⟨t ^ (-n), by rw [map_zpow₀, ht, ← WithZero.exp_zsmul, smul_eq_mul, neg_mul_neg,
      mul_one]⟩

/-- Two equivalent normalized `ℤᵐ⁰`-valuations are equal. -/
theorem eq_of_isEquiv_of_surjective {v w : _root_.Valuation F ℤᵐ⁰}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w := by
  have hmem := h.ord_nonneg_iff
  have hzero := h.ord_eq_zero_iff
  -- Choose order-one elements for both normalized valuations and compare their orders.
  obtain ⟨t, ht⟩ := ord_surjective v hv 1
  obtain ⟨s, hs⟩ := ord_surjective w hw 1
  have ht0 : t ≠ 0 := fun h' => by simp [h'] at ht
  have hs0 : s ≠ 0 := fun h' => by simp [h'] at hs
  have htW : 1 ≤ ord w t := by
    have h₁ := (hmem t).mp (by omega)
    have h₂ := (hzero t).not.mp (by omega)
    omega
  have hsV : 1 ≤ ord v s := by
    have h₁ := (hmem s).mpr (by omega)
    have h₂ := (hzero s).not.mpr (by omega)
    omega
  -- Dividing `s` by the appropriate power of `t` has order zero for both valuations;
  -- this forces the chosen `v`-uniformizer `t` to have `w`-order one.
  have hone : ord w t = 1 := by
    have hst : ord v (s / t ^ ord v s) = 0 := by
      rw [ord_div_zpow v hs0 ht0, ht]
      ring
    have hW := (hzero _).mp hst
    rw [ord_div_zpow w hs0 ht0, hs] at hW
    nlinarith [htW, hsV]
  -- Removing the `v`-order of an arbitrary nonzero element now shows that both orders,
  -- and hence both valuations, agree pointwise.
  refine _root_.Valuation.ext fun f => ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have key : ord w f = ord v f := by
    have h₀ : ord v (f / t ^ ord v f) = 0 := by
      rw [ord_div_zpow v hf ht0, ht]
      ring
    have hW := (hzero _).mp h₀
    rw [ord_div_zpow w hf ht0, hone] at hW
    omega
  rw [valuation_eq_exp_neg_ord v (v.ne_zero_iff.mpr hf),
    valuation_eq_exp_neg_ord w (w.ne_zero_iff.mpr hf), key]

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

/-- The valuation ring of a surjective `ℤᵐ⁰`-valued valuation is a DVR. -/
theorem valuationSubring_isDiscreteValuationRing_of_surjective
    (v : _root_.Valuation F ℤᵐ⁰) (hv : Function.Surjective v) :
    IsDiscreteValuationRing v.valuationSubring := by
  let _ := nontrivial_valueGroup_of_surjective v hv
  exact _root_.Valuation.valuationSubring_isDiscreteValuationRing v

theorem isUnit_iff_ord_eq_zero (v : _root_.Valuation F ℤᵐ⁰) {x : v.valuationSubring}
    (hx : (x : F) ≠ 0) : IsUnit x ↔ ord v (x : F) = 0 := by
  rw [_root_.Valuation.Integers.isUnit_iff_valuation_eq_one
      (_root_.Valuation.valuationSubring.integers v),
    Algebra.algebraMap_ofSubsemiring_apply,
    ord_eq_iff_valuation_eq_exp_neg v (v.ne_zero_iff.mpr hx),
    neg_zero, WithZero.exp_zero]

/-- Existence half of the uniformizer expansion for a surjective valuation. -/
theorem exists_eq_zpow_mul_unit_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    [Nontrivial v.valueGroup] (hv : Function.Surjective v)
    {t : F} (ht : v.IsUniformizer t) {f : F} (hf : f ≠ 0) :
    ∃ u : v.valuationSubringˣ, f = t ^ ord v f * (u : F) := by
  have ht1 : ord v t = 1 := (isUniformizer_iff_ord_eq_one_of_surjective v hv).mp ht
  have ht0 : t ≠ 0 := fun h => by simp [h] at ht1
  have hne : f / t ^ ord v f ≠ 0 := div_ne_zero hf (zpow_ne_zero _ ht0)
  have hord : ord v (f / t ^ ord v f) = 0 := by
    rw [ord_div_zpow v hf ht0, ht1]
    ring
  have hmem : f / t ^ ord v f ∈ v.valuationSubring :=
    (mem_valuationSubring_iff_ord_nonneg v).mpr hord.ge
  have hunit : IsUnit (⟨_, hmem⟩ : v.valuationSubring) :=
    (isUnit_iff_ord_eq_zero v hne).mpr hord
  refine ⟨hunit.unit, ?_⟩
  have hu : ((hunit.unit : v.valuationSubring) : F) = f / t ^ ord v f := by
    rw [IsUnit.unit_spec]
  rw [hu]
  field_simp

theorem mem_maximalIdeal_iff_ord_pos (v : _root_.Valuation F ℤᵐ⁰)
    {f : v.valuationSubring} (hf : (f : F) ≠ 0) :
    f ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ 0 < ord v (f : F) := by
  rw [_root_.Valuation.mem_maximalIdeal_iff, valuation_eq_exp_neg_ord v (v.ne_zero_iff.mpr hf),
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem valuationSubring_ne_top_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : v.valuationSubring ≠ ⊤ := by
  obtain ⟨t, ht⟩ := ord_surjective v hv 1
  intro h
  have ht' : t⁻¹ ∈ v.valuationSubring := h ▸ ValuationSubring.mem_top _
  rw [mem_valuationSubring_iff_ord_nonneg v, ord_inv, ht] at ht'
  omega

end Field

end Valuation
