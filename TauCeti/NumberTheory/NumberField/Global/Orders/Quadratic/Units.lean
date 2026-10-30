/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.IntAddMulOrder
public import TauCeti.NumberTheory.NumberField.Quadratic.Units
import Mathlib.NumberTheory.NumberField.Norm
import TauCeti.RingTheory.Norm.Quadratic
import TauCeti.RingTheory.RootsOfUnity.FourthAndSixth

/-!
# Units of the order of conductor `f` in an imaginary quadratic field

Let `K` be a quadratic field and `O_f = ℤ + f 𝓞 K` its order of conductor `f`. For `f > 1` the
only roots of unity of `K` lying in `O_f` are `±1`. Write a root of unity `ζ ∉ {±1}` of `K` as
`ζ = a + f y` with `a ∈ ℤ` and `y ∈ 𝓞 K`. Its order is `3`, `4` or `6`, so `ζ` is a root of
`X² + t X + 1` with `t ∈ {1, 0, -1}`, and the discriminant `t² - 4` of that polynomial equals
`f²` times the discriminant `Tr(y)² - 4 N(y)` of `y`. As `t² - 4` is `-3` or `-4`, this forces
`f = 1`: for `f = 2` and `t = 0` it would give `Tr(y)² + 1 = 4 N(y)`, which is impossible
modulo `4`.

Every unit of an imaginary quadratic field is a root of unity, so the image of the units of
`O_f` in `(𝓞 K)ˣ` is `{1, -1}` when `f > 1`. Its index `[(𝓞 K)ˣ : O_fˣ]` is therefore half the
number `w` of roots of unity of `K`: it is `3` for discriminant `-3`, `2` for discriminant `-4`
and `1` otherwise, and it is `1` for `f = 1`. This is the unit index in the class number formula
`h(O_f) = h_K f / [(𝓞 K)ˣ : O_fˣ] · ∏_{p ∣ f} (1 - (D / p) / p)` for orders.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.eq_one_or_eq_neg_one_of_mem_intAddMulOrder`: in a
  quadratic field, a root of unity in `ℤ + f 𝓞 K` with `f > 1` is `±1`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.coe_range_unitsMap_intAddMulOrder`: in an
  imaginary quadratic field, the units of `ℤ + f 𝓞 K` with `f > 1` are `±1`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.index_range_unitsMap_intAddMulOrder_mul_two`: for
  `f > 1`, twice the unit index `[(𝓞 K)ˣ : O_fˣ]` is the number of roots of unity of `K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.index_range_unitsMap_intAddMulOrder`: the unit
  index is `1` for `f = 1`, and for `f > 1` it is `2` if `disc K = -4`, `3` if `disc K = -3` and
  `1` otherwise.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.24 (the class number formula for
  orders, in which this unit index appears).
-/

public section

open NumberField NumberField.Units Module
open TauCeti.NumberField.Units (torsionOrder_eq_two_or_four_or_six
  torsion_eq_top_of_isTotallyComplex torsionOrder_eq_of_finrank_eq_two)
open scoped NumberField

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {f : ℕ} [NeZero f]

/-- If an algebraic integer `ζ ∈ ℤ + f 𝓞 K` of a quadratic field is a root of `X² + t X + 1`
with `t² < 4`, then `f = 1`. Writing `ζ = a + f y`, the discriminant `t² - 4` of `X² + t X + 1`
is `f²` times the discriminant `Tr(y)² - 4 N(y)` of `y`. -/
private theorem eq_one_of_mem_intAddMulOrder_of_sq_add_mul_add_one (hK : finrank ℚ K = 2)
    {ζ : 𝓞 K} (hζ : ζ ∈ (intAddMulOrder K f).toRingOfIntegers) {t : ℤ} (ht : t ^ 2 < 4)
    (h : (ζ : K) ^ 2 + t * (ζ : K) + 1 = 0) : f = 1 := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  obtain ⟨a, y, hy⟩ := mem_toRingOfIntegers_intAddMulOrder.mp hζ
  -- `ζ` is irrational, since `X² + t X + 1` has negative discriminant.
  have hζℚ : (ζ : K) ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, hq⟩
    have hq' : q ^ 2 + t * q + 1 = 0 := by
      apply (algebraMap ℚ K).injective
      rw [← hq] at h
      simpa using h
    have ht' : (t : ℚ) ^ 2 < 4 := by exact_mod_cast ht
    nlinarith [sq_nonneg (2 * q + t)]
  have h' : (ζ : K) ^ 2 + algebraMap ℚ K t * (ζ : K) + algebraMap ℚ K 1 = 0 := by simpa using h
  have htr := Algebra.IsQuadraticExtension.trace_eq_neg_of_sq_add_mul_add_eq_zero hζℚ h'
  have hn := Algebra.IsQuadraticExtension.norm_eq_of_sq_add_mul_add_eq_zero hζℚ h'
  have hζK : (ζ : K) = algebraMap ℚ K a + algebraMap ℚ K f * (y : K) := by
    rw [hy]
    simp
  rw [hζK, Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul,
    ← Algebra.coe_trace_int] at htr
  rw [hζK, Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul,
    ← Algebra.coe_trace_int, ← Algebra.coe_norm_int] at hn
  set T := Algebra.trace ℤ (𝓞 K) y
  set N := Algebra.norm ℤ y
  have htr' : (f : ℤ) * T + 2 * a = -t := by exact_mod_cast htr
  have hn' : a ^ 2 + f * a * T + f ^ 2 * N = 1 := by exact_mod_cast hn
  -- The two discriminants differ by the factor `f²`.
  have key : (f : ℤ) ^ 2 * (4 * N - T ^ 2) = 4 - t ^ 2 := by
    linear_combination 4 * hn' + (t - f * T - 2 * a) * htr'
  by_contra hf
  have hf2 : (2 : ℤ) ≤ f := by
    have := NeZero.ne f
    omega
  have hk : 4 * N - T ^ 2 = 1 := by
    have hk0 : 0 < 4 * N - T ^ 2 := by
      by_contra hk0
      nlinarith [sq_nonneg (f : ℤ)]
    nlinarith
  -- `T² + 1 = 4 N` has no solution modulo `4`.
  have h4 := congrArg (Int.cast : ℤ → ZMod 4) (show T ^ 2 + 1 = 4 * N by linarith)
  push_cast at h4
  rw [show (4 : ZMod 4) = 0 by decide, zero_mul] at h4
  generalize (T : ZMod 4) = x at h4
  revert x
  decide

/-- **Roots of unity in `ℤ + f 𝓞 K`.** In a quadratic field, a root of unity lying in the order
`ℤ + f 𝓞 K` of conductor `f > 1` is `1` or `-1`. -/
theorem eq_one_or_eq_neg_one_of_mem_intAddMulOrder (hK : finrank ℚ K = 2) (hf : 1 < f)
    {u : (𝓞 K)ˣ} (hu : u ∈ torsion K)
    (huf : (u : 𝓞 K) ∈ (intAddMulOrder K f).toRingOfIntegers) : u = 1 ∨ u = -1 := by
  have hdvd : orderOf u ∣ torsionOrder K := by
    calc orderOf u = orderOf (⟨u, hu⟩ : torsion K) :=
          orderOf_injective (torsion K).subtype Subtype.coe_injective ⟨u, hu⟩
      _ ∣ Nat.card (torsion K) := orderOf_dvd_natCard _
  have hζ : IsPrimitiveRoot ((u : 𝓞 K) : K) (orderOf u) :=
    (IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf u)).map_of_injective
      (f := algebraMap (𝓞 K) K) RingOfIntegers.coe_injective
  have hpos : 0 < orderOf u := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero
    (torsionOrder_ne_zero K))
  have hle : orderOf u ≤ 6 := by
    rcases torsionOrder_eq_two_or_four_or_six hK.le with h | h | h <;> rw [h] at hdvd <;>
      exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num)
  have hf' : f ≠ 1 := hf.ne'
  interval_cases h : orderOf u
  · exact Or.inl (orderOf_eq_one_iff.mp h)
  · refine Or.inr (Units.ext (RingOfIntegers.coe_injective ?_))
    simpa using hζ.eq_neg_one_of_two_right
  · refine absurd (eq_one_of_mem_intAddMulOrder_of_sq_add_mul_add_one hK huf (t := 1)
      (by norm_num) ?_) hf'
    have := hζ.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one] at this
    push_cast
    linear_combination this
  · refine absurd (eq_one_of_mem_intAddMulOrder_of_sq_add_mul_add_one hK huf (t := 0)
      (by norm_num) ?_) hf'
    have := (hζ.pow (by norm_num) (show 4 = 2 * 2 by rfl)).eq_neg_one_of_two_right
    push_cast
    linear_combination this
  · rcases torsionOrder_eq_two_or_four_or_six hK.le with h' | h' | h' <;>
      rw [h'] at hdvd <;> norm_num at hdvd
  · refine absurd (eq_one_of_mem_intAddMulOrder_of_sq_add_mul_add_one hK huf (t := -1)
      (by norm_num) ?_) hf'
    push_cast
    linear_combination TauCeti.isPrimitiveRoot_six_iff.mp hζ

/-- **The units of `ℤ + f 𝓞 K` are `±1`.** In an imaginary quadratic field, the image of the units
of the order of conductor `f > 1` in `(𝓞 K)ˣ` is `{1, -1}`. -/
theorem coe_range_unitsMap_intAddMulOrder [IsTotallyComplex K] (hK : finrank ℚ K = 2)
    (hf : 1 < f) :
    ((Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
      (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range : Set (𝓞 K)ˣ) = {1, -1} := by
  ext u
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact eq_one_or_eq_neg_one_of_mem_intAddMulOrder hK hf
      (torsion_eq_top_of_isTotallyComplex hK ▸ Subgroup.mem_top _)
      (w : (intAddMulOrder K f).toRingOfIntegers).2
  · rintro (rfl | rfl)
    · exact ⟨1, map_one _⟩
    · exact ⟨-1, Units.ext (by simp)⟩

/-- **The unit index of `ℤ + f 𝓞 K` is `w / 2`.** In an imaginary quadratic field with `w` roots
of unity, the units of the order of conductor `f > 1` have index `w / 2` in `(𝓞 K)ˣ`. -/
theorem index_range_unitsMap_intAddMulOrder_mul_two [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (hf : 1 < f) :
    (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
      (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index * 2 = torsionOrder K := by
  have hne : (1 : (𝓞 K)ˣ) ≠ -1 := by
    intro h
    have := congrArg (fun v : (𝓞 K)ˣ ↦ ((v : 𝓞 K) : K)) h
    norm_num at this
  have hcard : Nat.card (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
      (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range = 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, coe_range_unitsMap_intAddMulOrder hK hf,
      Set.ncard_pair hne]
  rw [← hcard, Subgroup.index_mul_card, torsionOrder, torsion_eq_top_of_isTotallyComplex hK,
    Subgroup.card_top]

/-- **The unit index of the order of conductor `f`.** In an imaginary quadratic field `K`, the
index `[(𝓞 K)ˣ : O_fˣ]` of the units of `O_f = ℤ + f 𝓞 K` is `1` for `f = 1`; for `f > 1` it is
`2` if `disc K = -4`, `3` if `disc K = -3`, and `1` otherwise. -/
theorem index_range_unitsMap_intAddMulOrder [IsTotallyComplex K] (hK : finrank ℚ K = 2) :
    (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
      (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index =
      if f = 1 then 1
      else if NumberField.discr K = -4 then 2 else if NumberField.discr K = -3 then 3 else 1 := by
  split_ifs with hf h4 h3
  · subst hf
    refine Subgroup.index_eq_one.mpr (MonoidHom.range_eq_top.mpr fun u ↦ ?_)
    have hmem (x : 𝓞 K) : x ∈ (intAddMulOrder K 1).toRingOfIntegers :=
      mem_toRingOfIntegers_intAddMulOrder.mpr ⟨0, x, by simp⟩
    exact ⟨⟨⟨u, hmem _⟩, ⟨_, hmem (u⁻¹ : (𝓞 K)ˣ)⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩,
      Units.ext rfl⟩
  all_goals
    have hf' : 1 < f := by
      have := NeZero.ne f
      omega
    have := index_range_unitsMap_intAddMulOrder_mul_two hK hf'
    rw [torsionOrder_eq_of_finrank_eq_two hK] at this
    split_ifs at this
    omega

end TauCeti.GlobalNumberFields.NumberFieldOrder
