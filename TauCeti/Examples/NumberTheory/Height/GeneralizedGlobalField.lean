/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import TauCeti.NumberTheory.Height.GeneralizedGlobalField

/-!
# Tests of generalized global fields

* Over `ℚ`, at `a = 2`, the archimedean factor of the product formula is `2` and the
  nonarchimedean factor is `1 / 2`, with product `2 · 1/2 = 1`.
* `ℚ(i)`, here any `4`-th cyclotomic extension of `ℚ`, has a single archimedean absolute
  value, whose completion is `ℂ`, counted twice.
* Omitting the archimedean place of `ℚ` breaks the product formula at `2`: an admissible family
  on `ℚ` whose nonarchimedean members are the finite places of `ℚ` has an archimedean member.
-/

public section

open Height AdmissibleAbsValues NumberField

namespace TauCeti.Examples.GeneralizedGlobalField

/-- Over `ℚ`, at `a = 2`, the archimedean factor of the product formula is `2`: `ℚ` has one
archimedean absolute value, the real one, counted once. -/
theorem prod_archAbsVal_rat_two : (archAbsVal.map (· (2 : ℚ))).prod = 2 := by
  rw [prod_archAbsVal_eq]
  exact (InfinitePlace.prod_eq_abs_norm (2 : ℚ)).trans (by simp [Algebra.norm_self])

/-- Over `ℚ`, at `a = 2`, the nonarchimedean factor of the product formula is `1 / 2`. -/
theorem finprod_nonarchAbsVal_rat_two :
    ∏ᶠ v : nonarchAbsVal, v.val (2 : ℚ) = 1 / 2 := by
  rw [prod_nonarchAbsVal_eq (· (2 : ℚ))]
  exact (FinitePlace.prod_eq_inv_abs_norm two_ne_zero).trans (by simp [Algebra.norm_self])

/-- **Check.** Over `ℚ`, at `a = 2`, the product formula reads `2 · 1/2 = 1`. -/
example : (archAbsVal.map (· (2 : ℚ))).prod = 2 ∧
    ∏ᶠ v : nonarchAbsVal, v.val (2 : ℚ) = 1 / 2 ∧ (2 : ℝ) * (1 / 2) = 1 :=
  ⟨prod_archAbsVal_rat_two, finprod_nonarchAbsVal_rat_two, by norm_num⟩

section Gaussian

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- **Check.** `ℚ(i)`, a `4`-th cyclotomic extension of `ℚ`, has one archimedean absolute value,
whose completion is `ℂ`, and it occurs twice in `archAbsVal`. -/
theorem exists_archAbsVal_eq_replicate_two_of_isCyclotomicExtension_four :
    ∃ v : AbsoluteValue K ℝ,
      archAbsVal = Multiset.replicate 2 v ∧ Nonempty (v.Completion ≃+* ℂ) := by
  have hc := IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 4 K
  have hr := IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K (n := 4) (by norm_num)
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc]
    decide
  obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 hcard
  have := IsCyclotomicExtension.Rat.isTotallyComplex K (n := 4) (by norm_num)
  have hwc : w.IsComplex := IsTotallyComplex.isComplex w
  refine ⟨w.val, Multiset.eq_replicate.2 ⟨?_, fun b hb ↦ ?_⟩,
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc⟩⟩
  · have h : totalWeight K = 2 := by
      rw [totalWeight_eq_sum_mult, Fintype.sum_eq_single w fun w' h ↦ (h (hw w')).elim,
        hwc.mult_eq_two]
    simpa only [totalWeight] using h
  · obtain ⟨w', rfl⟩ := (isInfinitePlace_iff b).1 (mem_multisetInfinitePlace.1 hb)
    rw [hw w']

end Gaussian

/-- **Check.** The archimedean place of `ℚ` cannot be omitted: an admissible family of absolute
values on `ℚ` whose nonarchimedean members are the finite places of `ℚ` has an archimedean member,
because at `2` the nonarchimedean factor alone is `1 / 2 ≠ 1`. -/
theorem archAbsVal_ne_zero_of_nonarchAbsVal_eq_setOf_isFinitePlace (I : AdmissibleAbsValues ℚ)
    (hn : I.nonarchAbsVal = {v | IsFinitePlace v}) : I.archAbsVal ≠ 0 := by
  intro ha
  have h := I.product_formula (x := 2) two_ne_zero
  rw [ha, hn, Multiset.map_zero, Multiset.prod_zero, one_mul] at h
  have h' := finprod_nonarchAbsVal_rat_two
  -- The number-field instance `NumberField.instAdmissibleAbsValues` defines `nonarchAbsVal` as
  -- the set of finite places, so `h'` is a statement about the same finite product as `h`.
  change ∏ᶠ v : {v : AbsoluteValue ℚ ℝ | IsFinitePlace v}, v.val (2 : ℚ) = 1 / 2 at h'
  rw [h'] at h
  norm_num at h

end TauCeti.Examples.GeneralizedGlobalField
