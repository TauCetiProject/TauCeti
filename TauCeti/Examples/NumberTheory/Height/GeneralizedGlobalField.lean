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
* Omitting the archimedean place of `ℚ` breaks the product formula at `2`: no admissible family on
  `ℚ` has no archimedean members and the finite places of `ℚ` as nonarchimedean members.
-/

public section

open Height AdmissibleAbsValues NumberField

namespace TauCeti.Examples.GeneralizedGlobalField

/-- Every infinite place of a field takes the value `2` at `2`. -/
theorem infinitePlace_apply_two {K : Type*} [Field K] (w : InfinitePlace K) :
    w (2 : K) = 2 := by
  rw [← w.norm_embedding_eq, map_ofNat]
  simp

/-- Over `ℚ`, at `a = 2`, the archimedean factor of the product formula is `2`: `ℚ` has one
archimedean absolute value, the real one, counted once. -/
theorem prod_archAbsVal_rat_two : (archAbsVal.map (· (2 : ℚ))).prod = 2 := by
  rw [prod_archAbsVal_eq, Fintype.prod_unique]
  set w : InfinitePlace ℚ := default
  have hw : w.IsReal := by
    rw [InfinitePlace.isReal_iff]
    exact ComplexEmbedding.isReal_iff.2 (Subsingleton.elim _ _)
  rw [hw.mult_eq_one, pow_one]
  exact infinitePlace_apply_two w

/-- Over `ℚ`, at `a = 2`, the nonarchimedean factor of the product formula is `1 / 2`. -/
theorem finprod_nonarchAbsVal_rat_two :
    ∏ᶠ v : nonarchAbsVal, v.val (2 : ℚ) = 1 / 2 := by
  have h := product_formula (K := ℚ) (x := 2) two_ne_zero
  rw [prod_archAbsVal_rat_two] at h
  rw [eq_div_iff two_ne_zero, mul_comm, h]

/-- **Check.** Over `ℚ`, at `a = 2`, the product formula reads `2 · 1/2 = 1`. -/
example : (archAbsVal.map (· (2 : ℚ))).prod = 2 ∧
    ∏ᶠ v : nonarchAbsVal, v.val (2 : ℚ) = 1 / 2 ∧ (2 : ℝ) * (1 / 2) = 1 :=
  ⟨prod_archAbsVal_rat_two, finprod_nonarchAbsVal_rat_two, by norm_num⟩

section Gaussian

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- `ℚ(i)`, a `4`-th cyclotomic extension of `ℚ`, has exactly one infinite place, and it is
complex. -/
theorem exists_eq_isComplex_of_isCyclotomicExtension_four :
    ∃ w : InfinitePlace K, (∀ w', w' = w) ∧ w.IsComplex := by
  have hc := IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 4 K
  have hr := IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K (n := 4) (by norm_num)
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc]
    decide
  obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 hcard
  refine ⟨w, hw, ?_⟩
  have := IsCyclotomicExtension.Rat.isTotallyComplex K (n := 4) (by norm_num)
  exact IsTotallyComplex.isComplex w

/-- **Check.** `ℚ(i)`, a `4`-th cyclotomic extension of `ℚ`, has one archimedean absolute value,
whose completion is `ℂ`, and it occurs twice in `archAbsVal`. -/
theorem exists_archAbsVal_eq_replicate_two_of_isCyclotomicExtension_four :
    ∃ v : AbsoluteValue K ℝ,
      archAbsVal = Multiset.replicate 2 v ∧ Nonempty (v.Completion ≃+* ℂ) := by
  obtain ⟨w, hw, hwc⟩ := exists_eq_isComplex_of_isCyclotomicExtension_four K
  refine ⟨w.val, Multiset.eq_replicate.2 ⟨?_, fun b hb ↦ ?_⟩,
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc⟩⟩
  · change totalWeight _ = 2
    rw [totalWeight_eq_sum_mult, Fintype.sum_eq_single w fun w' h ↦ (h (hw w')).elim,
      hwc.mult_eq_two]
  · obtain ⟨w', rfl⟩ := (isInfinitePlace_iff b).1 (mem_multisetInfinitePlace.1 hb)
    rw [hw w']

end Gaussian

/-- **Check.** The archimedean place of `ℚ` cannot be omitted: no admissible family of absolute
values on `ℚ` has no archimedean members and the finite places of `ℚ` as its nonarchimedean
members, because at `2` the nonarchimedean factor alone is `1 / 2 ≠ 1`. -/
theorem not_exists_admissibleAbsValues_rat_archAbsVal_eq_zero :
    ¬ ∃ I : AdmissibleAbsValues ℚ,
      I.archAbsVal = 0 ∧ I.nonarchAbsVal = {v | IsFinitePlace v} := by
  rintro ⟨I, ha, hn⟩
  have h := @AdmissibleAbsValues.product_formula ℚ _ I 2 two_ne_zero
  rw [ha, hn, Multiset.map_zero, Multiset.prod_zero, one_mul] at h
  have h' := finprod_nonarchAbsVal_rat_two
  change ∏ᶠ v : {v : AbsoluteValue ℚ ℝ | IsFinitePlace v}, v.val (2 : ℚ) = 1 / 2 at h'
  rw [h'] at h
  norm_num at h

end TauCeti.Examples.GeneralizedGlobalField
