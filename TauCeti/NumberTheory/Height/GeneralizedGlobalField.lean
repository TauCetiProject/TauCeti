/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.RingTheory.TensorProduct.Reduced
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic

/-!
# Generalized global fields

A *generalized global field* (Conrad, Definition 8.1) is a field `K` with a family of absolute
values satisfying the product formula, in which the absolute values are pairwise inequivalent,
there are infinitely many nonarchimedean ones and finitely many archimedean ones, and each
nonarchimedean absolute value is discrete with an excellent valuation ring.

`Height.GeneralizedGlobalField K` strengthens Mathlib's `Height.AdmissibleAbsValues K`, which
already provides the product formula, the finiteness of the multiset `archAbsVal` of archimedean
absolute values (counted with multiplicity) and the set `nonarchAbsVal` of nonarchimedean ones.
The archimedean absolute values are genuine absolute values satisfying the triangle inequality,
so a complex place is recorded once with multiplicity two. The extra fields are:

* every member of `archAbsVal` is archimedean (not nonarchimedean), so in particular nontrivial;
* a member of `archAbsVal` occurs with multiplicity `2` if its completion is isomorphic to `ℂ` (a
  complex place) and `1` otherwise (a real place);
* equivalent members of `archAbsVal`, and equivalent members of `nonarchAbsVal`, are equal;
* `nonarchAbsVal` is infinite;
* every member `v` of `nonarchAbsVal` is discrete: there is `π` with `0 < v π < 1` such that every
  nonzero value of `v` is an integer power of `v π`;
* the completion of `K` at every member of `nonarchAbsVal` is geometrically reduced (separable)
  over `K`. For a discrete valuation ring with fraction field `K` this is equivalent to excellence:
  its only nontrivial formal fibre is the completion of `K`, and a field extension is geometrically
  regular exactly when it is separable.

The members of the family are chosen data satisfying the product formula; the class does not
determine their scale. For a number field, `ofNumberField` normalizes the finite places by the
absolute norm of their prime.

`Height.GeneralizedGlobalField.ofNumberField` is the instance for a number field, extending
Mathlib's `NumberField.instAdmissibleAbsValues`: infinite places with their multiplicities, a
complex place being the ordinary modulus, and finite places normalized by the absolute norm of
their prime.

## References

* B. Conrad, *Chow's K/k-image and K/k-trace, and the Lang–Néron theorem*, Enseign. Math. 52
  (2006), Definition 8.1.
-/

public section

noncomputable section

namespace Height

open AdmissibleAbsValues

open Classical in
/-- A generalized global field: a field with an admissible family of absolute values
(`Height.AdmissibleAbsValues`) whose members are pairwise inequivalent, with infinitely many
nonarchimedean ones, each archimedean member genuinely archimedean and counted twice exactly when
its completion is `ℂ`, and each nonarchimedean member discrete with completion separable over `K`
(equivalently, with excellent valuation ring). See Conrad, Definition 8.1. -/
class GeneralizedGlobalField (K : Type*) [Field K] extends AdmissibleAbsValues K where
  /-- The archimedean absolute values are not nonarchimedean. -/
  not_isNonarchimedean_of_mem_archAbsVal {v : AbsoluteValue K ℝ} (hv : v ∈ archAbsVal) :
    ¬ IsNonarchimedean v
  /-- Equivalent archimedean absolute values are equal; they may still occur with multiplicity. -/
  eq_of_mem_archAbsVal_of_isEquiv {v w : AbsoluteValue K ℝ} (hv : v ∈ archAbsVal)
    (hw : w ∈ archAbsVal) (h : v.IsEquiv w) : v = w
  /-- An archimedean absolute value occurs twice if its completion is isomorphic to `ℂ` (a
  complex place) and once otherwise (a real place). -/
  count_archAbsVal {v : AbsoluteValue K ℝ} (hv : v ∈ archAbsVal) :
    archAbsVal.count v = if Nonempty (v.Completion ≃+* ℂ) then 2 else 1
  /-- Equivalent nonarchimedean absolute values are equal. -/
  eq_of_mem_nonarchAbsVal_of_isEquiv {v w : AbsoluteValue K ℝ} (hv : v ∈ nonarchAbsVal)
    (hw : w ∈ nonarchAbsVal) (h : v.IsEquiv w) : v = w
  /-- There are infinitely many nonarchimedean absolute values. -/
  infinite_nonarchAbsVal : nonarchAbsVal.Infinite
  /-- Each nonarchimedean absolute value is discrete: its nonzero values are the integer powers
  of the value `v π ∈ (0, 1)` of a uniformizer `π`. -/
  exists_uniformizer {v : AbsoluteValue K ℝ} (hv : v ∈ nonarchAbsVal) :
    ∃ π : K, 0 < v π ∧ v π < 1 ∧ ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = v π ^ n
  /-- The completion at each nonarchimedean absolute value is separable over `K`; for the
  discrete valuation ring of `v` this is excellence. -/
  isGeometricallyReduced_completion {v : AbsoluteValue K ℝ} (hv : v ∈ nonarchAbsVal) :
    Algebra.IsGeometricallyReduced K v.Completion

namespace GeneralizedGlobalField

variable (K : Type*) [Field K] [NumberField K]

open NumberField in
/-- A number field is a generalized global field, with its infinite places counted with
multiplicity and its finite places normalized by the absolute norm of their prime. -/
instance ofNumberField : GeneralizedGlobalField K where
  toAdmissibleAbsValues := NumberField.instAdmissibleAbsValues
  not_isNonarchimedean_of_mem_archAbsVal {v} hv h := by
    obtain ⟨w, rfl⟩ := (isInfinitePlace_iff v).1 (mem_multisetInfinitePlace.1 hv)
    exact w.not_isNonarchimedean h
  eq_of_mem_archAbsVal_of_isEquiv {v w} hv hw h := by
    obtain ⟨v, rfl⟩ := (isInfinitePlace_iff _).1 (mem_multisetInfinitePlace.1 hv)
    obtain ⟨w, rfl⟩ := (isInfinitePlace_iff _).1 (mem_multisetInfinitePlace.1 hw)
    exact congrArg Subtype.val (InfinitePlace.eq_iff_isEquiv.2 h)
  count_archAbsVal {v} hv := by
    classical
    obtain ⟨w, rfl⟩ := (isInfinitePlace_iff v).1 (mem_multisetInfinitePlace.1 hv)
    simp only [archAbsVal]
    rw [count_multisetInfinitePlace_eq_mult, InfinitePlace.mult]
    rcases w.isReal_or_isComplex with h | h
    · simp [h, h.not_nonempty_ringEquiv_complex]
    · simp [InfinitePlace.not_isReal_iff_isComplex.2 h,
        (⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex h⟩ : Nonempty (_ ≃+* ℂ))]
  eq_of_mem_nonarchAbsVal_of_isEquiv {v w} hv hw h := by
    obtain ⟨v, rfl⟩ := (isFinitePlace_iff _).1 hv
    obtain ⟨w, rfl⟩ := (isFinitePlace_iff _).1 hw
    exact congrArg Subtype.val (FinitePlace.eq_iff_isEquiv.2 h)
  infinite_nonarchAbsVal := by
    exact Set.infinite_coe_iff.mp (inferInstance : Infinite (FinitePlace K))
  exists_uniformizer {v} hv := by
    obtain ⟨v, rfl⟩ := (isFinitePlace_iff _).1 hv
    have hN : (1 : ℝ) < v.maximalIdeal.asIdeal.absNorm := mod_cast
      HeightOneSpectrum.one_lt_absNorm v.maximalIdeal
    obtain ⟨π, hπ, hvπ⟩ := v.exists_ne_zero_apply_eq_absNorm_zpow (-1)
    refine ⟨π, v.pos_iff.2 hπ, ?_, fun x hx ↦ ⟨-WithZero.log (v.maximalIdeal.valuation K x), ?_⟩⟩
    · rw [FinitePlace.coe_apply] at hvπ
      rw [hvπ, zpow_neg_one]
      exact inv_lt_one_of_one_lt₀ hN
    · rw [← FinitePlace.coe_apply, ← FinitePlace.coe_apply, hvπ, v.apply_eq_absNorm_zpow hx,
        ← zpow_mul]
      simp
  isGeometricallyReduced_completion _ := inferInstance

end GeneralizedGlobalField

end Height
