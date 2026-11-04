/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Closed-ball boxes in the mixed space

Mathlib's `NumberField.mixedEmbedding.convexBodyLT` cuts out the open product of balls
`‖x w‖ < f w` in `mixedSpace K` and computes its volume in `convexBodyLT_volume`.
Geometry-of-numbers arguments on compact bodies, such as the archimedean halves of approximation
domains, instead impose closed inequalities `normAtPlace w x ≤ f w` at the infinite places.

Because closed and open balls in `ℝ` and `ℂ` have the same Lebesgue measure at nonnegative radii,
the closed box `{x : mixedSpace K | ∀ w, normAtPlace w x ≤ f w}` has the same volume formula
`convexBodyLTFactor K * ∏ w, f w ^ mult w` whenever `f` is nonnegative, and is empty if `f` takes a
negative value at some infinite place. The proof of `volume_setOf_forall_normAtPlace_le` is adapted
from Mathlib's `NumberField.mixedEmbedding.convexBodyLT_volume` (Xavier Roblot, Apache 2.0),
replacing `volume_ball` with `volume_closedBall`.

## Main results

* `NumberField.mixedEmbedding.normAtPlace_congr`: `normAtPlace w x` depends only on the
  `w`-coordinate of `x`.
* `NumberField.mixedEmbedding.setOf_forall_normAtPlace_le_eq_prod`: the set
  `{x : mixedSpace K | ∀ w, normAtPlace w x ≤ f w}` is the product of the closed balls of radii
  `f w` at the real and complex places.
* `NumberField.mixedEmbedding.volume_setOf_forall_normAtPlace_le` and
  `NumberField.mixedEmbedding.volume_real_setOf_forall_normAtPlace_le`: its `ℝ≥0∞`-valued volume
  (unconditionally, since `ENNReal.ofReal` vanishes on negative radii) and its `ℝ`-valued volume for
  nonnegative `f`.
* `NumberField.mixedEmbedding.setOf_forall_normAtPlace_le_eq_empty_of_neg`: if `f w < 0` at
  some infinite place `w`, the box is empty.
-/

public section

open ENNReal MeasureTheory Metric NNReal NumberField NumberField.InfinitePlace

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K]

/-- `normAtPlace w` depends only on the `w`-coordinate of an element of `mixedSpace K`. -/
theorem normAtPlace_congr (w : InfinitePlace K) {x y : mixedSpace K}
    (h₁ : ∀ hw : IsReal w, x.1 ⟨w, hw⟩ = y.1 ⟨w, hw⟩)
    (h₂ : ∀ hw : IsComplex w, x.2 ⟨w, hw⟩ = y.2 ⟨w, hw⟩) :
    normAtPlace w x = normAtPlace w y := by
  by_cases hw : IsReal w
  · simp [normAtPlace_apply_of_isReal hw, h₁ hw]
  · have hwc : IsComplex w := not_isReal_iff_isComplex.mp hw
    simp [normAtPlace_apply_of_isComplex hwc, h₂ hwc]

/-- The set of points of `mixedSpace K` bounded at every infinite place `w` by `f w` is the product
of the closed balls of radii `f w` at the real and complex places. -/
theorem setOf_forall_normAtPlace_le_eq_prod (f : InfinitePlace K → ℝ) :
    {x : mixedSpace K | ∀ w : InfinitePlace K, normAtPlace w x ≤ f w} =
      (Set.univ.pi fun w : {w : InfinitePlace K // IsReal w} ↦ closedBall 0 (f w.1)) ×ˢ
      (Set.univ.pi fun w : {w : InfinitePlace K // IsComplex w} ↦ closedBall 0 (f w.1)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_closedBall_zero_iff]
  refine ⟨fun hx ↦ ⟨fun w ↦ ?_, fun w ↦ ?_⟩, fun ⟨h₁, h₂⟩ w ↦ ?_⟩
  · simpa only [normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs] using hx w.1
  · simpa only [normAtPlace_apply_of_isComplex w.2] using hx w.1
  · by_cases hw : IsReal w
    · simpa only [normAtPlace_apply_of_isReal hw, Real.norm_eq_abs] using h₁ ⟨w, hw⟩
    · have hwc : IsComplex w := not_isReal_iff_isComplex.mp hw
      simpa only [normAtPlace_apply_of_isComplex hwc] using h₂ ⟨w, hwc⟩

/-- If `f w < 0` at some infinite place `w`, the closed-ball box `{x | ∀ w, normAtPlace w x ≤ f w}`
is empty. -/
theorem setOf_forall_normAtPlace_le_eq_empty_of_neg {f : InfinitePlace K → ℝ}
    {w : InfinitePlace K} (hw : f w < 0) :
    {x : mixedSpace K | ∀ u : InfinitePlace K, normAtPlace u x ≤ f u} = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
    ((normAtPlace_nonneg w x).trans (hx w)).not_gt hw

variable [NumberField K]

-- Adapted from `NumberField.mixedEmbedding.convexBodyLT_volume` in Mathlib.
open scoped Classical in
/-- **Volume of a closed-ball box in the mixed space.** The set of points `x : mixedSpace K` with
`normAtPlace w x ≤ f w` at every infinite place has volume
`convexBodyLTFactor K * ∏ w, ENNReal.ofReal (f w) ^ mult w` (vanishing automatically via
`ENNReal.ofReal` if `f w < 0` at some place). -/
theorem volume_setOf_forall_normAtPlace_le (f : InfinitePlace K → ℝ) :
    volume {x : mixedSpace K | ∀ w : InfinitePlace K, normAtPlace w x ≤ f w} =
      convexBodyLTFactor K * ∏ w, ENNReal.ofReal (f w) ^ mult w := by
  rw [setOf_forall_normAtPlace_le_eq_prod]
  calc
    _ = (∏ x : {w // IsReal w}, ENNReal.ofReal (2 * f x.val)) *
          ∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2 * NNReal.pi := by
      simp_rw [Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi,
        Real.volume_closedBall, Complex.volume_closedBall]
    _ = ((2 : ℝ≥0) ^ nrRealPlaces K *
          ∏ x : {w // IsReal w}, ENNReal.ofReal (f x.val)) *
          ((∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) *
            NNReal.pi ^ nrComplexPlaces K) := by
      simp_rw [ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2), Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, ofReal_ofNat, coe_ofNat]
    _ = convexBodyLTFactor K * ((∏ x : {w // IsReal w}, ENNReal.ofReal (f x.val)) *
          ∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) := by
      simp_rw [convexBodyLTFactor, coe_mul, ENNReal.coe_pow]
      ring
    _ = convexBodyLTFactor K * ∏ w, ENNReal.ofReal (f w) ^ mult w := by
      simp_rw [prod_eq_prod_mul_prod, mult_isReal, mult_isComplex, pow_one]

open scoped Classical in
/-- **Real-valued volume of a closed-ball box in the mixed space.** For nonnegative radii `f w`,
the real volume of `{x : mixedSpace K | ∀ w, normAtPlace w x ≤ f w}` is
`2 ^ nrRealPlaces K * π ^ nrComplexPlaces K * ∏ w, f w ^ mult w`. -/
theorem volume_real_setOf_forall_normAtPlace_le {f : InfinitePlace K → ℝ} (hf : ∀ w, 0 ≤ f w) :
    volume.real {x : mixedSpace K | ∀ w : InfinitePlace K, normAtPlace w x ≤ f w} =
      2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K * ∏ w, f w ^ mult w := by
  rw [measureReal_def, volume_setOf_forall_normAtPlace_le, ENNReal.toReal_mul,
    ENNReal.toReal_prod]
  simp only [convexBodyLTFactor, coe_mul, ENNReal.coe_pow, coe_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_pow, toReal_ofNat, coe_toReal, NNReal.coe_real_pi]
  congr 1
  exact Finset.prod_congr rfl fun w _ ↦ by rw [toReal_ofReal (hf w)]

end NumberField.mixedEmbedding
