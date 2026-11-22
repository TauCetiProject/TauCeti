/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Interpolation

/-!
# Hölder bounds for the fields of every order

A bounded parabolic Hölder map `u` of order `k` controls the Hölder regularity of its fields
`D_t^r D_x^m u` of every parabolic order `2 r + m ≤ k`, not only of the top one. For `α ≤ 1`:

* every field of order `2 r + m ≤ k` is parabolically `α`-Hölder with constant `6 ‖u‖`
  (`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_of_le`): at the top order by
  definition, and below it because the field is bounded, Lipschitz in space, with the next
  spatial field as derivative, and Lipschitz or `(1 + α) / 2`-Hölder in time;
* every field of order `2 r + m ≤ k - 1` has `(1 + α) / 2`-Hölder time slices with constant
  `3 ‖u‖` (`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_slabMk_of_add_one_le`): at the
  order `k - 1` by definition, and below it because the field is bounded and Lipschitz in time.

The lower orders use the interpolation of a bounded Lipschitz map at scale one
(`TauCeti.ParabolicSpaceTime.timeEHolderNorm_le_of_timeEHolderNorm_le` and
`TauCeti.ParabolicSpaceTime.eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le`), which
is where `α ≤ 1` enters.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_of_le`: every field of order at most `k` is
  parabolically `α`-Hölder with constant `6 ‖u‖`.
* `TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_slabMk_of_add_one_le`: every field of
  order at most `k - 1` has `(1 + α) / 2`-Hölder time slices with constant `3 ‖u‖`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
-/

public section

noncomputable section

namespace TauCeti

namespace ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped NNReal ENNReal

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- A field of order at most `k - 2` is Lipschitz in time, with constant `‖u‖`. -/
private theorem timeEHolderNorm_one_mixedDerivL_le (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 2 ≤ k) :
    timeEHolderNorm 1 (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤ ‖u‖₊ := by
  have key := timeEHolderNorm_one_le_of_hasDerivWithinAt (a := a) (b := b)
    (w := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m u))
    (wₜ := fun y t ↦ mixedDerivL (r + 1) m u (slabMk y (projIcc a b hab.le t))) (C := ‖u‖₊)
    (fun y t ht ↦ by
      simpa only [projIcc_of_mem hab.le ht] using hasDerivWithinAt_mixedDerivL u h y ⟨t, ht⟩)
    (fun y t _ ↦ by
      rw [coe_nnNorm]
      exact ((mixedDerivL (r + 1) m u).norm_coe_le_norm _).trans (norm_mixedDerivL_le u _ _))
  rwa [ParabolicC2HolderSpace.timeExtension_space_slabTime] at key

/-- A field of order at most `k - 1` is Lipschitz in space, with constant `‖u‖`. -/
private theorem spaceEHolderNorm_one_mixedDerivL_le (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) :
    spaceEHolderNorm 1 (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤ ‖u‖₊ := by
  have key := spaceEHolderNorm_one_le_of_hasFDerivAt (a := a) (b := b)
    (w := ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL r m u))
    (w' := fun y t ↦ (mixedDerivL r (m + 1) u (slabMk y (projIcc a b hab.le t))).curryLeft)
    (C := ‖u‖₊)
    (fun t ht y ↦ by
      simpa only [ParabolicC2HolderSpace.timeExtension_def, projIcc_of_mem hab.le ht] using
        hasFDerivAt_mixedDerivL u h ⟨t, ht⟩ y)
    (fun y t _ ↦ by
      rw [coe_nnNorm, ContinuousMultilinearMap.curryLeft_norm]
      exact ((mixedDerivL r (m + 1) u).norm_coe_le_norm _).trans (norm_mixedDerivL_le u _ _))
  rwa [ParabolicC2HolderSpace.timeExtension_space_slabTime] at key

/-- The time slices of a field of order exactly `k - 1` are `(1 + α) / 2`-Hölder with constant
`‖u‖`. -/
private theorem timeEHolderNorm_mixedDerivL_le_of_add_one_eq
    (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ} (h : 2 * r + m + 1 = k) :
    timeEHolderNorm ((1 + α) / 2) (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤
      ‖u‖₊ := by
  refine timeEHolderNorm_le_iff.2 fun x ↦ (holderWith_mixedDerivL_slabMk u h x).mono ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
  exact norm_timeSliceL_le u r m

/-- Values of a field lie within distance `2 ‖u‖` of each other. -/
private theorem dist_mixedDerivL_le (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ)
    (p q : slab (E := E) a b) :
    dist (mixedDerivL r m u p) (mixedDerivL r m u q) ≤ ((2 * ‖u‖₊ : ℝ≥0) : ℝ) := by
  simpa using BoundedContinuousFunction.dist_le_two_norm'
    (fun p ↦ ((mixedDerivL r m u).norm_coe_le_norm p).trans (norm_mixedDerivL_le u r m)) p q

/-- The time exponent `(1 + α) / 2` is at most one for `α ≤ 1`. -/
private theorem one_add_div_two_le_one (hα : α ≤ 1) : (1 + α) / 2 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  calc 1 + α ≤ 1 + 1 := by gcongr
    _ = 2 := one_add_one_eq_two

/-- **Every field is parabolically Hölder.** For `α ≤ 1`, each field `D_t^r D_x^m u` of order
`2 r + m ≤ k` is parabolically `α`-Hölder with constant `6 ‖u‖`. -/
theorem holderWith_mixedDerivL_of_le (hα : α ≤ 1) (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) :
    HolderWith (6 * ‖u‖₊) α (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) := by
  rcases h.eq_or_lt with h | h
  · intro p q
    have hp := (mixedDerivHolderL r m u).holderWith_nnnorm p q
    rw [mixedDerivHolderL_apply u h, mixedDerivHolderL_apply u h] at hp
    refine hp.trans ?_
    gcongr
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_mul, coe_nnNorm]
    have := norm_mixedDerivHolderL_le u r m
    push_cast
    linarith [norm_nonneg u]
  · -- Below the top order, the field is Lipschitz in space, and in time it is Lipschitz or, at
    -- the order `k - 1`, `(1 + α) / 2`-Hölder; either time exponent is at least `α / 2`.
    have hhalf : α / 2 ≤ (1 + α) / 2 := by
      gcongr
      exact le_add_self
    obtain ⟨β, hβ, htime⟩ : ∃ β : ℝ≥0, α / 2 ≤ β ∧
        timeEHolderNorm β (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤ ‖u‖₊ := by
      by_cases h2 : 2 * r + m + 2 ≤ k
      · exact ⟨1, hhalf.trans (one_add_div_two_le_one hα), timeEHolderNorm_one_mixedDerivL_le u h2⟩
      · exact ⟨_, hhalf, timeEHolderNorm_mixedDerivL_le_of_add_one_eq u (by omega)⟩
    have hle := eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le
      (spaceEHolderNorm_one_mixedDerivL_le u (r := r) (m := m) (by omega)) htime
      (dist_mixedDerivL_le u r m) hα hβ one_pos one_pos
    simp only [NNReal.one_rpow, mul_one] at hle
    refine eHolderNorm_le_iff.1 (hle.trans (le_of_eq ?_))
    congr 1
    ring

/-- **Every field below the top order has Hölder time slices.** For `α ≤ 1`, each field
`D_t^r D_x^m u` of order `2 r + m ≤ k - 1` has `(1 + α) / 2`-Hölder time slices with constant
`3 ‖u‖`. -/
theorem holderWith_mixedDerivL_slabMk_of_add_one_le (hα : α ≤ 1)
    (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (x : E) :
    HolderWith (3 * ‖u‖₊) ((1 + α) / 2) fun t : Icc a b ↦ mixedDerivL r m u (slabMk x t) := by
  have hbound : timeEHolderNorm ((1 + α) / 2)
      (mixedDerivL r m u : slab (E := E) a b → E [×m]→L[ℝ] F) ≤ ↑(3 * ‖u‖₊) := by
    rcases h.eq_or_lt with h | h
    · refine (timeEHolderNorm_mixedDerivL_le_of_add_one_eq u h).trans (ENNReal.coe_le_coe.2 ?_)
      exact le_mul_of_one_le_left zero_le (by norm_num)
    · -- Below the order `k - 1`, the field is bounded and Lipschitz in time.
      have hle := timeEHolderNorm_le_of_timeEHolderNorm_le
        (timeEHolderNorm_one_mixedDerivL_le u (r := r) (m := m) (by omega))
        (dist_mixedDerivL_le u r m) (one_add_div_two_le_one hα) one_pos
      simp only [NNReal.one_rpow, mul_one] at hle
      refine hle.trans (le_of_eq ?_)
      congr 1
      ring
  exact fun t s ↦ timeEHolderNorm_le_iff.1 hbound x t s

end ParabolicCkHolderSpace

end TauCeti
