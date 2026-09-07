/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.CDF

/-!
# Extensionality for symmetric finite real measures

This file gives an extensionality principle for symmetric finite measures on the real line:
their pushforwards under squaring determine them. It packages the elementary observation that the
square records the mass of intervals symmetric about zero, while reflection invariance makes the
two complementary tails equal.

## Main result

* `TauCeti.MeasureTheory.Measure.eq_of_map_sq_eq_of_map_neg_eq_self` — two symmetric finite real
  measures with the same pushforward after squaring are equal.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace MeasureTheory

/-- Two reflection-invariant finite measures on `ℝ` are equal if their pushforwards under
squaring are equal. -/
theorem Measure.eq_of_map_sq_eq_of_map_neg_eq_self {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμneg : μ.map (fun x : ℝ ↦ -x) = μ) (hνneg : ν.map (fun x : ℝ ↦ -x) = ν)
    (hsq : μ.map (fun x : ℝ ↦ x ^ 2) = ν.map (fun x : ℝ ↦ x ^ 2)) :
    μ = ν := by
  apply Measure.ext_of_Iic
  intro x
  rw [← measureReal_eq_measureReal_iff]
  have htotal : μ.real univ = ν.real univ := by
    have h := congrArg (fun ρ : Measure ℝ ↦ ρ.real univ) hsq
    simpa only [map_measureReal_apply (μ := μ) (f := fun y : ℝ ↦ y ^ 2) (by fun_prop)
        MeasurableSet.univ,
      map_measureReal_apply (μ := ν) (f := fun y : ℝ ↦ y ^ 2) (by fun_prop)
        MeasurableSet.univ,
      preimage_univ] using h
  by_cases hx : 0 ≤ x
  -- On the nonnegative half-line, the squared law fixes the central interval `[-x, x]`.
  -- Symmetry equates its two open complementary tails, hence fixes `Iic x`.
  · have hsq_preimage : (fun y : ℝ ↦ y ^ 2) ⁻¹' Iic (x ^ 2) = Icc (-x) x := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_Icc]
      constructor
      · exact fun hy ↦ abs_le_of_sq_le_sq' hy hx
      · exact fun hy ↦ sq_le_sq' hy.1 hy.2
    have hcentral : μ.real (Icc (-x) x) = ν.real (Icc (-x) x) := by
      have h := congrArg (fun ρ : Measure ℝ ↦ ρ.real (Iic (x ^ 2))) hsq
      rw [map_measureReal_apply (μ := μ) (f := fun y : ℝ ↦ y ^ 2) (by fun_prop)
          measurableSet_Iic,
        map_measureReal_apply (μ := ν) (f := fun y : ℝ ↦ y ^ 2) (by fun_prop)
          measurableSet_Iic,
        hsq_preimage] at h
      exact h
    have hneg_preimage : (fun y : ℝ ↦ -y) ⁻¹' Ioi x = Iio (-x) := by
      ext y
      simp only [mem_preimage, mem_Ioi, mem_Iio]
      constructor <;> intro h <;> linarith
    have hμtails : μ.real (Iio (-x)) = μ.real (Ioi x) := by
      have h := congrArg (fun ρ : Measure ℝ ↦ ρ.real (Ioi x)) hμneg
      rw [map_measureReal_apply (μ := μ) (f := fun y : ℝ ↦ -y) (by fun_prop)
        measurableSet_Ioi, hneg_preimage] at h
      exact h
    have hνtails : ν.real (Iio (-x)) = ν.real (Ioi x) := by
      have h := congrArg (fun ρ : Measure ℝ ↦ ρ.real (Ioi x)) hνneg
      rw [map_measureReal_apply (μ := ν) (f := fun y : ℝ ↦ -y) (by fun_prop)
        measurableSet_Ioi, hneg_preimage] at h
      exact h
    have hbounds : -x ≤ x := by linarith
    have hdisj_inner : Disjoint (Icc (-x) x) (Ioi x) :=
      (Iic_disjoint_Ioi le_rfl).mono Icc_subset_Iic_self Subset.rfl
    have hμtotal :
        μ.real univ = μ.real (Iio (-x)) + (μ.real (Icc (-x) x) + μ.real (Ioi x)) := by
      rw [← Iio_union_Ici (a := -x),
        measureReal_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici,
        ← Icc_union_Ioi_eq_Ici hbounds,
        measureReal_union hdisj_inner measurableSet_Ioi]
    have hνtotal :
        ν.real univ = ν.real (Iio (-x)) + (ν.real (Icc (-x) x) + ν.real (Ioi x)) := by
      rw [← Iio_union_Ici (a := -x),
        measureReal_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici,
        ← Icc_union_Ioi_eq_Ici hbounds,
        measureReal_union hdisj_inner measurableSet_Ioi]
    have hμcdf : μ.real (Iic x) = μ.real (Iio (-x)) + μ.real (Icc (-x) x) := by
      rw [← Iio_union_Icc_eq_Iic hbounds,
        measureReal_union ((Iio_disjoint_Ici le_rfl).mono_right Icc_subset_Ici_self)
          measurableSet_Icc]
    have hνcdf : ν.real (Iic x) = ν.real (Iio (-x)) + ν.real (Icc (-x) x) := by
      rw [← Iio_union_Icc_eq_Iic hbounds,
        measureReal_union ((Iio_disjoint_Ici le_rfl).mono_right Icc_subset_Ici_self)
          measurableSet_Icc]
    rw [hμcdf, hνcdf]
    linarith
  -- For negative `x`, the squared law fixes `(x, -x)`.  Symmetry equates the two closed
  -- complementary tails, of which `Iic x` is one.
  · have hx' : x < 0 := lt_of_not_ge hx
    have hsq_preimage : (fun y : ℝ ↦ y ^ 2) ⁻¹' Iio (x ^ 2) = Ioo x (-x) := by
      ext y
      simp only [mem_preimage, mem_Iio, mem_Ioo]
      constructor
      · intro hy
        have h : y ^ 2 < (-x) ^ 2 := by simpa only [neg_sq] using hy
        simpa only [neg_neg] using abs_lt_of_sq_lt_sq' h (by linarith)
      · intro hy
        have h : -(-x) < y := by linarith [hy.1]
        simpa only [neg_sq] using sq_lt_sq' h hy.2
    have hmiddle : μ.real (Ioo x (-x)) = ν.real (Ioo x (-x)) := by
      have h := congrArg (fun ρ : Measure ℝ ↦ ρ.real (Iio (x ^ 2))) hsq
      rw [map_measureReal_apply (μ := μ) (f := fun y : ℝ ↦ y ^ 2) (by fun_prop)
          measurableSet_Iio,
        map_measureReal_apply (μ := ν) (f := fun y : ℝ ↦ y ^ 2) (by fun_prop)
          measurableSet_Iio,
        hsq_preimage] at h
      exact h
    have hneg_preimage : (fun y : ℝ ↦ -y) ⁻¹' Ici (-x) = Iic x := by
      ext y
      simp only [mem_preimage, mem_Ici, mem_Iic]
      constructor <;> intro h <;> linarith
    have hμtails : μ.real (Iic x) = μ.real (Ici (-x)) := by
      have h := congrArg (fun ρ : Measure ℝ ↦ ρ.real (Ici (-x))) hμneg
      rw [map_measureReal_apply (μ := μ) (f := fun y : ℝ ↦ -y) (by fun_prop)
        measurableSet_Ici, hneg_preimage] at h
      exact h
    have hνtails : ν.real (Iic x) = ν.real (Ici (-x)) := by
      have h := congrArg (fun ρ : Measure ℝ ↦ ρ.real (Ici (-x))) hνneg
      rw [map_measureReal_apply (μ := ν) (f := fun y : ℝ ↦ -y) (by fun_prop)
        measurableSet_Ici, hneg_preimage] at h
      exact h
    have hbounds : x < -x := by linarith
    have hdisj_inner : Disjoint (Ioo x (-x)) (Ici (-x)) :=
      (Iio_disjoint_Ici le_rfl).mono Ioo_subset_Iio_self Subset.rfl
    have hμtotal :
        μ.real univ = μ.real (Iic x) + (μ.real (Ioo x (-x)) + μ.real (Ici (-x))) := by
      rw [← Iic_union_Ioi (a := x),
        measureReal_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
        ← Ioo_union_Ici_eq_Ioi hbounds,
        measureReal_union hdisj_inner measurableSet_Ici]
    have hνtotal :
        ν.real univ = ν.real (Iic x) + (ν.real (Ioo x (-x)) + ν.real (Ici (-x))) := by
      rw [← Iic_union_Ioi (a := x),
        measureReal_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
        ← Ioo_union_Ici_eq_Ioi hbounds,
        measureReal_union hdisj_inner measurableSet_Ici]
    linarith

end MeasureTheory

end TauCeti
