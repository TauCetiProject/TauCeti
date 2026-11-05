/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Equation

/-!
# Darboux bounds for renewal convolutions

A decreasing forcing function, truncated to ages below a finite cutoff, is squeezed
between its left- and right-endpoint step functions. After convolution these become
finite sums of reflected interval masses. These bounds reduce compactly supported
monotone forcing to interval increments, without requiring continuity of the forcing
or absence of atoms in the measure.

Age cells are left-closed and right-open. Reflection turns them into left-open,
right-closed intervals, so an arrival exactly at the observation time is retained.
The cutoff itself is excluded; it can be included in a separate tail estimate.
Partitions may have repeated endpoints, and the empty partition is allowed.

This is the step-function comparison used in renewal theory; see W. Feller,
*An Introduction to Probability Theory and Its Applications*, volume II,
second edition, Chapter XI. The results apply to any measure finite on the
observation interval, not only to renewal measures.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {μ : Measure ℝ≥0} {h : ℝ≥0 → ℝ} {t a b : ℝ≥0}

/-- Truncating a forcing function to an age cell reflects that cell about the observation
time. This identity keeps the endpoints even when the measure has atoms. -/
theorem renewalConv_indicator_Ico (hab : a ≤ b) (hbt : b ≤ t) :
    renewalConv ((Ico a b).indicator h) μ t =
      ∫ s in Ioc (t - b) (t - a), h (t - s) ∂μ := by
  classical
  rw [renewalConv_eq_integral_indicator, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with s
  have he : s ≤ t ∧ a ≤ t - s ∧ t - s < b ↔ t - b < s ∧ s ≤ t - a := by
    constructor
    · rintro ⟨hst, ha, hb⟩
      constructor
      · exact (tsub_lt_iff_right hbt).2 ((tsub_lt_iff_left hst).1 hb)
      · exact (le_tsub_iff_right (hab.trans hbt)).2 ((le_tsub_iff_left hst).1 ha)
    · rintro ⟨hb, ha⟩
      have hst : s ≤ t := ha.trans tsub_le_self
      exact ⟨hst, (le_tsub_iff_left hst).2 ((le_tsub_iff_right (hab.trans hbt)).1 ha),
        (tsub_lt_iff_left hst).2 ((tsub_lt_iff_right hbt).1 hb)⟩
  simp only [indicator_apply, mem_Iic, mem_Ico, mem_Ioc]
  split_ifs <;> simp_all

/-- Splitting ages at consecutive partition points splits the convolution into reflected
interval integrals. Integrability is required only on the reflected truncation.
The cutoff is excluded, and the initial age zero is included. -/
theorem renewalConv_indicator_Iio_eq_sum
    (p : ℕ → ℝ≥0) (hp : Monotone p) (hp0 : p 0 = 0) (N : ℕ) (hNt : p N ≤ t)
    (hint : IntegrableOn (fun s ↦ h (t - s)) (Ioc (t - p N) t) μ) :
    renewalConv ((Iio (p N)).indicator h) μ t =
      ∑ k ∈ Finset.range N, ∫ s in Ioc (t - p (k + 1)) (t - p k), h (t - s) ∂μ := by
  have hcell (k : ℕ) (hk : k + 1 ≤ N) : IntegrableOn (fun s ↦ h (t - s))
      (Ioc (t - p (k + 1)) (t - p k)) μ :=
    hint.mono_set fun s hs ↦
      ⟨(tsub_le_tsub_left (hp hk) t).trans_lt hs.1, hs.2.trans tsub_le_self⟩
  have hsplit (n : ℕ) (hn : n ≤ N) :
      (∫ s in Ioc (t - p n) t, h (t - s) ∂μ) =
        ∑ k ∈ Finset.range n, ∫ s in Ioc (t - p (k + 1)) (t - p k), h (t - s) ∂μ := by
    induction n with
    | zero => simp [hp0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih (Nat.le_of_succ_le hn), ← setIntegral_union]
      · rw [union_comm, Ioc_union_Ioc_eq_Ioc (tsub_le_tsub_left (hp (Nat.le_succ n)) t)
          tsub_le_self]
      · exact (Ioc_disjoint_Ioc_of_le le_rfl).symm
      · exact measurableSet_Ioc
      · exact hint.mono_set fun s hs ↦
          ⟨(tsub_le_tsub_left (hp (Nat.le_of_succ_le hn)) t).trans_lt hs.1, hs.2⟩
      · exact hcell n hn
  have he : Iio (p N) = Ico 0 (p N) := by ext s; simp
  rw [he, renewalConv_indicator_Ico zero_le hNt, tsub_zero]
  exact hsplit N le_rfl

/-- The right-endpoint Darboux sum bounds a truncated decreasing forcing convolution from
below. Repeated partition points contribute empty intervals. -/
theorem sum_mul_measureReal_Ioc_le_renewalConv (hh : Antitone h)
    (hμ : μ (Iic t) ≠ ∞) (p : ℕ → ℝ≥0) (hp : Monotone p) (hp0 : p 0 = 0)
    (N : ℕ) (hNt : p N ≤ t) :
    (∑ k ∈ Finset.range N,
      h (p (k + 1)) * μ.real (Ioc (t - p (k + 1)) (t - p k))) ≤
      renewalConv ((Iio (p N)).indicator h) μ t := by
  have hC : ∀ s ≤ t, |h s| ≤ max |h t| |h 0| :=
    fun s hs ↦ abs_le_max_abs_abs (hh hs) (hh zero_le)
  have hi := integrableOn_Iic_sub hh.measurable hC hμ
  rw [renewalConv_indicator_Iio_eq_sum p hp hp0 N hNt (hi.mono_set Ioc_subset_Iic_self)]
  apply Finset.sum_le_sum
  intro k hk
  have hkt : p (k + 1) ≤ t := (hp (Finset.mem_range.mp hk)).trans hNt
  have hfin : μ (Ioc (t - p (k + 1)) (t - p k)) ≠ ∞ :=
    ne_top_of_le_ne_top hμ (measure_mono fun s hs ↦ hs.2.trans tsub_le_self)
  have hint := hi.mono_set (s := Ioc (t - p (k + 1)) (t - p k))
    (fun s hs ↦ hs.2.trans tsub_le_self)
  simpa [mul_comm] using setIntegral_mono_on (integrableOn_const hfin) hint
    measurableSet_Ioc (fun s hs ↦ hh ((tsub_le_iff_left).2
      (le_of_lt ((tsub_lt_iff_right hkt).1 hs.1))))

/-- The left-endpoint Darboux sum bounds a truncated decreasing forcing convolution from
above. No nonnegativity or continuity hypothesis on the forcing is needed. -/
theorem renewalConv_le_sum_mul_measureReal_Ioc (hh : Antitone h)
    (hμ : μ (Iic t) ≠ ∞) (p : ℕ → ℝ≥0) (hp : Monotone p) (hp0 : p 0 = 0)
    (N : ℕ) (hNt : p N ≤ t) :
    renewalConv ((Iio (p N)).indicator h) μ t ≤
      ∑ k ∈ Finset.range N,
        h (p k) * μ.real (Ioc (t - p (k + 1)) (t - p k)) := by
  have hC : ∀ s ≤ t, |h s| ≤ max |h t| |h 0| :=
    fun s hs ↦ abs_le_max_abs_abs (hh hs) (hh zero_le)
  have hi := integrableOn_Iic_sub hh.measurable hC hμ
  rw [renewalConv_indicator_Iio_eq_sum p hp hp0 N hNt (hi.mono_set Ioc_subset_Iic_self)]
  apply Finset.sum_le_sum
  intro k hk
  have hkt : p k ≤ t := (hp (le_of_lt (Finset.mem_range.mp hk))).trans hNt
  have hfin : μ (Ioc (t - p (k + 1)) (t - p k)) ≠ ∞ :=
    ne_top_of_le_ne_top hμ (measure_mono fun s hs ↦ hs.2.trans tsub_le_self)
  have hint := hi.mono_set (s := Ioc (t - p (k + 1)) (t - p k))
    (fun s hs ↦ hs.2.trans tsub_le_self)
  simpa [mul_comm] using setIntegral_mono_on hint (integrableOn_const hfin)
    measurableSet_Ioc (fun s hs ↦ hh ((le_tsub_iff_right (hs.2.trans tsub_le_self)).2
      ((le_tsub_iff_left hkt).1 hs.2)))

end TauCeti.Probability
