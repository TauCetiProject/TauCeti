/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Half-line Darboux sums with vanishing mesh

For a nonnegative decreasing integrable function on the positive half-line, the upper and
lower uniform-mesh Darboux sums bracket its integral. Their difference is exactly the mesh
size times the value at zero. Consequently both sums converge to the integral as the mesh
tends to zero through positive values, even on the unbounded interval and without continuity.
These estimates allow step-function approximations in convolution limit theorems.

The proofs use Mathlib's integral test (`AntitoneOn.summable_of_integrableOn_Ioi_zero`,
`AntitoneOn.tsum_add_one_le_integral`, and `AntitoneOn.integral_le_tsum`) after dilation.
The half-line approximation is used in Feller, *An Introduction to Probability Theory and
Its Applications*, vol. II, second edition, Chapter XI, in the key renewal theorem.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace AntitoneOn

variable {f : ℝ → ℝ}

/-- A positive-mesh sample of a nonnegative decreasing integrable function on the half-line
is summable, including its value at zero. -/
theorem summable_mul_natCast (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x)
    {δ : ℝ} (hδ : 0 < δ) : Summable (fun n : ℕ => f (δ * n)) := by
  have hanti : AntitoneOn (fun x => f (δ * x)) (Ici 0) :=
    fun x hx y hy hxy => hf (mul_nonneg hδ.le hx) (mul_nonneg hδ.le hy)
      (mul_le_mul_of_nonneg_left hxy hδ.le)
  have hint : IntegrableOn (fun x => f (δ * x)) (Ioi 0) := by
    simpa using (integrableOn_Ioi_comp_mul_left_iff f 0 hδ).2 (by simpa using hi)
  exact hanti.summable_of_integrableOn_Ioi_zero hint fun x hx => hn _ (mul_pos hδ hx)

/-- Lower and upper uniform-mesh Darboux sums bracket the half-line integral. No continuity
is needed, and either sum may include values at discontinuities. -/
theorem mul_tsum_le_integral_le_mul_tsum (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x)
    {δ : ℝ} (hδ : 0 < δ) :
    δ * (∑' n : ℕ, f (δ * (n + 1))) ≤ ∫ x in Ioi 0, f x ∧
      (∫ x in Ioi 0, f x) ≤ δ * (∑' n : ℕ, f (δ * n)) := by
  have hanti : AntitoneOn (fun x => f (δ * x)) (Ici 0) :=
    fun x hx y hy hxy => hf (mul_nonneg hδ.le hx) (mul_nonneg hδ.le hy)
      (mul_le_mul_of_nonneg_left hxy hδ.le)
  have hint : IntegrableOn (fun x => f (δ * x)) (Ioi 0) := by
    simpa using (integrableOn_Ioi_comp_mul_left_iff f 0 hδ).2 (by simpa using hi)
  have hnonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f (δ * x) :=
    fun x hx => hn _ (mul_pos hδ hx)
  have hscale : δ * (∫ x in Ioi 0, f (δ * x)) = ∫ x in Ioi 0, f x := by
    simpa using integral_comp_mul_left_Ioi' f 0 hδ
  constructor
  · have h := mul_le_mul_of_nonneg_left (hanti.tsum_add_one_le_integral hint hnonneg) hδ.le
    simpa only [Nat.cast_add, Nat.cast_one, hscale] using h
  · have h := mul_le_mul_of_nonneg_left
      (hanti.integral_le_tsum (hf.summable_mul_natCast hi hn hδ) hnonneg) hδ.le
    rwa [hscale] at h

/-- The error in the upper half-line Darboux sum is at most the mesh times the value at zero.
In particular this controls the infinite tail as well as the bounded part of the integral. -/
theorem abs_mul_tsum_sub_integral_le (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x)
    {δ : ℝ} (hδ : 0 < δ) :
    |δ * (∑' n : ℕ, f (δ * n)) - ∫ x in Ioi 0, f x| ≤ δ * f 0 := by
  obtain ⟨hl, hu⟩ := hf.mul_tsum_le_integral_le_mul_tsum hi hn hδ
  have hsum := (hf.summable_mul_natCast hi hn hδ).tsum_eq_zero_add
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsum
  rw [abs_of_nonneg (sub_nonneg.mpr hu), hsum, mul_add]
  linarith

/-- Upper uniform-mesh Darboux sums of a nonnegative decreasing integrable function converge
to its integral as the mesh tends to zero from above. -/
theorem tendsto_mul_tsum_integral (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x) :
    Tendsto (fun δ : ℝ => δ * ∑' n : ℕ, f (δ * n)) (𝓝[>] 0)
      (𝓝 (∫ x in Ioi 0, f x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (g := fun δ : ℝ => δ * f 0)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    simpa only [Real.norm_eq_abs] using hf.abs_mul_tsum_sub_integral_le hi hn hδ
  · have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul] using hid.mul_const (f 0)

/-- Lower uniform-mesh Darboux sums have the same integral limit. This remains valid for
functions with jumps, including a jump at zero. -/
theorem tendsto_mul_tsum_add_one_integral (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x) :
    Tendsto (fun δ : ℝ => δ * ∑' n : ℕ, f (δ * (n + 1))) (𝓝[>] 0)
      (𝓝 (∫ x in Ioi 0, f x)) := by
  have hid : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim := (hf.tendsto_mul_tsum_integral hi hn).sub (hid.mul_const (f 0))
  simp only [zero_mul, sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hsum := (hf.summable_mul_natCast hi hn hδ).tsum_eq_zero_add
  simp only [Nat.cast_zero, mul_zero, Nat.cast_add, Nat.cast_one] at hsum
  rw [hsum, mul_add, add_sub_cancel_left]

end AntitoneOn
