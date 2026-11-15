/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Darboux sums and decreasing integrable functions

For a nonnegative decreasing integrable function on the positive half-line, the upper and
lower uniform-mesh Darboux sums bracket its integral. Their difference is exactly the mesh
size times the value at zero. Consequently both sums converge to the integral as the mesh
tends to zero through positive values, even on the unbounded interval and without continuity.
These estimates allow step-function approximations in convolution limit theorems.
Finite uniform-mesh sums also bracket the integral on `[0, δ * N]`, including zero mesh,
and their gap vanishes under refinement of a fixed interval. A nonnegative decreasing
integrable function on the positive half-line vanishes at infinity.

The proofs use Mathlib's integral test (`AntitoneOn.summable_of_integrableOn_Ioi_zero`,
`AntitoneOn.tsum_add_one_le_integral`, and `AntitoneOn.integral_le_tsum`) after dilation,
and the finite comparisons `AntitoneOn.sum_le_integral` and `AntitoneOn.integral_le_sum`.
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

/-- Finite uniform-mesh Darboux sums bracket the integral of a decreasing function.
The endpoints of the interval are zero and the mesh times the number of cells. -/
theorem mul_sum_le_integral_le_mul_sum {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ) (hf : AntitoneOn f (Icc 0 (δ * N))) :
    δ * (∑ k ∈ Finset.range N, f (δ * (k + 1))) ≤ ∫ x in 0..δ * N, f x ∧
      (∫ x in 0..δ * N, f x) ≤ δ * (∑ k ∈ Finset.range N, f (δ * k)) := by
  have hg : AntitoneOn (fun x => f (δ * x)) (Icc 0 (N : ℝ)) := by
    intro x hx y hy hxy
    exact hf ⟨mul_nonneg hδ hx.1, mul_le_mul_of_nonneg_left hx.2 hδ⟩
      ⟨mul_nonneg hδ hy.1, mul_le_mul_of_nonneg_left hy.2 hδ⟩
      (mul_le_mul_of_nonneg_left hxy hδ)
  have heq : δ * (∫ x in (0 : ℝ)..N, f (δ * x)) = ∫ x in 0..δ * N, f x := by
    simpa using intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := N) f δ
  have hg' : AntitoneOn (fun x => f (δ * x)) (Icc 0 (0 + (N : ℝ))) := by
    simpa only [zero_add] using hg
  constructor
  · have hl := mul_le_mul_of_nonneg_left (hg'.sum_le_integral (x₀ := 0) (a := N)) hδ
    simpa only [zero_add, Nat.cast_add, Nat.cast_one, heq] using hl
  · have hu := mul_le_mul_of_nonneg_left (hg'.integral_le_sum (x₀ := 0) (a := N)) hδ
    simpa only [zero_add, heq] using hu

/-- Uniform-mesh sums bracket a nonnegative multiple of the integral on `[0, A]`, and
their gap tends to zero as the mesh is refined. The function can have either sign. -/
theorem uniform_mesh_darboux_bounds {A : ℝ} (hf : AntitoneOn f (Icc 0 A))
    (hA : 0 ≤ A) {r : ℝ} (hr : 0 ≤ r) :
    let δ (n : ℕ) : ℝ := A / (n + 1)
    let p (n k : ℕ) : ℝ := δ n * k
    let L (n : ℕ) : ℝ := r * δ n * ∑ k ∈ Finset.range (n + 1), f (p n (k + 1))
    let U (n : ℕ) : ℝ := r * δ n * ∑ k ∈ Finset.range (n + 1), f (p n k)
    (∀ n, L n ≤ r * ∫ x in (0 : ℝ)..A, f x ∧
      r * (∫ x in (0 : ℝ)..A, f x) ≤ U n) ∧
      Tendsto (fun n => U n - L n) atTop (𝓝 0) := by
  intro δ p L U
  have hp0 (n : ℕ) : p n 0 = 0 := by simp [p]
  have hpN (n : ℕ) : p n (n + 1) = A := by
    dsimp [p, δ]
    simp only [Nat.cast_add, Nat.cast_one]
    exact div_mul_cancel₀ A (by positivity)
  constructor
  · intro n
    have hend : δ n * ↑(n + 1) = A := hpN n
    have hf' : AntitoneOn f (Icc 0 (δ n * ↑(n + 1))) := by rwa [hend]
    have hb : δ n * (∑ k ∈ Finset.range (n + 1), f (δ n * (k + 1))) ≤
        ∫ x in (0 : ℝ)..A, f x ∧
        (∫ x in (0 : ℝ)..A, f x) ≤ δ n * ∑ k ∈ Finset.range (n + 1), f (δ n * k) := by
      simpa only [hend] using hf'.mul_sum_le_integral_le_mul_sum (δ := δ n)
        (div_nonneg hA (by positivity) : 0 ≤ δ n) (n + 1)
    exact ⟨by simpa only [L, p, Nat.cast_add, Nat.cast_one, mul_assoc] using
      mul_le_mul_of_nonneg_left hb.1 hr,
      by simpa only [U, p, mul_assoc] using mul_le_mul_of_nonneg_left hb.2 hr⟩
  · have hgap (n : ℕ) : U n - L n = r * δ n * (f 0 - f A) := by
      have hs := Finset.sum_range_sub' (fun k => f (p n k)) (n + 1)
      simp only [hp0, hpN] at hs
      dsimp [U, L]
      rw [← mul_sub, ← Finset.sum_sub_distrib, hs]
    have hdlim : Tendsto δ atTop (𝓝 0) := by
      simpa only [δ] using (tendsto_const_nhds (x := A)).div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
          (tendsto_const_nhds (x := (1 : ℝ))))
    simpa only [hgap, mul_zero, zero_mul] using (hdlim.const_mul r).mul_const (f 0 - f A)

/-- A nonnegative decreasing integrable function on the positive half-line vanishes at
infinity, without any continuity assumption. -/
theorem tendsto_zero_of_integrableOn_Ioi (hf : AntitoneOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x) :
    Tendsto f atTop (𝓝 0) := by
  have hs := (hf.summable_of_integrableOn_Ioi_zero hi hn).tendsto_atTop_zero
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ha.trans_le (hn x hx)
  · obtain ⟨n, hn'⟩ := (hs.eventually_lt_const hb).exists
    filter_upwards [eventually_ge_atTop (n : ℝ)] with x hx
    exact (hf (Nat.cast_nonneg n) ((Nat.cast_nonneg n).trans hx) hx).trans_lt hn'

end AntitoneOn
