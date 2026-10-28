/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Riemann sums along a simple function

A simple function `u : α →ₛ β` cuts a set `K` into the finitely many measurable pieces
`K ∩ u ⁻¹' {z}`, one for each value `z` of `u`, and assigns the sample point `z` to that piece.
If `h (u y)` stays within `η` of `g y` on `K`, the resulting Riemann sum
`∑ z ∈ u.range, μ.real (K ∩ u ⁻¹' {z}) • h z` is within `η * μ.real K` of `∫ y in K, g y ∂μ`.

Taking for `u` a simple function uniformly close to the identity on a compact set, as provided by
`MeasureTheory.SimpleFunc.tendstoUniformlyOn_nearestPt`, every uniformly continuous function is
approximated by Riemann sums with these common sample points. Using one set of sample points for
several functions at once is what allows a linear functional which is only controlled on finite
linear combinations to be interchanged with an integral.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.SimpleFunc

variable {α β X : Type*} [MeasurableSpace α]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {μ : Measure α}

/-- **Riemann sums along a simple function.** If `h (u y)` is within `η` of `g y` for every `y` in
a measurable set `K` of finite measure, then the Riemann sum of `h` over the pieces
`K ∩ u ⁻¹' {z}` is within `η * μ.real K` of the integral of `g` over `K`. -/
theorem norm_sum_measureReal_smul_sub_setIntegral_le (u : SimpleFunc α β) {K : Set α}
    (hK : MeasurableSet K) (hμK : μ K ≠ ∞) {g : α → X} (hg : IntegrableOn g K μ) {h : β → X}
    {η : ℝ} (hgh : ∀ y ∈ K, ‖g y - h (u y)‖ ≤ η) :
    ‖∑ z ∈ u.range, μ.real (K ∩ u ⁻¹' {z}) • h z - ∫ y in K, g y ∂μ‖ ≤ η * μ.real K := by
  have hA (z : β) : MeasurableSet (K ∩ u ⁻¹' {z}) := hK.inter (u.measurableSet_fiber z)
  have hμA (z : β) : μ (K ∩ u ⁻¹' {z}) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt hμK.lt_top).ne
  have hdisj : (u.range : Set β).PairwiseDisjoint fun z ↦ K ∩ u ⁻¹' {z} := fun z _ w _ hzw ↦
    ((disjoint_singleton.2 hzw).preimage u).mono inter_subset_right inter_subset_right
  have hK' : (⋃ z ∈ u.range, K ∩ u ⁻¹' {z}) = K := by
    ext y
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff, exists_prop]
    exact ⟨fun ⟨_, _, hy, _⟩ ↦ hy, fun hy ↦ ⟨u y, u.mem_range_self y, hy, rfl⟩⟩
  have hint := integral_biUnion_finset u.range (fun z _ ↦ hA z) hdisj
    (fun z _ ↦ hg.mono_set inter_subset_left)
  have hμ := measureReal_biUnion_finset (μ := μ) hdisj (fun z _ ↦ hA z) (fun z _ ↦ hμA z)
  rw [hK'] at hint hμ
  rw [hint, hμ, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ ↦ ?_)
  -- On the piece where `u = z`, the integrand `h z - g y` is bounded by `η`.
  have hc : IntegrableOn (fun _ ↦ h z) (K ∩ u ⁻¹' {z}) μ := integrableOn_const (hμA z)
  rw [← setIntegral_const, ← MeasureTheory.integral_sub hc (hg.mono_set inter_subset_left)]
  refine norm_setIntegral_le_of_norm_le_const (hμA z).lt_top fun y hy ↦ ?_
  rw [norm_sub_rev, ← hy.2]
  exact hgh y hy.1

end MeasureTheory.SimpleFunc
