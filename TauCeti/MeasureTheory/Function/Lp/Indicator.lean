/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Indicator classes in `Lᵖ`

The class `MeasureTheory.indicatorConstLp p hs hμs c` of `s.indicator fun _ => c` is linear in the
constant `c`: Mathlib provides additivity, `MeasureTheory.indicatorConstLp_add`, and this file adds
compatibility with scalar multiplication. Together with the norm formula
`MeasureTheory.norm_indicatorConstLp`, this makes `c ↦ indicatorConstLp p hs hμs c` a bounded
linear map, so closed subspaces of `Lᵖ` can be tested on indicator classes of a dense set of
constants.

Indicator classes of pairwise disjoint sets of finite measure span a weighted finite `ℓ¹` space
inside `L¹`: the norm of `∑ i, indicatorConstLp 1 (hs i) (hμs i) (c i)` is
`∑ i, μ(s i) * ‖c i‖`.

## Main declarations

* `TauCeti.indicatorConstLp_smul`: the indicator class of `a • c` is `a` times that of `c`.
* `TauCeti.norm_sum_indicatorConstLp_one`: the `L¹` norm of a sum of indicator classes of pairwise
  disjoint sets.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [NormedAddCommGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {s : Set α}

/-- A version of `Set.indicator_const_smul` for `MeasureTheory.indicatorConstLp`. -/
theorem indicatorConstLp_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (a : 𝕜) (c : E) :
    indicatorConstLp p hs hμs (a • c) = a • indicatorConstLp p hs hμs c := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := a • c),
    Lp.coeFn_smul a (indicatorConstLp p hs hμs c),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃]
  by_cases hx : x ∈ s <;> simp [hx]


section Disjoint

variable {ι : Type*} [Fintype ι] {s : ι → Set α}

/-- The `L¹` norm of a sum of indicator classes of pairwise disjoint sets of finite measure is the
sum of the norms of the constants, weighted by the measures of the sets. -/
theorem norm_sum_indicatorConstLp_one (hs : ∀ i, MeasurableSet (s i)) (hμs : ∀ i, μ (s i) ≠ ∞)
    (hd : Pairwise (Function.onFun Disjoint s)) (c : ι → E) :
    ‖∑ i, indicatorConstLp 1 (hs i) (hμs i) (c i)‖ = ∑ i, μ.real (s i) * ‖c i‖ := by
  rw [L1.norm_eq_integral_norm]
  -- Almost everywhere, at most one of the indicator functions is nonzero.
  have hae : (fun x ↦ ‖(∑ i, indicatorConstLp 1 (hs i) (hμs i) (c i)) x‖) =ᵐ[μ]
      fun x ↦ ∑ i, (s i).indicator (fun _ ↦ ‖c i‖) x := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        fun i ↦ indicatorConstLp 1 (hs i) (hμs i) (c i),
      ae_all_iff.2 fun i ↦ indicatorConstLp_coeFn (p := 1) (hs := hs i) (hμs := hμs i)
        (c := c i)] with x h₁ h₂
    simp only [h₁, h₂]
    by_cases hx : ∃ k, x ∈ s k
    · obtain ⟨k, hk⟩ := hx
      have hne (i : ι) (hi : i ≠ k) : x ∉ s i := fun hxi ↦ Set.disjoint_left.1 (hd hi) hxi hk
      rw [Finset.sum_eq_single k (fun i _ hi ↦ by simp [hne i hi]) (by simp),
        Finset.sum_eq_single k (fun i _ hi ↦ by simp [hne i hi]) (by simp)]
      simp [hk]
    · simp only [not_exists] at hx
      simp [hx]
  rw [integral_congr_ae hae, integral_finsetSum _ fun i _ ↦
    (integrableOn_const (hμs i)).integrable_indicator (hs i)]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [integral_indicator_const _ (hs i), smul_eq_mul]

end Disjoint

end TauCeti
