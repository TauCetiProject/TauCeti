/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Scalar

/-!
# Compact chart seminorms on the scalar field under dilations

On the scalar field `𝕜`, with its identity chart, the compact chart seminorms of a map
`f : 𝕜 → F` are suprema of the norms of its ordinary iterated derivatives `iteratedDeriv m f`
over a compact subset `K` of `𝕜` (`ContMDiffMap.chartCkSeminorm_selfChartCompacts_le_iff`).

This file computes these seminorms under the simplest change of coordinates, the dilation
`y ↦ c * y`. If `g y = f (c * y)`, the chain rule gives
`iteratedDeriv m g y = c ^ m • iteratedDeriv m f (c * y)`, so the `m`th derivative seminorm of `g`
on `K` is exactly `‖c‖ ^ m` times that of `f` on the image `c • K`
(`ContMDiffMap.chartDerivativeSeminorm_selfChartCompacts_of_forall_apply_eq_apply_mul`).
Consequently the compact `C^k` seminorm of `g` is at most `max 1 ‖c‖ ^ k` times that of `f`
(`ContMDiffMap.chartCkSeminorm_selfChartCompacts_le_of_forall_apply_eq_apply_mul`). For a
contraction, `‖c‖ ≤ 1`, the constant is `1` in every order
(`ContMDiffMap.chartCkSeminorm_selfChartCompacts_le_of_forall_apply_eq_apply_mul_of_norm_le_one`);
for an expansion it is `‖c‖ ^ k`, which grows with the order. These give explicit constants in
the scalar-field analogue of the comparison of compact chart seminorms under a change of charts
(`ContMDiffMap.exists_chartCkSeminorm_le_coordChange`), where the change of coordinates is
applied to the map rather than to the chart.

## Main results

* `ContMDiffMap.chartDerivativeSeminorm_selfChartCompacts_of_forall_apply_eq_apply_mul`:
  dilating the variable by `c` multiplies the `m`th derivative seminorm by `‖c‖ ^ m`.
* `ContMDiffMap.chartCkSeminorm_selfChartCompacts_le_of_forall_apply_eq_apply_mul`: dilating
  the variable by `c` multiplies the `C^k` seminorm by at most `max 1 ‖c‖ ^ k`.
-/

public section

open Set TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}

/-- **Compact chart seminorms under a dilation.** If `g y = f (c * y)` on `𝕜`, the `m`th
derivative seminorm of `g` on a compact set `K` is `‖c‖ ^ m` times that of `f` on the image
`c • K`, in the charts at any two points. -/
theorem chartDerivativeSeminorm_selfChartCompacts_of_forall_apply_eq_apply_mul
    {f g : C^n⟮𝓘(𝕜), 𝕜; 𝓘(𝕜, F), F⟯} {c : 𝕜} (hg : ∀ y, g y = f (c * y)) (x y : 𝕜)
    (K : Compacts 𝕜) (m : ℕ) (hm : m ≤ n) :
    chartDerivativeSeminorm x (selfChartCompacts x K) m hm g =
      ‖c‖ ^ m * chartDerivativeSeminorm y
        (selfChartCompacts y (K.map (c * ·) (continuous_const_mul c))) m hm f := by
  set A := chartDerivativeSeminorm x (selfChartCompacts x K) m hm g
  set B := chartDerivativeSeminorm y
    (selfChartCompacts y (K.map (c * ·) (continuous_const_mul c))) m hm f
  have hmem {z : 𝕜} (hz : z ∈ K) : c * z ∈ K.map (c * ·) (continuous_const_mul c) := by
    rw [← SetLike.mem_coe, Compacts.coe_map]
    exact mem_image_of_mem _ hz
  have hnorm (z : 𝕜) : ‖iteratedDeriv m g z‖ = ‖c‖ ^ m * ‖iteratedDeriv m f (c * z)‖ := by
    rw [show (g : 𝕜 → F) = fun y ↦ f (c * y) from funext hg,
      iteratedDeriv_comp_const_smul ((contMDiff_iff_contDiff.mp f.contMDiff).of_le hm), norm_smul,
      norm_pow]
  refine le_antisymm ((chartDerivativeSeminorm_selfChartCompacts_le_iff g x K m hm
    (by positivity)).mpr fun z hz ↦ ?_) ?_
  · rw [hnorm]
    gcongr
    exact norm_iteratedDeriv_le_chartDerivativeSeminorm f y _ m hm (hmem hz)
  · rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ ‖c‖ ^ m) with hc | hc
    · rw [← hc, zero_mul]
      exact apply_nonneg _ _
    rw [← le_div_iff₀' hc]
    refine (chartDerivativeSeminorm_selfChartCompacts_le_iff f y _ m hm
      (by positivity)).mpr fun w hw ↦ ?_
    rw [← SetLike.mem_coe, Compacts.coe_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [le_div_iff₀' hc, ← hnorm]
    exact norm_iteratedDeriv_le_chartDerivativeSeminorm g x K m hm hz

/-- **Compact `C^k` seminorms under a dilation.** If `g y = f (c * y)` on `𝕜`, the compact
`C^k` seminorm of `g` on a compact set `K` is at most `max 1 ‖c‖ ^ k` times that of `f` on the
image `c • K`, in the charts at any two points. -/
theorem chartCkSeminorm_selfChartCompacts_le_of_forall_apply_eq_apply_mul
    {f g : C^n⟮𝓘(𝕜), 𝕜; 𝓘(𝕜, F), F⟯} {c : 𝕜} (hg : ∀ y, g y = f (c * y)) (x y : 𝕜)
    (K : Compacts 𝕜) (k : ℕ) (hk : k ≤ n) :
    chartCkSeminorm x (selfChartCompacts x K) k hk g ≤
      max 1 ‖c‖ ^ k * chartCkSeminorm y
        (selfChartCompacts y (K.map (c * ·) (continuous_const_mul c))) k hk f := by
  refine (chartCkSeminorm_selfChartCompacts_le_iff g x K k hk (by positivity)).mpr
    fun m hm z hz ↦ ?_
  have hmn : (m : WithTop ℕ∞) ≤ n := (Nat.cast_le.mpr hm).trans hk
  -- Bound the `m`th derivative by its seminorm, then apply the dilation law in order `m`.
  refine (norm_iteratedDeriv_le_chartDerivativeSeminorm g x K m hmn hz).trans ?_
  rw [chartDerivativeSeminorm_selfChartCompacts_of_forall_apply_eq_apply_mul hg x y K m hmn]
  gcongr
  · exact (pow_le_pow_left₀ (norm_nonneg c) (le_max_right 1 ‖c‖) m).trans
      (pow_le_pow_right₀ (le_max_left 1 ‖c‖) hm)
  · exact (chartDerivativeSeminorm_selfChartCompacts_le_iff f y _ m hmn (apply_nonneg _ _)).mpr
      fun w hw ↦ norm_iteratedDeriv_le_chartCkSeminorm f y _ k hk hm hw

/-- **Compact `C^k` seminorms under a contraction.** If `g y = f (c * y)` on `𝕜` with `‖c‖ ≤ 1`,
the compact `C^k` seminorm of `g` on a compact set `K` is at most that of `f` on the image
`c • K`, with constant `1` in every order `k`. -/
theorem chartCkSeminorm_selfChartCompacts_le_of_forall_apply_eq_apply_mul_of_norm_le_one
    {f g : C^n⟮𝓘(𝕜), 𝕜; 𝓘(𝕜, F), F⟯} {c : 𝕜} (hg : ∀ y, g y = f (c * y)) (hc : ‖c‖ ≤ 1)
    (x y : 𝕜) (K : Compacts 𝕜) (k : ℕ) (hk : k ≤ n) :
    chartCkSeminorm x (selfChartCompacts x K) k hk g ≤
      chartCkSeminorm y (selfChartCompacts y (K.map (c * ·) (continuous_const_mul c))) k hk f := by
  simpa [max_eq_left hc] using
    chartCkSeminorm_selfChartCompacts_le_of_forall_apply_eq_apply_mul hg x y K k hk

end ContMDiffMap
