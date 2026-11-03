/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform derivative bounds for a linear change of variables

Fix maps `τ : E → F` and `L : E → (G →L H)` that are `C^n` on `s`. The operator
`φ ↦ (z ↦ L z (φ (τ z)))` is linear in `φ`, and by the Leibniz and Faà di Bruno bounds its
order-`n` derivative on a compact set `K ⊆ s` is controlled by the derivatives of `φ` of order at
most `n` along `τ '' K`, with a constant depending only on `τ`, `L`, `K` and `n`. Consequently, if
those derivatives of a family `φ i` tend to zero uniformly along `τ` on `K`, so does the order-`n`
derivative of `z ↦ L z (φ i (τ z))`.

This is the estimate behind continuity of such operators for topologies of uniform convergence of
derivatives on compact sets: a bilinear form read in one chart is of this shape in any other
chart, with `τ` the transition map and `L z` the pullback along its derivative.

## Main results

* `ContDiffOn.exists_bound_iteratedFDerivWithin`: on a compact subset, the derivatives of order at
  most `n` of a `C^n` map are bounded by one constant.
* `ContDiffOn.exists_norm_iteratedFDerivWithin_clm_apply_comp_le`: the linear bound on the
  derivatives of `z ↦ L z (φ (τ z))`.
* `ContDiffOn.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp`: its consequence for uniform
  convergence to zero.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- On a compact subset `K` of `s`, the derivatives within `s` of order at most `n` of a map that
is `C^n` on `s` are bounded by a single constant. -/
theorem ContDiffOn.exists_bound_iteratedFDerivWithin {u : E → F} {s K : Set E} {n : ℕ}
    (hu : ContDiffOn 𝕜 n u s) (hs : UniqueDiffOn 𝕜 s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ A, ∀ i ≤ n, ∀ z ∈ K, ‖iteratedFDerivWithin 𝕜 i u s z‖ ≤ A := by
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
    (f := fun z ↦ ∑ i ∈ Finset.range (n + 1), ‖iteratedFDerivWithin 𝕜 i u s z‖)
    (continuousOn_finsetSum _ fun i hi ↦
      ((hu.continuousOn_iteratedFDerivWithin (by exact_mod_cast Finset.mem_range_succ_iff.mp hi)
        hs).mono hKs).norm)
  refine ⟨A, fun i hi z hz ↦ ((Finset.single_le_sum (f := fun i ↦ ‖iteratedFDerivWithin 𝕜 i u s z‖)
    (fun _ _ ↦ norm_nonneg _) (Finset.mem_range_succ_iff.mpr hi)).trans (le_abs_self _)).trans ?_⟩
  simpa only [Real.norm_eq_abs] using hA z hz

/-- On a compact set `K`, the order-`n` derivative of `z ↦ L z (φ (τ z))` is bounded by a constant
multiple of any common bound `δ` for the derivatives of `φ` of order at most `n` along `τ '' K`.
The constant depends on `L`, `τ`, `K` and `n` but not on `φ`. -/
theorem ContDiffOn.exists_norm_iteratedFDerivWithin_clm_apply_comp_le {L : E → G →L[𝕜] H}
    {τ : E → F} {s : Set E} {t : Set F} {K : Set E} {n : ℕ} (hL : ContDiffOn 𝕜 n L s)
    (hτ : ContDiffOn 𝕜 n τ s) (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t)
    (hst : MapsTo τ s t) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ C, ∀ φ : F → G, ContDiffOn 𝕜 n φ t → ∀ δ : ℝ,
      (∀ i ≤ n, ∀ z ∈ K, ‖iteratedFDerivWithin 𝕜 i φ t (τ z)‖ ≤ δ) →
      ∀ z ∈ K, ‖iteratedFDerivWithin 𝕜 n (fun y ↦ L y (φ (τ y))) s z‖ ≤ C * δ := by
  obtain ⟨A, hA⟩ := hL.exists_bound_iteratedFDerivWithin hs hK hKs
  obtain ⟨D₀, hD₀⟩ := hτ.exists_bound_iteratedFDerivWithin hs hK hKs
  set D := max 1 D₀
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * ((n - i).factorial * D ^ (n - i)),
    fun φ hφ δ hδ z hz ↦ ?_⟩
  have hφτ : ContDiffOn 𝕜 n (φ ∘ τ) s := hφ.comp hτ hst
  refine (norm_iteratedFDerivWithin_clm_apply hL hφτ hs (hKs hz) le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hi : i ≤ n := Finset.mem_range_succ_iff.mp hi
  -- Faà di Bruno bound for the composite `φ ∘ τ`, using `D ≥ 1` to absorb the powers.
  have hcomp : ‖iteratedFDerivWithin 𝕜 (n - i) (φ ∘ τ) s z‖ ≤
      (n - i).factorial * δ * D ^ (n - i) :=
    norm_iteratedFDerivWithin_comp_le hφ hτ (by exact_mod_cast Nat.sub_le n i) ht hs hst (hKs hz)
      (fun j hj ↦ hδ j (hj.trans (Nat.sub_le n i)) z hz)
      fun j hj hjn ↦ (hD₀ j (hjn.trans (Nat.sub_le n i)) z hz).trans
        ((le_max_right 1 D₀).trans (le_self_pow₀ (le_max_left 1 D₀) (by omega)))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le n) z hz)
  calc (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i L s z‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) (φ ∘ τ) s z‖
      ≤ (n.choose i : ℝ) * A * ((n - i).factorial * δ * D ^ (n - i)) := by
        gcongr
        exact hA i hi z hz
    _ = (n.choose i : ℝ) * A * ((n - i).factorial * D ^ (n - i)) * δ := by ring

/-- If the derivatives of order at most `n` of a family `φ i` tend to zero uniformly along `τ` on a
compact set `K`, then so does the order-`n` derivative of `z ↦ L z (φ i (τ z))`. -/
theorem ContDiffOn.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp {ι : Type*}
    {l : Filter ι} {L : E → G →L[𝕜] H} {τ : E → F} {s : Set E} {t : Set F} {K : Set E} {n : ℕ}
    (hL : ContDiffOn 𝕜 n L s) (hτ : ContDiffOn 𝕜 n τ s) (hs : UniqueDiffOn 𝕜 s)
    (ht : UniqueDiffOn 𝕜 t) (hst : MapsTo τ s t) (hK : IsCompact K) (hKs : K ⊆ s)
    {φ : ι → F → G} (hφ : ∀ᶠ i in l, ContDiffOn 𝕜 n (φ i) t)
    (hφ₀ : ∀ j ≤ n, TendstoUniformlyOn (fun i z ↦ iteratedFDerivWithin 𝕜 j (φ i) t (τ z))
      (fun _ ↦ 0) l K) :
    TendstoUniformlyOn (fun i z ↦ iteratedFDerivWithin 𝕜 n (fun y ↦ L y (φ i (τ y))) s z)
      (fun _ ↦ 0) l K := by
  obtain ⟨C, hC⟩ := hL.exists_norm_iteratedFDerivWithin_clm_apply_comp_le hτ hs ht hst hK hKs
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  have hδ : 0 < ε / (|C| + 1) := by positivity
  have hev : ∀ᶠ i in l, ∀ j ∈ Finset.range (n + 1), ∀ z ∈ K,
      dist 0 (iteratedFDerivWithin 𝕜 j (φ i) t (τ z)) < ε / (|C| + 1) :=
    (Filter.eventually_all_finset _).mpr fun j hj ↦
      Metric.tendstoUniformlyOn_iff.mp (hφ₀ j (Finset.mem_range_succ_iff.mp hj)) _ hδ
  filter_upwards [hφ, hev] with i hφi hi z hz
  rw [dist_zero_left]
  calc _ ≤ C * (ε / (|C| + 1)) := hC (φ i) hφi _ (fun j hj z hz ↦ by
        simpa only [dist_zero_left] using (hi j (Finset.mem_range_succ_iff.mpr hj) z hz).le) z hz
    _ ≤ |C| * (ε / (|C| + 1)) := by gcongr; exact le_abs_self C
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg C]
