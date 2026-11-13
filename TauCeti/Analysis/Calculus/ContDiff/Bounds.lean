/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Uniform derivative bounds on compact sets

This file collects bounds on iterated derivatives that follow from their continuity on compact
sets: a uniform bound for a linear change of variables, and a bound by any power of the Japanese
bracket near the zero frequency. It also records the Leibniz bound for a bilinear expression in two
maps whose derivatives have uniform bounds, and the effect of a dilation on such bounds.

Fix maps `τ : E → F` and `L : E → (G →L H)` that are `C^n` on `s`. The operator
`φ ↦ (z ↦ L z (φ (τ z)))` is linear in `φ`, and by the Leibniz and Faà di Bruno bounds its
order-`n` derivative on a compact set `K ⊆ s` is controlled by the derivatives of `φ` of order at
most `n` along `τ '' K`, with a constant depending only on `τ`, `L`, `K` and `n`. Consequently, if
those derivatives of a family `φ i` tend to zero uniformly along `τ` on `K`, so does the order-`n`
derivative of `z ↦ L z (φ i (τ z))`.

This is the estimate behind continuity of such operators for topologies of uniform convergence of
derivatives on compact sets: a bilinear form read in one chart is of this shape in any other
chart, with `τ` the transition map and `L z` the pullback along its derivative.

A `C^k` function of a position `x` and a frequency `ξ` has bounded derivatives for `x` in a compact
set and `ξ` in a ball, and the Japanese bracket `(1 + ‖ξ‖ ^ 2) ^ (1 / 2)` is bounded above and
below on a ball. So these derivatives are bounded by every power of the Japanese bracket, which is
how symbol estimates are proved near the zero frequency, where no decay is needed.

## Main results

* `ContDiffOn.exists_bound_iteratedFDerivWithin`: on a compact subset, the derivatives of order at
  most `n` of a `C^n` map are bounded by one constant.
* `ContDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen`: the same for the derivatives of a
  map that is `C^n` on an open set, with a nonnegative constant.
* `IsCompact.exists_norm_fderiv_le`: the derivative of a map that is `C^1` at every point of a
  compact set is bounded on that set.
* `HasCompactSupport.exists_bound_iteratedFDeriv_of_contDiff`: the derivatives of order at most `n`
  of a compactly supported `C^n` map are bounded by one constant.
* `ContDiffAt.exists_ball_bound_iteratedFDeriv`: on some ball around a point where a map is
  `C^n`, its derivatives of order at most `n` are bounded by one constant.
* `ContDiffOn.exists_norm_iteratedFDerivWithin_clm_apply_comp_le`: the linear bound on the
  derivatives of `z ↦ L z (φ (τ z))`.
* `ContDiffOn.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp`: its consequence for uniform
  convergence to zero.
* `ContDiff.exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_norm_le`: for `x` in a compact set
  and `ξ` in a ball, the derivatives of a `C^k` function of `(x, ξ)` are bounded by every power of
  the Japanese bracket `(1 + ‖ξ‖ ^ 2) ^ (1 / 2)`.
* `ContDiff.exists_norm_iteratedFDeriv_le_of_eq_of_lt_norm`: a smooth map which agrees outside a
  ball with a map of bounded order-`n` derivative has a bounded order-`n` derivative.
* `ContinuousLinearMap.norm_iteratedFDeriv_le_two_pow_mul_of_bilinear`: the Leibniz bound for
  `x ↦ B (f x) (g x)` when the derivatives of `f` and `g` have uniform bounds.
* `ContDiff.norm_iteratedFDeriv_comp_const_smul_le`: rescaling the variable by `c` with
  `1 ≤ ‖c‖` multiplies uniform derivative bounds of order at most `N` by at most `‖c‖ ^ N`.
* `ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear`: along any filter, if the derivatives of
  order at most `n` of `f` and `g` are `O(ρ₁)` and `O(ρ₂)`, then the order-`n` derivative of
  `y ↦ B (f y) (g y)` is `O(ρ₁ ρ₂)`.
* `ContDiff.isBigO_iteratedFDeriv_smulRight`: the same for `y ↦ (f y).smulRight (g y)`.
-/

public section

open Set
open scoped NNReal

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

/-- The derivative of a map that is `C^n`, with `1 ≤ n`, at every point of a compact set `K` is
bounded on `K` by a single constant. -/
theorem IsCompact.exists_norm_fderiv_le {f : E → F} {K : Set E} {n : WithTop ℕ∞}
    (hK : IsCompact K) (hn : 1 ≤ n) (hf : ∀ x ∈ K, ContDiffAt 𝕜 n f x) :
    ∃ M : ℝ≥0, ∀ x ∈ K, ‖fderiv 𝕜 f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn fun x hx ↦
    ((hf x hx).fderiv_right (m := 0) (by simpa using hn)).continuousAt.continuousWithinAt
  exact ⟨M.toNNReal, fun x hx ↦ (hM x hx).trans (Real.le_coe_toNNReal M)⟩

/-- On a compact subset `K` of an open set `s`, the derivatives of order at most `n` of a map that
is `C^n` on `s` are bounded by a single nonnegative constant. -/
theorem ContDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen {u : E → F} {s K : Set E} {n : ℕ}
    (hu : ContDiffOn 𝕜 n u s) (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ A, 0 ≤ A ∧ ∀ i ≤ n, ∀ z ∈ K, ‖iteratedFDeriv 𝕜 i u z‖ ≤ A := by
  obtain ⟨A, hA⟩ := hu.exists_bound_iteratedFDerivWithin hs.uniqueDiffOn hK hKs
  refine ⟨max A 0, le_max_right _ _, fun i hi z hz ↦ ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen i hs (hKs hz)]
  exact (hA i hi z hz).trans (le_max_left _ _)

/-- The derivatives of order at most `n` of a compactly supported `C^n` map are bounded by a
single constant. Mathlib's `HasCompactSupport.exists_bound_iteratedFDeriv` assumes the map
smooth. -/
theorem HasCompactSupport.exists_bound_iteratedFDeriv_of_contDiff {f : E → F} {n : ℕ}
    (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 n f) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ n, ∀ y, ‖iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := (hf'.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
      (hf.iteratedFDeriv 0)
    refine ⟨max C 0, le_max_right _ _, fun i hi y ↦ ?_⟩
    obtain rfl : i = 0 := by omega
    exact (hC y).trans (le_max_left _ _)
  | succ n ih =>
    obtain ⟨N, hN0, hN⟩ := ih (hf'.of_le (by exact_mod_cast n.le_succ))
    obtain ⟨C, hC⟩ := (hf'.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
      (hf.iteratedFDeriv (n + 1))
    refine ⟨max N C, hN0.trans (le_max_left _ _), fun i hi y ↦ ?_⟩
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact (hN i (by omega) y).trans (le_max_left _ _)
    · exact (hC y).trans (le_max_right _ _)

/-- On some ball around a point `x` at which `f` is `C^n`, the derivatives of order at most `n`
of `f` are bounded by a single constant. -/
theorem ContDiffAt.exists_ball_bound_iteratedFDeriv {f : E → F} {x : E} {n : ℕ}
    (hf : ContDiffAt 𝕜 n f x) :
    ∃ r > 0, ∃ A, ∀ i ≤ n, ∀ y ∈ Metric.ball x r, ‖iteratedFDeriv 𝕜 i f y‖ ≤ A := by
  have hev : ∀ᶠ y in nhds x, ∀ i ∈ Finset.range (n + 1),
      ‖iteratedFDeriv 𝕜 i f y‖ < ‖iteratedFDeriv 𝕜 i f x‖ + 1 :=
    (Filter.eventually_all_finset _).mpr fun i hi ↦ ((hf.continuousAt_iteratedFDeriv
      (by exact_mod_cast Finset.mem_range_succ_iff.mp hi)).norm).eventually
        (gt_mem_nhds (lt_add_one _))
  obtain ⟨r, hr0, hr⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨r, hr0, ∑ i ∈ Finset.range (n + 1), (‖iteratedFDeriv 𝕜 i f x‖ + 1),
    fun i hi y hy ↦ ?_⟩
  have hi' := Finset.mem_range_succ_iff.mpr hi
  exact (hr y hy i hi').le.trans (Finset.single_le_sum
    (f := fun i ↦ ‖iteratedFDeriv 𝕜 i f x‖ + 1) (fun _ _ ↦ by positivity) hi')

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

/-- A `C^k` function on `E × F` satisfies, for `x` in a compact set and `ξ` in a ball, the
estimate `‖D^k f(x, ξ)‖ ≤ C (1 + ‖ξ‖ ^ 2) ^ (r / 2)` for every real `r`: the derivative is bounded
there, and the weight is bounded below. -/
theorem ContDiff.exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [ProperSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}
    {f : E × F → G} (hf : ContDiff ℝ k f) {K : Set E} (hK : IsCompact K) (R r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ : F, ‖ξ‖ ≤ R →
      ‖iteratedFDeriv ℝ k f (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : F) R)).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv le_rfl).continuousOn
  refine ⟨max C 0 / (1 + R ^ 2) ^ (-|r| / 2), by positivity, fun x hx ξ hξ ↦ ?_⟩
  calc ‖iteratedFDeriv ℝ k f (x, ξ)‖ ≤ max C 0 :=
        (hC (x, ξ) ⟨hx, by simpa using hξ⟩).trans (le_max_left _ _)
    _ = max C 0 / (1 + R ^ 2) ^ (-|r| / 2) * (1 + R ^ 2) ^ (-|r| / 2) := by field_simp
    _ ≤ max C 0 / (1 + R ^ 2) ^ (-|r| / 2) * (1 + ‖ξ‖ ^ 2) ^ (r / 2) :=
        mul_le_mul_of_nonneg_left (TauCeti.one_add_sq_rpow_neg_abs_le_one_add_norm_sq_rpow hξ r)
          (by positivity)

/-- A `C^n` map which agrees outside a ball with a map whose order-`n` derivative is bounded
there has a bounded order-`n` derivative: on the closed ball the derivative is continuous, and
outside it the two derivatives coincide. -/
theorem ContDiff.exists_norm_iteratedFDeriv_le_of_eq_of_lt_norm [ProperSpace E] {n : ℕ}
    {f g : E → F} (hf : ContDiff 𝕜 n f) {R C : ℝ} (hfg : ∀ x, R < ‖x‖ → f x = g x)
    (hg : ∀ x, R < ‖x‖ → ‖iteratedFDeriv 𝕜 n g x‖ ≤ C) :
    ∃ C', ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ C' := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv le_rfl).continuousOn
  refine ⟨max C₀ C, fun x ↦ ?_⟩
  by_cases hx : ‖x‖ ≤ R
  · exact (hC₀ x (mem_closedBall_zero_iff.2 hx)).trans (le_max_left _ _)
  rw [not_le] at hx
  have hfg' : f =ᶠ[nhds x] g := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact hfg y hy
  rw [(hfg'.iteratedFDeriv 𝕜 n).eq_of_nhds]
  exact (hg x hx).trans (le_max_right _ _)

/-- **Leibniz bound with uniform constants.** If the derivatives of order at most `N` of `f` and
`g` are bounded by `C` and `D` everywhere, those of `x ↦ B (f x) (g x)` of order `p ≤ N` are
bounded by `2 ^ p * (C * D)`, for a bilinear map `B` of norm at most one. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_two_pow_mul_of_bilinear
    (B : F →L[𝕜] G →L[𝕜] H) (hB : ‖B‖ ≤ 1) {N : ℕ} {f : E → F} {g : E → G}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) {C D : ℝ}
    (hfC : ∀ p ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 p f x‖ ≤ C)
    (hgD : ∀ p ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 p g x‖ ≤ D) {p : ℕ} (hp : p ≤ N) (x : E) :
    ‖iteratedFDeriv 𝕜 p (fun y ↦ B (f y) (g y)) x‖ ≤ 2 ^ p * (C * D) := by
  refine (B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hg x (by exact_mod_cast hp)
    hB).trans ?_
  calc ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ *
        ‖iteratedFDeriv 𝕜 (p - i) g x‖
      ≤ ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * C * D := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi : i ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hC : 0 ≤ C := (norm_nonneg _).trans (hfC 0 (Nat.zero_le _) x)
        gcongr
        exacts [hfC i (hi.trans hp) x, hgD (p - i) ((Nat.sub_le p i).trans hp) x]
    _ = 2 ^ p * (C * D) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        push_cast [← Nat.cast_sum, Nat.sum_range_choose]
        ring

/-- Rescaling the variable by `c` with `1 ≤ ‖c‖` multiplies uniform bounds for the derivatives
of order at most `N` by at most `‖c‖ ^ N`. -/
theorem ContDiff.norm_iteratedFDeriv_comp_const_smul_le {N : ℕ} {f : E → F}
    (hf : ContDiff 𝕜 N f) {C : ℝ} (hC : ∀ p ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 p f x‖ ≤ C) {c : 𝕜}
    (hc : 1 ≤ ‖c‖) {p : ℕ} (hp : p ≤ N) (x : E) :
    ‖iteratedFDeriv 𝕜 p (fun y ↦ f (c • y)) x‖ ≤ ‖c‖ ^ N * C := by
  rw [iteratedFDeriv_comp_const_smul c (hf.of_le (by exact_mod_cast hp)), norm_smul, norm_pow]
  exact mul_le_mul (pow_le_pow_right₀ hc hp) (hC p hp _) (norm_nonneg _) (by positivity)

open Asymptotics in
/-- **Asymptotic bounds on the derivatives of a bilinear expression.** Along any filter, if the
derivatives of order at most `n` of `f` and `g` are `O(ρ₁)` and `O(ρ₂)`, then the order-`n`
derivative of `y ↦ B (f y) (g y)` is `O(ρ₁ ρ₂)`, by the Leibniz bound
`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear`. -/
theorem ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear {D : Type*} [NormedAddCommGroup D]
    [NormedSpace 𝕜 D] (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : WithTop ℕ∞}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) {n : ℕ} (hn : n ≤ N) {l : Filter D}
    {ρ₁ ρ₂ : D → ℝ} (hfn : ∀ i ≤ n, iteratedFDeriv 𝕜 i f =O[l] ρ₁)
    (hgn : ∀ i ≤ n, iteratedFDeriv 𝕜 i g =O[l] ρ₂) :
    iteratedFDeriv 𝕜 n (fun y ↦ B (f y) (g y)) =O[l] fun y ↦ ρ₁ y * ρ₂ y := by
  have hsum : (fun y ↦ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv 𝕜 i f y‖ * ‖iteratedFDeriv 𝕜 (n - i) g y‖) =O[l]
        fun y ↦ ρ₁ y * ρ₂ y := by
    refine IsBigO.const_mul_left (IsBigO.fun_sum fun i hi ↦ ?_) _
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact ((hfn i hi').norm_left.const_mul_left _).mul (hgn (n - i) (Nat.sub_le n i)).norm_left
  refine IsBigO.trans (IsBigO.of_bound 1 (Filter.Eventually.of_forall fun y ↦ ?_)) hsum
  rw [one_mul, Real.norm_eq_abs]
  exact (B.norm_iteratedFDeriv_le_of_bilinear hf hg y hn).trans (le_abs_self _)

open Asymptotics in
/-- The case `(c, v) ↦ c.smulRight v` of `ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear`:
along any filter, if the derivatives of order at most `n` of `f` and `g` are `O(ρ₁)` and `O(ρ₂)`,
then the order-`n` derivative of `y ↦ (f y).smulRight (g y)` is `O(ρ₁ ρ₂)`. -/
theorem ContDiff.isBigO_iteratedFDeriv_smulRight {D : Type*} [NormedAddCommGroup D]
    [NormedSpace 𝕜 D] {f : D → E →L[𝕜] 𝕜} {g : D → G} {N : WithTop ℕ∞} (hf : ContDiff 𝕜 N f)
    (hg : ContDiff 𝕜 N g) {n : ℕ} (hn : n ≤ N) {l : Filter D} {ρ₁ ρ₂ : D → ℝ}
    (hfn : ∀ i ≤ n, iteratedFDeriv 𝕜 i f =O[l] ρ₁)
    (hgn : ∀ i ≤ n, iteratedFDeriv 𝕜 i g =O[l] ρ₂) :
    iteratedFDeriv 𝕜 n (fun y ↦ (f y).smulRight (g y)) =O[l] fun y ↦ ρ₁ y * ρ₂ y := by
  simpa using (ContinuousLinearMap.smulRightL 𝕜 E G).isBigO_iteratedFDeriv_of_bilinear hf hg hn
    hfn hgn

namespace TauCeti

open Set Filter
open scoped Topology ContDiff

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The composition norm estimate depends only on smoothness near the two evaluation points. -/
theorem norm_iteratedFDeriv_comp_le_of_contDiffAt {n : ℕ} {f : E → F}
    {g : F → G} {x : E} {C D : ℝ}
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
    (hC : ∀ j, j ≤ n → ‖iteratedFDeriv 𝕜 j g (f x)‖ ≤ C)
    (hD : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv 𝕜 j f x‖ ≤ D ^ j) :
    ‖iteratedFDeriv 𝕜 n (g ∘ f) x‖ ≤ Nat.factorial n * C * D ^ n := by
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨V, hVt, hV, hfxV⟩ := mem_nhds_iff.mp ht
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
  have hsV : s ∩ f ⁻¹' V ∈ 𝓝 x :=
    inter_mem hs (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hfxV))
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hsV
  have hUV : MapsTo f U V := fun y hy ↦ (hUs hy).2
  have H := norm_iteratedFDerivWithin_comp_le (hgt.mono hVt)
    (hfs.mono (hUs.trans inter_subset_left)) (le_refl (n : ℕ∞ω))
    hV.uniqueDiffOn hU.uniqueDiffOn hUV hxU (C := C) (D := D) ?_ ?_
  · rwa [iteratedFDerivWithin_of_isOpen n hU hxU] at H
  · intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hV hfxV]
    exact hC j hj
  · intro j hj₁ hj
    rw [iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hD j hj₁ hj

end TauCeti
