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
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Uniform derivative bounds on compact sets

This file collects bounds on iterated derivatives that follow from their continuity on compact
sets: a uniform bound for a linear change of variables, and a bound by any power of the Japanese
bracket near the zero frequency. It also records the Leibniz bound for a bilinear expression in two
maps whose derivatives are bounded at a point, and the effect of a dilation on such bounds.

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
* `ContDiffOn.exists_nonneg_bound_iteratedFDeriv_uncurry_of_isOpen`: for a family `f p` that is
  `C^n` jointly in `(p, x)`, the derivatives of order at most `n` of the partial maps `f p` are
  bounded on a compact set by one constant, uniformly for `p` in a compact set.
* `TauCeti.exists_forall_norm_iteratedFDeriv_le_of_isCompact`: one nonnegative constant bounds the
  derivatives of order at most `n` of finitely many `C^n` maps on a compact set.
* `HasCompactSupport.exists_bound_iteratedFDeriv_of_contDiff`: the derivatives of order at most `n`
  of a compactly supported `C^n` map are bounded by one constant.
* `ContDiff.exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv`: a `C¹` function on
  `ℝ^ι` whose derivative has compact support has bounded squared gradient.
* `ContDiffAt.exists_ball_bound_iteratedFDeriv`: on some ball around a point where a map is
  `C^n`, its derivatives of order at most `n` are bounded by one constant.
* `ContDiffAt.exists_closedBall_differentiableAt_lipschitz_fderiv`: on some closed ball around a
  point where a map is `C²`, it is differentiable with Lipschitz derivative.
* `ContDiffOn.exists_norm_iteratedFDerivWithin_clm_apply_comp_le`: the linear bound on the
  derivatives of `z ↦ L z (φ (τ z))`.
* `ContDiffOn.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp`: its consequence for uniform
  convergence to zero.
* `ContDiff.exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_norm_le`: for `x` in a compact set
  and `ξ` in a ball, the derivatives of a `C^k` function of `(x, ξ)` are bounded by every power of
  the Japanese bracket `(1 + ‖ξ‖ ^ 2) ^ (1 / 2)`.
* `Continuous.exists_norm_le_one_add_norm_sq_rpow_of_norm_le`: on a ball, a continuous function
  is bounded by every power of the Japanese bracket.
* `ContDiff.exists_norm_iteratedFDeriv_le_of_eq_of_lt_norm`: a smooth map which agrees outside a
  ball with a map of bounded order-`n` derivative has a bounded order-`n` derivative.
* `ContDiff.exists_bound_iteratedFDeriv_of_eqOn_compl`: a `C^i` map, `1 ≤ i`, which is affine
  outside a compact set has a bounded `i`-th derivative.
* `ContDiff.exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_eq_zero_of_lt_norm`: the
  order-`n` derivative of a `C^n` map vanishing outside a ball is bounded by every power of the
  Japanese bracket.
* `ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_left_le`: composing on the left with a
  continuous linear map preserves a bound on the `k`-th derivative by a multiple of a weight.
* `ContinuousLinearMap.norm_iteratedFDeriv_le_two_pow_mul_of_bilinear`: the Leibniz bound at a
  point for `x ↦ B (f x) (g x)` from bounds on the derivatives of `f` and `g` at that point;
  `TauCeti.norm_iteratedFDeriv_mul_le_of_tsupport_subset` is the version for a product `f g`
  where `f` is only controlled near the support of `g`.
* `ContDiff.norm_iteratedFDeriv_mul_le_two_pow`: the same for a product `f * g` in a normed
  algebra, with one bound for all orders at most `N`.
* `ContDiff.norm_iteratedFDeriv_pow_le_two_pow`: the resulting bound for a power `f ^ j`.
* `ContDiffAt.norm_iteratedFDeriv_smul_const_le`: the order-`k` derivative of `y ↦ f y • v` is at
  most that of `f` times `‖v‖`.
* `ContDiff.norm_iteratedFDeriv_comp_const_smul_le`: rescaling the variable by `c` with
  `1 ≤ ‖c‖` multiplies uniform derivative bounds of order at most `N` by at most `‖c‖ ^ N`.
* `ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear`: along any filter, if the derivatives of
  order at most `n` of `f` and `g` are `O(ρ₁)` and `O(ρ₂)`, then the order-`n` derivative of
  `y ↦ B (f y) (g y)` is `O(ρ₁ ρ₂)`.
* `ContDiff.isBigO_iteratedFDeriv_smulRight`: the same for `y ↦ (f y).smulRight (g y)`.
* `ContinuousLinearMap.isBigO_iteratedFDeriv_comp_left`: along any filter, if the order-`n`
  derivative of `f` is `O(ρ)`, then so is that of `y ↦ L (f y)`.
* `ContinuousLinearMap.norm_iteratedFDeriv_comp_left_le_of_forall_le`: bounded derivatives of `f`
  up to order `N` give bounded derivatives of `L ∘ f`, with the bound multiplied by `‖L‖`.
* `ContinuousLinearMap.exists_bound_iteratedFDeriv_comp_left`: the same with a separate bound for
  each order, in existential form.
* `TauCeti.norm_iteratedFDeriv_smul_le_of_isOpen`: the Leibniz bound for `z ↦ c z • f z` at a
  point of an open set on which both factors are smooth.
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

/-- A `C¹` function `u` on `ℝ^ι` whose derivative has compact support has bounded squared gradient
`∑ᵢ (∂ᵢ u)²`. -/
theorem ContDiff.exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {u : (ι → ℝ) → ℝ} (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport (fderiv ℝ u)) :
    ∃ K, ∀ x, ∑ i, fderiv ℝ u x (Pi.single i 1) ^ 2 ≤ K := by
  obtain ⟨B, hB⟩ :=
    (hu.continuous_fderiv one_ne_zero).norm.bddAbove_range_of_hasCompactSupport hcs.norm
  refine ⟨Fintype.card ι * B ^ 2, fun x ↦ ?_⟩
  refine (Finset.sum_le_sum fun i _ ↦ (?_ : _ ≤ B ^ 2)).trans_eq (by simp)
  rw [← sq_abs, ← Real.norm_eq_abs]
  refine pow_le_pow_left₀ (norm_nonneg _) (((fderiv ℝ u x).le_opNorm _).trans ?_) 2
  rw [Pi.norm_single, norm_one, mul_one]
  exact hB ⟨x, rfl⟩

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

/-- On some closed ball around a point `x` at which `f` is `C²`, the map `f` is differentiable
and its derivative is Lipschitz. -/
theorem ContDiffAt.exists_closedBall_differentiableAt_lipschitz_fderiv {𝕂 : Type*} [RCLike 𝕂]
    {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [NormedAddCommGroup F']
    [NormedSpace 𝕂 F'] {f : E' → F'} {x : E'} (hf : ContDiffAt 𝕂 2 f x) :
    ∃ r > 0, ∃ K : NNReal, (∀ y ∈ Metric.closedBall x r, DifferentiableAt 𝕂 f y) ∧
      ∀ y ∈ Metric.closedBall x r, ∀ z ∈ Metric.closedBall x r,
        ‖fderiv 𝕂 f y - fderiv 𝕂 f z‖ ≤ K * ‖y - z‖ := by
  obtain ⟨K, t₀, ht₀, hK⟩ := (hf.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrf⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
    ((hf.eventually (by simp)).and ht₀)
  exact ⟨r, hr, K, fun y hy ↦ (hrf hy).1.differentiableAt (by norm_num), fun y hy z hz ↦ by
    simpa [dist_eq_norm] using hK.dist_le_mul y (hrf hy).2 z (hrf hz).2⟩

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
  obtain ⟨C', hC'0, hC'⟩ := TauCeti.exists_le_mul_one_add_norm_sq_rpow_of_norm_le (E := F) C R r
  exact ⟨C', hC'0, fun x hx ξ hξ ↦ (hC (x, ξ) ⟨hx, by simpa using hξ⟩).trans (hC' ξ hξ)⟩

/-- On a ball, a continuous function is bounded by every power of the Japanese bracket:
`‖f ξ‖ ≤ C (1 + ‖ξ‖ ^ 2) ^ (r / 2)` for `‖ξ‖ ≤ R`. -/
theorem Continuous.exists_norm_le_one_add_norm_sq_rpow_of_norm_le {E F : Type*}
    [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F] {f : E → F} (hf : Continuous f)
    (R r : ℝ) : ∃ C, 0 ≤ C ∧ ∀ ξ, ‖ξ‖ ≤ R → ‖f ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨C, hC0, hC⟩ := TauCeti.exists_le_mul_one_add_norm_sq_rpow_of_norm_le (E := E) M R r
  exact ⟨C, hC0, fun ξ hξ ↦ (hM ξ (mem_closedBall_zero_iff.2 hξ)).trans (hC ξ hξ)⟩

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

/-- A `C^i` map, `1 ≤ i`, which agrees outside a compact set with an affine map `x ↦ b + L x` has
a bounded derivative of order `i`: outside a ball containing the compact set, its order-`i`
derivative is that of the affine map, which is bounded by `‖L‖`. -/
theorem ContDiff.exists_bound_iteratedFDeriv_of_eqOn_compl [ProperSpace E] {f : E → F} {i : ℕ}
    (hf : ContDiff 𝕜 i f) (hi : 1 ≤ i) {K : Set E} (hK : IsCompact K) {b : F} {L : E →L[𝕜] F}
    (hfK : EqOn f (fun x ↦ b + L x) Kᶜ) :
    ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 i f x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine hf.exists_norm_iteratedFDeriv_le_of_eq_of_lt_norm (R := R) (C := ‖L‖)
    (fun x hx ↦ hfK fun hxK ↦ hx.not_ge (mem_closedBall_zero_iff.1 (hR hxK))) fun x _ ↦ ?_
  -- The derivatives of positive order of the affine map are those of the constant `L`.
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hfd : fderiv 𝕜 (fun x ↦ b + L x) = fun _ ↦ L := by
    ext1 y
    exact ((L.hasFDerivAt (x := y)).const_add b).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  rcases j with _ | j
  · simp
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]

/-- The order-`n` derivative of a `C^n` map vanishing outside a ball is bounded by every power of
the Japanese bracket: `‖D^n f(x)‖ ≤ C (1 + ‖x‖ ^ 2) ^ (r / 2)`. -/
theorem ContDiff.exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_eq_zero_of_lt_norm
    [ProperSpace E] {n : ℕ} {f : E → F} (hf : ContDiff 𝕜 n f) {R : ℝ}
    (hf0 : ∀ x, R < ‖x‖ → f x = 0) (r : ℝ) :
    ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (r / 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    (hf.continuous_iteratedFDeriv le_rfl).exists_norm_le_one_add_norm_sq_rpow_of_norm_le R r
  refine ⟨C, fun x ↦ ?_⟩
  rcases le_or_gt ‖x‖ R with hx | hx
  · exact hC x hx
  -- Outside the ball, `x` lies outside the topological support of `f`.
  have hsupp : tsupport f ⊆ Metric.closedBall 0 R :=
    closure_minimal (fun y hy ↦ mem_closedBall_zero_iff.2 (not_lt.1 (mt (hf0 y) hy)))
      Metric.isClosed_closedBall
  rw [image_eq_zero_of_notMem_tsupport fun h ↦
      hx.not_ge (mem_closedBall_zero_iff.1 (hsupp (tsupport_iteratedFDeriv_subset n h))),
    norm_zero]
  positivity

/-- Composing on the left with a continuous linear map `L` preserves a bound
`‖D^k g x‖ ≤ C w x` on the `k`-th derivative of a `C^k` map `g` by a multiple of a weight `w`. -/
theorem ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_left_le (L : F →L[𝕜] G) {g : E → F}
    {k : ℕ} (hg : ContDiff 𝕜 k g) {w : E → ℝ}
    (hgk : ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 k g x‖ ≤ C * w x) :
    ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 k (fun x ↦ L (g x)) x‖ ≤ C * w x := by
  obtain ⟨C, hC⟩ := hgk
  refine ⟨‖L‖ * C, fun x ↦ ?_⟩
  calc ‖iteratedFDeriv 𝕜 k (fun x ↦ L (g x)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv 𝕜 k g x‖ :=
        L.norm_iteratedFDeriv_comp_left hg.contDiffAt le_rfl
    _ ≤ ‖L‖ * (C * w x) := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg L)
    _ = ‖L‖ * C * w x := (mul_assoc _ _ _).symm

/-- **Leibniz bound at a point.** If the derivatives of order at most `N` of `f` and `g` at `x`
are bounded by `C` and `D`, those of `y ↦ B (f y) (g y)` at `x` of order `p ≤ N` are bounded by
`2 ^ p * (C * D)`, for a bilinear map `B` of norm at most one. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le_two_pow_mul_of_bilinear
    (B : F →L[𝕜] G →L[𝕜] H) (hB : ‖B‖ ≤ 1) {N : ℕ} {f : E → F} {g : E → G}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) {x : E} {C D : ℝ}
    (hfC : ∀ p ≤ N, ‖iteratedFDeriv 𝕜 p f x‖ ≤ C)
    (hgD : ∀ p ≤ N, ‖iteratedFDeriv 𝕜 p g x‖ ≤ D) {p : ℕ} (hp : p ≤ N) :
    ‖iteratedFDeriv 𝕜 p (fun y ↦ B (f y) (g y)) x‖ ≤ 2 ^ p * (C * D) := by
  refine (B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hg x (by exact_mod_cast hp)
    hB).trans ?_
  calc ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f x‖ *
        ‖iteratedFDeriv 𝕜 (p - i) g x‖
      ≤ ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * C * D := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi : i ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hC : 0 ≤ C := (norm_nonneg _).trans (hfC 0 (Nat.zero_le _))
        gcongr
        exacts [hfC i (hi.trans hp), hgD (p - i) ((Nat.sub_le p i).trans hp)]
    _ = 2 ^ p * (C * D) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        push_cast [← Nat.cast_sum, Nat.sum_range_choose]
        ring

/-- **Leibniz bound for a product at a point.** If the derivatives of order at most `N` of `f` and
`g` at `x` are bounded by `C` and `D`, those of `f * g` at `x` of order at most `N` are bounded by
`2 ^ N * (C * D)`. -/
theorem ContDiff.norm_iteratedFDeriv_mul_le_two_pow {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
    {N : ℕ} {f g : E → A} (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) {x : E} {C D : ℝ}
    (hfC : ∀ p ≤ N, ‖iteratedFDeriv 𝕜 p f x‖ ≤ C)
    (hgD : ∀ p ≤ N, ‖iteratedFDeriv 𝕜 p g x‖ ≤ D) :
    ∀ p ≤ N, ‖iteratedFDeriv 𝕜 p (f * g) x‖ ≤ 2 ^ N * (C * D) := by
  intro p hp
  have hC : 0 ≤ C := (norm_nonneg _).trans (hfC 0 (Nat.zero_le _))
  have hD : 0 ≤ D := (norm_nonneg _).trans (hgD 0 (Nat.zero_le _))
  refine ((ContinuousLinearMap.mul 𝕜 A).norm_iteratedFDeriv_le_two_pow_mul_of_bilinear
    (ContinuousLinearMap.opNorm_mul_le _ _) hf hg hfC hgD hp).trans ?_
  gcongr
  exact one_le_two

/-- **Leibniz bound for a power at a point.** If the derivatives of order at most `N` of `f` at
`x` are bounded by `C`, those of `f ^ j` at `x` of order at most `N` are bounded by
`(2 ^ N * C) ^ j`, provided `‖1‖ ≤ 1`. -/
theorem ContDiff.norm_iteratedFDeriv_pow_le_two_pow {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] (h1 : ‖(1 : A)‖ ≤ 1) {N : ℕ} {f : E → A} (hf : ContDiff 𝕜 N f) {x : E}
    {C : ℝ} (hfC : ∀ p ≤ N, ‖iteratedFDeriv 𝕜 p f x‖ ≤ C) (j : ℕ) :
    ∀ p ≤ N, ‖iteratedFDeriv 𝕜 p (f ^ j) x‖ ≤ (2 ^ N * C) ^ j := by
  induction j with
  | zero =>
    intro p _
    rw [pow_zero, pow_zero]
    exact (TauCeti.norm_iteratedFDeriv_const_le p 1 x).trans h1
  | succ j ih =>
    intro p hp
    have hfj : ContDiff 𝕜 N (f ^ j) := hf.pow j
    rw [pow_succ, pow_succ]
    exact (hfj.norm_iteratedFDeriv_mul_le_two_pow hf ih hfC p hp).trans_eq (by ring)

/-- Rescaling the variable by `c` with `1 ≤ ‖c‖` multiplies uniform bounds for the derivatives
of order at most `N` by at most `‖c‖ ^ N`. -/
theorem ContDiff.norm_iteratedFDeriv_comp_const_smul_le {N : ℕ} {f : E → F}
    (hf : ContDiff 𝕜 N f) {C : ℝ} (hC : ∀ p ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 p f x‖ ≤ C) {c : 𝕜}
    (hc : 1 ≤ ‖c‖) {p : ℕ} (hp : p ≤ N) (x : E) :
    ‖iteratedFDeriv 𝕜 p (fun y ↦ f (c • y)) x‖ ≤ ‖c‖ ^ N * C := by
  rw [iteratedFDeriv_comp_const_smul c (hf.of_le (by exact_mod_cast hp)), norm_smul, norm_pow]
  exact mul_le_mul (pow_le_pow_right₀ hc hp) (hC p hp _) (norm_nonneg _) (by positivity)

/-- The order-`k` derivative of `y ↦ f y • v` at `x`, for a scalar-valued `f` that is `C^k` at `x`
and a fixed vector `v`, is at most that of `f` times `‖v‖`. -/
theorem ContDiffAt.norm_iteratedFDeriv_smul_const_le {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F] {f : E → A} {k : ℕ}
    {x : E} (hf : ContDiffAt 𝕜 k f x) (v : F) :
    ‖iteratedFDeriv 𝕜 k (fun y ↦ f y • v) x‖ ≤ ‖iteratedFDeriv 𝕜 k f x‖ * ‖v‖ := by
  rw [iteratedFDeriv_smul_const_apply hf, mul_comm]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  gcongr
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun z ↦ ?_
  simpa [mul_comm] using norm_smul_le z v

open Asymptotics in
/-- **Asymptotic bounds on the derivatives of a bilinear expression.** Along any filter, if the
derivatives of order at most `n` of `f` and `g` are `O(ρ₁)` and `O(ρ₂)`, then the order-`n`
derivative of `y ↦ B (f y) (g y)` is `O(ρ₁ ρ₂)`. This is the case of global smoothness and
index-independent bounds of `ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_of_contDiffAt`.
-/
theorem ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear {D : Type*} [NormedAddCommGroup D]
    [NormedSpace 𝕜 D] (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : WithTop ℕ∞}
    (hf : ContDiff 𝕜 N f) (hg : ContDiff 𝕜 N g) {n : ℕ} (hn : n ≤ N) {l : Filter D}
    {ρ₁ ρ₂ : D → ℝ} (hfn : ∀ i ≤ n, iteratedFDeriv 𝕜 i f =O[l] ρ₁)
    (hgn : ∀ i ≤ n, iteratedFDeriv 𝕜 i g =O[l] ρ₂) :
    iteratedFDeriv 𝕜 n (fun y ↦ B (f y) (g y)) =O[l] fun y ↦ ρ₁ y * ρ₂ y :=
  B.isBigO_iteratedFDeriv_of_bilinear_of_contDiffAt (ρ₁ := fun _ ↦ ρ₁) (ρ₂ := fun _ ↦ ρ₂)
    (.of_forall fun _ ↦ hf.contDiffAt) (.of_forall fun _ ↦ hg.contDiffAt) hn hfn hgn
    fun _ _ ↦ isBigO_refl _ _

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
  simpa using (StrongDual.smulRightL 𝕜 E G).isBigO_iteratedFDeriv_of_bilinear hf hg hn
    hfn hgn

open Asymptotics in
/-- **Asymptotic bounds on the derivatives of `L ∘ f`.** Along any filter, if the derivative of
order `n` of a `Cⁿ` map `f` is `O(ρ)`, then so is that of `y ↦ L (f y)` for a continuous linear
map `L`, by `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`. -/
theorem ContinuousLinearMap.isBigO_iteratedFDeriv_comp_left {D : Type*} [NormedAddCommGroup D]
    [NormedSpace 𝕜 D] (L : E →L[𝕜] F) {f : D → E} {N : WithTop ℕ∞} (hf : ContDiff 𝕜 N f) {n : ℕ}
    (hn : n ≤ N) {l : Filter D} {R : Type*} [Norm R] {ρ : D → R}
    (hfn : iteratedFDeriv 𝕜 n f =O[l] ρ) :
    iteratedFDeriv 𝕜 n (fun y ↦ L (f y)) =O[l] ρ :=
  (IsBigO.of_bound ‖L‖ (Filter.Eventually.of_forall fun _ ↦
    L.norm_iteratedFDeriv_comp_left hf.contDiffAt hn)).trans hfn

/-- If the derivatives of `f` of order at most `N` are bounded by `M`, those of `L ∘ f` are
bounded by `‖L‖ * M`, for a continuous linear map `L`. The map `L` may be linear over a normed
`𝕜`-algebra `𝕜'`, such as `ℂ` over `ℝ`. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_comp_left_le_of_forall_le
    {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
    [IsScalarTower 𝕜 𝕜' F] [NormedSpace 𝕜' G] [IsScalarTower 𝕜 𝕜' G] (L : F →L[𝕜'] G)
    {f : E → F} {N : ℕ} {M : ℝ} (hf : ContDiff 𝕜 N f)
    (hbd : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ M) :
    ∀ n ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 n (L ∘ f) x‖ ≤ ‖L‖ * M := fun n hn x ↦
  ((L.restrictScalars 𝕜).norm_iteratedFDeriv_comp_left hf.contDiffAt (mod_cast hn)).trans
    (mul_le_mul_of_nonneg_left (hbd n hn x) (norm_nonneg _))

/-- **Uniform bounds on the derivatives of `L ∘ f`.** If each derivative of order at most `N` of a
`C^N` map `f` is bounded, so is the corresponding derivative of `L ∘ f`, for a continuous linear map
`L`. The map `L` may be linear over a normed `𝕜`-algebra `𝕜'`, such as `ℂ` over `ℝ`. -/
theorem ContinuousLinearMap.exists_bound_iteratedFDeriv_comp_left
    {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
    [IsScalarTower 𝕜 𝕜' F] [NormedSpace 𝕜' G] [IsScalarTower 𝕜 𝕜' G] (L : F →L[𝕜'] G)
    {f : E → F} {N : ℕ} (hf : ContDiff 𝕜 N f)
    (hbd : ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ C) :
    ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 n (L ∘ f) x‖ ≤ C := fun n hn ↦ by
  obtain ⟨C, hC⟩ := hbd n hn
  exact ⟨‖L‖ * C, fun x ↦
    ((L.restrictScalars 𝕜).norm_iteratedFDeriv_comp_left hf.contDiffAt (mod_cast hn)).trans
      (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))⟩

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

/-- On a compact set `K`, the derivatives of order at most `n` of finitely many `C^n` maps
`f i`, `i ∈ s`, are bounded by a single nonnegative constant. -/
theorem exists_forall_norm_iteratedFDeriv_le_of_isCompact {ι : Type*} (s : Finset ι)
    {f : ι → E → F} {n : ℕ} (hf : ∀ i ∈ s, ContDiff 𝕜 n (f i)) {K : Set E} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ i ∈ s, ∀ j ≤ n, ∀ y ∈ K, ‖iteratedFDeriv 𝕜 j (f i) y‖ ≤ C := by
  have h (i : ι) : ∃ C, 0 ≤ C ∧ (i ∈ s → ∀ j ≤ n, ∀ y ∈ K, ‖iteratedFDeriv 𝕜 j (f i) y‖ ≤ C) := by
    by_cases hi : i ∈ s
    · obtain ⟨C, hC0, hC⟩ := (hf i hi).contDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen
        isOpen_univ hK (subset_univ K)
      exact ⟨C, hC0, fun _ ↦ hC⟩
    · exact ⟨0, le_rfl, fun h ↦ absurd h hi⟩
  choose C hC0 hC using h
  exact ⟨∑ i ∈ s, C i, Finset.sum_nonneg fun i _ ↦ hC0 i, fun i hi j hj y hy ↦
    (hC i hi j hj y hy).trans (Finset.single_le_sum (fun i _ ↦ hC0 i) hi)⟩

/-- **Leibniz bound with uniform constants on a support.** Let `g` be `C^N` with topological
support in `K`, and let `f` be `C^N` on an open set `W ⊇ K`. If the derivatives of order at most
`n ≤ N` of `f` are bounded by `C ≥ 0` on `K` and those of `g` by `D` everywhere, then those of
`f g` are bounded by `2 ^ n * C * D` everywhere; the values of `f` outside `W` do not matter. -/
theorem norm_iteratedFDeriv_mul_le_of_tsupport_subset {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] {f g : E → A} {K W : Set E} (hW : IsOpen W) (hKW : K ⊆ W) {N : WithTop ℕ∞}
    (hf : ContDiffOn 𝕜 N f W) (hg : ContDiff 𝕜 N g) (hgK : tsupport g ⊆ K) {n : ℕ}
    (hn : n ≤ N) {C D : ℝ} (hC0 : 0 ≤ C)
    (hfC : ∀ i ≤ n, ∀ y ∈ K, ‖iteratedFDeriv 𝕜 i f y‖ ≤ C)
    (hgD : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv 𝕜 i g y‖ ≤ D) (y : E) :
    ‖iteratedFDeriv 𝕜 n (fun z ↦ f z * g z) y‖ ≤ 2 ^ n * C * D := by
  by_cases hy : y ∈ tsupport g
  · have hyW := hKW (hgK hy)
    have h := norm_iteratedFDerivWithin_mul_le hf hg.contDiffOn hW.uniqueDiffOn hyW hn
    simp_rw [iteratedFDerivWithin_of_isOpen _ hW hyW] at h
    refine h.trans ?_
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f y‖ *
          ‖iteratedFDeriv 𝕜 (n - i) g y‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * D := by
          gcongr with i hi
          · exact hfC i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) y (hgK hy)
          · exact hgD _ (Nat.sub_le n i) y
      _ = 2 ^ n * C * D := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose n
  · have h0 : (fun z ↦ f z * g z) =ᶠ[nhds y] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy] with z hz
      simp [hz]
    rw [(h0.iteratedFDeriv (𝕜 := 𝕜) n).self_of_nhds, iteratedFDeriv_zero, Pi.zero_apply,
      norm_zero]
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hgD 0 (Nat.zero_le _) y)
    positivity

/-- The Leibniz bound `norm_iteratedFDeriv_smul_le` at a point of an open set on which both
factors are smooth. -/
theorem norm_iteratedFDeriv_smul_le_of_isOpen {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {U : Set E} (hU : IsOpen U) {c : E → 𝕜'}
    {f : E → F} {N : ℕ∞ω} (hc : ContDiffOn 𝕜 N c U) (hf : ContDiffOn 𝕜 N f U) {x : E}
    (hx : x ∈ U) {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv 𝕜 k (fun z ↦ c z • f z) x‖ ≤ ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i c x‖ * ‖iteratedFDeriv 𝕜 (k - i) f x‖ := by
  have h := norm_iteratedFDerivWithin_smul_le hc hf hU.uniqueDiffOn hx hk
  rw [iteratedFDerivWithin_of_isOpen k hU hx] at h
  refine h.trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [iteratedFDerivWithin_of_isOpen i hU hx, iteratedFDerivWithin_of_isOpen _ hU hx]

end TauCeti

/-- Let `f p` be maps depending on a parameter `p`, jointly `C^n` in `(p, x)` on an open set `W`
containing `C ×ˢ K` for compact sets `C` and `K`. For `p ∈ C` the partial map `f p` is `C^n` at
every point of `K`, and its derivatives there of order at most `n` are bounded by a single
nonnegative constant, uniformly in `p`. -/
theorem ContDiffOn.exists_nonneg_bound_iteratedFDeriv_uncurry_of_isOpen {P : Type*}
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] {f : P → E → F} {W : Set (P × E)} {C : Set P}
    {K : Set E} {n : ℕ} (hf : ContDiffOn 𝕜 n (Function.uncurry f) W) (hW : IsOpen W)
    (hC : IsCompact C) (hK : IsCompact K) (hCKW : C ×ˢ K ⊆ W) :
    ∃ A, 0 ≤ A ∧ ∀ p ∈ C, ∀ x ∈ K, ContDiffAt 𝕜 n (f p) x ∧
      ∀ i ≤ n, ‖iteratedFDeriv 𝕜 i (f p) x‖ ≤ A := by
  obtain ⟨A, hA0, hA⟩ := hf.exists_nonneg_bound_iteratedFDeriv_of_isOpen hW (hC.prod hK) hCKW
  refine ⟨A, hA0, fun p hp x hx ↦ ?_⟩
  have hpx : (p, x) ∈ C ×ˢ K := ⟨hp, hx⟩
  have hfpx : ContDiffAt 𝕜 n (Function.uncurry f) (p, x) :=
    hf.contDiffAt (hW.mem_nhds (hCKW hpx))
  exact ⟨hfpx.comp x (contDiffAt_const.prodMk contDiffAt_id), fun i hi ↦
    (hfpx.norm_iteratedFDeriv_prod_right_le i (mod_cast hi)).trans (hA i hi _ hpx)⟩
