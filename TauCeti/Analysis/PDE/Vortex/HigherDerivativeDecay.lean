/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Decay
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.InnerProductSpace.Laplacian.DerivativeDecay

/-!
# Exponential decay of all derivatives of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)`, so `|α|² = 4 (p² + q²)`. For a smooth vortex on the whole plane with `|α| → 1`
at infinity, the modulus defect `1 - |α|²` decays like `exp (-c |z|)` for every rate `c < 1 / 2`
(`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`), and so do the first derivatives
(`TauCeti.Vortex.exists_norm_fderiv_normSq_le_mul_exp`). This file proves the same decay for the
derivatives of every order of the two gauge-invariant scalars of the vortex:

* `ℓ = log |α|²`: `‖Dⁿ ℓ(z)‖ ≤ K exp (-c |z|)` outside a compact set
  (`TauCeti.Vortex.exists_eventually_norm_iteratedFDeriv_log_normSq_le_mul_exp`);
* `|α|² - 1`: `‖Dⁿ (|α|² - 1)(z)‖ ≤ K exp (-c |z|)` outside a compact set
  (`TauCeti.Vortex.exists_eventually_norm_iteratedFDeriv_normSq_sub_one_le_mul_exp`).

By the curvature row of the vortex equations the curvature is `(1 - |α|²) / 8`, so all its
derivatives decay as well.

Outside a large disc `ℓ` solves the scalar equation `Δ ℓ = (exp ℓ - 1) / 4`
(`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`), and `|ℓ| ≤ 2 (1 - |α|²)` there
because `|α|² ≥ 1 / 2`. Modifying `ℓ` inside the disc to a smooth function on the whole plane, the
exterior bootstrap `TauCeti.exists_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_comp` gains one
derivative at a time from the interior gradient estimate for Poisson's equation, keeping the
exponential rate. The decay of `|α|² - 1 = exp ℓ - 1` then follows from the Faà di Bruno bound
`ContDiff.exists_norm_iteratedFDeriv_comp_le_mul`.

## Main results

* `TauCeti.Vortex.exists_eventually_norm_iteratedFDeriv_log_normSq_le_mul_exp`: every derivative
  of `log |α|²` decays at every rate `c < 1 / 2`.
* `TauCeti.Vortex.exists_eventually_norm_iteratedFDeriv_normSq_sub_one_le_mul_exp`: every
  derivative of `|α|² - 1` decays at every rate `c < 1 / 2`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology InnerProductSpace Laplacian
open scoped ContDiff

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- A smooth framed vortex has, for every `n` and every rate `0 ≤ c < 1 / 2`, a smooth function `L`
on the plane and a radius `R` such that `L = log |α|²` near every point outside the disc of radius
`R`, `|α|² = exp L` there, and the derivatives of `L` of order at most `n` are bounded by
`K exp (-c |z|)` outside the disc of radius `R + n`. -/
private theorem exists_log_normSq_decay (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) (n : ℕ) :
    ∃ L : ℂ → ℝ, ∃ R K : ℝ, ContDiff ℝ ∞ L ∧ 0 ≤ K ∧
      (∀ z, R < ‖z‖ → L =ᶠ[𝓝 z] fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) ∧
      (∀ z, R < ‖z‖ → Real.exp (L z) = 4 * (x z 2 ^ 2 + x z 3 ^ 2)) ∧
      ∀ z, R + n < ‖z‖ → ∀ i ≤ n, ‖iteratedFDeriv ℝ i L z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hcd (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hb₁ : Differentiable ℝ fun w ↦ x w 0 := (hcd 0).differentiable (by simp)
  have hb₂ : Differentiable ℝ fun w ↦ x w 1 := (hcd 1).differentiable (by simp)
  have hp : ContDiff ℝ 2 fun w ↦ x w 2 := (hcd 2).of_le (by simp)
  have hq : ContDiff ℝ 2 fun w ↦ x w 3 := (hcd 3).of_le (by simp)
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2) with hs
  have hscd : ContDiff ℝ ∞ s := contDiff_normSq (hcd 2) (hcd 3)
  have hs₀ : ∀ w, 0 ≤ s w := fun w ↦ by positivity
  have hs₁ : ∀ w, s w ≤ 1 := normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim
  -- Outside a disc of radius `R₀`, `|α|² > 1 / 2`.
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨R₁, -, hR₁⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hlim.eventually (lt_mem_nhds hhalf))
  set R₀ := max R₁ 1
  have hR₀ : 0 < R₀ := zero_lt_one.trans_le (le_max_right _ _)
  have hsR : ∀ w, R₀ ≤ ‖w‖ → 1 / 2 < s w := fun w hw ↦ hR₁ ((le_max_left _ _).trans hw)
  -- A smooth modification of `log |α|²` inside the disc of radius `R₀ + 2`.
  let β : ContDiffBump (0 : ℂ) := ⟨R₀ + 1, R₀ + 2, by linarith, by linarith⟩
  have hβ₁ : ∀ w, ‖w‖ ≤ R₀ + 1 → β w = 1 := fun w hw ↦
    β.one_of_mem_closedBall (by simpa using hw)
  have hβ₀ : ∀ w, R₀ + 2 ≤ ‖w‖ → β w = 0 := fun w hw ↦ β.zero_of_le_dist (by simpa using hw)
  have hpos : ∀ w, 0 < s w + β w := by
    intro w
    rcases le_or_gt ‖w‖ (R₀ + 1) with hw | hw
    · rw [hβ₁ w hw]
      linarith [hs₀ w]
    · linarith [hsR w (by linarith), β.nonneg (x := w)]
  set L : ℂ → ℝ := fun w ↦ Real.log (s w + β w) with hL
  have hLcd : ContDiff ℝ ∞ L := (hscd.add β.contDiff).log fun w ↦ (hpos w).ne'
  set R := R₀ + 2
  have hLeq : ∀ z, R < ‖z‖ → L =ᶠ[𝓝 z] fun w ↦ Real.log (s w) := by
    intro z hz
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    simp only [hL, hβ₀ w hw.le, add_zero]
  have hexp : ∀ z, R < ‖z‖ → Real.exp (L z) = s z := by
    intro z hz
    rw [hLeq z hz |>.eq_of_nhds, Real.exp_log (by linarith [hsR z (by linarith)])]
  -- The scalar equation `Δ L = (exp L - 1) / 4` outside the disc of radius `R`.
  have heq : ∀ z, R < ‖z‖ → Δ L z = (Real.exp (L z) - 1) / 4 := by
    intro z hz
    rw [(laplacian_congr_nhds (hLeq z hz)).eq_of_nhds, hexp z hz]
    have hsz := hsR z (by linarith)
    exact laplacian_log_normSq_of_equation_eq_zero (hb₁ z) (hb₂ z) hp.contDiffAt hq.contDiffAt
      (by nlinarith) (Eventually.of_forall hsol)
  -- The exponential decay of `L` itself: `|log s| ≤ 2 (1 - s)` for `1 / 2 ≤ s ≤ 1`.
  obtain ⟨K₀, hK₀⟩ := exists_one_sub_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc
  have hdecay : ∀ z, R < ‖z‖ → |L z| ≤ 2 * K₀ * Real.exp (-(c * ‖z‖)) := by
    intro z hz
    have hsz := hsR z (by linarith)
    have hLz : L z = Real.log (s z) := hLeq z hz |>.eq_of_nhds
    have hlog₁ : Real.log (s z) ≤ 0 := Real.log_nonpos (hs₀ z) (hs₁ z)
    have hlog₂ : 1 - (s z)⁻¹ ≤ Real.log (s z) := Real.one_sub_inv_le_log_of_pos (by linarith)
    have hinv : (s z)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hkey : 1 - (s z)⁻¹ = -((1 - s z) * (s z)⁻¹) := by field_simp; ring
    have h1s : 0 ≤ 1 - s z := by linarith [hs₁ z]
    rw [hLz, abs_of_nonpos hlog₁]
    have := hK₀ z
    nlinarith [mul_le_mul_of_nonneg_left hinv h1s]
  obtain ⟨K, hK, hbound⟩ := exists_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_comp hLcd
    (G := fun t ↦ (Real.exp t - 1) / 4) (by fun_prop) (by simp) hc₀ heq hdecay n
  exact ⟨L, R, K, hLcd, hK, hLeq, hexp, hbound⟩

/-- **Exponential decay of all derivatives of `log |α|²`.** For a smooth vortex on the whole plane
whose section satisfies `|α| → 1` at infinity, every derivative of `log |α|²` decays like
`exp (-c |z|)` for every rate `c < 1 / 2`: outside a compact set,
`‖Dⁿ log |α|² (z)‖ ≤ K exp (-c |z|)`. -/
theorem exists_eventually_norm_iteratedFDeriv_log_normSq_le_mul_exp (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) (n : ℕ) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ n (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨L, R, K, -, hK, hLeq, -, hbound⟩ := exists_log_normSq_decay hx hsol hlim
    (le_max_right c 0) (max_lt hc (by norm_num)) n
  refine ⟨K, ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (R + n)] with z hz
  have hRz : R < ‖z‖ := lt_of_le_of_lt (by simp) hz
  rw [← ((hLeq z hRz).iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
  refine (hbound z hz n le_rfl).trans (mul_le_mul_of_nonneg_left ?_ hK)
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg _)))

/-- **Exponential decay of all derivatives of the modulus defect.** For a smooth vortex on the
whole plane whose section satisfies `|α| → 1` at infinity, every derivative of `|α|² - 1` decays
like `exp (-c |z|)` for every rate `c < 1 / 2`: outside a compact set,
`‖Dⁿ (|α|² - 1) (z)‖ ≤ K exp (-c |z|)`. -/
theorem exists_eventually_norm_iteratedFDeriv_normSq_sub_one_le_mul_exp (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) (n : ℕ) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ n (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2) - 1) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  set c' := max c 0
  obtain ⟨L, R, K, hLcd, -, -, hexp, hbound⟩ := exists_log_normSq_decay hx hsol hlim
    (le_max_right c 0) (max_lt hc (by norm_num)) n
  -- `|α|² - 1 = g ∘ L` near every point outside the disc, with `g t = exp t - 1`.
  have hg : ContDiff ℝ (n + 1) fun t : ℝ ↦ Real.exp t - 1 := by fun_prop
  obtain ⟨K', hK'⟩ := hg.exists_norm_iteratedFDeriv_comp_le_mul (E := ℂ) (by simp) K
  refine ⟨max K' 0, ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (R + n)] with z hz
  have hRz : R < ‖z‖ := lt_of_le_of_lt (by simp) hz
  have hev : (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2) - 1) =ᶠ[𝓝 z]
      (fun t : ℝ ↦ Real.exp t - 1) ∘ L := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hRz] with w hw
    simp [hexp w hw]
  rw [(hev.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
  have hw₁ : Real.exp (-(c' * ‖z‖)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (le_max_right c 0) (norm_nonneg z)))
  refine (hK' L z _ (hLcd.contDiffAt.of_le (by simp)) (Real.exp_pos _).le hw₁
    (hbound z hz)).trans ?_
  refine mul_le_mul (le_max_left _ _) ?_ (Real.exp_pos _).le (le_max_right _ _)
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg _)))

end TauCeti.Vortex
