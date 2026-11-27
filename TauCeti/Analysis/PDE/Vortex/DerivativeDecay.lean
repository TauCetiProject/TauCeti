/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Decay
import TauCeti.Analysis.InnerProductSpace.Laplacian.DerivativeDecay
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.PDE.Regularity.PlanarGradientEstimate
import TauCeti.Analysis.PDE.Regularity.PlanarPoisson
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exponential decay of the derivatives of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`, so `|α|² = 4 (p² + q²)`. For a vortex on the
whole plane with `|α| → 1` at infinity, the modulus defect `1 - |α|²` and the curvature decay
exponentially at every rate `c < 1 / 2` (`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`). This
file proves the same decay for the first derivatives: the gradient of `|α|²`, the gauge-invariant
covariant derivative `d_a α`, and hence the whole energy density, which decays at every rate
`c < 1`.

The argument works with `ℓ = log |α|²` outside a large disc, where it solves the scalar equation
`Δ ℓ = (|α|² - 1) / 4 = (exp ℓ - 1) / 4`
(`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`). For a translation `h`, the
difference `D = ℓ - ℓ (· + h)` therefore satisfies the linear equation `Δ D = V D`, where
`V = (exp ℓ - exp ℓ (· + h)) / (4 (ℓ - ℓ (· + h)))` is a difference quotient of `exp / 4`. It is
at least the smaller of the values of `|α|² / 4` at the two points, so `V ≥ c²` outside a large
disc. Both `D` and `-D` are then subsolutions of `-Δ + V`, and the exterior comparison principle
with a variable potential bounds `|D|` by its values on a circle times `exp (-c |z|)`
(`TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one`). On that circle `|D| ≤ L |h|` by the
mean value inequality, so dividing by `|h|` bounds the gradient of `ℓ`. Only `C²` regularity of
the section is used: no third derivative and no commutation of `Δ` with a derivative is needed.

The covariant derivative is controlled by the gradient of `|α|²`. Since `∂bar_a α = 0`, the
covariant derivative is complex linear, `d_a α (v) = v · d_a α (1)`
(`TauCeti.Vortex.covariantDerivative_eq_mul_of_equation_eq_zero`), and
`(∂_s |α|²)² + (∂_t |α|²)² = 4 |α|² |d_a α (1)|²`
(`TauCeti.Vortex.fderiv_normSq_apply_one_sq_add_apply_I_sq`). Where `|α|² ≥ 1 / 2` this bounds
`|d_a α|` by the gradient of `|α|²`
(`TauCeti.Vortex.norm_covariantDerivative_one_le_norm_fderiv_normSq`).

For a vortex with `C²` section the same holds at every order: every iterated derivative of
`log |α|²` and of `|α|² - 1` is `O(exp (-c |z|))` for every `c < 1 / 2`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_log_normSq`,
`TauCeti.Vortex.isBigO_iteratedFDeriv_normSq_sub_one`). These follow from the general estimate
for decaying solutions of `Δ ℓ = κ (exp ℓ - 1)` with `c² < κ`
(`TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`), here with `κ = 1 / 4`; its
hypotheses are the decay of `log |α|²`, which is controlled by the modulus defect, and
smoothness of `log |α|²` near infinity. Wherever `α ≠ 0`, the
`C²` function `log |α|²` solves the scalar equation, hence by Green's identity weakly, so it is
smooth there by planar elliptic regularity
(`TauCeti.Vortex.contDiffAt_log_normSq_of_equation_eq_zero`, via
`TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`). In particular the second
derivative of `log |α|²` decays
(`TauCeti.Vortex.exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp`).

The same comparison applies to two vortices `x` and `y` whose moduli exceed `2 c` outside a disc:
their logarithmic moduli solve the scalar equation there, so their difference is bounded by its
largest value on the boundary circle times `exp (-c (|z| - R))`
(`TauCeti.Vortex.abs_log_normSq_sub_log_normSq_le_mul_exp`). Since `|α| ≤ 1`, the exponential is
`1`-Lipschitz on the values of `ℓ`, so `u = ℓ_x - ℓ_y` has `|Δ u| ≤ |u| / 4`, and the interior
gradient estimate for Poisson's equation
(`TauCeti.norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le`) bounds `D u` by the
same exponential (`TauCeti.Vortex.norm_fderiv_log_normSq_sub_log_normSq_le_mul_exp`).

These are gauge-invariant estimates for classical solutions. The decay of the connection
coefficients themselves depends on a choice of gauge, such as the winding-`m` end trivialization,
and is not treated here.

## Main results

* `TauCeti.Vortex.exists_eventually_norm_fderiv_log_normSq_le_mul_exp`: outside a compact set,
  `|∇ log |α|²| ≤ K exp (-c |z|)` for every `c < 1 / 2`.
* `TauCeti.Vortex.exists_norm_fderiv_normSq_le_mul_exp`: `|∇ |α|²| ≤ K exp (-c |z|)`.
* `TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp`:
  `|d_a α (v)| ≤ K |v| exp (-c |z|)`, so `d_a α (v) → 0` at infinity
  (`TauCeti.Vortex.tendsto_covariantDerivative_cocompact`).
* `TauCeti.Vortex.exists_energyDensity_le_mul_exp`: the energy density is bounded by
  `K exp (-c |z|)` for every `c < 1`.
* `TauCeti.Vortex.contDiffAt_log_normSq_of_equation_eq_zero`: `log |α|²` is smooth wherever
  `α ≠ 0`, for a vortex with `C²` section; `TauCeti.Vortex.contDiffAt_log_normSq_of_pos` is its
  global case.
* `TauCeti.Vortex.isBigO_iteratedFDeriv_log_normSq`,
  `TauCeti.Vortex.isBigO_iteratedFDeriv_normSq_sub_one`: every iterated derivative of `log |α|²`
  and of `|α|² - 1` is `O(exp (-c |z|))` for every `c < 1 / 2`.
* `TauCeti.Vortex.abs_log_normSq_sub_log_normSq_le_mul_exp`,
  `TauCeti.Vortex.norm_fderiv_log_normSq_sub_log_normSq_le_mul_exp`: two vortices with moduli
  above `2 c` outside the disc of radius `R`, whose logarithmic moduli are within `M` of each other
  on its boundary, have `|ℓ_x(z) - ℓ_y(z)| ≤ M exp (-c (|z| - R))` and
  `‖D (ℓ_x - ℓ_y)(z)‖ ≤ 93 M exp (-c (|z| - (R + 3)))` for `|z| ≥ R + 3`.
* `TauCeti.Vortex.exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp`: outside a compact
  set, the second derivative of `log |α|²` is at most `K exp (-c |z|)`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Asymptotics Complex Filter Metric Topology InnerProductSpace Laplacian
open scoped ContDiff

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Exterior decay of the translation differences of `ℓ = log |α|²`.** Suppose that
`|α|² > 0` and `|α|² ≥ 4 c²` on `R - 1 ≤ |w|`, and that `|ℓ (z + h) - ℓ z| ≤ L |h|` on the circle
`|z| = R`. Then `|ℓ z - ℓ (z + h)| ≤ L |h| exp (-c (|z| - R))` for `|z| ≥ R`: `ℓ` and its
translate `ℓ (· + h)` both solve the scalar equation there
(`TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one`). -/
private theorem abs_log_normSq_sub_log_normSq_add_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c R L : ℝ}
    (hc₀ : 0 ≤ c) (hR : 0 < R)
    (hpos : ∀ w : ℂ, R - 1 ≤ ‖w‖ → 0 < 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hc4 : ∀ w : ℂ, R - 1 ≤ ‖w‖ → 4 * c ^ 2 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hmv : ∀ z h : ℂ, ‖z‖ = R → ‖h‖ ≤ 1 →
      |Real.log (4 * (x (z + h) 2 ^ 2 + x (z + h) 3 ^ 2)) -
        Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2))| ≤ L * ‖h‖)
    {h : ℂ} (hh : ‖h‖ ≤ 1) {z : ℂ} (hz : R ≤ ‖z‖) :
    |Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) - Real.log (4 * (x (z + h) 2 ^ 2 + x (z + h) 3 ^ 2))| ≤
      L * ‖h‖ * Real.exp (-(c * (‖z‖ - R))) := by
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  set ℓ : ℂ → ℝ := fun w ↦ Real.log (s w)
  have hscd : ContDiff ℝ 2 s := contDiff_normSq hp hq
  have hw₁ : ∀ w : ℂ, R ≤ ‖w‖ → R - 1 ≤ ‖w‖ := fun w hw ↦ by linarith
  have hwh : ∀ w : ℂ, R ≤ ‖w‖ → R - 1 ≤ ‖w + h‖ := fun w hw ↦ by
    have := abs_norm_sub_norm_le (w + h) w
    rw [add_sub_cancel_left, abs_le] at this
    linarith
  -- Off the zeros, `ℓ` solves the scalar equation `Δ ℓ = (exp ℓ - 1) / 4`.
  have hΔ (w : ℂ) (hw : R - 1 ≤ ‖w‖) : Δ ℓ w = (Real.exp (ℓ w) - 1) / 4 :=
    laplacian_log_normSq_eq_exp hp.contDiffAt hq.contDiffAt (hpos w hw) (Eventually.of_forall hsol)
  have hℓlim : Tendsto ℓ (cocompact ℂ) (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
    rw [Real.log_one] at h
    exact h
  -- Compare `ℓ` with its translate `ℓ (· + h)`, which solves the same equation.
  exact abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one (ℓ₂ := fun w ↦ ℓ (w + h)) (κ := 1 / 4) hR
    hc₀ (fun w hw ↦ hscd.contDiffAt.log (hpos w (hw₁ w hw)).ne')
    (fun w hw ↦ (hscd.contDiffAt.log (hpos (w + h) (hwh w hw)).ne').comp w
      (contDiffAt_id.add contDiffAt_const))
    (fun w hw ↦ by rw [hΔ w (hw₁ w hw)]; ring)
    (fun w hw ↦ by rw [congrFun (laplacian_comp_add_right ℓ h) w, hΔ (w + h) (hwh w hw)]; ring)
    (fun w hw ↦ by rw [Real.exp_log (hpos w (hw₁ w hw))]; linarith [hc4 w (hw₁ w hw)])
    (fun w hw ↦ by rw [Real.exp_log (hpos (w + h) (hwh w hw))]; linarith [hc4 (w + h) (hwh w hw)])
    hℓlim (hℓlim.comp (Homeomorph.addRight h).isClosedEmbedding.tendsto_cocompact)
    (fun w hw ↦ (abs_sub_comm _ _).trans_le (hmv w h hw hh)) hz

/-- The case `0 ≤ c` of `exists_eventually_norm_fderiv_log_normSq_le_mul_exp`, with a
nonnegative constant. -/
private theorem exists_eventually_norm_fderiv_log_normSq_le_mul_exp_of_nonneg
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K, 0 ≤ K ∧ ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  set ℓ : ℂ → ℝ := fun z ↦ Real.log (s z)
  have hscd : ContDiff ℝ 2 s := contDiff_normSq hp hq
  -- Outside a disc of radius `R - 1`, `|α|² > max (4 c²) (1 / 2)`.
  have hθ : max (4 * c ^ 2) (1 / 2) < 1 := max_lt (by nlinarith) (by norm_num)
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hlim.eventually (lt_mem_nhds hθ))
  set R := max R₀ 0 + 1
  have hR₀' : 0 < R := by positivity
  have hsR : ∀ w : ℂ, R - 1 ≤ ‖w‖ → max (4 * c ^ 2) (1 / 2) < s w := fun w hw ↦
    hR₀ ((le_max_left R₀ 0).trans (by linarith))
  have hpos : ∀ w : ℂ, R - 1 ≤ ‖w‖ → 0 < s w := fun w hw ↦
    (lt_max_of_lt_right (by norm_num)).trans (hsR w hw)
  have hℓcd : ∀ w : ℂ, R - 1 ≤ ‖w‖ → ContDiffAt ℝ 2 ℓ w := fun w hw ↦
    hscd.contDiffAt.log (hpos w hw).ne'
  -- A bound `L` for the gradient of `ℓ` on the annulus `R - 1 ≤ |w| ≤ R + 1`.
  set A : Set ℂ := closedBall 0 (R + 1) ∩ {w | R - 1 ≤ ‖w‖}
  have hAc : IsCompact A := (isCompact_closedBall 0 (R + 1)).inter_right
    (isClosed_le continuous_const continuous_norm)
  obtain ⟨L₀, hL₀⟩ := hAc.exists_bound_of_continuousOn (f := fun w ↦ fderiv ℝ ℓ w)
    fun w hw ↦ ((hℓcd w hw.2).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  set L := max L₀ 0
  -- The mean value inequality on unit discs centred on the circle `|z| = R`.
  have hmv : ∀ z h : ℂ, ‖z‖ = R → ‖h‖ ≤ 1 → |ℓ (z + h) - ℓ z| ≤ L * ‖h‖ := by
    intro z h hz hh
    have hball : closedBall z 1 ⊆ A := fun w hw ↦ by
      rw [mem_closedBall, dist_eq_norm] at hw
      have := abs_norm_sub_norm_le w z
      rw [abs_le] at this
      exact ⟨mem_closedBall_zero_iff.mpr (by linarith), show R - 1 ≤ ‖w‖ by linarith⟩
    have hzh : z + h ∈ closedBall z 1 := by
      rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    have h := (convex_closedBall z 1).norm_image_sub_le_of_norm_fderiv_le (f := ℓ) (C := L)
      (fun w hw ↦ (hℓcd w (hball hw).2).differentiableAt (by norm_num))
      (fun w hw ↦ (hL₀ w (hball hw)).trans (le_max_left _ _)) (mem_closedBall_self zero_le_one)
      hzh
    rwa [add_sub_cancel_left, Real.norm_eq_abs] at h
  -- Dividing the decay of `ℓ - ℓ (· + h)` by `|h|` bounds the gradient of `ℓ`.
  refine ⟨L * Real.exp (c * R), by positivity, ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop R] with z hz
  have hd : HasFDerivAt ℓ (fderiv ℝ ℓ z) z :=
    ((hℓcd z (by linarith)).differentiableAt (by norm_num)).hasFDerivAt
  have hC : 0 ≤ L * Real.exp (-(c * (‖z‖ - R))) := by positivity
  have hle := hd.le_of_lip' hC (by
    filter_upwards [closedBall_mem_nhds z one_pos] with y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have h := abs_log_normSq_sub_log_normSq_add_le_mul_exp hp hq hsol hlim hc₀ hR₀' hpos
      (fun w hw ↦ (le_max_left _ _).trans (hsR w hw).le) hmv hy hz
    rw [add_sub_cancel] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h.trans_eq (by ring))
  calc ‖fderiv ℝ ℓ z‖ ≤ L * Real.exp (-(c * (‖z‖ - R))) := hle
    _ = L * Real.exp (c * R) * Real.exp (-(c * ‖z‖)) := by rw [exp_neg_mul_sub, mul_assoc]

/-- **Exponential decay of the gradient of `log |α|²`.** Outside a compact set, a vortex on the
whole plane whose section satisfies `|α| → 1` at infinity has
`|∇ log |α|²| ≤ K exp (-c |z|)`, for every rate `c < 1 / 2`. -/
theorem exists_eventually_norm_fderiv_log_normSq_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK₀, hK⟩ := exists_eventually_norm_fderiv_log_normSq_le_mul_exp_of_nonneg
    hp hq hsol hlim (le_max_right c 0) (max_lt hc (by norm_num))
  refine ⟨K, hK.mono fun z hz ↦ hz.trans (mul_le_mul_of_nonneg_left ?_ hK₀)⟩
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg _)))

/-- **Exponential decay of the gradient of `|α|²`.** A vortex on the whole plane whose section
satisfies `|α| → 1` at infinity has `|∇ |α|²| ≤ K exp (-c |z|)` for every rate `c < 1 / 2`. -/
theorem exists_norm_fderiv_normSq_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z, ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hscd := contDiff_normSq hp hq
  obtain ⟨K, hK⟩ := exists_eventually_norm_fderiv_log_normSq_le_mul_exp hp hq hsol hlim hc
  refine exists_forall_le_mul_exp_of_eventually_le (K := K)
    (hscd.continuous_fderiv (by norm_num)).norm ?_
  filter_upwards [hK, hlim.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with z hz hpos
  -- Where `0 < |α|² ≤ 1`, `|∇ |α|²| ≤ |∇ log |α|²|`.
  exact (norm_fderiv_le_norm_fderiv_log ((hscd.differentiable (by norm_num)) z) hpos
    (normSq_le_one_of_tendsto hp hq hsol hlim z)).trans hz

/-- **Exponential decay of the covariant derivative of a plane vortex.** A vortex on the whole
plane whose section satisfies `|α| → 1` at infinity has `|d_a α (v)| ≤ K |v| exp (-c |z|)` for
every rate `c < 1 / 2`. -/
theorem exists_norm_covariantDerivative_le_mul_exp
    (hb₁ : Continuous (fun w ↦ x w 0))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z v, ‖covariantDerivative x z v‖ ≤ K * ‖v‖ * Real.exp (-(c * ‖z‖)) := by
  have hp₁ : Differentiable ℝ (fun w ↦ x w 2) := hp.differentiable (by norm_num)
  have hq₁ : Differentiable ℝ (fun w ↦ x w 3) := hq.differentiable (by norm_num)
  have hcont : Continuous fun z ↦ ‖covariantDerivative x z 1‖ :=
    (continuous_covariantDerivative_one hb₁ (hp.of_le (by norm_num))
      (hq.of_le (by norm_num))).norm
  obtain ⟨K, hK⟩ := exists_norm_fderiv_normSq_le_mul_exp hp hq hsol hlim hc
  -- Where `|α|² ≥ 1 / 2`, the covariant derivative is bounded by the gradient of `|α|²`.
  obtain ⟨K', hK'⟩ := exists_forall_le_mul_exp_of_eventually_le hcont (c := c) (K := K) (by
    filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with z hz
    exact (norm_covariantDerivative_one_le_norm_fderiv_normSq (hp₁ z) (hq₁ z) (by simp [hsol z])
      (by simp [hsol z]) hz.le).trans (hK z))
  refine ⟨K', fun z v ↦ ?_⟩
  rw [norm_covariantDerivative_eq_mul_of_equation_eq_zero (hp₁ z) (hq₁ z) (by simp [hsol z])
    (by simp [hsol z]) v, mul_comm K', mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK' z) (norm_nonneg v)

/-- **The covariant derivative of a plane vortex vanishes at infinity.** A vortex on the whole
plane whose section satisfies `|α| → 1` at infinity has `d_a α (v) → 0` at infinity, for every
tangent vector `v`. This is the hypothesis on `d_a α` in the Fredholm theory of the gauge-fixed
operator. -/
theorem tendsto_covariantDerivative_cocompact
    (hb₁ : Continuous (fun w ↦ x w 0))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) (v : ℂ) :
    Tendsto (fun z ↦ covariantDerivative x z v) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_norm_covariantDerivative_le_mul_exp hb₁ hp hq hsol hlim
    (c := 1 / 4) (by norm_num)
  have hexp : Tendsto (fun z : ℂ ↦ K * ‖v‖ * Real.exp (-(1 / 4 * ‖z‖))) (cocompact ℂ) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_norm_cocompact_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4)))
  exact squeeze_zero_norm (fun z ↦ hK z v) hexp

/-- **Exponential decay of the energy density of a plane vortex.** A vortex on the whole plane
whose section satisfies `|α| → 1` at infinity has energy density
`|F_a|² + |d_a α|² + (1 - |α|²)²` bounded by `K exp (-c |z|)` for every rate `c < 1`. -/
theorem exists_energyDensity_le_mul_exp
    (hb₁ : Continuous (fun w ↦ x w 0))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1) :
    ∃ K, ∀ z, energyDensity x z ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hc' : c / 2 < 1 / 2 := by linarith
  obtain ⟨K₁, hK₁⟩ := exists_one_sub_normSq_le_mul_exp hp hq hsol hlim hc'
  obtain ⟨K₂, hK₂⟩ := exists_norm_covariantDerivative_le_mul_exp hb₁ hp hq hsol hlim hc'
  refine ⟨65 / 64 * K₁ ^ 2 + 2 * K₂ ^ 2, fun z ↦ ?_⟩
  -- The modulus defect is bounded by `K₁ exp (-(c / 2) |z|)`, and `|d_a α (1)|` by
  -- `K₂ exp (-(c / 2) |z|)`.
  refine (energyDensity_le_of_equation_eq_zero ((hp.differentiable (by norm_num)) z)
    ((hq.differentiable (by norm_num)) z) (hsol z)
    (by linarith [normSq_le_one_of_tendsto hp hq hsol hlim z]) (hK₁ z)
    (by simpa using hK₂ z 1)).trans_eq ?_
  rw [mul_pow, mul_pow, exp_neg_half_mul_sq]
  ring

/-! ### Derivatives of all orders -/

/-- **Smoothness of `log |α|²` for a vortex with `C²` section.** Near a point where the section is
`C²` and nonzero and `x` solves the vortex equations, `log |α|²` is smooth. It is a `C²` solution of
`Δ ℓ = (exp ℓ - 1) / 4` there, hence a weak solution by Green's identity, so it is smooth by
planar elliptic regularity (`TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`). -/
theorem contDiffAt_log_normSq_of_equation_eq_zero {z : ℂ}
    (hp : ContDiffAt ℝ 2 (fun w ↦ x w 2) z) (hq : ContDiffAt ℝ 2 (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0) (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0) :
    ContDiffAt ℝ ∞ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z := by
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)
  -- An open neighbourhood `U` of `z` on which the section is `C²` and nonzero and `x` solves the
  -- vortex equations.
  have hα' : ∀ᶠ w in 𝓝 z, x w 2 ^ 2 + x w 3 ^ 2 ≠ 0 :=
    ((hp.continuousAt.pow 2).add (hq.continuousAt.pow 2)).eventually_ne hα
  obtain ⟨t, ht, htopen, hzt⟩ := _root_.eventually_nhds_iff.mp
    ((hp.eventually (by simp)).and ((hq.eventually (by simp)).and (hα'.and hsol.eventually_nhds)))
  let U : TopologicalSpace.Opens ℂ := ⟨t, htopen⟩
  have hℓU : ContDiffOn ℝ 2 (fun w ↦ Real.log (s w)) U := fun w hw ↦ by
    obtain ⟨hpw, hqw, hαw, -⟩ := ht w hw
    exact (contDiffAt_const.mul ((hpw.pow 2).add (hqw.pow 2))).log
      (mul_ne_zero four_ne_zero hαw) |>.contDiffWithinAt
  -- On `U`, `ℓ` solves `Δ ℓ = (exp ℓ - 1) / 4`, hence weakly by Green's identity.
  have hΔ : ∀ w ∈ U, Δ (fun w ↦ Real.log (s w)) w = 1 / 4 * (Real.exp (Real.log (s w)) - 1) :=
    fun w hw ↦ by
      obtain ⟨hpw, hqw, hαw, hsolw⟩ := ht w hw
      rw [laplacian_log_normSq_of_equation_eq_zero hpw hqw hαw hsolw,
        Real.exp_log (lt_of_le_of_ne (by positivity) (mul_ne_zero four_ne_zero hαw).symm)]
      ring
  have hF : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ ↦ 1 / 4 * (Real.exp p.2 - 1)) (U ×ˢ Set.univ) :=
    (contDiff_const.mul (Real.contDiff_exp.comp contDiff_snd |>.sub contDiff_const)).contDiffOn
  have hsmooth : ContDiffOn ℝ ∞ (fun w ↦ Real.log (s w)) U := by
    simpa using contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp (k := ⊤) hF
      hℓU.continuousOn fun φ ↦ by
        have h := ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian
          (μ := MeasureTheory.volume) hℓU φ
        simp only [smul_eq_mul] at h
        rw [h]
        refine MeasureTheory.integral_congr_ae (.of_forall fun y ↦ ?_)
        by_cases hy : y ∈ U
        · simp only [hΔ y hy]
        · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (φ.tsupport_subset h)]
  exact hsmooth.contDiffAt (htopen.mem_nhds hzt)

/-- **Smoothness of `log |α|²` where `|α|² > 0`.** For a solution of the vortex equations on the
whole plane with `C²` section, `log |α|²` is smooth near every point where the squared modulus is
positive: the global case of `TauCeti.Vortex.contDiffAt_log_normSq_of_equation_eq_zero`. -/
theorem contDiffAt_log_normSq_of_pos (hp : ContDiff ℝ 2 (fun w ↦ x w 2))
    (hq : ContDiff ℝ 2 (fun w ↦ x w 3)) (hsol : ∀ z, equation x z = 0)
    {z : ℂ} (hz : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ContDiffAt ℝ ∞ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z :=
  contDiffAt_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt
    (right_ne_zero_of_mul hz.ne') (Eventually.of_forall hsol)

/-- The hypotheses of `TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one` for
`ℓ = log |α|²` and `κ = 1 / 4`, at some positive rate `c' ≥ c` with `c' < 1 / 2`, given a rate
`c < 1 / 2`. -/
private theorem laplacian_log_normSq_hypotheses
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ c', c ≤ c' ∧ 0 < c' ∧ c' ^ 2 < 1 / 4 ∧
      (∀ᶠ z in cocompact ℂ, ContDiffAt ℝ ∞ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z) ∧
      (∀ᶠ z in cocompact ℂ, Δ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z =
        1 / 4 * (Real.exp (Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2))) - 1)) ∧
      (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) =O[cocompact ℂ]
        fun z ↦ Real.exp (-(c' * ‖z‖)) := by
  -- It suffices to treat a positive rate `c' ≥ c`.
  set c' := max c (1 / 4)
  have hc'pos : 0 < c' := lt_max_of_lt_right (by norm_num)
  have hc'lt : c' < 1 / 2 := max_lt hc (by norm_num)
  refine ⟨c', le_max_left _ _, hc'pos, by nlinarith, ?_⟩
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2) with hs
  have hpos : ∀ᶠ z in cocompact ℂ, 1 / 2 < s z := hlim.eventually (lt_mem_nhds (by norm_num))
  have hs₁ : ∀ z, s z ≤ 1 := normSq_le_one_of_tendsto hp hq hsol hlim
  have hα : ∀ z, 1 / 2 < s z → x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := fun z hz h ↦ by
    simp only [hs, h, mul_zero] at hz
    norm_num at hz
  -- Where `|α|² > 1 / 2`, `ℓ` solves `Δ ℓ = (exp ℓ - 1) / 4`.
  have hΔ : ∀ z, 1 / 2 < s z →
      Δ (fun w ↦ Real.log (s w)) z = 1 / 4 * (Real.exp (Real.log (s z)) - 1) := fun z hz ↦ by
    rw [laplacian_log_normSq_eq_exp hp.contDiffAt hq.contDiffAt ((one_half_pos).trans hz)
      (Eventually.of_forall hsol)]
    ring
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hpos] with z hz
    exact contDiffAt_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt (hα z hz)
      (Eventually.of_forall hsol)
  · filter_upwards [hpos] with z hz
    exact hΔ z hz
  · -- `|log |α|²| ≤ 2 (1 - |α|²)` where `|α|² ≥ 1 / 2`.
    obtain ⟨K, hK⟩ := exists_one_sub_normSq_le_mul_exp hp hq hsol hlim hc'lt
    refine IsBigO.of_bound (2 * K) ?_
    filter_upwards [hpos] with z hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.abs_log_le_two_mul_one_sub hz.le (hs₁ z)).trans (by linarith [hK z])

/-- **Exponential decay of all derivatives of `log |α|²`.** For a plane vortex with `C²` section
whose section satisfies `|α| → 1` at infinity, every iterated derivative of `log |α|²` is
`O(exp (-c |z|))` at infinity, for every rate `c < 1 / 2`. -/
theorem isBigO_iteratedFDeriv_log_normSq
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨c', hcc', hc'pos, hc'κ, hsmooth, heq, hℓd⟩ :=
    laplacian_log_normSq_hypotheses hp hq hsol hlim hc
  exact (isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one hc'pos hc'κ hsmooth heq hℓd
    n).trans (isBigO_exp_neg_mul_norm_of_le hcc' _)

/-- **Exponential decay of the second derivative of `log |α|²`.** For a plane vortex with `C²`
section whose section satisfies `|α| → 1` at infinity, the second derivative of `log |α|²` is at
most `K exp (-c |z|)` outside a compact set, for every rate `c < 1 / 2`. -/
theorem exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := (isBigO_iteratedFDeriv_log_normSq hp hq hsol hlim hc 2).bound
  refine ⟨K, hK.mono fun z hz ↦ ?_⟩
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rwa [Real.norm_of_nonneg (Real.exp_pos _).le] at hz

/-- **Exponential decay of all derivatives of `|α|² - 1`.** For a plane vortex with `C²` section
whose section satisfies `|α| → 1` at infinity, every iterated derivative of `|α|² - 1` is
`O(exp (-c |z|))` at infinity, for every rate `c < 1 / 2`. Equivalently, by the curvature equation,
every derivative of the curvature decays at that rate. -/
theorem isBigO_iteratedFDeriv_normSq_sub_one
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2) - 1) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨c', hcc', hc'pos, hc'κ, hsmooth, heq, hℓd⟩ :=
    laplacian_log_normSq_hypotheses hp hq hsol hlim hc
  have h := isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one hc'pos hc'κ hsmooth
    heq hℓd n
  -- Near infinity `exp (log |α|²) = |α|²`.
  have hpos : ∀ᶠ z in cocompact ℂ, 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    hlim.eventually (lt_mem_nhds (by norm_num))
  refine (h.congr' ?_ EventuallyEq.rfl).trans (isBigO_exp_neg_mul_norm_of_le hcc' _)
  obtain ⟨R, -, hR⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hpos)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
  refine Filter.EventuallyEq.eq_of_nhds (Filter.EventuallyEq.iteratedFDeriv ℝ ?_ n)
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
  rw [Real.exp_log (by linarith [hR (Set.mem_ofPred.mpr hw.le)])]

/-! ### Two vortices with nonvanishing sections outside a disc -/

section TwoVortices

variable {y : ℂ → EuclideanSpace ℝ (Fin 4)} {R c M : ℝ}

/-- Where `|α|² > 4 c²`, the logarithmic modulus `ℓ = log |α|²` of a vortex is smooth, solves the
scalar equation `Δ ℓ = (exp ℓ - 1) / 4` and has `exp ℓ / 4 ≥ c²`: the hypotheses of
`TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one` with `κ = 1 / 4`. -/
private theorem log_normSq_spec_of_lt (hp : ContDiff ℝ 2 (fun w ↦ x w 2))
    (hq : ContDiff ℝ 2 (fun w ↦ x w 3)) (hsol : ∀ z, equation x z = 0) {z : ℂ}
    (hz : 4 * c ^ 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ContDiffAt ℝ ∞ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z ∧
      Δ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z =
        1 / 4 * (Real.exp (Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2))) - 1) ∧
      c ^ 2 ≤ 1 / 4 * Real.exp (Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2))) := by
  have hpos := (by positivity : (0 : ℝ) ≤ 4 * c ^ 2).trans_lt hz
  refine ⟨contDiffAt_log_normSq_of_pos hp hq hsol hpos, ?_, ?_⟩
  · rw [laplacian_log_normSq_eq_exp hp.contDiffAt hq.contDiffAt hpos (.of_forall hsol)]
    ring
  · rw [Real.exp_log hpos]
    linarith

/-- **The logarithmic moduli of two vortices converge to each other outside a disc.** Let `x` and
`y` be solutions of the vortex equations with `C²` sections and `|α|² → 1` at infinity, let
`0 < R` and `0 ≤ c`, and suppose that both moduli satisfy `|α|² > 4 c²` outside the disc of
radius `R` and that their logarithmic moduli `ℓ = log |α|²` differ by at most `M` on its boundary
circle. Then `|ℓ_x(z) - ℓ_y(z)| ≤ M exp (-c (|z| - R))` outside the disc: the case of
`TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one` for vortices. -/
theorem abs_log_normSq_sub_log_normSq_le_mul_exp
    (hxp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hxq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hyp : ContDiff ℝ 2 (fun w ↦ y w 2)) (hyq : ContDiff ℝ 2 (fun w ↦ y w 3))
    (hxs : ∀ z, equation x z = 0) (hys : ∀ z, equation y z = 0)
    (hxl : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hyl : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hR : 0 < R) (hc : 0 ≤ c)
    (hxR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (hyR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 < 4 * (y z 2 ^ 2 + y z 3 ^ 2))
    (hbd : ∀ z, ‖z‖ = R → |Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) -
      Real.log (4 * (y z 2 ^ 2 + y z 3 ^ 2))| ≤ M) {z : ℂ} (hz : R ≤ ‖z‖) :
    |Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) - Real.log (4 * (y z 2 ^ 2 + y z 3 ^ 2))| ≤
      M * Real.exp (-(c * (‖z‖ - R))) := by
  have hx (w : ℂ) (hw : R ≤ ‖w‖) := log_normSq_spec_of_lt hxp hxq hxs (hxR w hw)
  have hy (w : ℂ) (hw : R ≤ ‖w‖) := log_normSq_spec_of_lt hyp hyq hys (hyR w hw)
  exact abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one hR hc
    (fun w hw ↦ (hx w hw).1.of_le (by simp)) (fun w hw ↦ (hy w hw).1.of_le (by simp))
    (fun w hw ↦ (hx w hw).2.1) (fun w hw ↦ (hy w hw).2.1)
    (fun w hw ↦ (hx w hw).2.2) (fun w hw ↦ (hy w hw).2.2)
    (by simpa using hxl.log one_ne_zero) (by simpa using hyl.log one_ne_zero) hbd hz

/-- **The gradients of two vortices converge to each other outside a disc.** Let `x` and `y` be
solutions of the vortex equations with `C²` sections and `|α|² → 1` at infinity, let `0 < R` and
`0 ≤ c`, and suppose that both moduli satisfy `|α|² > 4 c²` outside the disc of radius `R` and
that their logarithmic moduli `ℓ = log |α|²` differ by at most `M` on its boundary circle. Then at
distance at least `3` from the disc,

`‖D (ℓ_x - ℓ_y)(z)‖ ≤ 93 M exp (-c (|z| - (R + 3)))`. -/
theorem norm_fderiv_log_normSq_sub_log_normSq_le_mul_exp
    (hxp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hxq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hyp : ContDiff ℝ 2 (fun w ↦ y w 2)) (hyq : ContDiff ℝ 2 (fun w ↦ y w 3))
    (hxs : ∀ z, equation x z = 0) (hys : ∀ z, equation y z = 0)
    (hxl : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hyl : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hR : 0 < R) (hc : 0 ≤ c)
    (hxR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (hyR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 < 4 * (y z 2 ^ 2 + y z 3 ^ 2))
    (hbd : ∀ z, ‖z‖ = R → |Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) -
      Real.log (4 * (y z 2 ^ 2 + y z 3 ^ 2))| ≤ M) {z : ℂ} (hz : R + 3 ≤ ‖z‖) :
    ‖fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) -
      Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2))) z‖ ≤ 93 * M * Real.exp (-(c * (‖z‖ - (R + 3)))) := by
  set ℓx : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))
  set ℓy : ℂ → ℝ := fun w ↦ Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2))
  set u : ℂ → ℝ := ℓx - ℓy
  obtain ⟨ε, hε⟩ : ∃ ε, ε = M * Real.exp (-(c * (‖z‖ - (R + 3)))) := ⟨_, rfl⟩
  have hM := nonneg_of_forall_norm_eq_abs_le hR.le hbd
  -- Every point within `3` of `z` lies outside the disc, where `|u| ≤ ε`.
  have hfar (w : ℂ) (hw : w ∈ closedBall z 3) : ‖z‖ - 3 ≤ ‖w‖ := by
    have := norm_sub_norm_le z w
    rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub] at hw
    linarith
  have hfarR (w : ℂ) (hw : w ∈ closedBall z 3) : R ≤ ‖w‖ := by linarith [hfar w hw]
  have hu (w : ℂ) (hw : w ∈ closedBall z 3) : |ℓx w - ℓy w| ≤ ε := by
    rw [hε]
    refine (abs_log_normSq_sub_log_normSq_le_mul_exp hxp hxq hyp hyq hxs hys hxl hyl hR hc hxR
      hyR hbd (hfarR w hw)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM)
    nlinarith [mul_nonneg hc (by linarith [hfar w hw] : (0 : ℝ) ≤ ‖w‖ - (‖z‖ - 3))]
  have hx (w : ℂ) (hw : R ≤ ‖w‖) := log_normSq_spec_of_lt hxp hxq hxs (hxR w hw)
  have hy (w : ℂ) (hw : R ≤ ‖w‖) := log_normSq_spec_of_lt hyp hyq hys (hyR w hw)
  -- Outside the disc `Δ u = (exp ℓx - exp ℓy) / 4`, by the scalar equation for both vortices.
  have hΔu (w : ℂ) (hw : R ≤ ‖w‖) : Δ u w = 1 / 4 * (Real.exp (ℓx w) - Real.exp (ℓy w)) :=
    laplacian_sub_eq_of_laplacian_eq_exp_sub_one ((hx w hw).1.of_le (by simp))
      ((hy w hw).1.of_le (by simp)) (hx w hw).2.1 (hy w hw).2.1
  -- Since `ℓx, ℓy ≤ 0`, the exponential is `1`-Lipschitz on their values, so `|Δ u| ≤ |u| / 4`.
  have hΔ (w : ℂ) (hw : w ∈ closedBall z 3) : |Δ u w| ≤ ε / 4 := by
    have h : |Real.exp (ℓx w) - Real.exp (ℓy w)| ≤ Real.exp 0 * |ℓx w - ℓy w| :=
      Real.abs_exp_sub_exp_le (log_normSq_nonpos hxp hxq hxs hxl w)
        (log_normSq_nonpos hyp hyq hys hyl w)
    rw [hΔu w (hfarR w hw), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    rw [Real.exp_zero, one_mul] at h
    linarith [hu w hw]
  -- The interior gradient estimate for Poisson's equation on the disc of radius `3` about `z`.
  have hgrad := norm_iteratedFDeriv_succ_le_of_norm_iteratedFDeriv_laplacian_le (n := 0)
    (x := z) (ρ := 1) (u := u)
    (fun w hw ↦ ((hx w (hfarR w (by simpa using hw))).1.sub
      (hy w (hfarR w (by simpa using hw))).1).of_le (by simp)) one_pos
    (fun w hw ↦ by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact hu w (ball_subset_closedBall (ball_subset_ball (by norm_num) hw)))
    (fun w hw ↦ by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact hΔ w (ball_subset_closedBall (by simpa using hw)))
  rw [zero_add, norm_iteratedFDeriv_one] at hgrad
  -- The estimate reads `‖D u (z)‖ ≤ 8 ε / ρ + 340 K ρ` with `ρ = 1` and `K = ε / 4`; this is
  -- `(8 + 85) ε = 93 ε`.
  calc ‖fderiv ℝ u z‖ ≤ 8 * ε / 1 + 340 * (ε / 4) * 1 := hgrad
    _ = 93 * M * Real.exp (-(c * (‖z‖ - (R + 3)))) := by rw [hε]; ring

end TwoVortices

end TauCeti.Vortex
