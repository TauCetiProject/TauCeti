/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Decay
import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# Exponential decay of the first derivatives of a plane vortex

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
at least the smaller of the values of `|α|² / 4` at the two points
(`Real.mul_sq_log_sub_log_le_sub_mul_log_sub_log`), so `V ≥ c²` outside a large disc. Both `D` and
`-D` are then subsolutions of `-Δ + V`, and the exterior comparison principle with a variable
potential (`TauCeti.le_mul_exp_of_mul_le_laplacian`) bounds `|D|` by its values on a circle times
`exp (-c |z|)`. On that circle `|D| ≤ L |h|` by the mean value inequality, so dividing by `|h|`
bounds the gradient of `ℓ`. Only `C²` regularity of the section is used: no third derivative
and no commutation of `Δ` with a derivative is needed.

The covariant derivative is controlled by the gradient of `|α|²`. Since `∂bar_a α = 0`, the
covariant derivative is complex linear, `d_a α (v) = v · d_a α (1)`
(`TauCeti.Vortex.covariantDerivative_eq_mul_of_equation_eq_zero`), and
`(∂_s |α|²)² + (∂_t |α|²)² = 4 |α|² |d_a α (1)|²`
(`TauCeti.Vortex.fderiv_normSq_apply_one_sq_add_apply_I_sq`). Where `|α|² ≥ 1 / 2` this bounds
`|d_a α|` by the gradient of `|α|²`
(`TauCeti.Vortex.norm_covariantDerivative_one_le_norm_fderiv_normSq`).

These are gauge-invariant estimates for classical solutions. The decay of the connection
coefficients themselves depends on a choice of gauge, such as the winding-`m` end trivialization,
and is not treated here; neither are higher derivatives.

## Main results

* `TauCeti.Vortex.exists_eventually_norm_fderiv_log_normSq_le_mul_exp`: outside a compact set,
  `|∇ log |α|²| ≤ K exp (-c |z|)` for every `c < 1 / 2`.
* `TauCeti.Vortex.exists_norm_fderiv_normSq_le_mul_exp`: `|∇ |α|²| ≤ K exp (-c |z|)`.
* `TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp`:
  `|d_a α (v)| ≤ K |v| exp (-c |z|)`.
* `TauCeti.Vortex.exists_energyDensity_le_mul_exp`: the energy density is bounded by
  `K exp (-c |z|)` for every `c < 1`.

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

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- Where `|α|² > 0` at `w` and at `w + h`, the difference `D = ℓ - ℓ (· + h)` of `ℓ = log |α|²`
satisfies `Δ D (w) = (|α|²(w) - |α|²(w + h)) / 4`, by the scalar equation at both points. -/
private theorem laplacian_log_normSq_sub_comp_add_right
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {w h : ℂ} (hw : 0 < 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hwh : 0 < 4 * (x (w + h) 2 ^ 2 + x (w + h) 3 ^ 2)) :
    Δ (fun y ↦ Real.log (4 * (x y 2 ^ 2 + x y 3 ^ 2)) -
        Real.log (4 * (x (y + h) 2 ^ 2 + x (y + h) 3 ^ 2))) w =
      (4 * (x w 2 ^ 2 + x w 3 ^ 2) - 4 * (x (w + h) 2 ^ 2 + x (w + h) 3 ^ 2)) / 4 := by
  set ℓ : ℂ → ℝ := fun y ↦ Real.log (4 * (x y 2 ^ 2 + x y 3 ^ 2))
  have hscd := contDiff_normSq hp hq
  have hshift : ContDiffAt ℝ 2 (fun y ↦ ℓ (y + h)) w :=
    (hscd.contDiffAt.log hwh.ne').comp w (contDiffAt_id.add contDiffAt_const)
  rw [show (fun y ↦ ℓ y - ℓ (y + h)) = ℓ - fun y ↦ ℓ (y + h) from rfl,
    (hscd.contDiffAt.log hw.ne').laplacian_sub hshift, congrFun (laplacian_comp_add_right ℓ h) w,
    laplacian_log_normSq_of_equation_eq_zero (hb₁ w) (hb₂ w) hp.contDiffAt hq.contDiffAt
      (right_ne_zero_of_mul hw.ne') (Eventually.of_forall hsol),
    laplacian_log_normSq_of_equation_eq_zero (hb₁ (w + h)) (hb₂ (w + h)) hp.contDiffAt
      hq.contDiffAt (right_ne_zero_of_mul hwh.ne') (Eventually.of_forall hsol)]
  ring

/-- **Exterior decay of the translation differences of `ℓ = log |α|²`.** Suppose that
`|α|² > 0` and `|α|² ≥ 4 c²` on `R - 1 ≤ |w|`, and that `|ℓ (z + h) - ℓ z| ≤ L |h|` on the circle
`|z| = R`. Then `|ℓ z - ℓ (z + h)| ≤ L |h| exp (-c (|z| - R))` for `|z| ≥ R`. The difference
solves `Δ D = V D` for a potential `V ≥ c²`, so `D` and `-D` are subsolutions of `-Δ + V`. -/
private theorem abs_log_normSq_sub_log_normSq_add_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c R L : ℝ}
    (hc₀ : 0 ≤ c) (hR : 0 < R) (hL : 0 ≤ L)
    (hpos : ∀ w : ℂ, R - 1 ≤ ‖w‖ → 0 < 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hc4 : ∀ w : ℂ, R - 1 ≤ ‖w‖ → 4 * c ^ 2 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hmv : ∀ z h : ℂ, ‖z‖ = R → ‖h‖ ≤ 1 →
      |Real.log (4 * (x (z + h) 2 ^ 2 + x (z + h) 3 ^ 2)) -
        Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2))| ≤ L * ‖h‖)
    {h : ℂ} (hh : ‖h‖ ≤ 1) {z : ℂ} (hz : R ≤ ‖z‖) :
    |Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) - Real.log (4 * (x (z + h) 2 ^ 2 + x (z + h) 3 ^ 2))| ≤
      L * ‖h‖ * Real.exp (-(c * (‖z‖ - R))) := by
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  set D : ℂ → ℝ := fun w ↦ Real.log (s w) - Real.log (s (w + h))
  have hscd : ContDiff ℝ 2 s := contDiff_normSq hp hq
  have hw₁ : ∀ w : ℂ, R ≤ ‖w‖ → R - 1 ≤ ‖w‖ := fun w hw ↦ by linarith
  have hwh : ∀ w : ℂ, R ≤ ‖w‖ → R - 1 ≤ ‖w + h‖ := fun w hw ↦ by
    have := abs_norm_sub_norm_le (w + h) w
    rw [add_sub_cancel_left, abs_le] at this
    linarith
  have hDcd : ∀ w : ℂ, R ≤ ‖w‖ → ContDiffAt ℝ 2 D w := fun w hw ↦
    (hscd.contDiffAt.log (hpos w (hw₁ w hw)).ne').sub
      ((hscd.contDiffAt.log (hpos (w + h) (hwh w hw)).ne').comp w
        (contDiffAt_id.add contDiffAt_const))
  have hΔD : ∀ w : ℂ, R ≤ ‖w‖ → Δ D w = (s w - s (w + h)) / 4 := fun w hw ↦
    laplacian_log_normSq_sub_comp_add_right hb₁ hb₂ hp hq hsol (hpos w (hw₁ w hw))
      (hpos (w + h) (hwh w hw))
  -- The potential `V = Δ D / D` is a difference quotient of `exp / 4`, hence at least `c²`.
  set V : ℂ → ℝ := fun w ↦ if D w = 0 then c ^ 2 else Δ D w / D w with hV
  have hVD : ∀ w : ℂ, R ≤ ‖w‖ → V w * D w = Δ D w := fun w hw ↦ by
    by_cases h₀ : D w = 0
    · have hss : s w = s (w + h) := Real.log_injOn_pos (Set.mem_Ioi.mpr (hpos w (hw₁ w hw)))
        (Set.mem_Ioi.mpr (hpos (w + h) (hwh w hw))) (sub_eq_zero.mp h₀)
      rw [hΔD w hw, hss, h₀]
      simp
    · simp only [hV, h₀, ↓reduceIte]
      field_simp
  have hVc : ∀ w : ℂ, R < ‖w‖ → c ^ 2 ≤ V w := fun w hw ↦ by
    by_cases h₀ : D w = 0
    · simp [hV, h₀]
    · simp only [hV, h₀, ↓reduceIte]
      have hmono : 4 * c ^ 2 * D w ^ 2 ≤ (s w - s (w + h)) * D w :=
        Real.mul_sq_log_sub_log_le_sub_mul_log_sub_log (hpos w (hw₁ w hw.le))
          (hpos (w + h) (hwh w hw.le)) (hc4 w (hw₁ w hw.le)) (hc4 (w + h) (hwh w hw.le))
      have hD2 : 0 < D w ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 h₀).symm
      have hquot : Δ D w / D w = (s w - s (w + h)) * D w / (4 * D w ^ 2) := by
        rw [hΔD w hw.le]
        field_simp
      rw [hquot, le_div_iff₀ (by positivity)]
      linarith
  -- Both `D` and `-D` tend to zero at infinity and are bounded by `L |h|` on the circle.
  have hcont : ContinuousOn D {w | R ≤ ‖w‖} := fun w hw ↦
    (hDcd w hw).continuousAt.continuousWithinAt
  have hℓlim : Tendsto (fun w ↦ Real.log (s w)) (cocompact ℂ) (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
    rw [Real.log_one] at h
    exact h
  have hDlim : Tendsto D (cocompact ℂ) (𝓝 0) := by
    have := hℓlim.sub (hℓlim.comp (Homeomorph.addRight h).isClosedEmbedding.tendsto_cocompact)
    simpa [Function.comp_def] using this
  have hM : 0 ≤ L * ‖h‖ := mul_nonneg hL (norm_nonneg _)
  have hup := le_mul_exp_of_mul_le_laplacian hR hc₀ hM hcont (fun w hw ↦ hDcd w hw.le) hVc
    (fun w hw ↦ (hVD w hw.le).le)
    (fun w hw ↦ (le_abs_self _).trans ((abs_sub_comm _ _).trans_le (hmv w h hw hh))) hDlim hz
  have hdown := le_mul_exp_of_mul_le_laplacian (u := -D) hR hc₀ hM hcont.neg
    (fun w hw ↦ (hDcd w hw.le).neg) hVc
    (fun w hw ↦ by rw [laplacian_neg, Pi.neg_apply, Pi.neg_apply, mul_neg, hVD w hw.le])
    (fun w hw ↦ (neg_le_abs _).trans ((abs_sub_comm _ _).trans_le (hmv w h hw hh)))
    (by have h' := hDlim.neg; rw [neg_zero] at h'; exact h') hz
  exact abs_le.mpr ⟨by simp only [Pi.neg_apply] at hdown; linarith, hup⟩

/-- The case `0 ≤ c` of `exists_eventually_norm_fderiv_log_normSq_le_mul_exp`, with a
nonnegative constant. -/
private theorem exists_eventually_norm_fderiv_log_normSq_le_mul_exp_of_nonneg
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
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
    have h := abs_log_normSq_sub_log_normSq_add_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc₀ hR₀'
      (le_max_right _ _) hpos (fun w hw ↦ (le_max_left _ _).trans (hsR w hw).le) hmv hy hz
    rw [add_sub_cancel] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h.trans_eq (by ring))
  calc ‖fderiv ℝ ℓ z‖ ≤ L * Real.exp (-(c * (‖z‖ - R))) := hle
    _ = L * Real.exp (c * R) * Real.exp (-(c * ‖z‖)) := by rw [exp_neg_mul_sub, mul_assoc]

/-- **Exponential decay of the gradient of `log |α|²`.** Outside a compact set, a vortex on the
whole plane whose section satisfies `|α| → 1` at infinity has
`|∇ log |α|²| ≤ K exp (-c |z|)`, for every rate `c < 1 / 2`. -/
theorem exists_eventually_norm_fderiv_log_normSq_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK₀, hK⟩ := exists_eventually_norm_fderiv_log_normSq_le_mul_exp_of_nonneg hb₁ hb₂
    hp hq hsol hlim (le_max_right c 0) (max_lt hc (by norm_num))
  refine ⟨K, hK.mono fun z hz ↦ hz.trans (mul_le_mul_of_nonneg_left ?_ hK₀)⟩
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg _)))

/-- **Exponential decay of the gradient of `|α|²`.** A vortex on the whole plane whose section
satisfies `|α| → 1` at infinity has `|∇ |α|²| ≤ K exp (-c |z|)` for every rate `c < 1 / 2`. -/
theorem exists_norm_fderiv_normSq_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z, ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hscd := contDiff_normSq hp hq
  obtain ⟨K, hK⟩ := exists_eventually_norm_fderiv_log_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc
  refine exists_forall_le_mul_exp_of_eventually_le (K := K)
    (hscd.continuous_fderiv (by norm_num)).norm ?_
  filter_upwards [hK, hlim.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with z hz hpos
  -- Where `|α|² > 0`, `∇ |α|² = |α|² ∇ log |α|²` and `|α|² ≤ 1`.
  have hd := ((hscd.differentiable (by norm_num)) z).hasFDerivAt.log hpos.ne'
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos] at hz
  have h₁ := normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim z
  have heq : ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ =
      4 * (x z 2 ^ 2 + x z 3 ^ 2) * ((4 * (x z 2 ^ 2 + x z 3 ^ 2))⁻¹ *
        ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖) := by
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  rw [heq]
  exact (mul_le_mul h₁ hz (by positivity) zero_le_one).trans_eq (one_mul _)

/-- **Exponential decay of the covariant derivative of a plane vortex.** A vortex on the whole
plane whose section satisfies `|α| → 1` at infinity has `|d_a α (v)| ≤ K |v| exp (-c |z|)` for
every rate `c < 1 / 2`. -/
theorem exists_norm_covariantDerivative_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z v, ‖covariantDerivative x z v‖ ≤ K * ‖v‖ * Real.exp (-(c * ‖z‖)) := by
  have hp₁ : Differentiable ℝ (fun w ↦ x w 2) := hp.differentiable (by norm_num)
  have hq₁ : Differentiable ℝ (fun w ↦ x w 3) := hq.differentiable (by norm_num)
  -- The covariant derivative along `1` is continuous.
  have hαcd : ContDiff ℝ 2 (sectionValue x) := contDiff_sectionValue hp hq
  have hcont : Continuous fun z ↦ ‖covariantDerivative x z 1‖ := by
    have h₁ : Continuous fun z ↦ fderiv ℝ (sectionValue x) z 1 :=
      (hαcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have h₂ := hαcd.continuous
    have h₀ : Continuous fun z ↦ x z 0 := hb₁.continuous
    simp only [covariantDerivative_apply, one_re, one_im, mul_one, mul_zero, add_zero]
    exact (h₁.add ((continuous_const.mul (continuous_ofReal.comp h₀)).mul h₂)).norm
  obtain ⟨K, hK⟩ := exists_norm_fderiv_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc
  -- Where `|α|² ≥ 1 / 2`, the covariant derivative is bounded by the gradient of `|α|²`.
  obtain ⟨K', hK'⟩ := exists_forall_le_mul_exp_of_eventually_le hcont (c := c) (K := K) (by
    filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with z hz
    exact (norm_covariantDerivative_one_le_norm_fderiv_normSq (hp₁ z) (hq₁ z) (by simp [hsol z])
      (by simp [hsol z]) hz.le).trans (hK z))
  refine ⟨K', fun z v ↦ ?_⟩
  rw [covariantDerivative_eq_mul_of_equation_eq_zero (hp₁ z) (hq₁ z) (by simp [hsol z])
    (by simp [hsol z]) v, norm_mul, mul_comm K', mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK' z) (norm_nonneg v)

/-- **Exponential decay of the energy density of a plane vortex.** A vortex on the whole plane
whose section satisfies `|α| → 1` at infinity has energy density
`|F_a|² + |d_a α|² + (1 - |α|²)²` bounded by `K exp (-c |z|)` for every rate `c < 1`. -/
theorem exists_energyDensity_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1) :
    ∃ K, ∀ z, energyDensity x z ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hc' : c / 2 < 1 / 2 := by linarith
  obtain ⟨K₁, hK₁⟩ := exists_one_sub_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc'
  obtain ⟨K₂, hK₂⟩ := exists_norm_covariantDerivative_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc'
  refine ⟨(1 / 64 + 1) * K₁ ^ 2 + 2 * K₂ ^ 2, fun z ↦ ?_⟩
  set E := Real.exp (-(c / 2 * ‖z‖)) with hE
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hEsq : E ^ 2 = Real.exp (-(c * ‖z‖)) := by
    rw [hE, ← Real.exp_nat_mul]
    ring_nf
  -- The modulus defect, and hence the curvature, is bounded by `K₁ E`.
  have hdef₀ : 0 ≤ 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
    linarith [normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim z]
  have hdef : (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) ^ 2 ≤ K₁ ^ 2 * E ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hdef₀ (hK₁ z) 2
  have hcov (v : ℂ) (hv : ‖v‖ = 1) : ‖covariantDerivative x z v‖ ^ 2 ≤ K₂ ^ 2 * E ^ 2 := by
    rw [← mul_pow]
    have := hK₂ z v
    rw [hv, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have h1 := hcov 1 norm_one
  have hI := hcov I norm_I
  rw [energyDensity_apply, curvature_apply, curvature_eq_of_equation_eq_zero (hsol z),
    sq_norm_sectionValue, ← hEsq]
  nlinarith

end TauCeti.Vortex
