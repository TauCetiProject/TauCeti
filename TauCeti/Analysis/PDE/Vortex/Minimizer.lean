/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ReducedFunctional
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.Sequences
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
import TauCeti.Analysis.PDE.Vortex.Potential
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# A minimizer of Taubes's functional on `W^{1,2}(ℂ)`

Let `P` be a complex polynomial of degree `m ≥ 1`, and put `h = ‖P‖² / (1 + ‖P‖²)` and
`c = 2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8`. Taubes obtains the vortex with zero divisor `P`
from a minimizer of the functional

`I(w) = ‖∇w‖₂² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) + ∫ c w`

(`TauCeti.Vortex.reducedFunctional` on compactly supported `C¹` functions). This file extends
`I` to the Sobolev space `W^{1,2}(ℂ)` (`TauCeti.W1p volume ⊤ 2`) and proves that it attains its
minimum there.

On `W^{1,2}(ℂ)` the potential `∫ h (exp (2w) - 1 - 2w)` can be infinite, so it is taken as an
extended nonnegative integral (`TauCeti.Vortex.sobolevReducedPotential`) and the functional takes
values in `EReal` (`TauCeti.Vortex.sobolevReducedFunctional`). On compactly supported `C¹`
functions it agrees with `reducedFunctional`
(`TauCeti.Vortex.sobolevReducedFunctional_eq_reducedFunctional`).

The proof is the direct method.

* **Approximation.** Every value of `I` on `W^{1,2}(ℂ)` is approached from above by values on
  smooth compactly supported functions
  (`TauCeti.Vortex.exists_reducedFunctional_lt_of_sobolevReducedFunctional_lt`). Test functions
  `φₙ → u` are dense in `W^{1,2}(ℂ)`, but `exp (2φₙ)` need not converge, so the `φₙ` are first
  composed with the bounded truncation `θ_K(t) = K arctan (t / K)`. On functions bounded above
  the potential is continuous in `L²`, `θ_K` decreases the Dirichlet energy and the potential,
  and `θ_K u → u` as `K → ∞`.
* **Compactness.** A minimizing sequence of test functions is bounded in `W^{1,2}(ℂ)` by the
  coercivity estimate `TauCeti.Vortex.exists_integral_le_of_reducedFunctional_le`. The Hilbert
  space `W^{1,2}(ℂ)` is uniformly convex, hence reflexive
  (`TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace`), so a subsequence converges
  weakly.
* **Lower semicontinuity.** The Dirichlet energy is weakly lower semicontinuous because norm
  balls are convex and closed, the potential by
  `TauCeti.Vortex.lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub`, and the linear term
  is weakly continuous.

Hence the weak limit `w` has finite potential and `I(w) ≤ I(v)` for every `v ∈ W^{1,2}(ℂ)`
(`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`). The Euler–Lagrange equation of
`w`, its regularity and its decay are not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal Gradient

variable {P : Polynomial ℂ}

/-- The nonlinear potential `∫ h (exp (2u) - 1 - 2u)`, `h = ‖P‖² / (1 + ‖P‖²)`, of Taubes's
functional at a function `u ∈ W^{1,2}(ℂ)`, as an extended nonnegative integral. It may be
infinite. -/
def sobolevReducedPotential (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
    (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))

/-- **Taubes's functional on `W^{1,2}(ℂ)`**:

`I(u) = ‖∇u‖₂² / 2 + ∫ c u + (1 / 16) ∫ h (exp (2u) - 1 - 2u)`,

where `c = 2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8` and `h = ‖P‖² / (1 + ‖P‖²)`, with the
potential `TauCeti.Vortex.sobolevReducedPotential P u` possibly infinite. On compactly
supported `C¹` functions it is `TauCeti.Vortex.reducedFunctional P`. -/
def sobolevReducedFunctional (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) : EReal :=
  ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) +
    ((sobolevReducedPotential P u / 16 : ℝ≥0∞) : EReal)

/-- The defining formula of the Sobolev potential. -/
theorem sobolevReducedPotential_def (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedPotential P u = ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) := (rfl)

/-- The defining formula of Taubes's functional on `W^{1,2}(ℂ)`. -/
theorem sobolevReducedFunctional_def (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u =
      ((‖W1p.gradient u‖ ^ 2 / 2 + ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 /
          (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) +
        ((sobolevReducedPotential P u / 16 : ℝ≥0∞) : EReal) := (rfl)

/-! ### Pointwise facts -/

/-- The integrand `exp (2t) - 1 - 2t` of the potential is nonnegative. -/
private theorem exp_two_mul_sub_one_sub_nonneg (t : ℝ) : 0 ≤ Real.exp (2 * t) - 1 - 2 * t := by
  linarith [Real.add_one_le_exp (2 * t)]

private theorem weight_nonneg (P : Polynomial ℂ) (z : ℂ) :
    0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by positivity

private theorem weight_le_one (P : Polynomial ℂ) (z : ℂ) :
    ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ≤ 1 :=
  (div_le_one (by positivity)).2 (by linarith)

private theorem ofReal_div_sixteen (x : ℝ) : ENNReal.ofReal x / 16 = ENNReal.ofReal (x / 16) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

private theorem ae_restrict_top_iff {p : ℂ → Prop} :
    (∀ᵐ z ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ), p z) ↔ ∀ᵐ z, p z := by simp

private theorem integral_restrict_top (f : ℂ → ℝ) :
    ∫ z in ((⊤ : Opens ℂ) : Set ℂ), f z = ∫ z, f z := by simp

private theorem lintegral_restrict_top (f : ℂ → ℝ≥0∞) :
    ∫⁻ z in ((⊤ : Opens ℂ) : Set ℂ), f z = ∫⁻ z, f z := by simp

/-! ### Sobolev representatives of compactly supported functions -/

private theorem memLp_value (u : W1p (volume : Measure ℂ) ⊤ 2) :
    MemLp (W1p.value u : ℂ → ℝ) 2 volume := by
  have h := Lp.memLp (W1p.value u)
  simpa using h

private theorem integral_sq_eq_norm_value_sq {v : W1p (volume : Measure ℂ) ⊤ 2} {a : ℂ → ℝ}
    (ha : W1p.value v =ᵐ[volume] a) : ∫ z, a z ^ 2 = ‖W1p.value v‖ ^ 2 := by
  rw [← W1p.integral_value_sq_eq_norm_value_sq, integral_restrict_top]
  exact integral_congr_ae (ha.mono fun z hz ↦ by simp only [hz])

/-- The `L²` distance of a function from the value of `u`, through a Sobolev representative. -/
private theorem integral_sub_value_sq_eq {v u : W1p (volume : Measure ℂ) ⊤ 2} {a : ℂ → ℝ}
    (ha : W1p.value v =ᵐ[volume] a) :
    ∫ z, (a z - W1p.value u z) ^ 2 = ‖W1p.value v - W1p.value u‖ ^ 2 := by
  have hsub : W1p.value v - W1p.value u = W1p.value (v - u) := by
    simp only [← W1p.valueL_apply, map_sub]
  rw [hsub]
  refine integral_sq_eq_norm_value_sq ?_
  filter_upwards [ha, ae_restrict_top_iff.1 (W1p.value_sub_ae v u)] with z hz hsub
  rw [hsub, Pi.sub_apply, hz]

/-- The potential of a compactly supported `C¹` function is the real integral. -/
private theorem sobolevReducedPotential_eq_ofReal {w : ℂ → ℝ} (hw : ContDiff ℝ 1 w)
    (hws : HasCompactSupport w) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : W1p.value u =ᵐ[volume] w) :
    sobolevReducedPotential P u = ENNReal.ofReal
      (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z)) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_mul_exp_sub_one_sub P hw.continuous hws)
    (Eventually.of_forall fun z ↦ mul_nonneg (weight_nonneg P z)
      (exp_two_mul_sub_one_sub_nonneg _)), sobolevReducedPotential_def]
  exact lintegral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- The squared Dirichlet energy of a compactly supported `C¹` function is the squared norm of
the gradient of a Sobolev representative. -/
private theorem integral_norm_fderiv_sq_eq {w : ℂ → ℝ} {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hg : W1p.gradient u =ᵐ[volume] ∇ w) :
    ∫ z, ‖fderiv ℝ w z‖ ^ 2 = ‖W1p.gradient u‖ ^ 2 := by
  rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq, integral_restrict_top]
  refine integral_congr_ae (hg.mono fun z hz ↦ ?_)
  simp only [hz, norm_gradient_eq_norm_fderiv]

/-! ### Agreement with the functional on test functions -/

/-- On a compactly supported `C¹` function `w`, Taubes's functional on `W^{1,2}(ℂ)` is
`TauCeti.Vortex.reducedFunctional P w`. -/
theorem sobolevReducedFunctional_eq_reducedFunctional {w : ℂ → ℝ} (hw : ContDiff ℝ 1 w)
    (hws : HasCompactSupport w) {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : W1p.value u =ᵐ[volume] w) (hg : W1p.gradient u =ᵐ[volume] ∇ w) :
    sobolevReducedFunctional P u = reducedFunctional P w := by
  have hlin : (∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) =
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * w z :=
    integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])
  have hE : 0 ≤ ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * w z) - 1 - 2 * w z) :=
    integral_nonneg fun z ↦ mul_nonneg (weight_nonneg P z) (exp_two_mul_sub_one_sub_nonneg _)
  rw [sobolevReducedFunctional_def, ← integral_norm_fderiv_sq_eq hg, hlin,
    sobolevReducedPotential_eq_ofReal hw hws hv, ofReal_div_sixteen, EReal.coe_ennreal_ofReal,
    max_eq_left (by positivity), ← EReal.coe_add, reducedFunctional_def]
  congr 1
  ring

/-! ### The truncation `θ_K(t) = K arctan (t / K)` -/

/-- The truncation `θ_K(t) = K arctan (t / K)`: smooth, `1`-Lipschitz, bounded above by `K π / 2`,
fixing `0`, and moving every `t` towards `0`. -/
private def trunc (K t : ℝ) : ℝ := K * Real.arctan (t / K)

private theorem hasDerivAt_trunc {K : ℝ} (hK : 0 < K) (t : ℝ) :
    HasDerivAt (trunc K) (1 + (t / K) ^ 2)⁻¹ t := by
  have h := ((Real.hasDerivAt_arctan (t / K)).comp t ((hasDerivAt_id t).div_const K)).const_mul K
  refine h.congr_deriv ?_
  field_simp

private theorem contDiff_trunc (K : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (trunc K) :=
  contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const K))

private theorem trunc_zero (K : ℝ) : trunc K 0 = 0 := by simp [trunc]

private theorem trunc_le {K : ℝ} (hK : 0 < K) (t : ℝ) : trunc K t ≤ K * (Real.pi / 2) :=
  mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two _).le hK.le

private theorem abs_trunc_sub_le {K : ℝ} (hK : 0 < K) (s t : ℝ) :
    |trunc K s - trunc K t| ≤ |s - t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := univ) (x := t)
    (y := s) (C := 1) (fun x _ ↦ (hasDerivAt_trunc hK x).hasDerivWithinAt)
    (fun x _ ↦ ?_) convex_univ (mem_univ _) (mem_univ _)
  · simpa only [Real.norm_eq_abs, one_mul] using h
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (x / K)])

private theorem abs_trunc_le {K : ℝ} (hK : 0 < K) (t : ℝ) : |trunc K t| ≤ |t| := by
  simpa [trunc_zero] using abs_trunc_sub_le hK t 0

/-- `θ_K` moves `t ≥ 0` into `[0, t]`. -/
private theorem trunc_mem_Icc_of_nonneg {K : ℝ} (hK : 0 < K) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ trunc K t ∧ trunc K t ≤ t := by
  have h0 : 0 ≤ t / K := div_nonneg ht hK.le
  refine ⟨mul_nonneg hK.le (Real.arctan_nonneg.2 h0), ?_⟩
  calc trunc K t ≤ K * (t / K) := mul_le_mul_of_nonneg_left (Real.arctan_le_self h0) hK.le
    _ = t := by field_simp

/-- `θ_K` moves `t ≤ 0` into `[t, 0]`. -/
private theorem trunc_mem_Icc_of_nonpos {K : ℝ} (hK : 0 < K) {t : ℝ} (ht : t ≤ 0) :
    t ≤ trunc K t ∧ trunc K t ≤ 0 := by
  have h0 : t / K ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht hK.le
  refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos hK.le (Real.arctan_le_zero.2 h0)⟩
  calc t = K * (t / K) := by field_simp
    _ ≤ trunc K t := mul_le_mul_of_nonneg_left (Real.self_le_arctan h0) hK.le

/-- `θ_K(t) → t` as `K → ∞`. -/
private theorem tendsto_trunc (t : ℝ) :
    Tendsto (fun n : ℕ ↦ trunc ((n : ℝ) + 1) t) atTop (𝓝 t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [trunc_zero]
  have hslope : Tendsto (fun s : ℝ ↦ s⁻¹ * Real.arctan s) (𝓝[≠] 0) (𝓝 1) := by
    have h := (Real.hasDerivAt_arctan 0).tendsto_slope_zero
    simpa [Real.arctan_zero] using h
  have hs : Tendsto (fun n : ℕ ↦ t / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n ↦ div_ne_zero ht (by positivity))
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have h := (hslope.comp hs).const_mul t
  rw [mul_one] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_apply, trunc]
  field_simp

/-- The integrand `Φ(t) = exp (2t) - 1 - 2t` of the potential decreases under `θ_K`. -/
private theorem exp_trunc_le {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Real.exp (2 * trunc K t) - 1 - 2 * trunc K t ≤ Real.exp (2 * t) - 1 - 2 * t := by
  rcases le_total 0 t with ht | ht
  · obtain ⟨h0, h1⟩ := trunc_mem_Icc_of_nonneg hK ht
    have hle := Real.add_one_le_exp (2 * (t - trunc K t))
    have hexp : Real.exp (2 * t) = Real.exp (2 * trunc K t) * Real.exp (2 * (t - trunc K t)) := by
      rw [← Real.exp_add]
      ring_nf
    have hone : 1 ≤ Real.exp (2 * trunc K t) := Real.one_le_exp (by linarith)
    nlinarith
  · obtain ⟨h0, h1⟩ := trunc_mem_Icc_of_nonpos hK ht
    have hle := Real.add_one_le_exp (2 * (t - trunc K t))
    have hexp : Real.exp (2 * t) = Real.exp (2 * trunc K t) * Real.exp (2 * (t - trunc K t)) := by
      rw [← Real.exp_add]
      ring_nf
    have hle1 : Real.exp (2 * trunc K t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hpos := Real.exp_pos (2 * trunc K t)
    nlinarith

/-- `|exp (2s) - 1| ≤ 2 |s| exp (2M)` for `s ≤ M` with `0 ≤ M`. -/
private theorem abs_exp_two_mul_sub_one_le {M s : ℝ} (hM : 0 ≤ M) (hs : s ≤ M) :
    |Real.exp (2 * s) - 1| ≤ 2 * |s| * Real.exp (2 * M) := by
  have hexpM : 1 ≤ Real.exp (2 * M) := Real.one_le_exp (by linarith)
  rcases le_total 0 s with h | h
  · have h1 := Real.add_one_le_exp (-(2 * s))
    have h2 : Real.exp (2 * s) * Real.exp (-(2 * s)) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (2 * s) ≤ Real.exp (2 * M) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * s)]), abs_of_nonneg h]
    nlinarith [Real.exp_pos (2 * s)]
  · have h1 := Real.add_one_le_exp (2 * s)
    rw [abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 (by linarith : 2 * s ≤ 0)]),
      abs_of_nonpos h]
    nlinarith

/-- The potential integrand is locally Lipschitz with linear constant below a fixed level:
`|Φ(a) - Φ(b)| ≤ 4 exp (2M) (|a| + |b|) |a - b|` for `a, b ≤ M`. -/
private theorem abs_exp_sub_exp_sub_le {M a b : ℝ} (hM : 0 ≤ M) (ha : a ≤ M) (hb : b ≤ M) :
    |(Real.exp (2 * a) - 1 - 2 * a) - (Real.exp (2 * b) - 1 - 2 * b)| ≤
      4 * Real.exp (2 * M) * (|a| + |b|) * |a - b| := by
  have hderiv (x : ℝ) : HasDerivWithinAt (fun s ↦ Real.exp (2 * s) - 1 - 2 * s)
      (2 * (Real.exp (2 * x) - 1)) (uIcc b a) x := by
    have h1 : HasDerivAt (fun s ↦ Real.exp (2 * s)) (Real.exp (2 * x) * 2) x := by
      simpa using ((hasDerivAt_id x).const_mul 2).exp
    have h2 : HasDerivAt (fun s : ℝ ↦ 2 * s) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    refine (((h1.sub_const 1).sub h2).congr_deriv ?_).hasDerivWithinAt
    ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := uIcc b a)
    (x := b) (y := a) (C := 4 * Real.exp (2 * M) * (|a| + |b|)) (fun x _ ↦ hderiv x)
    (fun x hx ↦ ?_) (convex_uIcc b a) left_mem_uIcc right_mem_uIcc
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs, abs_mul, abs_two]
    have ha' := neg_abs_le a
    have hb' := neg_abs_le b
    have ha'' := le_abs_self a
    have hb'' := le_abs_self b
    have hxM : x ≤ M ∧ |x| ≤ |a| + |b| := by
      rcases mem_uIcc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact ⟨by linarith, abs_le.2 ⟨by linarith, by linarith⟩⟩
    have h := abs_exp_two_mul_sub_one_le hM hxM.1
    have h' := mul_le_mul_of_nonneg_right hxM.2 (Real.exp_pos (2 * M)).le
    nlinarith

/-! ### Convergence of the truncated terms -/

/-- The bound `|h Φ(θ_K s) - h Φ(θ_K t)| ≤ 4 exp (K π) (|s| + |t|) |s - t|` on the truncated
potential integrand, `Φ(t) = exp (2t) - 1 - 2t`. -/
private theorem abs_weight_mul_exp_trunc_sub_le {K : ℝ} (hK : 0 < K) (z : ℂ) (s t : ℝ) :
    |‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * trunc K s) - 1 - 2 * trunc K s) -
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * trunc K t) - 1 - 2 * trunc K t)| ≤
      4 * Real.exp (2 * (K * (Real.pi / 2))) * (|s| + |t|) * |s - t| := by
  have hM : 0 ≤ K * (Real.pi / 2) := by positivity
  have h := abs_exp_sub_exp_sub_le hM (trunc_le hK s) (trunc_le hK t)
  have hst : (|trunc K s| + |trunc K t|) * |trunc K s - trunc K t| ≤ (|s| + |t|) * |s - t| :=
    mul_le_mul (add_le_add (abs_trunc_le hK s) (abs_trunc_le hK t)) (abs_trunc_sub_le hK s t)
      (abs_nonneg _) (by positivity)
  rw [← mul_sub, abs_mul, abs_of_nonneg (weight_nonneg P z)]
  calc _ ≤ 1 * (4 * Real.exp (2 * (K * (Real.pi / 2))) * (|trunc K s| + |trunc K t|) *
        |trunc K s - trunc K t|) :=
        mul_le_mul (weight_le_one P z) h (abs_nonneg _) zero_le_one
    _ ≤ _ := by
        rw [one_mul, mul_assoc, mul_assoc (4 * _)]
        exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hst) (by positivity)

/-- On square integrable functions the truncated potential is integrable. -/
private theorem integrable_weight_mul_exp_trunc {K : ℝ} (hK : 0 < K) {a : ℂ → ℝ}
    (ha : MemLp a 2) :
    Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * trunc K (a z)) - 1 - 2 * trunc K (a z))) := by
  refine Integrable.mono' ((ha.integrable_sq).const_mul
    (4 * Real.exp (2 * (K * (Real.pi / 2))))) ?_ (Eventually.of_forall fun z ↦ ?_)
  · have hθ : Continuous (trunc K) := (contDiff_trunc K (n := 0)).continuous
    have hcont : Continuous (fun x : ℂ × ℝ ↦ ‖P.eval x.1‖ ^ 2 / (1 + ‖P.eval x.1‖ ^ 2) *
        (Real.exp (2 * trunc K x.2) - 1 - 2 * trunc K x.2)) := by
      fun_prop (disch := intro x; positivity)
    exact hcont.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk ha.aestronglyMeasurable)
  · have h := abs_weight_mul_exp_trunc_sub_le (P := P) hK z (a z) 0
    simp only [trunc_zero, mul_zero, Real.exp_zero, sub_self, sub_zero, abs_zero, add_zero] at h
    rw [Real.norm_eq_abs]
    calc _ ≤ 4 * Real.exp (2 * (K * (Real.pi / 2))) * |a z| * |a z| := h
      _ = _ := by rw [mul_assoc, ← sq, sq_abs]

/-- Truncated functions of square integrable functions are square integrable. -/
private theorem memLp_trunc_comp {K : ℝ} (hK : 0 < K) {a : ℂ → ℝ} (ha : MemLp a 2) :
    MemLp (fun z ↦ trunc K (a z)) 2 :=
  ha.of_le
    ((contDiff_trunc K (n := 0)).continuous.comp_aestronglyMeasurable ha.aestronglyMeasurable)
    (Eventually.of_forall fun z ↦ by
      simpa only [Real.norm_eq_abs] using abs_trunc_le hK (a z))

/-- **Continuity of the truncated potential in `L²`.** -/
private theorem tendsto_integral_weight_mul_exp_trunc {K : ℝ} (hK : 0 < K) {a : ℕ → ℂ → ℝ}
    {b : ℂ → ℝ} (ha : ∀ n, MemLp (a n) 2) (hb : MemLp b 2)
    (hab : Tendsto (fun n ↦ ∫ z, (a n z - b z) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * trunc K (a n z)) - 1 - 2 * trunc K (a n z))) atTop
      (𝓝 (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * trunc K (b z)) - 1 - 2 * trunc K (b z)))) := by
  set C := 4 * Real.exp (2 * (K * (Real.pi / 2)))
  have hk (n : ℕ) : MemLp (fun z ↦ C * (|a n z| + |b z|)) 2 :=
    (((ha n).abs).add hb.abs).const_mul C
  refine tendsto_integral_of_abs_sub_le_mul_abs_sub
    (fun n ↦ integrable_weight_mul_exp_trunc hK (ha n)) (integrable_weight_mul_exp_trunc hK hb)
    hk ha hb (M := 2 * C ^ 2 * (2 + 3 * ∫ z, b z ^ 2))
    ?_ hab fun n z ↦ abs_weight_mul_exp_trunc_sub_le hK z (a n z) (b z)
  filter_upwards [hab.eventually (ge_mem_nhds zero_lt_one)] with n hn
  have hsub : Integrable (fun z ↦ (a n z - b z) ^ 2) := ((ha n).sub hb).integrable_sq
  calc ∫ z, (C * (|a n z| + |b z|)) ^ 2
      ≤ ∫ z, 2 * C ^ 2 * (2 * (a n z - b z) ^ 2 + 3 * b z ^ 2) := by
        refine integral_mono (hk n).integrable_sq
          (((hsub.const_mul 2).add (hb.integrable_sq.const_mul 3)).const_mul _) fun z ↦ ?_
        nlinarith [sq_nonneg (|a n z| - |b z|), sq_abs (a n z), sq_abs (b z),
          sq_nonneg (a n z - 2 * b z), sq_nonneg C]
    _ = 2 * C ^ 2 * (2 * (∫ z, (a n z - b z) ^ 2) + 3 * ∫ z, b z ^ 2) := by
        rw [integral_const_mul, integral_add (hsub.const_mul 2) (hb.integrable_sq.const_mul 3),
          integral_const_mul, integral_const_mul]
    _ ≤ _ := by gcongr; linarith

/-- **Continuity of the truncated linear term in `L²`.** -/
private theorem tendsto_integral_coeff_mul_trunc (hm : 0 < P.natDegree) {K : ℝ} (hK : 0 < K)
    {a : ℕ → ℂ → ℝ} {b : ℂ → ℝ} (ha : ∀ n, MemLp (a n) 2) (hb : MemLp b 2)
    (hab : Tendsto (fun n ↦ ∫ z, (a n z - b z) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * trunc K (a n z)) atTop
      (𝓝 (∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * trunc K (b z))) := by
  have hc := memLp_reducedFunctional_coeff hm
  refine tendsto_integral_of_abs_sub_le_mul_abs_sub
    (fun n ↦ hc.integrable_mul (memLp_trunc_comp hK (ha n)))
    (hc.integrable_mul (memLp_trunc_comp hK hb)) (fun _ ↦ hc.abs) ha hb
    (Eventually.of_forall fun n ↦ le_of_eq (integral_congr_ae (Eventually.of_forall fun z ↦
      sq_abs _))) hab fun n z ↦ ?_
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_trunc_sub_le hK _ _) (abs_nonneg _)

/-- For each `ε > 0` some truncation changes the linear term by less than `ε`. -/
private theorem exists_integral_coeff_mul_trunc_lt (hm : 0 < P.natDegree) {b : ℂ → ℝ}
    (hb : MemLp b 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * trunc K (b z) <
      (∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * b z) + ε := by
  have hc := memLp_reducedFunctional_coeff hm
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * trunc ((n : ℝ) + 1) (b z))
    (fun z ↦ ‖(2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * b z‖)
    (fun n ↦ (hc.integrable_mul (memLp_trunc_comp (by positivity) hb)).aestronglyMeasurable)
    (hc.integrable_mul hb).norm
    (fun n ↦ Eventually.of_forall fun z ↦ by
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_trunc_le (by positivity) _) (abs_nonneg _))
    (Eventually.of_forall fun z ↦ (tendsto_trunc (b z)).const_mul _)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))).exists
  exact ⟨(n : ℝ) + 1, by positivity, hn⟩

/-- Truncation decreases the Dirichlet energy. -/
private theorem integral_norm_fderiv_trunc_comp_sq_le {K : ℝ} (hK : 0 < K) {g : ℂ → ℝ}
    (hg : ContDiff ℝ 1 g) (hgs : HasCompactSupport g) :
    ∫ z, ‖fderiv ℝ (fun z ↦ trunc K (g z)) z‖ ^ 2 ≤ ∫ z, ‖fderiv ℝ g z‖ ^ 2 := by
  have htg : ContDiff ℝ 1 (fun z ↦ trunc K (g z)) := (contDiff_trunc K).comp hg
  have htgs : HasCompactSupport (fun z ↦ trunc K (g z)) := hgs.comp_left (trunc_zero K)
  have hint (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f) :
      Integrable (fun z ↦ ‖fderiv ℝ f z‖ ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop (disch := exact one_ne_zero))
      ((hfs.fderiv ℝ).comp_left (g := fun x : ℂ →L[ℝ] ℝ ↦ ‖x‖ ^ 2) (by simp))
  refine integral_mono (hint _ htg htgs) (hint g hg hgs) fun z ↦ ?_
  have hd : HasFDerivAt (fun z ↦ trunc K (g z)) ((1 + (g z / K) ^ 2)⁻¹ • fderiv ℝ g z) z :=
    (hasDerivAt_trunc hK (g z)).comp_hasFDerivAt z ((hg.differentiable one_ne_zero) z).hasFDerivAt
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : (1 + (g z / K) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (g z / K)])
  have h0 : 0 ≤ (1 + (g z / K) ^ 2)⁻¹ := by positivity
  gcongr
  exact (mul_le_of_le_one_left (norm_nonneg _) h1)

/-- The truncated potential is at most the potential. -/
private theorem integral_weight_mul_exp_trunc_le {K : ℝ} (hK : 0 < K) {b : ℂ → ℝ}
    (hb : MemLp b 2) (hfin : ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * b z) - 1 - 2 * b z)) ≠ ⊤) :
    ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * trunc K (b z)) - 1 - 2 * trunc K (b z)) ≤
      (∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * b z) - 1 - 2 * b z))).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z ↦
    mul_nonneg (weight_nonneg P z) (exp_two_mul_sub_one_sub_nonneg _))
    (integrable_weight_mul_exp_trunc hK hb).aestronglyMeasurable]
  refine ENNReal.toReal_mono hfin (lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (exp_trunc_le hK _) (weight_nonneg P z)

/-! ### Approximation by test functions -/

/-- **Approximation from above.** Every real number above the value of Taubes's functional at
`u ∈ W^{1,2}(ℂ)` lies above its value at some smooth compactly supported function. In particular
the infimum of `TauCeti.Vortex.reducedFunctional P` over compactly supported `C¹` functions is
at most `sobolevReducedFunctional P u`. -/
theorem exists_reducedFunctional_lt_of_sobolevReducedFunctional_lt (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2} {t : ℝ} (hu : sobolevReducedFunctional P u < t) :
    ∃ w : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧ HasCompactSupport w ∧ reducedFunctional P w < t := by
  have hfin : sobolevReducedPotential P u ≠ ⊤ := by
    intro htop
    rw [sobolevReducedFunctional_def, htop, ENNReal.top_div_of_ne_top (by norm_num),
      EReal.coe_ennreal_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at hu
    exact not_top_lt hu
  have hf := memLp_value u
  -- The real form `A + L + Q / 16 < t` of the hypothesis.
  have hreal : ‖W1p.gradient u‖ ^ 2 / 2 + (∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 /
      (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) +
      (sobolevReducedPotential P u).toReal / 16 < t := by
    have hQ : ((sobolevReducedPotential P u / 16 : ℝ≥0∞) : EReal) =
        (((sobolevReducedPotential P u).toReal / 16 : ℝ) : EReal) := by
      rw [← ENNReal.ofReal_toReal (ENNReal.div_ne_top hfin (by norm_num)),
        EReal.coe_ennreal_ofReal, ENNReal.toReal_div, max_eq_left (by positivity)]
      norm_num
    rwa [sobolevReducedFunctional_def, hQ, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hu
  obtain ⟨K, hK, hKlt⟩ := exists_integral_coeff_mul_trunc_lt hm hf
    (half_pos (sub_pos.2 hreal))
  -- A sequence of test functions converging to `u` in `W^{1,2}(ℂ)`.
  obtain ⟨v, hv_mem, hv_lim⟩ := mem_closure_iff_seq_limit.1
    (W1p.denseRange_ofTestFunctionₗ_top (mu := (volume : Measure ℂ)) (p := 2)
      ENNReal.ofNat_ne_top u)
  choose φ hφ using hv_mem
  have hgv (n : ℕ) : W1p.value (v n) =ᵐ[volume] φ n := by
    rw [← hφ n]
    exact ae_restrict_top_iff.1 (W1p.value_ofTestFunctionₗ_ae (φ n))
  have hgg (n : ℕ) : W1p.gradient (v n) =ᵐ[volume] ∇ (φ n) := by
    rw [← hφ n, W1p.gradient_ofTestFunctionₗ]
    exact ae_restrict_top_iff.1 (gradientTestFunctionLp_apply_ae 2 (φ n))
  have hφL (n : ℕ) : MemLp (φ n : ℂ → ℝ) 2 :=
    (φ n).continuous.memLp_of_hasCompactSupport (φ n).hasCompactSupport
  obtain ⟨hval, hgrad⟩ := W1p.tendsto_iff_value_gradient.1 hv_lim
  have hconv : Tendsto (fun n ↦ ∫ z, (φ n z - W1p.value u z) ^ 2) atTop (𝓝 0) := by
    simp only [integral_sub_value_sq_eq (hgv _)]
    simpa using ((hval.sub_const (W1p.value u)).norm.pow 2)
  -- The truncated terms converge.
  have hB := ((hgrad.norm.pow 2).div_const 2).add
    (((tendsto_integral_weight_mul_exp_trunc (P := P) hK hφL hf hconv).div_const 16).add
      (tendsto_integral_coeff_mul_trunc hm hK hφL hf hconv))
  have hpot : _ ≤ (sobolevReducedPotential P u).toReal :=
    integral_weight_mul_exp_trunc_le (P := P) hK hf hfin
  obtain ⟨n, hn⟩ := (hB.eventually_lt_const (show _ < t by linarith)).exists
  refine ⟨fun z ↦ trunc K (φ n z), (contDiff_trunc K).comp (φ n).contDiff,
    (φ n).hasCompactSupport.comp_left (trunc_zero K), ?_⟩
  have hD := integral_norm_fderiv_trunc_comp_sq_le hK
    ((φ n).contDiff.of_le (by exact_mod_cast le_top)) (φ n).hasCompactSupport
  rw [integral_norm_fderiv_sq_eq (hgg n)] at hD
  rw [reducedFunctional_def]
  linarith

/-! ### Existence of a minimizer -/

/-- The linear term of Taubes's functional as a continuous linear functional on `W^{1,2}(ℂ)`. -/
private theorem exists_strongDual_eq_integral (hm : 0 < P.natDegree) :
    ∃ Λ : StrongDual ℝ (W1p (volume : Measure ℂ) ⊤ 2), ∀ v, Λ v =
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z := by
  have hc := (memLp_reducedFunctional_coeff hm).restrict ((⊤ : Opens ℂ) : Set ℂ)
  refine ⟨(innerSL ℝ hc.toLp).comp W1p.valueL, fun v ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.valueL_apply, L2.inner_def,
    integral_restrict_top]
  refine integral_congr_ae (ae_restrict_top_iff.1 (hc.coeFn_toLp.mono fun z hz ↦ ?_))
  simp only [hz, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Weak lower semicontinuity of the Dirichlet energy on `W^{1,2}(ℂ)`. -/
private theorem norm_gradient_le_of_tendsto_weak {U : ℕ → W1p (volume : Measure ℂ) ⊤ 2}
    {w : W1p (volume : Measure ℂ) ⊤ 2} {A : ℝ}
    (hlim : Tendsto (fun n ↦ toWeakSpace ℝ _ (U n)) atTop (𝓝 (toWeakSpace ℝ _ w)))
    (hA : Tendsto (fun n ↦ ‖W1p.gradient (U n)‖) atTop (𝓝 A)) :
    ‖W1p.gradient w‖ ≤ A := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set s : Set (W1p (volume : Measure ℂ) ⊤ 2) :=
    W1p.gradientL ⁻¹' Metric.closedBall 0 (A + ε)
  have hs : Convex ℝ s :=
    (convex_closedBall _ _).is_linear_preimage W1p.gradientL.toLinearMap.isLinear
  have hsc : IsClosed s := Metric.isClosed_closedBall.preimage W1p.gradientL.continuous
  have hws : IsClosed (toWeakSpace ℝ _ '' s) := by
    rw [← closure_eq_iff_isClosed, ← hs.toWeakSpace_closure ℝ, hsc.closure_eq]
  have hmem := hws.mem_of_tendsto hlim ((hA.eventually_lt_const (lt_add_of_pos_right A hε)).mono
    fun n hn ↦ mem_image_of_mem _ (by
      simpa only [s, mem_preimage, mem_closedBall_zero_iff, W1p.gradientL_apply] using hn.le))
  obtain ⟨v, hv, hvw⟩ := hmem
  rw [(toWeakSpace ℝ _).injective hvw] at hv
  simpa only [s, mem_preimage, mem_closedBall_zero_iff, W1p.gradientL_apply] using hv

/-- Weak lower semicontinuity of the potential on `W^{1,2}(ℂ)`. -/
private theorem sobolevReducedPotential_le_of_tendsto_weak
    {U : ℕ → W1p (volume : Measure ℂ) ⊤ 2} {w : W1p (volume : Measure ℂ) ⊤ 2} {b : ℕ → ℝ}
    {B : ℝ} (hlim : Tendsto (fun n ↦ toWeakSpace ℝ _ (U n)) atTop (𝓝 (toWeakSpace ℝ _ w)))
    (hb : Tendsto b atTop (𝓝 B))
    (hU : ∀ n, sobolevReducedPotential P (U n) = ENNReal.ofReal (b n)) :
    sobolevReducedPotential P w ≤ ENNReal.ofReal B := by
  have hlsc0 : ∀ μ : Measure ℂ, μ = volume → LowerSemicontinuous
      (fun u : WeakSpace ℝ (Lp ℝ 2 μ) ↦ ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 /
        (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm u z)) - 1 -
          2 * ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm u z))) ∂μ) := by
    rintro μ rfl
    exact lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub P
  have hlsc := (hlsc0 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))
    (by simp)).comp (WeakSpace.map W1p.valueL).continuous
  have heq (v : W1p (volume : Measure ℂ) ⊤ 2) :
      ((fun u : WeakSpace ℝ (Lp ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))) ↦
        ∫⁻ z in ((⊤ : Opens ℂ) : Set ℂ), ENNReal.ofReal (‖P.eval z‖ ^ 2 /
          (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * ((toWeakSpace ℝ _).symm u z)) - 1 -
            2 * ((toWeakSpace ℝ _).symm u z)))) ∘ WeakSpace.map W1p.valueL) (toWeakSpace ℝ _ v) =
        sobolevReducedPotential P v := by
    have hval : (toWeakSpace ℝ _).symm (WeakSpace.map W1p.valueL (toWeakSpace ℝ _ v)) =
        W1p.value v := by
      rw [← W1p.valueL_apply]
      rfl
    simp only [Function.comp_apply, hval, lintegral_restrict_top, sobolevReducedPotential_def]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hmem := (hlsc.isClosed_preimage (ENNReal.ofReal (B + ε))).mem_of_tendsto hlim
    ((hb.eventually_lt_const (lt_add_of_pos_right B (by exact_mod_cast hε))).mono fun n hn ↦ by
      rw [mem_preimage, heq, mem_Iic, hU]
      exact ENNReal.ofReal_le_ofReal hn.le)
  rw [mem_preimage, heq, mem_Iic] at hmem
  exact hmem.trans (ENNReal.ofReal_add_le.trans_eq (by rw [ENNReal.ofReal_coe_nnreal]))

/-- A minimizing sequence: a lower bound `m` of `reducedFunctional P` on compactly supported `C¹`
functions which is the limit of its values along a sequence of such functions. -/
private theorem exists_tendsto_reducedFunctional_of_le (hm : 0 < P.natDegree) :
    ∃ m : ℝ, (∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → m ≤ reducedFunctional P w) ∧
      ∃ w : ℕ → ℂ → ℝ, (∀ n, ContDiff ℝ 1 (w n)) ∧ (∀ n, HasCompactSupport (w n)) ∧
        Tendsto (fun n ↦ reducedFunctional P (w n)) atTop (𝓝 m) := by
  set S : Set ℝ :=
    {r | ∃ w : ℂ → ℝ, ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ reducedFunctional P w = r}
  have hSb : BddBelow S := by
    obtain ⟨C, hC⟩ := exists_le_reducedFunctional hm
    exact ⟨C, by rintro _ ⟨w, hw, hws, rfl⟩; exact hC w hw hws⟩
  have hSn : S.Nonempty := ⟨_, 0, contDiff_const, HasCompactSupport.zero, rfl⟩
  have hseq (n : ℕ) : ∃ w : ℂ → ℝ, ContDiff ℝ 1 w ∧ HasCompactSupport w ∧
      reducedFunctional P w < sInf S + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨w, hw, hws, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt hSn (lt_add_of_pos_right (sInf S)
        (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    exact ⟨w, hw, hws, hlt⟩
  choose w hw hws hwm using hseq
  have hm_le (v : ℂ → ℝ) (hv : ContDiff ℝ 1 v) (hvs : HasCompactSupport v) :
      sInf S ≤ reducedFunctional P v := csInf_le hSb ⟨v, hv, hvs, rfl⟩
  refine ⟨sInf S, hm_le, w, hw, hws, tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds ?_ (fun n ↦ hm_le _ (hw n) (hws n)) fun n ↦ (hwm n).le⟩
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (sInf S)

/-- **Compactness.** A sequence of compactly supported `C¹` functions whose values of Taubes's
functional converge has Sobolev representatives with a subsequence that converges weakly in
`W^{1,2}(ℂ)` and along which the Dirichlet energies converge. -/
private theorem exists_subseq_tendsto_weak (hm : 0 < P.natDegree) {w : ℕ → ℂ → ℝ} {m : ℝ}
    (hw : ∀ n, ContDiff ℝ 1 (w n)) (hws : ∀ n, HasCompactSupport (w n))
    (htend : Tendsto (fun n ↦ reducedFunctional P (w n)) atTop (𝓝 m)) :
    ∃ (u : ℕ → W1p (volume : Measure ℂ) ⊤ 2) (u₀ : W1p (volume : Measure ℂ) ⊤ 2) (A : ℝ)
      (k : ℕ → ℕ), (∀ n, W1p.value (u n) =ᵐ[volume] w (k n)) ∧
      (∀ n, W1p.gradient (u n) =ᵐ[volume] ∇ (w (k n))) ∧ Tendsto k atTop atTop ∧
      Tendsto (fun n ↦ toWeakSpace ℝ _ (u n)) atTop (𝓝 (toWeakSpace ℝ _ u₀)) ∧
      Tendsto (fun n ↦ ‖W1p.gradient (u n)‖) atTop (𝓝 A) := by
  -- Sobolev representatives of the `w n`, eventually bounded in `W^{1,2}(ℂ)` by coercivity.
  obtain ⟨C, hC⟩ := exists_integral_le_of_reducedFunctional_le hm (m + 1)
  have hrep (n : ℕ) : ∃ v : W1p (volume : Measure ℂ) ⊤ 2,
      W1p.value v =ᵐ[volume] w n ∧ W1p.gradient v =ᵐ[volume] ∇ (w n) := by
    obtain ⟨v, hv, hg, -⟩ := W1p.exists_value_gradient_ae_eq_of_hasCompactSupport
      (mu := (volume : Measure ℂ)) (p := 2) (hw n) (hws n)
    exact ⟨v, hv, hg⟩
  choose u huv hug using hrep
  have hbd : ∀ᶠ n in atTop, ‖W1p.gradient (u n)‖ ^ 2 ≤ C ∧ ‖W1p.value (u n)‖ ^ 2 ≤ C := by
    filter_upwards [htend.eventually_le_const (lt_add_one m)] with n hn
    rw [← integral_norm_fderiv_sq_eq (hug n), ← integral_sq_eq_norm_value_sq (huv n)]
    exact hC _ (hw n) (hws n) hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbd
  -- Closed balls of the Hilbert space `W^{1,2}(ℂ)` are weakly compact.
  have hball (n : ℕ) : u (n + N) ∈ Metric.closedBall 0 √(2 * C) := by
    rw [mem_closedBall_zero_iff, ← abs_norm]
    refine Real.abs_le_sqrt ?_
    rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
    linarith [hN (n + N) (Nat.le_add_left N n)]
  have hK := isCompact_toWeakSpace_closedBall
    (surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := ℝ)
      (E := W1p (volume : Measure ℂ) ⊤ 2)) 0 √(2 * C)
  obtain ⟨u₀, ψ, hψ, hlim⟩ :=
    tendsto_subseq_toWeakSpace_of_isCompact_closure (by rwa [hK.isClosed.closure_eq]) hball
  obtain ⟨A, -, χ, hχ, hA⟩ := tendsto_subseq_of_bounded (x := fun n ↦ ‖W1p.gradient (u (ψ n + N))‖)
    (Metric.isBounded_Icc 0 √C) fun n ↦ ⟨norm_nonneg _, by
      rw [← abs_norm]
      exact Real.abs_le_sqrt (hN _ (Nat.le_add_left N _)).1⟩
  exact ⟨fun n ↦ u (ψ (χ n) + N), u₀, A, fun n ↦ ψ (χ n) + N, fun n ↦ huv _, fun n ↦ hug _,
    (tendsto_add_atTop_nat N).comp (hψ.comp hχ).tendsto_atTop, hlim.comp hχ.tendsto_atTop, hA⟩

/-- **The direct method.** The weak limit of a minimizing sequence has finite potential, and its
value of Taubes's functional is at most the limit of the values. -/
private theorem exists_sobolevReducedFunctional_le_of_tendsto (hm : 0 < P.natDegree)
    {w : ℕ → ℂ → ℝ} {m : ℝ} (hw : ∀ n, ContDiff ℝ 1 (w n)) (hws : ∀ n, HasCompactSupport (w n))
    (htend : Tendsto (fun n ↦ reducedFunctional P (w n)) atTop (𝓝 m)) :
    ∃ u₀ : W1p (volume : Measure ℂ) ⊤ 2, sobolevReducedPotential P u₀ ≠ ⊤ ∧
      sobolevReducedFunctional P u₀ ≤ m := by
  obtain ⟨u, u₀, A, k, huv, hug, hk, hlim, hA⟩ := exists_subseq_tendsto_weak hm hw hws htend
  -- The linear term converges weakly, hence so does the potential.
  obtain ⟨Λ, hΛ⟩ := exists_strongDual_eq_integral hm
  have hΛlim := tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hlim Λ
  obtain ⟨b, hb_def⟩ : ∃ b : ℕ → ℝ, b = fun n ↦ ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * w (k n) z) - 1 - 2 * w (k n) z) := ⟨_, rfl⟩
  have hsplit (n : ℕ) : reducedFunctional P (w (k n)) =
      ‖W1p.gradient (u n)‖ ^ 2 / 2 + b n / 16 + Λ (u n) := by
    rw [reducedFunctional_def, integral_norm_fderiv_sq_eq (hug _), hΛ, hb_def]
    congr 1
    exact integral_congr_ae ((huv n).mono fun z hz ↦ by simp only [hz])
  have hb : Tendsto b atTop (𝓝 (16 * (m - A ^ 2 / 2 - Λ u₀))) := by
    have h := (((htend.comp hk).sub ((hA.pow 2).div_const 2)).sub hΛlim).const_mul 16
    refine h.congr fun n ↦ ?_
    simp only [Function.comp_apply, hsplit]
    ring
  have hB : 0 ≤ 16 * (m - A ^ 2 / 2 - Λ u₀) :=
    ge_of_tendsto' hb fun n ↦ hb_def ▸ integral_nonneg fun z ↦
      mul_nonneg (weight_nonneg P z) (exp_two_mul_sub_one_sub_nonneg _)
  -- Weak lower semicontinuity of the Dirichlet energy and of the potential.
  have hgrad := norm_gradient_le_of_tendsto_weak hlim hA
  have hpot := sobolevReducedPotential_le_of_tendsto_weak hlim hb
    fun n ↦ by rw [hb_def]; exact sobolevReducedPotential_eq_ofReal (hw _) (hws _) (huv _)
  refine ⟨u₀, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpot, ?_⟩
  rw [sobolevReducedFunctional_def, ← hΛ]
  calc _ ≤ (((A ^ 2 / 2 + Λ u₀ : ℝ)) : EReal) +
        ((ENNReal.ofReal (16 * (m - A ^ 2 / 2 - Λ u₀)) / 16 : ℝ≥0∞) : EReal) := by
        gcongr
        exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (by gcongr)
    _ = m := by
        rw [ofReal_div_sixteen, EReal.coe_ennreal_ofReal, max_eq_left (by positivity),
          ← EReal.coe_add]
        congr 1
        ring

/-- **Existence of a minimizer of Taubes's functional.** For a complex polynomial `P` of degree
at least one, Taubes's functional `TauCeti.Vortex.sobolevReducedFunctional P` attains its minimum
on `W^{1,2}(ℂ)` at a function of finite potential. -/
theorem exists_forall_sobolevReducedFunctional_le (hm : 0 < P.natDegree) :
    ∃ w : W1p (volume : Measure ℂ) ⊤ 2, sobolevReducedPotential P w ≠ ⊤ ∧
      ∀ v, sobolevReducedFunctional P w ≤ sobolevReducedFunctional P v := by
  obtain ⟨m, hm_le, w, hw, hws, htend⟩ := exists_tendsto_reducedFunctional_of_le hm
  obtain ⟨u₀, hfin, hle⟩ := exists_sobolevReducedFunctional_le_of_tendsto hm hw hws htend
  refine ⟨u₀, hfin, fun v ↦ hle.trans (not_lt.1 fun hlt ↦ ?_)⟩
  obtain ⟨w', hw', hws', hlt'⟩ := exists_reducedFunctional_lt_of_sobolevReducedFunctional_lt hm hlt
  exact (hm_le w' (hw'.of_le (by exact_mod_cast le_top)) hws').not_gt hlt'

end TauCeti.Vortex
