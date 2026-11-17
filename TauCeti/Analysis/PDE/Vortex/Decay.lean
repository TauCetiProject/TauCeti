/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ScalarEquation
import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Exponential decay of the curvature of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)`, curvature `F_a = i (∂₁ b₂ - ∂₂ b₁) ds ∧ dt` and section
`α = 2 (p + i q)`, so `|α|² = 4 (p² + q²)`. The curvature equation of a vortex reads
`∂₁ b₂ - ∂₂ b₁ = -(1 - |α|²) / 8`, so the curvature is controlled by the modulus defect
`1 - |α|²`.

For a vortex on the whole plane with `|α| → 1` at infinity, the modulus defect decays
exponentially at every rate `c < 1 / 2`: there is `K` with `1 - |α(z)|² ≤ K exp (-c |z|)`. Here
`1 / 2` is the mass of the vacuum, the square root of the constant `1 / 4` in
`L₀* L₀ = -Δ + 1 / 4` (`TauCeti.Vortex.temperedVacuumAdjoint_temperedVacuumOperator`). The proof
applies the exterior comparison principle `TauCeti.le_mul_exp_of_sq_mul_le_laplacian` to
`u = -log |α|²`: off the zeros of `α` the scalar equation
`Δ log |α|² = (|α|² - 1) / 4` (`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`) gives
`Δ u = (1 - |α|²) / 4 ≥ (|α|² / 4) u`, and `|α|² / 4 ≥ c²` outside a large disc. Since
`0 ≤ 1 - |α|² ≤ u`, the bound passes to the modulus defect, hence to the curvature, which is
therefore integrable for every additive Haar measure on the plane. This is the curvature
integrability needed to state the flux identity `(2π)⁻¹ ∫ i F_a = m`.

## Main results

* `TauCeti.Vortex.neg_log_normSq_le_mul_exp_of_le_normSq`: the exterior bound
  `-log |α|² ≤ M exp (-c (|z| - R))`, with the radius `R` of a disc outside which `|α|² ≥ 4 c²`
  and a bound `M` on the circle of radius `R` as explicit inputs.
* `TauCeti.Vortex.one_sub_normSq_le_mul_exp_of_le_normSq`: the resulting bound
  `1 - |α|² ≤ K exp (-c |z|)` on the whole plane, with `K` explicit in `c` and the radius `R`.
* `TauCeti.Vortex.exists_forall_one_sub_normSq_le_mul_exp_of_le_normSq`: for every `c < 1 / 2`,
  one constant `K` serves every vortex with `|α|² ≥ δ` outside a fixed disc. Two applications of
  the previous bound give it: first at the rate `√δ / 2`, which forces `|α|² ≥ 4 c²` past a
  radius depending only on `δ`, `c` and the disc, then at the rate `c`.
* `TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`: `1 - |α|² ≤ K exp (-c |z|)` for every
  `c < 1 / 2`.
* `TauCeti.Vortex.exists_abs_curvature_le_mul_exp`: the same bound for the curvature coefficient
  `∂₁ b₂ - ∂₂ b₁`.
* `TauCeti.Vortex.integrable_one_sub_normSq`, `TauCeti.Vortex.integrable_curvature`: the modulus
  defect and the curvature are integrable.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory Topology InnerProductSpace Laplacian

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- At a point where `4 c² ≤ |α|² ≤ 1` and `α ≠ 0`, the logarithmic modulus defect
`u = -log |α|²` of a vortex satisfies `c² u ≤ Δ u`: the scalar equation gives
`Δ u = (1 - |α|²) / 4`, and `|α|² u ≤ 1 - |α|²`. -/
private theorem sq_mul_neg_log_normSq_le_laplacian
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {c : ℝ} {z : ℂ} (hc : 4 * c ^ 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (hpos : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (hle : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 1) :
    c ^ 2 * -Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) ≤
      Δ (fun w ↦ -Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z := by
  set t := 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  have hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := fun h ↦ by simp [t, h] at hpos
  have hΔ : Δ (fun w ↦ -Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z = (1 - t) / 4 := by
    rw [← Pi.neg_def, congrFun laplacian_neg z,
      Pi.neg_apply, laplacian_log_normSq_of_equation_eq_zero hp.contDiffAt hq.contDiffAt hα
        (Eventually.of_forall hsol)]
    ring
  have hu₀ : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos hpos.le hle)
  -- `t (-log t) ≤ 1 - t`, from `1 - t⁻¹ ≤ log t`.
  have hut : t * -Real.log t ≤ 1 - t := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hpos) hpos.le
    rw [mul_sub, mul_inv_cancel₀ hpos.ne', mul_one] at h
    linarith
  have : c ^ 2 * -Real.log t ≤ t / 4 * -Real.log t :=
    mul_le_mul_of_nonneg_right (by linarith) hu₀
  rw [hΔ]
  linarith

/-- **Exterior decay of the logarithmic modulus defect, with explicit constants.** Let `x` be a
vortex on the whole plane whose section satisfies `|α| → 1` at infinity. Suppose that outside the
disc of radius `R > 0` the squared modulus `s = |α|²` is positive and at least `4 c²`, with
`c ≥ 0`, and that `-log s ≤ M` on the circle of radius `R`. Then
`-log s(z) ≤ M exp (-c (|z| - R))` for `|z| ≥ R`. The constants are those of the hypotheses, so
the bound is uniform over every family of vortices satisfying them with the same `c`, `R`
and `M`. -/
theorem neg_log_normSq_le_mul_exp_of_le_normSq
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c R M : ℝ}
    (hR : 0 < R) (hc₀ : 0 ≤ c)
    (hsR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (hpos : ∀ z, R ≤ ‖z‖ → 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (hbdry : ∀ z, ‖z‖ = R → -Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) ≤ M) {z : ℂ}
    (hz : R ≤ ‖z‖) :
    -Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) ≤ M * Real.exp (-(c * (‖z‖ - R))) := by
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  have hs₁ : ∀ z, s z ≤ 1 := normSq_le_one_of_tendsto hp hq hsol hlim
  have hscd : ContDiff ℝ 2 s := contDiff_normSq hp hq
  -- The logarithmic defect `u = -log |α|²` is a subsolution of `-Δ + c²` outside the disc.
  set u : ℂ → ℝ := fun z ↦ -Real.log (s z) with hu
  have hucont : ContinuousOn u {z | R ≤ ‖z‖} := fun z hz ↦
    (hscd.continuous.continuousAt.log (hpos z hz).ne').neg.continuousWithinAt
  have hucd : ∀ z, R < ‖z‖ → ContDiffAt ℝ 2 u z := fun z hz ↦
    (hscd.contDiffAt.log (hpos z hz.le).ne').neg
  have hsub : ∀ z, R < ‖z‖ → c ^ 2 * u z ≤ Δ u z := fun z hz ↦
    sq_mul_neg_log_normSq_le_laplacian hp hq hsol (hsR z hz.le) (hpos z hz.le) (hs₁ z)
  have hulim : Tendsto u (cocompact ℂ) (𝓝 0) := by
    simpa [hu] using ((Real.continuousAt_log one_ne_zero).tendsto.comp hlim).neg
  -- `M ≥ u ≥ 0` at the point `R` of the circle, since `0 < |α|² ≤ 1` there.
  have hR' : ‖(R : ℂ)‖ = R := by simp [hR.le]
  have hM : 0 ≤ M := (neg_nonneg.mpr (Real.log_nonpos (hpos _ hR'.ge).le (hs₁ _))).trans
    (hbdry _ hR')
  exact TauCeti.le_mul_exp_of_sq_mul_le_laplacian hR hc₀ hM hucont hucd hsub hbdry hulim hz

/-- **Exterior decay of the modulus defect, with explicit constants.** Let `x` be a vortex on the
whole plane whose section satisfies `|α| → 1` at infinity, and suppose that `|α|² ≥ 4 c²`, with
`c > 0`, outside the disc of radius `R > 0`. Then at every point
`1 - |α(z)|² ≤ max (-log (4 c²)) 1 exp (c R) exp (-c |z|)`. -/
theorem one_sub_normSq_le_mul_exp_of_le_normSq
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c R : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hsR : ∀ z, R ≤ ‖z‖ → 4 * c ^ 2 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2))
    (z : ℂ) :
    1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤
      max (-Real.log (4 * c ^ 2)) 1 * Real.exp (c * R) * Real.exp (-(c * ‖z‖)) := by
  have hpos : ∀ z, R ≤ ‖z‖ → 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := fun z hz ↦
    (by positivity : 0 < 4 * c ^ 2).trans_le (hsR z hz)
  rcases le_or_gt R ‖z‖ with hz | hz
  · calc 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ -Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) := by
          linarith [Real.log_le_sub_one_of_pos (hpos z hz)]
      _ ≤ -Real.log (4 * c ^ 2) * Real.exp (-(c * (‖z‖ - R))) :=
          neg_log_normSq_le_mul_exp_of_le_normSq hp hq hsol hlim hR hc.le hsR hpos
            (fun w hw ↦ neg_le_neg (Real.log_le_log (by positivity) (hsR w hw.ge))) hz
      _ ≤ max (-Real.log (4 * c ^ 2)) 1 * Real.exp (-(c * (‖z‖ - R))) := by
          gcongr
          exact le_max_left _ _
      _ = _ := by rw [exp_neg_mul_sub, mul_assoc]
  · have hs0 : 0 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by positivity
    calc 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 1 * 1 := by linarith
      _ ≤ max (-Real.log (4 * c ^ 2)) 1 * Real.exp (c * R - c * ‖z‖) := by
          gcongr
          · exact le_max_right _ _
          · exact Real.one_le_exp (by nlinarith)
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, mul_assoc]

/-- **Uniform exponential decay of the modulus defect from an exterior lower bound.** Let `R` be
a radius, `δ > 0` and `c < 1 / 2`. There is a constant `K` such that every vortex `x` on the
whole plane with `C²` section, `|α| → 1` at infinity and `δ ≤ |α(z)|²` whenever `R ≤ |z|`
satisfies `1 - |α(z)|² ≤ K exp (-c |z|)` at every point. -/
theorem exists_forall_one_sub_normSq_le_mul_exp_of_le_normSq (R : ℝ) {δ c : ℝ} (hδ : 0 < δ)
    (hc : c < 1 / 2) :
    ∃ K, ∀ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 (fun w ↦ x w 2) →
      ContDiff ℝ 2 (fun w ↦ x w 3) → (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1) →
      (∀ z, R ≤ ‖z‖ → δ ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) →
      ∀ z, 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ K * Real.exp (-(c * ‖z‖)) := by
  -- First step: the rate `c₀ = √δ / 2` outside the disc of radius `R₀`.
  set R₀ := max R 0 + 1
  have hR₀0 : 0 < R₀ := by positivity
  set c₀ := √δ / 2
  have hc₀ : 0 < c₀ := by positivity
  have h4c₀ : 4 * c₀ ^ 2 = δ := by
    simp only [c₀, div_pow, Real.sq_sqrt hδ.le]
    ring
  set K₀ := max (-Real.log (4 * c₀ ^ 2)) 1 * Real.exp (c₀ * R₀)
  -- Past a radius `R₁`, the first bound forces `|α|² ≥ 4 c'²` for `c' = max c (1 / 4) < 1 / 2`.
  set c' := max c (1 / 4)
  have hc' : 0 < c' := lt_max_of_lt_right (by norm_num)
  have h4c' : 0 < 1 - 4 * c' ^ 2 := by nlinarith [max_lt hc (by norm_num : (1 / 4 : ℝ) < 1 / 2)]
  obtain ⟨R₁, hR₁, hK₀⟩ : ∃ R₁, 0 < R₁ ∧ K₀ * Real.exp (-(c₀ * R₁)) ≤ 1 - 4 * c' ^ 2 := by
    have h : Tendsto (fun T ↦ K₀ * Real.exp (-(c₀ * T))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hc₀)).const_mul K₀
    exact ((eventually_gt_atTop 0).and (h.eventually (ge_mem_nhds h4c'))).exists
  refine ⟨max (-Real.log (4 * c' ^ 2)) 1 * Real.exp (c' * R₁),
    fun x hp hq hsol hlim hδx z ↦ ?_⟩
  have hstep₁ := one_sub_normSq_le_mul_exp_of_le_normSq hp hq hsol hlim hR₀0 hc₀
    fun w hw ↦ h4c₀ ▸ hδx w ((le_max_left R 0).trans (by linarith))
  -- Second step: the rate `c'` outside the disc of radius `R₁`, and `c ≤ c'`.
  refine (one_sub_normSq_le_mul_exp_of_le_normSq hp hq hsol hlim hR₁ hc' (fun w hw ↦ ?_) z).trans
    ?_
  · have h := (hstep₁ w).trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_left hw hc₀.le))) (by positivity)).trans hK₀)
    linarith
  · gcongr
    exact le_max_left _ _

/-- **Exponential decay of the modulus defect of a plane vortex.** A vortex on the whole plane
whose section satisfies `|α| → 1` at infinity has `1 - |α(z)|² ≤ K exp (-c |z|)` for every rate
`c < 1 / 2`, with a constant `K` depending on `c`. -/
theorem exists_one_sub_normSq_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z, 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ K * Real.exp (-(c * ‖z‖)) := by
  -- Outside a disc of radius `R`, `|α|² ≥ 1 / 2`.
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸
      hlim.eventually (le_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  obtain ⟨K, hK⟩ := exists_forall_one_sub_normSq_le_mul_exp_of_le_normSq R
    (by norm_num : (0 : ℝ) < 1 / 2) hc
  exact ⟨K, hK x hp hq hsol hlim fun z hz ↦ hR hz⟩

/-- **Exponential decay of the curvature of a plane vortex.** A vortex on the whole plane whose
section satisfies `|α| → 1` at infinity has curvature coefficient bounded by `K exp (-c |z|)` for
every rate `c < 1 / 2`. -/
theorem exists_abs_curvature_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z, |fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I| ≤
      K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := exists_one_sub_normSq_le_mul_exp hp hq hsol hlim hc
  refine ⟨K / 8, fun z ↦ ?_⟩
  have h₀ : 0 ≤ 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
    linarith [normSq_le_one_of_tendsto hp hq hsol hlim z]
  rw [curvature_eq_of_equation_eq_zero (hsol z), abs_neg, abs_of_nonneg (by linarith)]
  linarith [hK z]

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure]

/-- The modulus defect `1 - |α|²` of a vortex on the whole plane with `|α| → 1` at infinity is
integrable. -/
theorem integrable_one_sub_normSq
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable (fun z ↦ 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) μ := by
  obtain ⟨K, hK⟩ := exists_one_sub_normSq_le_mul_exp hp hq hsol hlim
    (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  have hint : Integrable (fun z : ℂ ↦ K * Real.exp (-(1 / 4 * ‖z‖))) μ :=
    (integrable_exp_neg_mul_norm μ (by norm_num : (0 : ℝ) < 1 / 4)).const_mul K
  have hcont : Continuous fun z ↦ 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    continuous_const.sub (continuous_const.mul ((hp.continuous.pow 2).add (hq.continuous.pow 2)))
  refine hint.mono' hcont.aestronglyMeasurable (.of_forall fun z ↦ ?_)
  have h₁ := normSq_le_one_of_tendsto hp hq hsol hlim z
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  exact hK z

/-- **Integrability of the curvature of a plane vortex.** A vortex on the whole plane whose
section satisfies `|α| → 1` at infinity has integrable curvature coefficient `∂₁ b₂ - ∂₂ b₁`. -/
theorem integrable_curvature
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable (fun z ↦ fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) μ := by
  refine ((integrable_one_sub_normSq μ hp hq hsol hlim).div_const 8).neg.congr
    (.of_forall fun z ↦ ?_)
  exact (curvature_eq_of_equation_eq_zero (hsol z)).symm

end TauCeti.Vortex
