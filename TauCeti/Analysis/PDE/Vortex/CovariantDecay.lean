/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Energy
public import Mathlib.Analysis.Calculus.Gradient.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.FDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Kato
import TauCeti.Analysis.InnerProductSpace.Laplacian.Liouville
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Exponential decay of the covariant derivative of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`, so `s = |α|² = 4 (p² + q²)`. For a vortex
on the whole plane with `|α| → 1` at infinity, the modulus defect `1 - |α|²` and the curvature
decay exponentially at every rate below `1 / 2` (`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`).
This file proves the same for the covariant derivative `d_a α`:

`‖d_a α (v)‖ ≤ K ‖v‖ exp (-c |z|)` for every `c < 1 / 2`

(`TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp`). As for the modulus defect, the
threshold `1 / 2` is the mass of the vacuum, the square root of the constant `1 / 4` in
`L₀* L₀ = -Δ + 1 / 4`. Together with the curvature, `d_a α` gives the gauge-invariant first
derivatives of the field; their decay is one input for normalizing a vortex into the affine
Sobolev space of framed fields.

The argument is gauge invariant. The holomorphicity rows `∂bar_a α = 0` give
`|α|² |d_a α|² = |∇ |α|²|² / 2` pointwise, including at the zeros of `α`
(`TauCeti.Vortex.normSq_mul_covariantDerivative_norm_sq_eq`). Off the zeros,
`u = log |α|²` satisfies the scalar equation `Δ u = (exp u - 1) / 4`
(`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`), so its gradient solves the linearized
equation `Δ (∇u) = (|α|² / 4) ∇u`. Hence:

* `|∇u|²` is subharmonic where `α ≠ 0`. It is also integrable near infinity, because there
  `|∇u|² ≤ 4 |d_a α|²` and the covariant kinetic energy is integrable
  (`TauCeti.Vortex.integrable_covariantDerivative_norm_sq`). The sub-mean-value inequality on unit
  balls then gives `|∇u| → 0` at infinity.
* By the Kato inequality the regularized norms `√(|∇u|² + δ) - √δ` are subsolutions of
  `-Δ + |α|² / 4`, and `|α|² / 4 > c²` outside a large disc. The exterior comparison principle
  bounds them by a multiple of `exp (-c |z|)` uniformly in `δ`, and letting `δ → 0`
  (`TauCeti.norm_le_mul_exp_of_laplacian_eq_smul`) gives
  `|∇ log |α|²| ≤ K exp (-c |z|)` for `c < 1 / 2`
  (`TauCeti.Vortex.exists_norm_gradient_log_normSq_le_mul_exp`).

Since `|d_a α|² = |α|² |∇u|² / 2 ≤ |∇u|² / 2` off the zeros, the covariant kinetic energy decays
at every rate below `1` (`TauCeti.Vortex.exists_covariantDerivative_norm_sq_le_mul_exp`).

These are decay estimates for gauge-invariant quantities of a classical vortex. They do not choose
a gauge, so they do not by themselves bound the connection or the derivatives of the section in a
winding gauge, nor higher derivatives of the field.

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
open scoped Gradient RealInnerProductSpace

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The holomorphicity rows `∂bar_a α = 0` determine the covariant derivative of the section by its
modulus: `|α|² |d_a α|² = |∇ |α|²|² / 2`. This also holds at the zeros of `α`, where both sides
vanish. Only first derivatives of the section are used, and none of the connection. -/
theorem normSq_mul_covariantDerivative_norm_sq_eq {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    4 * (x z 2 ^ 2 + x z 3 ^ 2) *
        (‖covariantDerivative x z 1‖ ^ 2 + ‖covariantDerivative x z I‖ ^ 2) =
      ‖∇ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ ^ 2 / 2 := by
  rw [← orthonormalBasisOneI.sum_sq_inner_left (∇ _ z), Fin.sum_univ_two, inner_gradient_left,
    inner_gradient_left]
  simp only [coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hsfun := funext (sectionValue_apply x)
  have hcastp := (ofRealCLM.hasFDerivAt.comp z hp.hasFDerivAt).fderiv
  have hcastq := (ofRealCLM.hasFDerivAt.comp z hq.hasFDerivAt).fderiv
  simp only [Function.comp_def, ofRealCLM_apply] at hcastp hcastq
  simp only [equation_apply_one, equation_apply_two] at h₁ h₂
  -- Solve the holomorphicity rows for the derivatives in the direction `i`.
  have hA : fderiv ℝ (fun w ↦ x w 3) z I =
      fderiv ℝ (fun w ↦ x w 2) z 1 - x z 0 * x z 3 - x z 1 * x z 2 := by linarith
  have hB : fderiv ℝ (fun w ↦ x w 2) z I =
      -(fderiv ℝ (fun w ↦ x w 3) z 1 + x z 0 * x z 2) + x z 1 * x z 3 := by linarith
  simp (disch := fun_prop) [covariantDerivative_apply, hsfun, Complex.sq_norm,
    Complex.normSq_apply, fderiv_fun_add, fderiv_fun_mul, fderiv_fun_pow, hcastp, hcastq, hA, hB]
  ring

/-- Off the zeros of the section, the covariant kinetic energy is `|α|² |∇ log |α|²|² / 2`. -/
private theorem covariantDerivative_norm_sq_eq {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hsol : equation x z = 0) (hα : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ‖covariantDerivative x z 1‖ ^ 2 + ‖covariantDerivative x z I‖ ^ 2 =
      4 * (x z 2 ^ 2 + x z 3 ^ 2) *
        ‖∇ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ^ 2 / 2 := by
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)
  have hs : DifferentiableAt ℝ s z := ((hp.pow 2).add (hq.pow 2)).const_mul 4
  have hid := normSq_mul_covariantDerivative_norm_sq_eq hp hq (by simp [hsol]) (by simp [hsol])
  have hlog : ‖∇ (fun w ↦ Real.log (s w)) z‖ = (s z)⁻¹ * ‖∇ s z‖ := by
    rw [TauCeti.norm_gradient_eq_norm_fderiv, TauCeti.norm_gradient_eq_norm_fderiv,
      (hs.hasFDerivAt.log hα.ne').fderiv, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hα)]
  have hs₀ : s z ≠ 0 := hα.ne'
  -- Both sides are in terms of `s = |α|²`; `change` only folds its definition.
  change _ = s z * ‖∇ (fun w ↦ Real.log (s w)) z‖ ^ 2 / 2
  change s z * _ = ‖∇ s z‖ ^ 2 / 2 at hid
  rw [hlog]
  field_simp
  linarith

/-- Off the zeros of the section of a vortex, the gradient of `u = log |α|²` is `C²` and solves
the linearization `Δ (∇u) = (|α|² / 4) ∇u` of the scalar equation `Δ u = (exp u - 1) / 4`. -/
private theorem contDiffAt_gradient_log_normSq_and_laplacian
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {z : ℂ} (hα : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    ContDiffAt ℝ 2 (∇ fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z ∧
      Δ (∇ fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z =
        (4 * (x z 2 ^ 2 + x z 3 ^ 2) / 4) •
          ∇ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z := by
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)
  have hs : ContDiff ℝ 3 s := contDiff_const.mul ((hp.pow 2).add (hq.pow 2))
  have hsd : DifferentiableAt ℝ s z := hs.differentiable (by norm_num) z
  have hu : ContDiffAt ℝ 3 (fun w ↦ Real.log (s w)) z := hs.contDiffAt.log hα.ne'
  refine ⟨hu.gradient_right (by norm_num), ?_⟩
  -- Near `z` the scalar equation `Δ log |α|² = (|α|² - 1) / 4` holds.
  have hΔ : Δ (fun w ↦ Real.log (s w)) =ᶠ[𝓝 z] fun w ↦ 4⁻¹ * (s w - 1) := by
    filter_upwards [hs.continuous.continuousAt.eventually (lt_mem_nhds hα)] with w hw
    have hw₀ : x w 2 ^ 2 + x w 3 ^ 2 ≠ 0 := fun h ↦ by
      simp only [s, h, mul_zero, lt_self_iff_false] at hw
    rw [laplacian_log_normSq_of_equation_eq_zero (hb₁ w) (hb₂ w)
      (hp.of_le (by norm_num)).contDiffAt (hq.of_le (by norm_num)).contDiffAt hw₀
      (.of_forall hsol)]
    ring
  have hD : fderiv ℝ (fun w ↦ 4⁻¹ * (s w - 1)) z =
      (s z / 4) • fderiv ℝ (fun w ↦ Real.log (s w)) z := by
    rw [(hsd.hasFDerivAt.log hα.ne').fderiv, smul_smul, div_mul_eq_mul_div,
      mul_inv_cancel₀ hα.ne', (HasFDerivAt.const_mul (hsd.hasFDerivAt.sub_const 1) 4⁻¹).fderiv]
    ext v
    simp [div_eq_inv_mul]
  rw [hu.laplacian_gradient, gradient, gradient, hΔ.fderiv_eq, hD, map_smulₛₗ, starRingEnd_apply,
    star_trivial]

/-- Where `|α|² > 1 / 2` outside a disc, `|∇ log |α|²|` tends to zero at infinity: its square is
subharmonic there and bounded by `4 |d_a α|²`, which is integrable. -/
private theorem tendsto_norm_gradient_log_normSq
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {R : ℝ}
    (hshalf : ∀ z, R ≤ ‖z‖ → 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :
    Tendsto (fun z ↦ ‖∇ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖) (cocompact ℂ)
      (𝓝 0) := by
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)
  set u : ℂ → ℝ := fun w ↦ Real.log (s w)
  have hp₂ : ContDiff ℝ 2 (fun w ↦ x w 2) := hp.of_le (by norm_num)
  have hq₂ : ContDiff ℝ 2 (fun w ↦ x w 3) := hq.of_le (by norm_num)
  have hspos : ∀ z, R ≤ ‖z‖ → 0 < s z := fun z hz ↦ by linarith [hshalf z hz]
  have hg : ∀ z, R ≤ ‖z‖ → ContDiffAt ℝ 2 (∇ u) z ∧ Δ (∇ u) z = (s z / 4) • ∇ u z :=
    fun z hz ↦ contDiffAt_gradient_log_normSq_and_laplacian hb₁ hb₂ hp hq hsol (hspos z hz)
  have hnormsq : Tendsto (fun z ↦ ‖∇ u z‖ ^ 2) (cocompact ℂ) (𝓝 0) := by
    have hS : MeasurableSet {z : ℂ | R < ‖z‖} := measurableSet_lt measurable_const measurable_norm
    have he := integrable_covariantDerivative_norm_sq volume hb₁ hb₂ hp₂ hq₂ hsol hlim
    refine tendsto_cocompact_of_integrableOn_of_laplacian_nonneg (μ := volume)
      (fun z hz ↦ (hg z hz.le).1.norm_sq ℝ) ?_ (fun z _ ↦ sq_nonneg _) fun z hz ↦ ?_
    · refine (he.integrableOn.const_mul 4).mono' ?_ ?_
      · exact ContinuousOn.aestronglyMeasurable (fun z hz ↦
          ((hg z (le_of_lt hz)).1.continuousAt.norm.pow 2).continuousWithinAt) hS
      · refine (ae_restrict_iff' hS).mpr (.of_forall fun z hz ↦ ?_)
        have hz' : R ≤ ‖z‖ := le_of_lt hz
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          covariantDerivative_norm_sq_eq (hp₂.differentiable (by norm_num) z)
            (hq₂.differentiable (by norm_num) z) (hsol z) (hspos z hz')]
        nlinarith [hshalf z hz', sq_nonneg ‖∇ u z‖]
    · rw [(hg z hz.le).1.laplacian_norm_sq orthonormalBasisOneI, (hg z hz.le).2, inner_smul_right,
        real_inner_self_eq_norm_sq]
      have := hspos z hz.le
      positivity
  simpa [Real.sqrt_sq (norm_nonneg _)] using hnormsq.sqrt

/-- The case `0 ≤ c` of `exists_norm_gradient_log_normSq_le_mul_exp`, with a nonnegative constant
and a radius beyond which `|α|² > 1 / 2`. -/
private theorem exists_norm_gradient_log_normSq_le_mul_exp_of_nonneg
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ R K, 0 ≤ K ∧ ∀ z, R ≤ ‖z‖ → 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) ∧
      ‖∇ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)
  set u : ℂ → ℝ := fun w ↦ Real.log (s w)
  -- Outside a disc of radius `R`, `|α|² > 4 c²` and `|α|² > 1 / 2`.
  have hthr : max (4 * c ^ 2) (1 / 2) < 1 := max_lt (by nlinarith) (by norm_num)
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hlim.eventually (lt_mem_nhds hthr))
  set R := max R₀ 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hsR : ∀ z, R ≤ ‖z‖ → max (4 * c ^ 2) (1 / 2) < s z :=
    fun z hz ↦ hR₀ ((le_max_left _ _).trans hz)
  have hshalf : ∀ z, R ≤ ‖z‖ → 1 / 2 < s z := fun z hz ↦ (le_max_right _ _).trans_lt (hsR z hz)
  have hspos : ∀ z, R ≤ ‖z‖ → 0 < s z := fun z hz ↦ by linarith [hshalf z hz]
  have hg : ∀ z, R ≤ ‖z‖ → ContDiffAt ℝ 2 (∇ u) z ∧ Δ (∇ u) z = (s z / 4) • ∇ u z :=
    fun z hz ↦ contDiffAt_gradient_log_normSq_and_laplacian hb₁ hb₂ hp hq hsol (hspos z hz)
  have hnorm := tendsto_norm_gradient_log_normSq hb₁ hb₂ hp hq hsol hlim hshalf
  -- A bound for `|∇u|` on the sphere of radius `R`.
  have hcont : ContinuousOn (∇ u) {z | R ≤ ‖z‖} := fun z hz ↦
    (hg z hz).1.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
    (hcont.mono fun z hz ↦ by simp [mem_sphere_zero_iff_norm.mp hz])
  -- The Kato decay estimate for `Δ (∇u) = (|α|² / 4) ∇u`, where `|α|² / 4 > c²`.
  refine ⟨R, max M 0 * Real.exp (c * R), by positivity, fun z hz ↦ ⟨hshalf z hz, ?_⟩⟩
  have hbound := norm_le_mul_exp_of_laplacian_eq_smul (k := fun w ↦ s w / 4) hR hc₀
    (le_max_right _ _) hcont (fun w hw ↦ (hg w hw.le).1) (fun w hw ↦ (hg w hw.le).2)
    (fun w hw ↦ by linarith [(le_max_left _ _).trans_lt (hsR w hw.le)])
    (fun w hw ↦ (hM w (mem_sphere_zero_iff_norm.mpr hw)).trans (le_max_left _ _))
    (tendsto_zero_iff_norm_tendsto_zero.mpr hnorm) hz
  rwa [exp_neg_mul_sub, ← mul_assoc] at hbound

/-- **Exponential decay of the gradient of `log |α|²` at a plane vortex.** Outside a disc, a vortex
on the whole plane whose section satisfies `|α| → 1` at infinity has
`|∇ log |α|²| ≤ K exp (-c |z|)`, for every rate `c < 1 / 2`. -/
theorem exists_norm_gradient_log_normSq_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ R K, ∀ z, R ≤ ‖z‖ →
      ‖∇ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨R, K, hK₀, hK⟩ := exists_norm_gradient_log_normSq_le_mul_exp_of_nonneg hb₁ hb₂ hp hq
    hsol hlim (le_max_right c 0) (max_lt hc (by norm_num))
  refine ⟨R, K, fun z hz ↦ (hK z hz).2.trans (mul_le_mul_of_nonneg_left ?_ hK₀)⟩
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg _)))

/-- **Exponential decay of the covariant kinetic energy of a plane vortex.** A vortex on the whole
plane whose section satisfies `|α| → 1` at infinity has
`|d_a α (1)|² + |d_a α (i)|² ≤ K exp (-c |z|)` for every rate `c < 1`. -/
theorem exists_covariantDerivative_norm_sq_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1) :
    ∃ K, ∀ z, ‖covariantDerivative x z 1‖ ^ 2 + ‖covariantDerivative x z I‖ ^ 2 ≤
      K * Real.exp (-(c * ‖z‖)) := by
  set e : ℂ → ℝ := fun z ↦ ‖covariantDerivative x z 1‖ ^ 2 + ‖covariantDerivative x z I‖ ^ 2
  have hp₂ : ContDiff ℝ 2 (fun w ↦ x w 2) := hp.of_le (by norm_num)
  have hq₂ : ContDiff ℝ 2 (fun w ↦ x w 3) := hq.of_le (by norm_num)
  set c' := max (c / 2) 0
  obtain ⟨R, K, hK₀, hK⟩ := exists_norm_gradient_log_normSq_le_mul_exp_of_nonneg hb₁ hb₂ hp hq
    hsol hlim (c := c') (le_max_right _ 0) (max_lt (by linarith) (by norm_num))
  -- The energy density is continuous, so a bound outside a disc extends to the whole plane.
  have hS : ContDiff ℝ 3 (sectionValue x) := by
    rw [funext (sectionValue_apply x)]
    exact contDiff_const.mul ((ofRealCLM.contDiff.comp hp).add
      ((ofRealCLM.contDiff.comp hq).mul contDiff_const))
  have hDcont (v : ℂ) := continuous_covariantDerivative hb₁.continuous hb₂.continuous
    (hS.of_le (by norm_num)) v
  have hecont : Continuous e := ((hDcont 1).norm.pow 2).add ((hDcont I).norm.pow 2)
  refine (TauCeti.exists_le_mul_exp_of_continuousOn_closedBall hecont.continuousOn (R := R)
    (K := K ^ 2 / 2) fun z hz ↦ ?_).imp fun _ h ↦ h.2
  -- Outside, `|d_a α|² = |α|² |∇u|² / 2 ≤ |∇u|² / 2` and `2 c' ≥ c`.
  obtain ⟨hhalf, hgrad⟩ := hK z hz
  have hs₁ := normSq_le_one_of_tendsto hb₁ hb₂ hp₂ hq₂ hsol hlim z
  have heq := covariantDerivative_norm_sq_eq (hp₂.differentiable (by norm_num) z)
    (hq₂.differentiable (by norm_num) z) (hsol z) (by linarith)
  have hexp : Real.exp (-(c' * ‖z‖)) ^ 2 ≤ Real.exp (-(c * ‖z‖)) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have : c ≤ 2 * c' := by linarith [le_max_left (c / 2) 0]
    push_cast
    nlinarith [norm_nonneg z]
  have hgrad₀ : 0 ≤ ‖∇ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ := norm_nonneg _
  calc e z = 4 * (x z 2 ^ 2 + x z 3 ^ 2) *
        ‖∇ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ^ 2 / 2 := heq
    _ ≤ (K * Real.exp (-(c' * ‖z‖))) ^ 2 / 2 := by
        gcongr
        calc _ ≤ 1 * ‖∇ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z‖ ^ 2 := by
              gcongr
          _ ≤ _ := by rw [one_mul]; gcongr
    _ = K ^ 2 / 2 * Real.exp (-(c' * ‖z‖)) ^ 2 := by ring
    _ ≤ K ^ 2 / 2 * Real.exp (-(c * ‖z‖)) := by gcongr

/-- **Exponential decay of the covariant derivative of a plane vortex.** A vortex on the whole
plane whose section satisfies `|α| → 1` at infinity has `|d_a α (v)| ≤ K |v| exp (-c |z|)` for every
rate `c < 1 / 2`. -/
theorem exists_norm_covariantDerivative_le_mul_exp
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 3 (fun w ↦ x w 2)) (hq : ContDiff ℝ 3 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ z v, ‖covariantDerivative x z v‖ ≤ K * ‖v‖ * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := exists_covariantDerivative_norm_sq_le_mul_exp hb₁ hb₂ hp hq hsol hlim
    (c := 2 * c) (by linarith)
  refine ⟨√K, fun z v ↦ ?_⟩
  set a := ‖covariantDerivative x z 1‖
  set b := ‖covariantDerivative x z I‖
  -- Cauchy–Schwarz in the frame `(1, i)`: `|d_a α (v)|² ≤ |v|² (a² + b²)`.
  have hv : ‖covariantDerivative x z v‖ ≤ |v.re| * a + |v.im| * b := by
    rw [covariantDerivative_eq_re_mul_add_im_mul]
    refine (norm_add_le _ _).trans_eq ?_
    simp [a, b]
  have hvn : ‖v‖ ^ 2 = |v.re| ^ 2 + |v.im| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sq_abs, sq_abs]
    ring
  have hexp : Real.exp (-(2 * c * ‖z‖)) = Real.exp (-(c * ‖z‖)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hsq : (|v.re| * a + |v.im| * b) ^ 2 ≤
      (‖v‖ * (√K * Real.exp (-(c * ‖z‖)))) ^ 2 := by
    have hK' := hK z
    rw [hexp] at hK'
    have hKnn : 0 ≤ K := by
      by_contra! h
      have : K * Real.exp (-(c * ‖z‖)) ^ 2 < 0 :=
        mul_neg_of_neg_of_pos h (by positivity)
      linarith [sq_nonneg a, sq_nonneg b]
    rw [mul_pow, mul_pow, Real.sq_sqrt hKnn, hvn]
    nlinarith [sq_nonneg (|v.re| * b - |v.im| * a), sq_nonneg |v.re|, sq_nonneg |v.im|]
  have hrhs : 0 ≤ ‖v‖ * (√K * Real.exp (-(c * ‖z‖))) := by positivity
  calc ‖covariantDerivative x z v‖ ≤ |v.re| * a + |v.im| * b := hv
    _ ≤ ‖v‖ * (√K * Real.exp (-(c * ‖z‖))) :=
        (pow_le_pow_iff_left₀ (by positivity) hrhs two_ne_zero).mp hsq
    _ = √K * ‖v‖ * Real.exp (-(c * ‖z‖)) := by ring

end TauCeti.Vortex
