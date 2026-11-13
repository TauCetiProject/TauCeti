/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
public import TauCeti.Analysis.PDE.Vortex.ScalarEquation
public import TauCeti.Analysis.PDE.Vortex.Zeros
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Uniqueness of plane vortices with the same zeros

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`. Let `x` and `y` be solutions of the plane
vortex equation on the whole plane with `|α| → 1` at infinity, where the connections of `x` and
`y` are continuous and the sections of `y` are `C²`, and suppose that their sections differ by a
nowhere-vanishing `C²` factor, `α_x = h α_y` (so the sections of `x` are `C²` too), while the zero
set of `α_y` has empty interior. Then `x` is the phase gauge transform of `y` by a `C²` phase `f`
with `h = exp (i f)`
(`TauCeti.Vortex.exists_eq_phaseGauge_of_forall_section_eq_mul`).

The argument is Taubes's. Away from the zeros of `α_y`, the scalar equations
`Δ log |α|² = (|α|² - 1) / 4` of the two fields show that `w = log |h|²` satisfies

`Δ w = (p_y² + q_y²) (|h|² - 1)`

(`TauCeti.Vortex.laplacian_log_norm_sq_eq`), and by continuity this holds everywhere. Since `w`
and `|h|² - 1` have the same sign, `w Δ w ≥ 0`, and `w → 0` at infinity, so the Liouville form
of the weak maximum principle forces `w = 0`, that is `|h| = 1`
(`TauCeti.Vortex.norm_eq_one_of_forall_section_eq_mul`). A smooth logarithm of `h` supplies the
phase (`TauCeti.exists_contDiff_eq_exp_ofReal_mul_I`). Finally, wherever `α ≠ 0` the
holomorphicity equation `∂bar_a α = 0` determines the connection from the section
(`TauCeti.Vortex.eq_of_forall_section_eq`), which identifies `x` with the gauge transform of `y`.

The zeros enter through the factor `h`. If the sections of two fields satisfying the
holomorphicity rows `∂bar_a α = 0` have the same zeros with the same multiplicities, then such a
factor exists and is as regular as the connections
(`TauCeti.Vortex.exists_contDiff_sectionValue_eq_mul`). Multiplicities are expressed by a function
`n` such that each section factors near every `z` as `(w - z) ^ n z * v w`, with `v` continuous and
nonzero at `z`; the similarity principle upgrades the factor to a `Cᵏ` one with the same exponent
(`TauCeti.eq_of_eventually_sub_pow_mul_eq`). The factor of the quotient at a zero is the quotient
of the two factors there.

For `Cᵏ` vortices, `k ≥ 2`, with the same end framing `α (z) · phase (z) → 1`, where
`|phase| → 1` (for example the winding phase `(z / |z|) ^ (-m)`), the factor is a gauge tending
to one at infinity which carries one vortex to the other. Its logarithmic derivative is the
difference of the two connections, so the gauge is `C^(k+1)`
(`TauCeti.Vortex.exists_contDiff_gaugeTransform_eq`). For smooth vortices it is therefore an
element of the smooth framed gauge group. Since the framed gauge action is free, two smooth framed
vortices with the same zero multiplicities differ by exactly one framed gauge
(`TauCeti.Vortex.existsUnique_framedGaugeGroup_smul_eq`). This is uniqueness modulo the framed
gauge action for each effective divisor; existence of a vortex with prescribed zeros is not
addressed here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Topology InnerProductSpace Laplacian

/-- If the sections satisfy `α_x = h α_y` at `z`, then `p_x² + q_x² = |h|² (p_y² + q_y²)`. -/
private theorem sq_add_sq_eq_norm_sq_mul {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {h : ℂ → ℂ}
    {z : ℂ} (hα : (x z 2 + x z 3 * I : ℂ) = h z * (y z 2 + y z 3 * I)) :
    x z 2 ^ 2 + x z 3 ^ 2 = ‖h z‖ ^ 2 * (y z 2 ^ 2 + y z 3 ^ 2) := by
  have := congrArg normSq hα
  rw [normSq_mul, normSq_add_mul_I, normSq_add_mul_I] at this
  rw [this, Complex.sq_norm]

/-- **The scalar equation for the ratio of two vortex sections.** Let `x` and `y` solve the vortex
equation near `z`, with sections `C²` at `z`, and with sections
related by `α_x = h α_y` near `z` for a `C²` factor `h` with `h z ≠ 0`. If `α_y (z) ≠ 0`, then
`Δ log |h|² = (p_y² + q_y²) (|h|² - 1)` at `z`. -/
theorem laplacian_log_norm_sq_eq {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {h : ℂ → ℂ} {z : ℂ}
    (hyp : ContDiffAt ℝ 2 (fun w ↦ y w 2) z) (hyq : ContDiffAt ℝ 2 (fun w ↦ y w 3) z)
    (hxsol : ∀ᶠ w in 𝓝 z, equation x w = 0) (hysol : ∀ᶠ w in 𝓝 z, equation y w = 0)
    (hh : ContDiffAt ℝ 2 h z) (hhz : h z ≠ 0)
    (hα : ∀ᶠ w in 𝓝 z, (x w 2 + x w 3 * I : ℂ) = h w * (y w 2 + y w 3 * I))
    (hyz : y z 2 ^ 2 + y z 3 ^ 2 ≠ 0) :
    Δ (fun w ↦ Real.log (‖h w‖ ^ 2)) z = (y z 2 ^ 2 + y z 3 ^ 2) * (‖h z‖ ^ 2 - 1) := by
  -- The sections of `x` are `C²` at `z`, being the real and imaginary parts of `h α_y` near `z`.
  have hprod : ContDiffAt ℝ 2 (fun w ↦ h w * ((y w 2 : ℂ) + y w 3 * I)) z :=
    hh.mul ((Complex.ofRealCLM.contDiff.comp_contDiffAt z hyp).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffAt z hyq).mul contDiffAt_const))
  have hxp : ContDiffAt ℝ 2 (fun w ↦ x w 2) z :=
    (Complex.reCLM.contDiff.comp_contDiffAt z hprod).congr_of_eventuallyEq
      (by filter_upwards [hα] with w hw; simpa using congrArg re hw)
  have hxq : ContDiffAt ℝ 2 (fun w ↦ x w 3) z :=
    (Complex.imCLM.contDiff.comp_contDiffAt z hprod).congr_of_eventuallyEq
      (by filter_upwards [hα] with w hw; simpa using congrArg im hw)
  have hhz' : ‖h z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hhz)
  have hxz : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := by
    rw [sq_add_sq_eq_norm_sq_mul hα.self_of_nhds]
    exact mul_ne_zero hhz' hyz
  have hw : ContDiffAt ℝ 2 (fun w ↦ Real.log (‖h w‖ ^ 2)) z := (hh.norm_sq ℝ).log hhz'
  have hℓy : ContDiffAt ℝ 2 (fun w ↦ Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2))) z :=
    (contDiffAt_const.mul ((hyp.pow 2).add (hyq.pow 2))).log
      (mul_ne_zero four_ne_zero hyz)
  -- Near `z`, `log |α_x|² = log |h|² + log |α_y|²`.
  have hev : (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) =ᶠ[𝓝 z]
      (fun w ↦ Real.log (‖h w‖ ^ 2)) + fun w ↦ Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2)) := by
    have hy₀ : ∀ᶠ w in 𝓝 z, y w 2 ^ 2 + y w 3 ^ 2 ≠ 0 :=
      ((hyp.continuousAt.pow 2).add (hyq.continuousAt.pow 2)).eventually_ne hyz
    filter_upwards [hα, hh.continuousAt.eventually_ne hhz, hy₀] with w hαw hhw hyw
    rw [Pi.add_apply, sq_add_sq_eq_norm_sq_mul hαw, mul_left_comm,
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 hhw)) (mul_ne_zero four_ne_zero hyw)]
  have hΔ := (laplacian_congr_nhds hev).eq_of_nhds
  rw [hw.laplacian_add hℓy,
    laplacian_log_normSq_of_equation_eq_zero hxp hxq hxz hxsol,
    laplacian_log_normSq_of_equation_eq_zero hyp hyq hyz hysol,
    sq_add_sq_eq_norm_sq_mul hα.self_of_nhds] at hΔ
  linarith

/-- **Two vortices whose sections differ by a nonvanishing factor have sections of equal
modulus.** Let `x` and `y` be solutions of the vortex equation on the plane with `C²` sections
and `|α| → 1` at infinity, whose sections satisfy `α_x = h α_y` for a nowhere-vanishing `C²`
function `h`. If the zero set of `α_y` has empty interior, then `|h| = 1`
everywhere. -/
theorem norm_eq_one_of_forall_section_eq_mul {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {h : ℂ → ℂ}
    (hyp : ContDiff ℝ 2 (fun w ↦ y w 2)) (hyq : ContDiff ℝ 2 (fun w ↦ y w 3))
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hylim : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hh : ContDiff ℝ 2 h) (hh₀ : ∀ z, h z ≠ 0)
    (hα : ∀ z, (x z 2 + x z 3 * I : ℂ) = h z * (y z 2 + y z 3 * I))
    (hdense : Dense {z | y z 2 ^ 2 + y z 3 ^ 2 ≠ 0}) (z : ℂ) :
    ‖h z‖ = 1 := by
  have hh₀' (z : ℂ) : ‖h z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (hh₀ z))
  have hw : ContDiff ℝ 2 fun z ↦ Real.log (‖h z‖ ^ 2) := (hh.norm_sq ℝ).log hh₀'
  -- The scalar equation for `w = log |h|²` holds off the zeros of `α_y`, hence everywhere.
  have hΔ : Δ (fun z ↦ Real.log (‖h z‖ ^ 2)) =
      fun z ↦ (y z 2 ^ 2 + y z 3 ^ 2) * (‖h z‖ ^ 2 - 1) :=
    hw.continuous_laplacian.ext_on hdense
      (((hyp.continuous.pow 2).add (hyq.continuous.pow 2)).mul
        ((hh.continuous.norm.pow 2).sub continuous_const))
      fun z hz ↦ laplacian_log_norm_sq_eq hyp.contDiffAt hyq.contDiffAt (.of_forall hxsol)
        (.of_forall hysol) hh.contDiffAt (hh₀ z) (.of_forall hα) hz
  -- Since `log t` and `t - 1` have the same sign, `w Δ w ≥ 0`.
  have hsign (z : ℂ) : 0 ≤ Real.log (‖h z‖ ^ 2) * Δ (fun z ↦ Real.log (‖h z‖ ^ 2)) z := by
    have ht : 0 < ‖h z‖ ^ 2 := lt_of_le_of_ne (by positivity) (hh₀' z).symm
    rw [hΔ, mul_left_comm]
    refine mul_nonneg (by positivity) ?_
    rcases le_total 1 (‖h z‖ ^ 2) with h₁ | h₁
    · exact mul_nonneg (Real.log_nonneg h₁) (sub_nonneg.2 h₁)
    · exact mul_nonneg_of_nonpos_of_nonpos (Real.log_nonpos ht.le h₁) (sub_nonpos.2 h₁)
  -- At infinity `|h|² = |α_x|² / |α_y|² → 1`, so `w → 0`.
  have hlim : Tendsto (fun z ↦ Real.log (‖h z‖ ^ 2)) (cocompact ℂ) (𝓝 0) := by
    have hnorm : Tendsto (fun z ↦ ‖h z‖ ^ 2) (cocompact ℂ) (𝓝 1) := by
      have hdiv := hxlim.div hylim one_ne_zero
      rw [div_one] at hdiv
      refine hdiv.congr' ?_
      filter_upwards [hylim.eventually_ne one_ne_zero] with z hz
      rw [Pi.div_apply, div_eq_iff hz, sq_add_sq_eq_norm_sq_mul (hα z)]
      ring
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hnorm
    rwa [Real.log_one] at hlog
  have hw₀ := congrFun (eq_zero_of_tendsto_cocompact_of_mul_laplacian_nonneg hw hsign hlim) z
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
    (Real.eq_one_of_pos_of_log_eq_zero (lt_of_le_of_ne (by positivity) (hh₀' z).symm) hw₀)

/-- **Uniqueness of plane vortices with the same zeros, modulo gauge.** Let `x` and `y` be
solutions of the vortex equation on the plane with `|α| → 1` at infinity, where the connections of
`x` and `y` are continuous and the sections of `y` are `C²`, whose sections satisfy `α_x = h α_y`
for a nowhere-vanishing `C²` function `h` (so the sections of `x` are `C²` too, being the real and
imaginary parts of `h α_y`), and suppose the zero set of `α_y` has empty interior. Then
`h = exp (i f)` for a `C²` real phase `f`, and `x` is the phase gauge transform of `y` by `f`. The
holomorphicity rows of the gauge transform involve the connection only through its values, so no
differentiability of either connection is needed. -/
theorem exists_eq_phaseGauge_of_forall_section_eq_mul {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    {h : ℂ → ℂ}
    (hxb₁ : Continuous (fun w ↦ x w 0)) (hxb₂ : Continuous (fun w ↦ x w 1))
    (hyb₁ : Continuous (fun w ↦ y w 0)) (hyb₂ : Continuous (fun w ↦ y w 1))
    (hyp : ContDiff ℝ 2 (fun w ↦ y w 2)) (hyq : ContDiff ℝ 2 (fun w ↦ y w 3))
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hylim : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hh : ContDiff ℝ 2 h) (hh₀ : ∀ z, h z ≠ 0)
    (hα : ∀ z, (x z 2 + x z 3 * I : ℂ) = h z * (y z 2 + y z 3 * I))
    (hdense : Dense {z | y z 2 ^ 2 + y z 3 ^ 2 ≠ 0}) :
    ∃ f : ℂ → ℝ, ContDiff ℝ 2 f ∧ (∀ z, h z = exp (f z * I)) ∧ x = phaseGauge y f := by
  have hnorm := norm_eq_one_of_forall_section_eq_mul hyp hyq hxsol hysol
    hxlim hylim hh hh₀ hα hdense
  obtain ⟨f, hf, hhf⟩ := exists_contDiff_eq_exp_ofReal_mul_I hh hnorm
  refine ⟨f, hf, hhf, ?_⟩
  -- The gauge transform of `y` has the section of `x` and satisfies the holomorphicity rows.
  have hsec (z : ℂ) : x z 2 = phaseGauge y f z 2 ∧ x z 3 = phaseGauge y f z 3 := by
    have h₂ := congrArg re (hα z)
    have h₃ := congrArg im (hα z)
    simp only [hhf z, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] at h₂ h₃
    rw [phaseGauge_apply_two, phaseGauge_apply_three]
    constructor <;> linarith
  have hfd : Continuous fun z ↦ fderiv ℝ f z := hf.continuous_fderiv two_ne_zero
  refine eq_of_forall_section_eq hxb₁ hxb₂ ?_ ?_
    (fun z ↦ ⟨by simp [hxsol z], by simp [hxsol z]⟩) (fun z ↦ ?_)
    (fun z ↦ (hsec z).1) (fun z ↦ (hsec z).2) ?_
  · simp only [phaseGauge_apply_zero]
    exact hyb₁.sub (hfd.clm_apply continuous_const)
  · simp only [phaseGauge_apply_one]
    exact hyb₂.sub (hfd.clm_apply continuous_const)
  · -- These rows differentiate only the sections, which are `C²`, and not the connection.
    have hf' := hf.differentiable two_ne_zero z
    have hp := hyp.differentiable two_ne_zero z
    have hq := hyq.differentiable two_ne_zero z
    have h₁ : equation y z 1 = 0 := by simp [hysol z]
    have h₂ : equation y z 2 = 0 := by simp [hysol z]
    simp only [equation_apply_one, equation_apply_two] at h₁ h₂
    simp [fderiv_fun_sub, fderiv_fun_add, fderiv_fun_mul, hp, hq, hf'.cos, hf'.sin,
      fderiv_cos hf', fderiv_sin hf']
    constructor
    · linear_combination Real.cos (f z) * h₁ - Real.sin (f z) * h₂
    · linear_combination Real.sin (f z) * h₁ + Real.cos (f z) * h₂
  · -- `α_x` and `α_y` have the same modulus, so they have the same zeros.
    refine hdense.mono fun z hz ↦ ?_
    have hsq : phaseGauge y f z 2 ^ 2 + phaseGauge y f z 3 ^ 2 = y z 2 ^ 2 + y z 3 ^ 2 := by
      rw [phaseGauge_apply_two, phaseGauge_apply_three]
      linear_combination (y z 2 ^ 2 + y z 3 ^ 2) * Real.sin_sq_add_cos_sq (f z)
    rw [Set.mem_ofPred_eq] at hz ⊢
    rwa [hsq]

/-! ### Vortices with the same zero multiplicities -/

section Divisor

open scoped ContDiff

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Vortices with the same zeros differ by a gauge one order smoother than the fields.** Let
`x` and `y` be `Cᵏ` solutions of the vortex equation on the plane, `k ≥ 2`, with the same end
framing `α (z) · phase (z) → 1`, where `|phase| → 1` at infinity; for example `phase` is the
winding phase `(z / |z|) ^ (-m)`. If `n` is a multiplicity function for both sections, meaning that
each of them factors near every `z` as `(w - z) ^ n z * v w` with `v` continuous and nonzero at
`z`, then `gaugeTransform u y = x` for a `C^(k+1)` circle-valued gauge `u` tending to one at
infinity: its logarithmic derivative `u⁻¹ du` is the difference of the two `Cᵏ` connections. -/
theorem exists_contDiff_gaugeTransform_eq {k : ℕ∞} (hk : 2 ≤ k) (hx : ContDiff ℝ k x)
    (hy : ContDiff ℝ k y) (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0)
    {phase : ℂ → ℂ} (hphase : Tendsto (fun z ↦ ‖phase z‖) (cocompact ℂ) (𝓝 1))
    (hxfr : Tendsto (fun z ↦ sectionValue x z * phase z) (cocompact ℂ) (𝓝 1))
    (hyfr : Tendsto (fun z ↦ sectionValue y z * phase z) (cocompact ℂ) (𝓝 1)) {n : ℂ → ℕ}
    (hnx : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w)
    (hny : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue y w = (w - z) ^ n z * v w) :
    ∃ u : ℂ → Circle, ContDiff ℝ (k + 1) (fun z ↦ (u z : ℂ)) ∧ Tendsto u (cocompact ℂ) (𝓝 1) ∧
      gaugeTransform u y = x := by
  have hk₁ : (1 : ℕ∞) ≤ k := le_trans (by norm_num) hk
  have hk₂ : ((2 : ℕ∞) : WithTop ℕ∞) ≤ k := by exact_mod_cast hk
  have hxi (i : Fin 4) : ContDiff ℝ k fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hyi (i : Fin 4) : ContDiff ℝ k fun w ↦ y w i := (contDiff_piLp 2).1 hy i
  have hxhol (w : ℂ) : equation x w 1 = 0 ∧ equation x w 2 = 0 := by simp [hxsol w]
  have hyhol (w : ℂ) : equation y w 1 = 0 ∧ equation y w 2 = 0 := by simp [hysol w]
  have hd (f : ℂ → ℝ) (hf : ContDiff ℝ k f) : Differentiable ℝ f :=
    hf.differentiable (lt_of_lt_of_le (by norm_num) hk₂).ne'
  obtain ⟨h, hh, hh₀, hα⟩ := exists_contDiff_sectionValue_eq_mul hk₁ (hxi 0) (hxi 1)
    (hd _ (hxi 2)) (hd _ (hxi 3)) hxhol (hyi 0) (hyi 1) (hd _ (hyi 2)) (hd _ (hyi 3)) hyhol hnx hny
  have hxlim := tendsto_normSq_of_tendsto_sectionValue_mul hphase hxfr
  have hylim := tendsto_normSq_of_tendsto_sectionValue_mul hphase hyfr
  have hyne : ∃ w, sectionValue y w ≠ 0 :=
    ((hyfr.eventually_ne one_ne_zero).exists).imp fun _ hw ↦ left_ne_zero_of_mul hw
  have hdense' : Dense {z | y z 2 ^ 2 + y z 3 ^ 2 ≠ 0} :=
    (dense_setOfPred_sectionValue_ne_zero hk₁ (hyi 0) (hyi 1) (hd _ (hyi 2)) (hd _ (hyi 3)) hyhol
      hyne).mono fun z hz ↦ by simpa [sectionValue_eq_zero_iff] using hz
  have hα' (z : ℂ) : (x z 2 + x z 3 * I : ℂ) = h z * (y z 2 + y z 3 * I) := by
    have := hα z
    rw [sectionValue_apply, sectionValue_apply] at this
    linear_combination this / 2
  obtain ⟨f, hf, hhf, hxy⟩ := exists_eq_phaseGauge_of_forall_section_eq_mul (hxi 0).continuous
    (hxi 1).continuous (hyi 0).continuous (hyi 1).continuous ((hyi 2).of_le hk₂)
    ((hyi 3).of_le hk₂) hxsol hysol hxlim hylim (hh.of_le hk₂) hh₀ hα' hdense'
  -- The gauge `exp (i f)` is `h`, which tends to one at infinity.
  have hcoe (w : ℂ) : ((Circle.exp (f w) : Circle) : ℂ) = h w := by
    rw [Circle.coe_exp, hhf]
  have hh1 : Tendsto h (cocompact ℂ) (𝓝 1) := by
    have hdiv := hxfr.div hyfr one_ne_zero
    rw [div_one] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [hyfr.eventually_ne one_ne_zero] with z hz
    rw [Pi.div_apply, hα z, mul_assoc, mul_div_cancel_right₀ _ hz]
  have hux : gaugeTransform (fun w ↦ Circle.exp (f w)) y = x := by
    rw [gaugeTransform_exp (hf.differentiable two_ne_zero)]
    exact hxy.symm
  -- Its logarithmic derivative is the difference of the `Cᵏ` connections.
  have hω : gaugeForm (fun w ↦ Circle.exp (f w)) =
      fun z ↦ (y z 0 - x z 0) • reCLM + (y z 1 - x z 1) • imCLM :=
    funext fun z ↦ (gaugeTransform_eq_iff.1 hux z).1
  refine ⟨fun w ↦ Circle.exp (f w), ?_, tendsto_subtype_rng.2 (hh1.congr fun w ↦ (hcoe w).symm),
    hux⟩
  refine contDiff_coe_of_contDiff_gaugeForm ?_ ?_
  · simpa only [hcoe] using hh.differentiable (lt_of_lt_of_le (by norm_num) hk₂).ne'
  · rw [hω]
    exact (((hyi 0).sub (hxi 0)).smul contDiff_const).add
      (((hyi 1).sub (hxi 1)).smul contDiff_const)

/-- **Uniqueness of framed plane vortices with prescribed zeros, modulo framed gauge.** Let `x`
and `y` be smooth solutions of the vortex equation on the plane with the same end framing
`α (z) · phase (z) → 1`, where `|phase| → 1` at infinity; for example `phase` is the winding
phase `(z / |z|) ^ (-m)`. If `n` is a multiplicity function for both sections, meaning that each of
them factors near every `z` as `(w - z) ^ n z * v w` with `v` continuous and nonzero at `z`, then
exactly one smooth framed gauge `u` satisfies `u • y = x`. -/
theorem existsUnique_framedGaugeGroup_smul_eq (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0) {phase : ℂ → ℂ}
    (hphase : Tendsto (fun z ↦ ‖phase z‖) (cocompact ℂ) (𝓝 1))
    (hxfr : Tendsto (fun z ↦ sectionValue x z * phase z) (cocompact ℂ) (𝓝 1))
    (hyfr : Tendsto (fun z ↦ sectionValue y z * phase z) (cocompact ℂ) (𝓝 1)) {n : ℂ → ℕ}
    (hnx : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w)
    (hny : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue y w = (w - z) ^ n z * v w) :
    ∃! u : framedGaugeGroup, u • y = x := by
  obtain ⟨u, hu, hu1, hxy⟩ := exists_contDiff_gaugeTransform_eq (k := ⊤) le_top hx hy hxsol hysol
    hphase hxfr hyfr hnx hny
  let u' : framedGaugeGroup := ⟨u, (mem_framedGaugeGroup _).2 ⟨by simpa using hu, hu1⟩⟩
  exact ⟨u', hxy, fun v hv ↦ IsCancelSMul.right_cancel v u' y (hv.trans hxy.symm)⟩

end Divisor

end TauCeti.Vortex
