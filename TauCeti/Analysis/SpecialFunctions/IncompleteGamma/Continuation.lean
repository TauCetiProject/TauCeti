/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Complementary
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# The upper incomplete Gamma function on the logarithmic plane

`Complex.upperIncompleteGammaLog a w` is `Γ(a, e^w)` continued to the whole `w`-plane, the
universal cover of the punctured `z`-plane. It starts from `Γ(a, e^{Re w})` on the positive real
axis and integrates `−e^{au − e^u}` along the vertical segment from `Re w` to `w`. This integrand
is entire in `u`, and on the strip `|Im u| < π` it is the derivative of the principal function
`Γ(a, e^u)`; the segment may leave that strip. The continuation is entire in `a` and in `w`, it is
the principal value `Γ(a, z)` at `w = log z` for `z` in the slit plane, and it satisfies the
continuation formulas DLMF 8.2.9–8.2.11.

## Main definitions

* `Complex.upperIncompleteGammaLog`: the continuation of `Γ(a, e^w)` to every `w ∈ ℂ`.

## Main results

* `Complex.hasDerivAt_upperIncompleteGammaLog`, `Complex.differentiable_upperIncompleteGammaLog`:
  `∂_w upperIncompleteGammaLog a w = −e^{aw − e^w}`, so it is entire in `w`;
* `Complex.differentiable_upperIncompleteGammaLog_left`: it is entire in `a`;
* `Complex.upperIncompleteGammaLog_eq_upperIncompleteGamma_exp`,
  `Complex.upperIncompleteGammaLog_log`: on the strip `|Im w| < π` it is `Γ(a, e^w)`, so
  `upperIncompleteGammaLog a (log z) = Γ(a, z)` on the slit plane;
* `Complex.lowerIncompleteGamma_exp`,
  `Complex.Gamma_mul_exp_mul_tricomiIncompleteGamma_exp_add_two_pi_mul_I`: the lower function
  `γ(a, e^w) = Γ(a) e^{aw} γ*(a, e^w)` on the principal strip, and its continuation in `w` across
  the sheets (DLMF 8.2.8);
* `Complex.upperIncompleteGammaLog_eq_Gamma_sub`: `Γ(a) − Γ(a) e^{aw} γ*(a, e^w)` for `a ∉ −ℕ`;
* `Complex.upperIncompleteGammaLog_add_two_pi_mul_I`: DLMF 8.2.9 for `a ∉ −ℕ`;
* `Complex.upperIncompleteGammaLog_neg_natCast_add_two_pi_mul_I`: its limiting form at `a = −n`,
  `Γ(−n, e^{w + 2πim}) = Γ(−n, e^w) − 2πim (−1)ⁿ/n!`;
* `Complex.exp_mul_upperIncompleteGammaLog_add_pi_mul_I_sub`: DLMF 8.2.10 for every `a`;
* `Complex.upperIncompleteGammaLog_log_add_pi_mul_I`,
  `Complex.upperIncompleteGammaLog_log_sub_pi_mul_I`: DLMF 8.2.11, both signs, for `a ∉ −ℕ`;
* `Complex.tendsto_upperIncompleteGamma_neg_add_mul_I`,
  `Complex.tendsto_upperIncompleteGamma_neg_sub_mul_I`: the values on the two banks of the cut,
  `Γ(a, −x ± iy) → upperIncompleteGammaLog a (ln x ± πi)` as `y → 0+`, for every `a`;
* `Complex.upperIncompleteGammaLog_one_left`: `upperIncompleteGammaLog 1 w = e^{−e^w}`.

## Implementation notes

The correction integral is the increment of any entire primitive `g` of `u ↦ e^{au − e^u}`
(Mathlib's `Differentiable.isExactOn_univ`) along the vertical segment. On the real axis
`x ↦ Γ(a, e^x) + g x` has derivative zero by DLMF 8.8.13, so `upperIncompleteGammaLog a` is a
constant minus `g`; this gives holomorphy in `w` for every `a`, including the poles of `Γ`. On the
strip `|Im w| < π` the same computation with `Γ(a, e^u)` in place of `−g` shows that the
continuation is `Γ(a, e^w)`. For `a ∉ −ℕ` the closed form in terms of Tricomi's `γ*` follows on
that strip from DLMF 8.2.3, and on all of `ℂ` by the identity theorem in `w`. The results at the
poles `a = −n` and DLMF 8.2.10 follow by continuity in `a`.

## References

* NIST Digital Library of Mathematical Functions, §8.2(ii), <https://dlmf.nist.gov/8.2.ii>.

The proofs of DLMF 8.2.9–8.2.11 and of the limiting form are adapted from the
lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/IncompleteGamma/ContinuedProperties.lean` (`upperIncompleteGammaOnLog_eq_Gamma_sub`,
`upperIncompleteGammaOnLog_monodromy`, `upperIncompleteGammaOnLog_monodromy_limit`,
`upperIncompleteGammaOnLog_halfTurn`, `upperIncompleteGammaOnLog_jump`), whose continuation
`upperIncompleteGammaOnLog` (in `DLMF/IncompleteGamma/Basic.lean`) starts the segment at
`log (exp w)` instead of `Re w`. The rest of the proofs are new.
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped Real Topology Nat

namespace Complex

/-- `Γ(a, e^w)` on the logarithmic plane, continued from the positive axis by integrating
`−e^{au − e^u}` along the vertical segment from `Re w` to `w`. This integrand is entire in `u`,
and on the strip `|Im u| < π` it is the derivative of the principal function `Γ(a, e^u)`. It is
entire in `a` and in `w` (`Complex.differentiable_upperIncompleteGammaLog_left`,
`Complex.differentiable_upperIncompleteGammaLog`). -/
def upperIncompleteGammaLog (a w : ℂ) : ℂ :=
  upperIncompleteGamma a (Real.exp w.re) -
    ∫ s in (0 : ℝ)..1, I * w.im *
      cexp (a * ((w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ)) -
        cexp ((w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ)))

/-- The defining correction integral along the vertical segment from `Re w` to `w`. -/
theorem upperIncompleteGammaLog_def (a w : ℂ) :
    upperIncompleteGammaLog a w =
      upperIncompleteGamma a (Real.exp w.re) -
        ∫ s in (0 : ℝ)..1, I * w.im *
          cexp (a * ((w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ)) -
            cexp ((w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ))) := (rfl)

/-- On the real axis the correction integral vanishes: `upperIncompleteGammaLog a x = Γ(a, e^x)`.
-/
@[simp]
theorem upperIncompleteGammaLog_ofReal (a : ℂ) (x : ℝ) :
    upperIncompleteGammaLog a x = upperIncompleteGamma a (cexp x) := by
  simp [upperIncompleteGammaLog_def]

/-- The correction integral of `Complex.upperIncompleteGammaLog` is the increment of `F` from
`Re w` to `w`, when `F` has derivative `e^{au − e^u}` on the vertical segment between them. -/
private theorem integral_correction_eq_sub {a w : ℂ} {F : ℂ → ℂ}
    (hF : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → HasDerivAt F
      (cexp (a * ((w.re : ℂ) + t • (I * w.im)) - cexp ((w.re : ℂ) + t • (I * w.im))))
      ((w.re : ℂ) + t • (I * w.im))) :
    ∫ s in (0 : ℝ)..1, I * w.im *
        cexp (a * ((w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ)) -
          cexp ((w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ))) = F w - F w.re := by
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (f' := fun u => cexp (a * u - cexp u)) (by fun_prop) hF
  -- the segment from `Re w` to `w`, parametrized as in `integral_unitInterval_deriv_eq_sub`
  have hγ (s : ℝ) : (w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ) = (w.re : ℂ) + s • (I * w.im) := by
    rw [real_smul, ofReal_mul]
    ring
  rw [mul_comm I, re_add_im, smul_eq_mul, ← intervalIntegral.integral_const_mul] at h
  simp_rw [hγ, mul_comm I]
  exact h

/-- On the strip `|Im u| < π`, `∂_u Γ(a, e^u) = −e^{au − e^u}` (DLMF 8.8.13 composed with
`exp`). -/
theorem hasDerivAt_upperIncompleteGamma_exp (a : ℂ) {u : ℂ} (hu : |u.im| < π) :
    HasDerivAt (fun v => upperIncompleteGamma a (cexp v)) (-cexp (a * u - cexp u)) u := by
  refine ((hasDerivAt_upperIncompleteGamma (exp_mem_slitPlane_of_abs_im_lt hu) a).comp u
    (hasDerivAt_exp u)).congr_deriv ?_
  obtain ⟨h₁, h₂⟩ := abs_lt.1 hu
  rw [cpow_def_of_ne_zero (exp_ne_zero u), log_exp h₁ h₂.le, neg_mul, ← exp_add, ← exp_add]
  ring_nf

/-- **DLMF 8.8.13 on the logarithmic plane**: `∂_w upperIncompleteGammaLog a w = −e^{aw − e^w}`,
for every `a`. -/
theorem hasDerivAt_upperIncompleteGammaLog (a w : ℂ) :
    HasDerivAt (upperIncompleteGammaLog a) (-cexp (a * w - cexp w)) w := by
  obtain ⟨g, hg⟩ := (by fun_prop : Differentiable ℂ fun u => cexp (a * u - cexp u)).isExactOn_univ
  have hg' (u : ℂ) : HasDerivAt g (cexp (a * u - cexp u)) u := hg u (mem_univ u)
  -- on the real axis `x ↦ Γ(a, e^x) + g x` has derivative zero, so it is constant
  have hd (x : ℝ) :
      HasDerivAt (fun x : ℝ => upperIncompleteGamma a (cexp x) + g x) 0 x := by
    have h := (hasDerivAt_upperIncompleteGamma_exp a (u := x)
      (by simpa using Real.pi_pos)).comp_ofReal
      |>.add (hg' x).comp_ofReal
    rwa [neg_add_cancel] at h
  have hconst (x : ℝ) : upperIncompleteGamma a (cexp x) + g x = upperIncompleteGamma a 1 + g 0 := by
    simpa using is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
      (fun x => (hd x).deriv) x 0
  have heq : upperIncompleteGammaLog a = fun w => upperIncompleteGamma a 1 + g 0 - g w := by
    funext w
    rw [upperIncompleteGammaLog_def, integral_correction_eq_sub fun t _ => hg' _, ofReal_exp,
      ← hconst w.re]
    ring
  rw [heq]
  exact (hg' w).const_sub _

/-- `upperIncompleteGammaLog a` is entire, for every `a`. -/
theorem differentiable_upperIncompleteGammaLog (a : ℂ) :
    Differentiable ℂ (upperIncompleteGammaLog a) :=
  fun w => (hasDerivAt_upperIncompleteGammaLog a w).differentiableAt

/-- `∂_w upperIncompleteGammaLog a w = −e^{aw − e^w}`, as a function. -/
@[simp]
theorem deriv_upperIncompleteGammaLog (a : ℂ) :
    deriv (upperIncompleteGammaLog a) = fun w => -cexp (a * w - cexp w) :=
  funext fun w => (hasDerivAt_upperIncompleteGammaLog a w).deriv

/-- `upperIncompleteGammaLog · w` is entire, for every `w`. -/
theorem differentiable_upperIncompleteGammaLog_left (w : ℂ) :
    Differentiable ℂ fun a => upperIncompleteGammaLog a w := by
  -- the correction integrand, as a function of the parameter and of the path variable
  set F : ℂ → ℝ → ℂ := fun a s => I * w.im *
    cexp (a * ((w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ)) -
      cexp ((w.re : ℂ) + I * ((s * w.im : ℝ) : ℂ))) with hF
  have hint : Differentiable ℂ fun a => ∫ s in (0 : ℝ)..1, F a s := by
    intro a₀
    -- `F` is bounded on the compact set `closedBall a₀ 1 × [0, 1]`
    obtain ⟨C, hC⟩ := ((isCompact_closedBall a₀ 1).prod isCompact_Icc).exists_bound_of_continuousOn
      (f := fun p : ℂ × ℝ => F p.1 p.2) (by rw [hF]; fun_prop)
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    refine (TauCeti.hasDerivAt_integral_of_dominated_of_differentiableOn (U := Metric.ball a₀ 1)
      (bound := fun _ => C) Metric.isOpen_ball (Metric.mem_ball_self one_pos)
      (fun a _ => (by rw [hF]; fun_prop : Continuous (F a)).aestronglyMeasurable) ?_
      (integrable_const C) (.of_forall fun s => ?_)).differentiableAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs a ha
      exact hC (a, s) ⟨Metric.ball_subset_closedBall ha, Ioc_subset_Icc_self hs⟩
    · exact (by rw [hF]; fun_prop : Differentiable ℂ fun a => F a s).differentiableOn
  have h := (differentiable_upperIncompleteGamma_left
    (ofReal_mem_slitPlane.2 (Real.exp_pos w.re))).sub hint
  refine fun a => (h a).congr_of_eventuallyEq (.of_forall fun b => ?_)
  exact upperIncompleteGammaLog_def b w

/-! ### The principal sheet -/

/-- On the strip `|Im w| < π` the continuation is `Γ(a, e^w)`. -/
theorem upperIncompleteGammaLog_eq_upperIncompleteGamma_exp (a : ℂ) {w : ℂ} (hw : |w.im| < π) :
    upperIncompleteGammaLog a w = upperIncompleteGamma a (cexp w) := by
  -- the vertical segment from `Re w` to `w` stays in the strip
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |((w.re : ℂ) + t • (I * w.im)).im| < π := by
    have h : ((w.re : ℂ) + t • (I * w.im)).im = t * w.im := by simp
    rw [h, abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt hw
  rw [upperIncompleteGammaLog_def, integral_correction_eq_sub (F := fun v =>
      -upperIncompleteGamma a (cexp v)) fun t ht =>
      (neg_neg (cexp _)) ▸ (hasDerivAt_upperIncompleteGamma_exp a (hseg t ht)).neg,
    ofReal_exp]
  ring

/-- **The principal sheet**: `upperIncompleteGammaLog a (log z) = Γ(a, z)` on the slit plane. -/
theorem upperIncompleteGammaLog_log {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) :
    upperIncompleteGammaLog a (Complex.log z) = upperIncompleteGamma a z := by
  have hz' := mem_slitPlane_iff_arg.1 hz
  rw [upperIncompleteGammaLog_eq_upperIncompleteGamma_exp a, exp_log hz'.2]
  rw [log_im, abs_lt]
  exact ⟨neg_pi_lt_arg z, (arg_le_pi z).lt_of_ne hz'.1⟩

/-- On the strip `−π < Im w ≤ π`, `γ(a, e^w) = Γ(a) e^{aw} γ*(a, e^w)`. -/
theorem lowerIncompleteGamma_exp (a : ℂ) {w : ℂ} (hw₁ : -π < w.im) (hw₂ : w.im ≤ π) :
    lowerIncompleteGamma a (cexp w) =
      Gamma a * cexp (a * w) * tricomiIncompleteGamma a (cexp w) := by
  rw [lowerIncompleteGamma_def, regularizedGamma_def, cpow_def_of_ne_zero (exp_ne_zero w),
    log_exp hw₁ hw₂, mul_comm w, mul_assoc]

/-- **DLMF 8.2.8** in the logarithmic coordinate: the continuation
`Γ(a) e^{aw} γ*(a, e^w)` of `γ(a, e^w)` (`Complex.lowerIncompleteGamma_exp`) picks up the factor
`e^{2πima}` on the `m`-th sheet. -/
theorem Gamma_mul_exp_mul_tricomiIncompleteGamma_exp_add_two_pi_mul_I (a w : ℂ) (m : ℤ) :
    Gamma a * cexp (a * (w + 2 * π * I * m)) * tricomiIncompleteGamma a (cexp (w + 2 * π * I * m)) =
      cexp (2 * π * I * m * a) * (Gamma a * cexp (a * w) * tricomiIncompleteGamma a (cexp w)) := by
  have he : cexp (w + 2 * π * I * m) = cexp w := by
    rw [exp_add, mul_comm _ (m : ℂ), exp_int_mul_two_pi_mul_I, mul_one]
  have ha : a * (w + 2 * π * I * m) = 2 * π * I * m * a + a * w := by ring
  rw [he, ha, exp_add]
  ring

/-- Away from the poles of `Γ`, `upperIncompleteGammaLog a w = Γ(a) − Γ(a) e^{aw} γ*(a, e^w)`. -/
theorem upperIncompleteGammaLog_eq_Gamma_sub {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ) :
    upperIncompleteGammaLog a w =
      Gamma a - Gamma a * cexp (a * w) * tricomiIncompleteGamma a (cexp w) := by
  have hR : Differentiable ℂ fun w =>
      Gamma a - Gamma a * cexp (a * w) * tricomiIncompleteGamma a (cexp w) := by
    have := differentiable_tricomiIncompleteGamma a
    fun_prop
  -- both sides are entire in `w` and agree on the strip `|Im w| < π`, by DLMF 8.2.3
  refine congrFun (AnalyticOnNhd.eq_of_eventuallyEq
    (fun u _ => (differentiable_upperIncompleteGammaLog a).analyticAt u)
    (fun u _ => hR.analyticAt u) (z₀ := 0) ?_) w
  filter_upwards [(isOpen_lt (continuous_abs.comp continuous_im) continuous_const).mem_nhds
    (by simpa using Real.pi_pos : |(0 : ℂ).im| < π)] with u hu
  obtain ⟨h₁, h₂⟩ := abs_lt.1 hu
  rw [upperIncompleteGammaLog_eq_upperIncompleteGamma_exp a hu,
    ← lowerIncompleteGamma_exp a h₁ h₂.le,
    ← upperIncompleteGamma_add_lowerIncompleteGamma ha (exp_mem_slitPlane_of_abs_im_lt hu)]
  ring

/-- `upperIncompleteGammaLog 1 w = e^{−e^w}`, the case `a = 1` of `Γ(1, z) = e^{−z}`. -/
@[simp]
theorem upperIncompleteGammaLog_one_left (w : ℂ) :
    upperIncompleteGammaLog 1 w = cexp (-cexp w) := by
  rw [upperIncompleteGammaLog_eq_Gamma_sub (ne_neg_natCast_of_re_pos (by simp)), Gamma_one,
    one_mul, one_mul, tricomiIncompleteGamma_one_left (exp_ne_zero w)]
  field_simp
  ring

/-! ### Continuation formulas -/

/-- **DLMF 8.2.9** away from the poles of `Γ`:
`Γ(a, e^{w + 2πim}) = e^{2πima} Γ(a, e^w) + (1 − e^{2πima}) Γ(a)`. -/
theorem upperIncompleteGammaLog_add_two_pi_mul_I {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ)
    (m : ℤ) :
    upperIncompleteGammaLog a (w + 2 * π * I * m) =
      cexp (2 * π * I * m * a) * upperIncompleteGammaLog a w +
        (1 - cexp (2 * π * I * m * a)) * Gamma a := by
  rw [upperIncompleteGammaLog_eq_Gamma_sub ha, upperIncompleteGammaLog_eq_Gamma_sub ha,
    Gamma_mul_exp_mul_tricomiIncompleteGamma_exp_add_two_pi_mul_I]
  ring

/-- **DLMF 8.2.9 at `a = −n`**, the limiting form:
`Γ(−n, e^{w + 2πim}) = Γ(−n, e^w) − 2πim (−1)ⁿ/n!`. -/
theorem upperIncompleteGammaLog_neg_natCast_add_two_pi_mul_I (n : ℕ) (w : ℂ) (m : ℤ) :
    upperIncompleteGammaLog (-n) (w + 2 * π * I * m) =
      upperIncompleteGammaLog (-n) w - 2 * π * I * m * (-1) ^ n / (n ! : ℂ) := by
  set c : ℂ := 2 * π * I * m with hc
  have hc₁ : cexp (c * -n) = 1 := by
    have h : c * -n = ((-(m * n) : ℤ) : ℂ) * (2 * π * I) := by
      rw [hc]
      push_cast
      ring
    rw [h, exp_int_mul_two_pi_mul_I]
  -- `φ a = Γ(a, e^{w + c}) − e^{ca} Γ(a, e^w)` is continuous in `a`
  have hφ : Tendsto (fun a => upperIncompleteGammaLog a (w + c) -
      cexp (c * a) * upperIncompleteGammaLog a w) (𝓝[≠] (-n : ℂ))
      (𝓝 (upperIncompleteGammaLog (-n) (w + c) - upperIncompleteGammaLog (-n) w)) := by
    have hcont : Continuous fun a => upperIncompleteGammaLog a (w + c) -
        cexp (c * a) * upperIncompleteGammaLog a w :=
      (differentiable_upperIncompleteGammaLog_left (w + c)).continuous.sub
        ((by fun_prop : Continuous fun a : ℂ => cexp (c * a)).mul
          (differentiable_upperIncompleteGammaLog_left w).continuous)
    have h := (hcont.tendsto (-n : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(-n : ℂ)}ᶜ))
    rwa [hc₁, one_mul] at h
  -- `(1 − e^{ca}) Γ(a) = −(slope of e^{c·} at −n) ((a + n) Γ(a)) → −c (−1)ⁿ/n!`
  have hd : HasDerivAt (fun a : ℂ => cexp (c * a)) c (-n) := by
    have h := ((hasDerivAt_id (-n : ℂ)).const_mul c).cexp
    simp only [id_eq] at h
    rwa [hc₁, one_mul, mul_one] at h
  have hlim : Tendsto (fun a => (1 - cexp (c * a)) * Gamma a) (𝓝[≠] (-n : ℂ))
      (𝓝 (-(c * ((-1) ^ n / (n ! : ℂ))))) := by
    refine ((hasDerivAt_iff_tendsto_slope.1 hd).mul (tendsto_add_natCast_mul_Gamma n)).neg.congr'
      ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : a + n ≠ 0 := fun h => ha (eq_neg_of_add_eq_zero_left h)
    rw [slope_def_field, hc₁, sub_neg_eq_add]
    field_simp
    ring
  -- off `−ℕ`, `φ a = (1 − e^{ca}) Γ(a)` by DLMF 8.2.9
  have hreg : ∀ᶠ a : ℂ in 𝓝[≠] (-n : ℂ), ∀ k : ℕ, a ≠ -k := by
    filter_upwards [(tendsto_add_natCast_mul_Gamma n).eventually_ne
      (div_ne_zero (pow_ne_zero n (neg_ne_zero.2 one_ne_zero))
        (by exact_mod_cast n.factorial_ne_zero))]
      with a ha k hk
    rw [hk, Gamma_neg_nat_eq_zero, mul_zero] at ha
    exact ha rfl
  have h := tendsto_nhds_unique hφ (hlim.congr' (hreg.mono fun a ha => by
    beta_reduce
    rw [hc, upperIncompleteGammaLog_add_two_pi_mul_I ha]
    ring))
  rw [hc] at h ⊢
  linear_combination h

/-- **DLMF 8.2.11** (upper sign): `Γ(a, z e^{πi}) = Γ(a) (1 − z^a e^{πia} γ*(a, −z))` for `a ∉ −ℕ`
and `z ≠ 0`. -/
theorem upperIncompleteGammaLog_log_add_pi_mul_I {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ}
    (hz : z ≠ 0) :
    upperIncompleteGammaLog a (Complex.log z + π * I) =
      Gamma a * (1 - z ^ a * cexp (π * I * a) * tricomiIncompleteGamma a (-z)) := by
  have he : a * (Complex.log z + π * I) = Complex.log z * a + π * I * a := by ring
  rw [upperIncompleteGammaLog_eq_Gamma_sub ha, exp_add, exp_log hz, exp_pi_mul_I, mul_neg_one,
    he, exp_add, cpow_def_of_ne_zero hz]
  ring

/-- **DLMF 8.2.11** (lower sign): `Γ(a, z e^{−πi}) = Γ(a) (1 − z^a e^{−πia} γ*(a, −z))` for
`a ∉ −ℕ` and `z ≠ 0`. -/
theorem upperIncompleteGammaLog_log_sub_pi_mul_I {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ}
    (hz : z ≠ 0) :
    upperIncompleteGammaLog a (Complex.log z - π * I) =
      Gamma a * (1 - z ^ a * cexp (-(π * I * a)) * tricomiIncompleteGamma a (-z)) := by
  have he : a * (Complex.log z - π * I) = Complex.log z * a + -(π * I * a) := by ring
  rw [upperIncompleteGammaLog_eq_Gamma_sub ha, exp_sub, exp_log hz, exp_pi_mul_I, div_neg, div_one,
    he, exp_add, cpow_def_of_ne_zero hz]
  ring

/-- **DLMF 8.2.10**, for every `a`:
`e^{−πia} Γ(a, e^{w + πi}) − e^{πia} Γ(a, e^{w − πi}) = −2πi / Γ(1 − a)`, with Mathlib's entire
reciprocal `(Γ(1 − a))⁻¹`. -/
theorem exp_mul_upperIncompleteGammaLog_add_pi_mul_I_sub (a w : ℂ) :
    cexp (-(π * I * a)) * upperIncompleteGammaLog a (w + π * I) -
        cexp (π * I * a) * upperIncompleteGammaLog a (w - π * I) =
      -(2 * π * I) * (Gamma (1 - a))⁻¹ := by
  -- both sides are continuous in `a`; they agree off the countable set `−ℕ`
  have hL : Continuous fun a => cexp (-(π * I * a)) * upperIncompleteGammaLog a (w + π * I) -
      cexp (π * I * a) * upperIncompleteGammaLog a (w - π * I) :=
    ((by fun_prop : Continuous fun a : ℂ => cexp (-(π * I * a))).mul
      (differentiable_upperIncompleteGammaLog_left _).continuous).sub
      ((by fun_prop : Continuous fun a : ℂ => cexp (π * I * a)).mul
        (differentiable_upperIncompleteGammaLog_left _).continuous)
  have hR : Continuous fun a : ℂ => -(2 * π * I) * (Gamma (1 - a))⁻¹ :=
    continuous_const.mul (differentiable_one_div_Gamma.continuous.comp (by fun_prop))
  refine congrFun (hL.ext_on ((countable_range fun n : ℕ => -(n : ℂ)).dense_compl ℂ) hR
    fun b hb => ?_) a
  have hb' : ∀ n : ℕ, b ≠ -n := fun n h => hb ⟨n, h.symm⟩
  -- the reflection formula `Γ(b)⁻¹ Γ(1 − b)⁻¹ = sin(πb)/π`
  have hr : (Gamma b)⁻¹ * (Gamma (1 - b))⁻¹ = Complex.sin (π * b) / π := by
    rw [← mul_inv, Gamma_mul_Gamma_one_sub, inv_div]
  have hG := Gamma_ne_zero hb'
  have hp : cexp (w + π * I) = -cexp w := by rw [exp_add, exp_pi_mul_I, mul_neg_one]
  have hm : cexp (w - π * I) = -cexp w := by rw [exp_sub, exp_pi_mul_I, div_neg, div_one]
  have e₁ : cexp (-(π * I * b)) * cexp (b * (w + π * I)) = cexp (b * w) := by
    rw [← exp_add]; ring_nf
  have e₂ : cexp (π * I * b) * cexp (b * (w - π * I)) = cexp (b * w) := by
    rw [← exp_add]; ring_nf
  simp only [upperIncompleteGammaLog_eq_Gamma_sub hb', hp, hm]
  rw [Complex.sin, eq_div_iff (ofReal_ne_zero.2 Real.pi_ne_zero)] at hr
  have hr' : (Gamma (1 - b))⁻¹ * π =
      Gamma b * ((cexp (-(π * b) * I) - cexp (π * b * I)) * I / 2) := by
    rw [← hr]; field_simp
  have e₃ : cexp (-(π * b) * I) = cexp (-(π * I * b)) := by ring_nf
  have e₄ : cexp (π * b * I) = cexp (π * I * b) := by ring_nf
  rw [e₃, e₄] at hr'
  linear_combination (-(Gamma b * tricomiIncompleteGamma b (-cexp w))) * e₁ +
    Gamma b * tricomiIncompleteGamma b (-cexp w) * e₂ + 2 * I * hr' +
    Gamma b * (cexp (-(π * I * b)) - cexp (π * I * b)) * I_sq

/-! ### The two banks of the cut -/

/-- **The upper bank of the cut**: for `x > 0` and every `a`,
`Γ(a, −x + iy) → upperIncompleteGammaLog a (ln x + πi)` as `y → 0+`. -/
theorem tendsto_upperIncompleteGamma_neg_add_mul_I (a : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => upperIncompleteGamma a (-x + y * I)) (𝓝[>] 0)
      (𝓝 (upperIncompleteGammaLog a (Real.log x + π * I))) := by
  -- the path `y ↦ −x + iy` approaches `−x` from the upper half-plane
  have hpath : Tendsto (fun y : ℝ => -(x : ℂ) + y * I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-(x : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using ((by fun_prop : Continuous fun y : ℝ => -(x : ℂ) + y * I).tendsto 0).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy.le
  have hlog := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (z := -(x : ℂ))
    (by simpa using hx) (by simp)).comp hpath
  rw [norm_neg, norm_real, Real.norm_of_nonneg hx.le] at hlog
  refine (((differentiable_upperIncompleteGammaLog a).continuous.tendsto _).comp hlog).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact upperIncompleteGammaLog_log (mem_slitPlane_iff.2 (Or.inr (by simpa using hy.ne'))) a

/-- **The lower bank of the cut**: for `x > 0` and every `a`,
`Γ(a, −x − iy) → upperIncompleteGammaLog a (ln x − πi)` as `y → 0+`. -/
theorem tendsto_upperIncompleteGamma_neg_sub_mul_I (a : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => upperIncompleteGamma a (-x - y * I)) (𝓝[>] 0)
      (𝓝 (upperIncompleteGammaLog a (Real.log x - π * I))) := by
  -- the path `y ↦ −x − iy` approaches `−x` from the lower half-plane
  have hpath : Tendsto (fun y : ℝ => -(x : ℂ) - y * I) (𝓝[>] 0)
      (𝓝[{z : ℂ | z.im < 0}] (-(x : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using ((by fun_prop : Continuous fun y : ℝ => -(x : ℂ) - y * I).tendsto 0).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  have hlog := (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := -(x : ℂ))
    (by simpa using hx) (by simp)).comp hpath
  rw [norm_neg, norm_real, Real.norm_of_nonneg hx.le] at hlog
  refine (((differentiable_upperIncompleteGammaLog a).continuous.tendsto _).comp hlog).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact upperIncompleteGammaLog_log (mem_slitPlane_iff.2 (Or.inr (by simpa using hy.ne'))) a

end Complex
