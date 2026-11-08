/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.ODE.LyapunovPerron.Basic
-- Private: the improper integrals, the exponential identities, the two-sided exponential integral
-- and Schur's test are used only inside the proofs below.
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# The whole-line Green integral of an exponential dichotomy

Let `A` be a bounded operator on a real Banach space `X` whose flow `exp (t A)` has an exponential
dichotomy: for a bounded operator `P`, constants `K` and `α > 0`,

`‖exp (t A) (P v)‖ ≤ K exp (-α t) ‖v‖` for `t ≥ 0`, and
`‖exp (t A) (v - P v)‖ ≤ K exp (α t) ‖v‖` for `t ≤ 0`.

These are the hypotheses of the Lyapunov--Perron construction in
`TauCeti.Analysis.ODE.LyapunovPerron.Basic`. The projection `P` need not be idempotent for any of
the results below.

The *Green integral* (`ContinuousLinearMap.greenIntegral`)

`G g (t) = ∫_{s ≤ t} exp ((t - s) A) (P (g s)) ds - ∫_{s > t} exp ((t - s) A) (g s - P (g s)) ds`

propagates the `P`-part of a forcing term forward from `-∞` and the remaining part backward from
`+∞`. Its kernel is bounded by `K exp (-α |t - s|)`, which has integral `2 K / α`, so Schur's test
bounds it on every `Lᵖ` (`ContinuousLinearMap.eLpNorm_greenIntegral_le`). For a bounded continuous
forcing term it solves `u' = A u + g` (`ContinuousLinearMap.hasDerivAt_greenIntegral`), and, when
`P` commutes with `A`, it recovers every compactly supported `C¹` path `u` from `u' - A u`
(`ContinuousLinearMap.greenIntegral_deriv_sub_eq`).

The application to the trajectory operator `d/ds - A` on `W^{1,p}(ℝ, X)` is in
`TauCeti.Analysis.ODE.TrajectoryOperator.Hyperbolic`.

## Main declarations

* `ContinuousLinearMap.greenIntegral`: the whole-line Green integral of a dichotomy.
* `ContinuousLinearMap.greenIntegral_smul`, `ContinuousLinearMap.greenIntegral_add`: linearity in
  the forcing term (additivity for continuous bounded forcing terms under a dichotomy).
* `ContinuousLinearMap.enorm_greenIntegral_le`: the pointwise bound by the kernel
  `K exp (-α |t - s|)`.
* `ContinuousLinearMap.eLpNorm_greenIntegral_le`: the bound `‖G g‖_{Lᵖ} ≤ 2 K / α ‖g‖_{Lᵖ}`.
* `ContinuousLinearMap.hasDerivAt_greenIntegral`: `G g` solves `u' = A u + g`.
* `ContinuousLinearMap.greenIntegral_deriv_sub_eq`: `G (u' - A u) = u` for compactly supported
  `C¹` paths `u`.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics **629**,
  Springer (1978) (exponential dichotomies and the Green function of `u' = A u + g`).
-/

public section

noncomputable section

open Filter MeasureTheory NormedSpace Set Topology
open scoped NNReal ENNReal

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The whole-line Green integral of the forcing term `g`:

`∫_{s ≤ t} exp ((t - s) A) (P (g s)) ds - ∫_{s > t} exp ((t - s) A) (g s - P (g s)) ds`.

The first integral propagates the part `P (g s)` of the forcing forward from `-∞`; the second
propagates the remaining part `g s - P (g s)` backward from `+∞`. When `X` is complete, `exp (t A)`
has an exponential dichotomy with projection `P`, and `g` is continuous and bounded, it solves
`u' = A u + g` (`ContinuousLinearMap.hasDerivAt_greenIntegral`). -/
def greenIntegral (A P : X →L[ℝ] X) (g : ℝ → X) (t : ℝ) : X :=
  (∫ s in Iic t, exp ((t - s) • A) (P (g s))) - ∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))

theorem greenIntegral_def (A P : X →L[ℝ] X) (g : ℝ → X) (t : ℝ) :
    greenIntegral A P g t = (∫ s in Iic t, exp ((t - s) • A) (P (g s))) -
      ∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s)) := (rfl)

variable [CompleteSpace X] {A P : X →L[ℝ] X} {K α : ℝ≥0} {M : ℝ} {g : ℝ → X}

/-! ### The Green integral solves `u' = A u + g` -/

/-- Under the forward exponential estimate, the stable integrand `exp (-s A) (P (g s))` of a
continuous forcing term bounded by `M` is integrable on every half-line `(-∞, c]`. -/
private theorem integrableOn_exp_neg_smul_apply_Iic
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) (c : ℝ) :
    IntegrableOn (fun s ↦ exp ((-s) • A) (P (g s))) (Iic c) := by
  have hα' : (0 : ℝ) < α := hα
  have hcont : Continuous fun s ↦ exp ((-s) • A) (P (g s)) :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_apply
      (P.continuous.comp hg)
  -- On `(-∞, 0]` the integrand decays like `exp (α s)`.
  have h₀ : IntegrableOn (fun s ↦ exp ((-s) • A) (P (g s))) (Iic 0) := by
    refine ((integrableOn_exp_mul_Iic hα' 0).const_mul (K * M)).mono'
      (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs0
    calc ‖exp ((-s) • A) (P (g s))‖ ≤ K * Real.exp (-α * -s) * ‖g s‖ :=
          hs _ (neg_nonneg.2 hs0) _
      _ ≤ K * Real.exp (-α * -s) * M := by gcongr; exact hgM s
      _ = K * M * Real.exp (α * s) := by ring_nf
  exact (h₀.union (hcont.integrableOn_Icc (a := 0) (b := c))).mono_set fun s hs' ↦
    (le_or_gt s 0).elim Or.inl fun h ↦ Or.inr ⟨h.le, hs'⟩

/-- Under the forward exponential estimate, the stable integrand of the Green integral of a
continuous forcing term bounded by `M` is integrable on `(-∞, t]`. -/
private theorem integrableOn_greenIntegral_stable
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) (t : ℝ) :
    IntegrableOn (fun s ↦ exp ((t - s) • A) (P (g s))) (Iic t) := by
  have hpull (s : ℝ) : exp ((t - s) • A) (P (g s)) = exp (t • A) (exp ((-s) • A) (P (g s))) := by
    simp only [← ContinuousLinearMap.exp_add_smul_apply, sub_eq_add_neg]
  simp only [hpull]
  exact (exp (t • A)).integrable_comp (integrableOn_exp_neg_smul_apply_Iic hs hα hg hgM t)

/-! ### Linearity in the forcing term -/

omit [CompleteSpace X] in
/-- The Green integral of the zero forcing term vanishes. -/
@[simp]
theorem greenIntegral_zero (t : ℝ) : greenIntegral A P 0 t = 0 := by
  simp [greenIntegral_def]

omit [CompleteSpace X] in
/-- The Green integral is homogeneous in its forcing term. -/
@[simp]
theorem greenIntegral_smul (c : ℝ) (g : ℝ → X) (t : ℝ) :
    greenIntegral A P (c • g) t = c • greenIntegral A P g t := by
  simp only [greenIntegral_def, Pi.smul_apply, map_smul, ← smul_sub, integral_smul]

omit [CompleteSpace X] in
/-- The Green integral commutes with negation of the forcing term. -/
@[simp]
theorem greenIntegral_neg (g : ℝ → X) (t : ℝ) :
    greenIntegral A P (-g) t = -greenIntegral A P g t := by
  simpa using greenIntegral_smul (A := A) (P := P) (-1) g t

section Additivity

variable {g₁ g₂ : ℝ → X} {M₁ M₂ : ℝ}
  (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α) (hg₁ : Continuous g₁) (hg₁M : ∀ s, ‖g₁ s‖ ≤ M₁) (hg₂ : Continuous g₂)
  (hg₂M : ∀ s, ‖g₂ s‖ ≤ M₂)
include hs hu hα hg₁ hg₁M hg₂ hg₂M

/-- Under an exponential dichotomy, the Green integral is additive on continuous bounded forcing
terms. -/
theorem greenIntegral_add (t : ℝ) :
    greenIntegral A P (g₁ + g₂) t = greenIntegral A P g₁ t + greenIntegral A P g₂ t := by
  have hstable (s : ℝ) : exp ((t - s) • A) (P ((g₁ + g₂) s)) =
      exp ((t - s) • A) (P (g₁ s)) + exp ((t - s) • A) (P (g₂ s)) := by
    simp only [Pi.add_apply, map_add]
  have hunstable (s : ℝ) : exp ((t - s) • A) ((g₁ + g₂) s - P ((g₁ + g₂) s)) =
      exp ((t - s) • A) (g₁ s - P (g₁ s)) + exp ((t - s) • A) (g₂ s - P (g₂ s)) := by
    simp only [Pi.add_apply, map_add, map_sub]
    abel
  simp only [greenIntegral_def, hstable, hunstable]
  rw [integral_add (integrableOn_greenIntegral_stable hs hα hg₁ hg₁M t)
      (integrableOn_greenIntegral_stable hs hα hg₂ hg₂M t),
    integral_add (integrableOn_lyapunovPerron_unstable hu hα t hg₁.continuousOn fun s _ ↦ hg₁M s)
      (integrableOn_lyapunovPerron_unstable hu hα t hg₂.continuousOn fun s _ ↦ hg₂M s)]
  abel

/-- Under an exponential dichotomy, the Green integral commutes with subtraction of continuous
bounded forcing terms. -/
theorem greenIntegral_sub (t : ℝ) :
    greenIntegral A P (g₁ - g₂) t = greenIntegral A P g₁ t - greenIntegral A P g₂ t := by
  rw [sub_eq_add_neg, greenIntegral_add hs hu hα hg₁ hg₁M hg₂.neg (M₂ := M₂) (by simpa using hg₂M),
    greenIntegral_neg, sub_eq_add_neg]

end Additivity

/-- The Green integral differs from the Lyapunov--Perron integral by the free solution
`exp (t A) c` with `c = ∫_{s ≤ 0} exp (-s A) (P (g s)) ds`. -/
private theorem greenIntegral_eq_lyapunovPerronIntegral_add
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) (t : ℝ) :
    greenIntegral A P g t = lyapunovPerronIntegral A P g t +
      exp (t • A) (∫ s in Iic 0, exp ((-s) • A) (P (g s))) := by
  set h : ℝ → X := fun s ↦ exp ((-s) • A) (P (g s)) with h_def
  have hint := integrableOn_exp_neg_smul_apply_Iic hs hα hg hgM
  have hpull (s : ℝ) : exp ((t - s) • A) (P (g s)) = exp (t • A) (h s) := by
    simp only [h_def, ← ContinuousLinearMap.exp_add_smul_apply, sub_eq_add_neg]
  have hIic : (∫ s in Iic t, exp ((t - s) • A) (P (g s))) =
      exp (t • A) (∫ s in Iic t, h s) := by
    simp only [hpull]
    exact (exp (t • A)).integral_comp_comm (hint t)
  have hIcc : (∫ s in (0 : ℝ)..t, exp ((t - s) • A) (P (g s))) =
      exp (t • A) (∫ s in (0 : ℝ)..t, h s) := by
    simp only [hpull]
    exact (exp (t • A)).intervalIntegral_comp_comm
      (((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_apply
        (P.continuous.comp hg) |>.intervalIntegrable _ _)
  have hsplit : (∫ s in Iic t, h s) = (∫ s in Iic 0, h s) + ∫ s in (0 : ℝ)..t, h s := by
    rw [← intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint t), add_sub_cancel]
  rw [greenIntegral_def, lyapunovPerronIntegral_def, hIic, hIcc, hsplit, map_add]
  abel

/-- **The Green integral solves the forced equation.** Under an exponential dichotomy, for a
continuous bounded forcing term `g`, the Green integral solves `u' = A u + g`. -/
theorem hasDerivAt_greenIntegral
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) (t : ℝ) :
    HasDerivAt (greenIntegral A P g) (A (greenIntegral A P g t) + g t) t := by
  set c := ∫ s in Iic 0, exp ((-s) • A) (P (g s))
  have hfun : greenIntegral A P g = fun t ↦ lyapunovPerronIntegral A P g t + exp (t • A) c :=
    funext (greenIntegral_eq_lyapunovPerronIntegral_add hs hα hg hgM)
  have hfree : HasDerivAt (fun t ↦ exp (t • A) c) (A (exp (t • A) c)) t := by
    simpa using (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t c)
  rw [hfun]
  refine ((hasDerivAt_lyapunovPerronIntegral hu hα hg hgM t).add hfree).congr_deriv ?_
  rw [map_add]
  abel

/-- Under an exponential dichotomy, the Green integral of a continuous bounded forcing term is
continuous. -/
theorem continuous_greenIntegral
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M) :
    Continuous (greenIntegral A P g) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_greenIntegral hs hu hα hg hgM t).continuousAt

/-! ### Pointwise and `Lᵖ` bounds -/

section Bounds

variable (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
include hs hu

omit [CompleteSpace X] in
/-- Under an exponential dichotomy, the Green integral is bounded pointwise by the integral of
`‖g‖` against the kernel `K exp (-α |t - s|)`. No integrability of `g` is needed. -/
theorem enorm_greenIntegral_le (g : ℝ → X) (t : ℝ) :
    ‖greenIntegral A P g t‖ₑ ≤
      ∫⁻ s, ENNReal.ofReal (K * Real.exp (-(α * |t - s|))) * ‖g s‖ₑ := by
  set k : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (K * Real.exp (-(α * |t - s|))) * ‖g s‖ₑ
  have h₁ : ‖∫ s in Iic t, exp ((t - s) • A) (P (g s))‖ₑ ≤ ∫⁻ s in Iic t, k s := by
    refine (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono_ae ((ae_restrict_mem measurableSet_Iic).mono fun s hst ↦ ?_))
    have hts : 0 ≤ t - s := sub_nonneg.2 hst
    calc ‖exp ((t - s) • A) (P (g s))‖ₑ = ENNReal.ofReal ‖exp ((t - s) • A) (P (g s))‖ := by
          rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (K * Real.exp (-(α * |t - s|)) * ‖g s‖) :=
          ENNReal.ofReal_le_ofReal ((hs _ hts _).trans_eq (by rw [abs_of_nonneg hts, neg_mul]))
      _ = k s := by rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
  have h₂ : ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖ₑ ≤ ∫⁻ s in Ioi t, k s := by
    refine (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono fun s hst ↦ ?_))
    have hts : t - s < 0 := sub_neg.2 hst
    calc ‖exp ((t - s) • A) (g s - P (g s))‖ₑ =
          ENNReal.ofReal ‖exp ((t - s) • A) (g s - P (g s))‖ := by rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (K * Real.exp (-(α * |t - s|)) * ‖g s‖) :=
          ENNReal.ofReal_le_ofReal
            ((hu _ hts.le _).trans_eq (by rw [abs_of_neg hts, mul_neg, neg_neg]))
      _ = k s := by rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]
  calc ‖greenIntegral A P g t‖ₑ
      ≤ ‖∫ s in Iic t, exp ((t - s) • A) (P (g s))‖ₑ +
          ‖∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))‖ₑ := enorm_sub_le
    _ ≤ (∫⁻ s in Iic t, k s) + ∫⁻ s in Ioi t, k s := add_le_add h₁ h₂
    _ = ∫⁻ s, k s := by rw [← compl_Iic, lintegral_add_compl _ measurableSet_Iic]

/-- **The Green integral is bounded on `Lᵖ`.** Under an exponential dichotomy with constant `K`
and rate `α > 0`, `‖G g‖_{Lᵖ} ≤ 2 K / α ‖g‖_{Lᵖ}` for every continuous bounded `g` and every
`1 ≤ p ≤ ∞`. This is Schur's test for
the kernel `K exp (-α |t - s|)`, whose row and column integrals are `2 K / α`. -/
theorem eLpNorm_greenIntegral_le (hα : 0 < α) (hg : Continuous g) (hgM : ∀ s, ‖g s‖ ≤ M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (greenIntegral A P g) p volume ≤ ENNReal.ofReal (2 * K / α) * eLpNorm g p volume := by
  set k : ℝ → ℝ → ℝ≥0∞ := fun t s ↦ ENNReal.ofReal (K * Real.exp (-(α * |t - s|)))
  have hk : AEMeasurable (Function.uncurry k) (volume.prod volume) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.sub continuous_snd).abs).neg))).measurable.aemeasurable
  have hrow (t : ℝ) : ∫⁻ s, k t s ≤ ENNReal.ofReal (2 * K / α) :=
    (lintegral_sub_left_eq_self (fun x ↦ ENNReal.ofReal (K * Real.exp (-(α * |x|)))) t).trans
      (TauCeti.lintegral_ofReal_mul_exp_neg_mul_abs (NNReal.coe_pos.2 hα) K) |>.le
  have hcol (s : ℝ) : ∫⁻ t, k t s ≤ ENNReal.ofReal (2 * K / α) :=
    (lintegral_sub_right_eq_self (fun x ↦ ENNReal.ofReal (K * Real.exp (-(α * |x|)))) s).trans
      (TauCeti.lintegral_ofReal_mul_exp_neg_mul_abs (NNReal.coe_pos.2 hα) K) |>.le
  have hexp : (1 - p.toReal⁻¹) + p.toReal⁻¹ = 1 := sub_add_cancel _ _
  calc eLpNorm (greenIntegral A P g) p volume
      ≤ eLpNorm (fun t ↦ ∫⁻ s, k t s * ‖g s‖ₑ) p volume :=
        eLpNorm_mono_enorm (continuous_greenIntegral hs hu hα hg hgM).aestronglyMeasurable
          fun t ↦ by simpa only [enorm_eq_self] using enorm_greenIntegral_le hs hu g t
    _ ≤ ENNReal.ofReal (2 * K / α) ^ (1 - p.toReal⁻¹) *
          ENNReal.ofReal (2 * K / α) ^ p.toReal⁻¹ * eLpNorm (fun s ↦ ‖g s‖ₑ) p volume :=
        TauCeti.eLpNorm_lintegral_mul_le hk hg.aestronglyMeasurable.enorm hp (ae_of_all _ hrow)
          (ae_of_all _ hcol)
    _ = ENNReal.ofReal (2 * K / α) * eLpNorm g p volume := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (TauCeti.one_sub_toReal_inv_nonneg hp)
        (inv_nonneg.2 ENNReal.toReal_nonneg), hexp, ENNReal.rpow_one,
        eLpNorm_enorm _ hg.aestronglyMeasurable]

end Bounds

/-- **The Green integral inverts `d/ds - A` on compactly supported paths.** If `P` commutes with
`A`, then every compactly supported `C¹` path `u` is the Green integral of `u' - A u`. No
dichotomy estimate is needed: both half-line integrals are integrals of derivatives of
compactly supported paths. -/
theorem greenIntegral_deriv_sub_eq (hAP : Commute A P) {u : ℝ → X}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (t : ℝ) :
    greenIntegral A P (fun s ↦ deriv u s - A (u s)) t = u t := by
  set g : ℝ → X := fun s ↦ deriv u s - A (u s) with g_def
  have hgc : Continuous g := (hu.continuous_deriv le_rfl).sub (A.continuous.comp hu.continuous)
  have hgs : HasCompactSupport g := huc.deriv.sub (huc.comp_left (map_zero A))
  -- `exp (r A)` commutes with `A` and with `P`.
  have hcA (r : ℝ) (v : X) : exp (r • A) (A v) = A (exp (r • A) v) := by
    rw [← mul_apply_eq_comp, ((Commute.refl A).smul_right r).exp_right.eq.symm,
      mul_apply_eq_comp]
  have hexp (s : ℝ) : HasDerivAt (fun s ↦ exp ((t - s) • A)) (-(A * exp ((t - s) • A))) s := by
    simpa [Function.comp_def] using
      (hasDerivAt_exp_smul_const' A (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
  -- Each half-line integrand is the derivative of a compactly supported path.
  have hcont (L : X →L[ℝ] X) : Continuous fun s ↦ exp ((t - s) • A) (L (g s)) :=
    ((differentiable_exp_smul_const ℝ A).continuous.comp
      (continuous_const.sub continuous_id)).clm_apply (L.continuous.comp hgc)
  have hsupp (L : X →L[ℝ] X) {w : ℝ → X} (hw : HasCompactSupport w) :
      HasCompactSupport fun s ↦ exp ((t - s) • A) (L (w s)) :=
    hw.mono fun s hs hw0 ↦ hs (by simp [hw0])
  have htendsto (L : X →L[ℝ] X) (l : Filter ℝ) (hl : l ≤ Filter.cocompact ℝ) :
      Tendsto (fun s ↦ exp ((t - s) • A) (L (u s))) l (𝓝 0) := by
    have h := hsupp L huc
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h
    exact (h.filter_mono hl).tendsto
  have hderiv (L : X →L[ℝ] X) (hL : Commute A L) (s : ℝ) :
      HasDerivAt (fun s ↦ exp ((t - s) • A) (L (u s))) (exp ((t - s) • A) (L (g s))) s := by
    refine ((hexp s).clm_apply (L.hasFDerivAt.comp_hasDerivAt s
      ((hu.differentiable one_ne_zero s).hasDerivAt))).congr_deriv ?_
    rw [g_def, map_sub, map_sub, ← mul_apply_eq_comp L A, ← hL.eq, mul_apply_eq_comp, hcA]
    simp only [neg_apply, mul_apply_eq_comp, Function.comp_apply]
    abel
  have hstable : (∫ s in Iic t, exp ((t - s) • A) (P (g s))) = P (u t) := by
    rw [integral_Iic_of_hasDerivAt_of_tendsto' (a := t) (fun s _ ↦ hderiv P hAP s)
      ((hcont P).integrable_of_hasCompactSupport (hsupp P hgs)).integrableOn
      (htendsto P atBot atBot_le_cocompact)]
    simp
  have hunstable : (∫ s in Ioi t, exp ((t - s) • A) (g s - P (g s))) = -(u t - P (u t)) := by
    have hL : Commute A (1 - P) := (Commute.one_right A).sub_right hAP
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := t) (fun s _ ↦ hderiv (1 - P) hL s)
      ((hcont (1 - P)).integrable_of_hasCompactSupport (hsupp (1 - P) hgs)).integrableOn
      (htendsto (1 - P) atTop atTop_le_cocompact)
    simpa using h
  rw [greenIntegral_def, hstable, hunstable]
  abel

end ContinuousLinearMap
