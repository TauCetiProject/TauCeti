/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.Prod

/-!
# The Green integral of an expanding scalar coefficient

Let `b : ℝ → ℝ` be a scalar coefficient whose equation `v' = b v` has a positive solution `g`
that grows at a uniform exponential rate: for constants `K` and `α > 0`,

`g s ≤ K exp (-α (t - s)) g t` whenever `s ≤ t`.

Then every solution of `v' = b v` other than `0` grows exponentially at `+∞`, and for a forcing
term `f` with values in a real Banach space `E` the forced equation `u' = b u + f` is solved by

`G f (s) = -g s ∫_{t > s} f t / g t dt = -∫_{t > s} (g s / g t) f t dt`

(`TauCeti.scalarGreenIntegral`), which propagates the forcing term backward from `+∞`. Its kernel
is bounded by `K exp (-α |s - t|)`, so for a measurable `g` and every a.e.-strongly measurable `f`,
`‖G f‖_{Lᵖ} ≤ 2 K / α ‖f‖_{Lᵖ}` for `1 ≤ p ≤ ∞` (`TauCeti.eLpNorm_scalarGreenIntegral_le`). For
a continuous bounded forcing term `f`, `G f` solves `u' = b u + f`
(`TauCeti.hasDerivAt_scalarGreenIntegral`). Conversely, `G` recovers every compactly supported
`C¹` path `u` from `u' - b u` (`TauCeti.scalarGreenIntegral_deriv_sub_eq`), which needs no growth
bound.

The application to the trajectory operator `d/ds - b(s)` on `W^{1,p}(ℝ, E)` is in
`TauCeti.Analysis.ODE.TrajectoryOperator.ScalarGreen`. This is the case of a coefficient with an
exponential dichotomy whose stable part is zero, with a time-dependent coefficient; the
constant-coefficient case with a general dichotomy is `TauCeti.Analysis.ODE.GreenIntegral`.

## Main declarations

* `TauCeti.scalarGreenIntegral`: the Green integral `-g s ∫_{t > s} f t / g t dt`.
* `TauCeti.scalarGreenIntegral_add` and `TauCeti.scalarGreenIntegral_sub`: additivity at `s` for
  forcing terms `f` with `f / g` integrable on `(s, ∞)`, which holds under the growth bound for
  every `f ∈ Lᵖ` (`TauCeti.integrableOn_inv_smul_Ioi`).
* `TauCeti.hasDerivAt_scalarGreenIntegral`: for continuous bounded `f`, it solves `u' = b u + f`.
* `TauCeti.eLpNorm_scalarGreenIntegral_le`: the bound `‖G f‖_{Lᵖ} ≤ 2 K / α ‖f‖_{Lᵖ}`, and
  `TauCeti.eLpNorm_scalarGreenIntegral_sub_le`, the resulting Lipschitz bound on `Lᵖ`.
* `TauCeti.scalarGreenIntegral_deriv_sub_eq`: `G (u' - b u) = u` for compactly supported `C¹`
  paths `u`.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics **629**,
  Springer (1978) (exponential dichotomies and the Green function of `u' = A(t) u + f`).
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Green integral `G f (s) = -g s ∫_{t > s} f t / g t dt` of the forcing term `f` for a scalar
fundamental solution `g`. When `E` is complete, `g` is a positive solution of `v' = b v` growing
at a uniform exponential rate and `f` is continuous and bounded, it solves `u' = b u + f`
(`TauCeti.hasDerivAt_scalarGreenIntegral`). -/
def scalarGreenIntegral (g : ℝ → ℝ) (f : ℝ → E) (s : ℝ) : E :=
  -(g s • ∫ t in Ioi s, (g t)⁻¹ • f t)

theorem scalarGreenIntegral_def (g : ℝ → ℝ) (f : ℝ → E) (s : ℝ) :
    scalarGreenIntegral g f s = -(g s • ∫ t in Ioi s, (g t)⁻¹ • f t) := (rfl)

/-- The Green integral as an integral against the kernel `g s / g t` on `t > s`. -/
theorem scalarGreenIntegral_eq_neg_integral (g : ℝ → ℝ) (f : ℝ → E) (s : ℝ) :
    scalarGreenIntegral g f s = -∫ t in Ioi s, (g s / g t) • f t := by
  rw [scalarGreenIntegral_def, ← integral_smul]
  simp only [smul_smul, div_eq_mul_inv]

/-- The Green integral of the zero forcing term vanishes. -/
@[simp]
theorem scalarGreenIntegral_zero (g : ℝ → ℝ) (s : ℝ) : scalarGreenIntegral g (0 : ℝ → E) s = 0 := by
  simp [scalarGreenIntegral_def]

/-- The Green integral is homogeneous in its forcing term. -/
@[simp]
theorem scalarGreenIntegral_smul (g : ℝ → ℝ) (c : ℝ) (f : ℝ → E) (s : ℝ) :
    scalarGreenIntegral g (c • f) s = c • scalarGreenIntegral g f s := by
  simp only [scalarGreenIntegral_def, Pi.smul_apply, smul_comm _ c, integral_smul, smul_neg]

/-- The Green integral commutes with negation of the forcing term. -/
@[simp]
theorem scalarGreenIntegral_neg (g : ℝ → ℝ) (f : ℝ → E) (s : ℝ) :
    scalarGreenIntegral g (-f) s = -scalarGreenIntegral g f s := by
  simpa using scalarGreenIntegral_smul g (-1) f s

/-- The Green integral at `s` depends only on the almost-everywhere class of the forcing term on
`(s, ∞)`. -/
theorem scalarGreenIntegral_congr_ae (g : ℝ → ℝ) {f₁ f₂ : ℝ → E} {s : ℝ}
    (h : f₁ =ᵐ[volume.restrict (Ioi s)] f₂) :
    scalarGreenIntegral g f₁ s = scalarGreenIntegral g f₂ s := by
  rw [scalarGreenIntegral_def, scalarGreenIntegral_def,
    integral_congr_ae (h.mono fun t ht ↦ by rw [ht])]

section Additivity

variable {g : ℝ → ℝ} {f₁ f₂ : ℝ → E} {s : ℝ}

/-- The Green integral is additive at `s` on forcing terms `f` for which `t ↦ f t / g t` is
integrable on `(s, ∞)`. -/
theorem scalarGreenIntegral_add (hf₁ : IntegrableOn (fun t ↦ (g t)⁻¹ • f₁ t) (Ioi s))
    (hf₂ : IntegrableOn (fun t ↦ (g t)⁻¹ • f₂ t) (Ioi s)) :
    scalarGreenIntegral g (f₁ + f₂) s =
      scalarGreenIntegral g f₁ s + scalarGreenIntegral g f₂ s := by
  simp only [scalarGreenIntegral_def, Pi.add_apply, smul_add]
  rw [integral_add hf₁ hf₂, smul_add, neg_add]

/-- The Green integral commutes at `s` with subtraction of forcing terms `f` for which
`t ↦ f t / g t` is integrable on `(s, ∞)`. -/
theorem scalarGreenIntegral_sub (hf₁ : IntegrableOn (fun t ↦ (g t)⁻¹ • f₁ t) (Ioi s))
    (hf₂ : IntegrableOn (fun t ↦ (g t)⁻¹ • f₂ t) (Ioi s)) :
    scalarGreenIntegral g (f₁ - f₂) s =
      scalarGreenIntegral g f₁ s - scalarGreenIntegral g f₂ s := by
  have hf₂' : IntegrableOn (fun t ↦ (g t)⁻¹ • (-f₂) t) (Ioi s) := by
    simp only [Pi.neg_apply, smul_neg]
    exact hf₂.neg
  rw [sub_eq_add_neg, scalarGreenIntegral_add hf₁ hf₂', scalarGreenIntegral_neg, sub_eq_add_neg]

end Additivity

/-- The Green integral of an a.e.-strongly measurable forcing term for a measurable `g` is
a.e.-strongly measurable. -/
theorem aestronglyMeasurable_scalarGreenIntegral {g : ℝ → ℝ} {f : ℝ → E} (hg : AEMeasurable g)
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (scalarGreenIntegral g f) := by
  have hF : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ (g z.2)⁻¹ • f z.2) (volume.prod volume) :=
    (hg.inv.aestronglyMeasurable.smul hf).comp_snd
  have hI := aestronglyMeasurable_setIntegral_of_measurableSet (K := fun _ s ↦ (g s)⁻¹ • f s) hF
    (R := fun s t ↦ s < t) (measurableSet_lt measurable_fst measurable_snd)
  simp only [Set.Ioi_def] at hI
  refine (hg.aestronglyMeasurable.smul hI).neg.congr (ae_of_all _ fun s ↦ ?_)
  simp only [Pi.neg_apply, Pi.smul_apply', scalarGreenIntegral_def]

/-- **The Green integral recovers compactly supported paths.** If `g` is a positive solution of
`v' = b v` for a continuous coefficient `b`, then every compactly supported `C¹` path `u` in a
real Banach space is the Green integral of `u' - b u`. No growth of `g` is needed: the integrand is
the derivative of the compactly supported path `t ↦ u t / g t`. -/
theorem scalarGreenIntegral_deriv_sub_eq [CompleteSpace E] {g b : ℝ → ℝ} (hb : Continuous b)
    (hg : ∀ s, HasDerivAt g (b s * g s) s) (hpos : ∀ s, 0 < g s) {u : ℝ → E}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (s : ℝ) :
    scalarGreenIntegral g (fun t ↦ deriv u t - b t • u t) s = u s := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s ↦ (hg s).continuousAt
  have hinv (t : ℝ) : HasDerivAt (fun t ↦ (g t)⁻¹) (-b t * (g t)⁻¹) t := by
    convert (hg t).inv (hpos t).ne' using 1
    field_simp [(hpos t).ne']
  -- The integrand is the derivative of the compactly supported path `t ↦ (g t)⁻¹ • u t`.
  have hderiv (t : ℝ) : HasDerivAt (fun t ↦ (g t)⁻¹ • u t)
      ((g t)⁻¹ • (deriv u t - b t • u t)) t := by
    convert (hinv t).smul (hu.differentiable one_ne_zero t).hasDerivAt using 1
    module
  have hcont : Continuous fun t ↦ (g t)⁻¹ • (deriv u t - b t • u t) :=
    (hgc.inv₀ fun t ↦ (hpos t).ne').smul
      ((hu.continuous_deriv le_rfl).sub (hb.smul hu.continuous))
  have hw : ContDiff ℝ 1 fun t ↦ (g t)⁻¹ • u t :=
    contDiff_one_iff_deriv.2 ⟨fun t ↦ (hderiv t).differentiableAt,
      (funext fun t ↦ (hderiv t).deriv) ▸ hcont⟩
  have hI := HasCompactSupport.integral_Ioi_deriv_eq hw huc.smul_left s
  simp only [fun t ↦ (hderiv t).deriv] at hI
  rw [scalarGreenIntegral_def, hI, smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ (hpos s).ne',
    one_smul]

section Growth

variable {g b : ℝ → ℝ} {K α M : ℝ} {f : ℝ → E}

/-- Under the growth bound, `1 / g` decays at the same exponential rate. -/
private theorem inv_le_mul_exp_mul_inv (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) {s t : ℝ} (hst : s ≤ t) :
    (g t)⁻¹ ≤ K * Real.exp (-α * (t - s)) * (g s)⁻¹ := by
  calc (g t)⁻¹ = g s / g t * (g s)⁻¹ := by field_simp [(hpos s).ne']
    _ ≤ K * Real.exp (-α * (t - s)) * (g s)⁻¹ :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ (hpos t)).2 (hK s t hst))
        (inv_nonneg.2 (hpos s).le)

/-- For a positive `g` with the growth bound `g s ≤ K exp (-α (t - s)) g t` for `s ≤ t`, the
growth constant `K` is at least `1`, by the bound at `s = t`. -/
theorem one_le_of_scalarGrowth (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) : 1 ≤ K := by
  have h := hK 0 0 le_rfl
  rw [sub_self, mul_zero, Real.exp_zero, mul_one] at h
  exact (le_mul_iff_one_le_left (hpos 0)).1 h

/-- Under the growth bound, `1 / g` lies in every `Lᵖ` of a half-line `(c, ∞)`. -/
private theorem memLp_inv_Ioi (hg : AEMeasurable g) (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (hα : 0 < α) (c : ℝ)
    (q : ℝ≥0∞) : MemLp (fun t ↦ (g t)⁻¹) q (volume.restrict (Ioi c)) := by
  have hK0 : 0 ≤ K := zero_le_one.trans (one_le_of_scalarGrowth hpos hK)
  refine ((memLp_exp_neg_mul_Ioi hα c q).const_mul (K * Real.exp (α * c) * (g c)⁻¹)).of_le
    hg.inv.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have := hpos c
  rw [Real.norm_of_nonneg (inv_nonneg.2 (hpos t).le), Real.norm_of_nonneg (by positivity)]
  calc (g t)⁻¹ ≤ K * Real.exp (-α * (t - c)) * (g c)⁻¹ := inv_le_mul_exp_mul_inv hpos hK ht.out.le
    _ = K * Real.exp (α * c) * (g c)⁻¹ * Real.exp (-α * t) := by
      rw [show -α * (t - c) = α * c + -α * t by ring, Real.exp_add]
      ring

/-- Under the growth bound, `t ↦ f t / g t` is integrable on a half-line `(c, ∞)` whenever `f`
lies in `Lᵖ` of that half-line for some `1 ≤ p ≤ ∞`: `1 / g` lies in the dual exponent. -/
theorem integrableOn_inv_smul_Ioi (hg : AEMeasurable g) (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (hα : 0 < α)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ} (hf : MemLp f p (volume.restrict (Ioi c))) :
    IntegrableOn (fun t ↦ (g t)⁻¹ • f t) (Ioi c) :=
  memLp_one_iff_integrable.1 <|
    (memLp_inv_Ioi hg hpos hK hα c (ENNReal.conjExponent p)).smul hf (r := 1)

/-- **The Green integral solves the forced equation.** If `g` is a positive solution of
`v' = b v` with `g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`, then for a continuous
bounded forcing term `f` in a real Banach space the Green integral solves `u' = b u + f`. -/
theorem hasDerivAt_scalarGreenIntegral [CompleteSpace E] (hg : ∀ s, HasDerivAt g (b s * g s) s)
    (hpos : ∀ s, 0 < g s) (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t)
    (hα : 0 < α) (hf : Continuous f) (hfM : ∀ t, ‖f t‖ ≤ M) (s : ℝ) :
    HasDerivAt (scalarGreenIntegral g f) (b s • scalarGreenIntegral g f s + f s) s := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s ↦ (hg s).continuousAt
  have hhc : Continuous fun t ↦ (g t)⁻¹ • f t := (hgc.inv₀ fun t ↦ (hpos t).ne').smul hf
  have hIderiv : HasDerivAt (fun x ↦ ∫ t in Ioi x, (g t)⁻¹ • f t) (-((g s)⁻¹ • f s)) s :=
    (integrableOn_inv_smul_Ioi hgc.aemeasurable hpos hK hα (p := ∞) (c := s - 1)
      ((memLp_top_of_bound hf.aestronglyMeasurable M (ae_of_all _ hfM)).restrict _)
      ).hasDerivAt_integral_Ioi hhc.continuousAt (sub_one_lt s)
  refine ((hg s).smul hIderiv).neg.congr_deriv ?_
  simp only [scalarGreenIntegral_def, smul_neg, smul_smul, mul_inv_cancel₀ (hpos s).ne',
    one_smul]
  abel

/-- Under the growth bound, the Green integral of a continuous bounded forcing term is
continuous. -/
theorem continuous_scalarGreenIntegral [CompleteSpace E] (hg : ∀ s, HasDerivAt g (b s * g s) s)
    (hpos : ∀ s, 0 < g s) (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t)
    (hα : 0 < α) (hf : Continuous f) (hfM : ∀ t, ‖f t‖ ≤ M) :
    Continuous (scalarGreenIntegral g f) :=
  continuous_iff_continuousAt.2 fun s ↦
    (hasDerivAt_scalarGreenIntegral hg hpos hK hα hf hfM s).continuousAt

/-- Under the growth bound, the Green integral is bounded pointwise by the integral of `‖f‖`
against the kernel `K exp (-α |s - t|)`. No integrability of `f` is needed. -/
theorem enorm_scalarGreenIntegral_le (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (f : ℝ → E) (s : ℝ) :
    ‖scalarGreenIntegral g f s‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal (K * Real.exp (-(α * |s - t|))) * ‖f t‖ₑ := by
  rw [scalarGreenIntegral_eq_neg_integral, eNorm_neg]
  refine (eNorm_integral_le_lintegral_eNorm _).trans
    ((lintegral_mono_ae ?_).trans (setLIntegral_le_lintegral _ _))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t hst
  have hk : g s / g t ≤ K * Real.exp (-(α * |s - t|)) :=
    calc g s / g t ≤ K * Real.exp (-α * (t - s)) := (div_le_iff₀ (hpos t)).2 (hK s t hst.le)
      _ = K * Real.exp (-(α * |s - t|)) := by
        rw [abs_of_nonpos (sub_nonpos.2 hst.le)]
        ring_nf
  rw [eNorm_smul, Real.eNorm_eq_ofReal (div_pos (hpos s) (hpos t)).le]
  gcongr

/-- **The Green integral is bounded on `Lᵖ`.** If `g` is a measurable positive function with
`g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`, then `‖G f‖_{Lᵖ} ≤ 2 K / α ‖f‖_{Lᵖ}` for
every a.e.-strongly measurable `f` and every `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_scalarGreenIntegral_le (hg : AEMeasurable g) (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (hα : 0 < α)
    (hf : AEStronglyMeasurable f) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (scalarGreenIntegral g f) p volume ≤ ENNReal.ofReal (2 * K / α) * eLpNorm f p volume :=
  eLpNorm_le_of_enorm_le_lintegral_exp_neg_mul_abs hα K
    (aestronglyMeasurable_scalarGreenIntegral hg hf) hf
    (ae_of_all _ (enorm_scalarGreenIntegral_le hpos hK f)) hp

/-- **The Green integral is Lipschitz on `Lᵖ`.** Under the growth bound, for forcing terms
`f₁, f₂ ∈ Lᵖ` with `1 ≤ p ≤ ∞`, `‖G f₁ - G f₂‖_{Lᵖ} ≤ 2 K / α ‖f₁ - f₂‖_{Lᵖ}`. -/
theorem eLpNorm_scalarGreenIntegral_sub_le (hg : AEMeasurable g) (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (hα : 0 < α)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f₁ f₂ : ℝ → E} (hf₁ : MemLp f₁ p) (hf₂ : MemLp f₂ p) :
    eLpNorm (scalarGreenIntegral g f₁ - scalarGreenIntegral g f₂) p volume ≤
      ENNReal.ofReal (2 * K / α) * eLpNorm (f₁ - f₂) p volume := by
  have hsub : scalarGreenIntegral g f₁ - scalarGreenIntegral g f₂ =
      scalarGreenIntegral g (f₁ - f₂) := funext fun s ↦ by
    rw [Pi.sub_apply, scalarGreenIntegral_sub
      (integrableOn_inv_smul_Ioi hg hpos hK hα (hf₁.restrict _))
      (integrableOn_inv_smul_Ioi hg hpos hK hα (hf₂.restrict _))]
  rw [hsub]
  exact eLpNorm_scalarGreenIntegral_le hg hpos hK hα
    (hf₁.aestronglyMeasurable.sub hf₂.aestronglyMeasurable) Fact.out

end Growth

end TauCeti
