/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.APriori
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The Green integral of an expanding scalar coefficient

Let `b : ℝ → ℝ` be a scalar coefficient whose equation `v' = b v` has a positive solution `g`
that grows at a uniform exponential rate: for constants `K` and `α > 0`,

`g s ≤ K exp (-α (t - s)) g t` whenever `s ≤ t`.

Then every solution of `v' = b v` other than `0` grows exponentially at `+∞`, and the forced
equation `u' = b u + f` has the bounded solution

`G f (s) = -g s ∫_{t > s} f t / g t dt = -∫_{t > s} (g s / g t) f t dt`

(`TauCeti.scalarGreenIntegral`), which propagates the forcing term backward from `+∞`. Its kernel
is bounded by `K exp (-α |s - t|)`, so `G` is bounded on every `Lᵖ` with norm at most `2 K / α`
(`TauCeti.eLpNorm_scalarGreenIntegral_le`), and for a continuous bounded forcing term it solves
`u' = b u + f` (`TauCeti.hasDerivAt_scalarGreenIntegral`). Conversely, it recovers every compactly
supported `C¹` path `u` from `u' - b u` (`TauCeti.scalarGreenIntegral_deriv_sub_eq`), which needs
no growth bound.

For a finite-dimensional real normed space `E`, `1 ≤ p < ∞` and a continuous essentially bounded
`b`, this inverts the trajectory operator `d/ds - b(s) : W^{1,p}(ℝ, E) → Lᵖ(ℝ, E)`
(`TauCeti.WeakDerivStep.trajectoryOperator` of the `L∞` class `AL` of `-b(s) • id`, which exists
because `b` is essentially bounded): it satisfies `‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - b u‖_{Lᵖ}`, is
bijective, and its inverse sends a continuous compactly supported `f` to `G f`. This is the case
of a coefficient with an exponential dichotomy whose stable part is zero, with a time-dependent
coefficient; the constant-coefficient case with a general dichotomy is
`TauCeti.Analysis.ODE.TrajectoryOperator.Hyperbolic`. A typical coefficient is `b → 1` at both
ends, as for the operator on a neck glued from `d/ds + tanh` and `d/ds - tanh`
(`TauCeti.Analysis.ODE.TrajectoryOperator.Neck`).

## Main declarations

* `TauCeti.scalarGreenIntegral`: the Green integral `-g s ∫_{t > s} f t / g t dt`.
* `TauCeti.hasDerivAt_scalarGreenIntegral`: it solves `u' = b u + f`.
* `TauCeti.eLpNorm_scalarGreenIntegral_le`: the bound `‖G f‖_{Lᵖ} ≤ 2 K / α ‖f‖_{Lᵖ}`.
* `TauCeti.scalarGreenIntegral_deriv_sub_eq`: `G (u' - b u) = u` for compactly supported `C¹`
  paths `u`.
* `TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth` and
  `TauCeti.WeakDerivStep.norm_le_mul_norm_trajectoryOperator_of_scalarGrowth`: the a priori
  estimates for `d/ds - b` on `W^{1,p}(ℝ, E)`.
* `TauCeti.WeakDerivStep.bijective_trajectoryOperator_of_scalarGrowth`: `d/ds - b` is bijective.
* `TauCeti.WeakDerivStep.prev_ae_eq_scalarGreenIntegral_of_trajectoryOperator_ae_eq`: its inverse
  is the Green integral on continuous compactly supported forcing terms.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics **629**,
  Springer (1978) (exponential dichotomies and the Green function of `u' = A(t) u + f`).
* K. J. Palmer, *Exponential dichotomies and transversal homoclinic points*, J. Differential
  Equations **55** (1984), 225--256 (the operator `u ↦ u' - A(t) u` under exponential
  dichotomies).
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Green integral `G f (s) = -g s ∫_{t > s} f t / g t dt` of the forcing term `f` for a scalar
fundamental solution `g`. When `g` is a positive solution of `v' = b v` growing at a uniform
exponential rate and `f` is continuous and bounded, it is the bounded solution of `u' = b u + f`
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

/-- **The Green integral recovers compactly supported paths.** If `g` is a positive solution of
`v' = b v` for a continuous coefficient `b`, then every compactly supported `C¹` path `u` is the
Green integral of `u' - b u`. No growth of `g` is needed: the integrand is the derivative of the
compactly supported path `t ↦ u t / g t`. -/
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
  have hsupp : HasCompactSupport fun t ↦ (g t)⁻¹ • (deriv u t - b t • u t) :=
    (huc.deriv.sub huc.smul_left).smul_left
  have htendsto : Tendsto (fun t ↦ (g t)⁻¹ • u t) atTop (𝓝 0) := by
    have h : HasCompactSupport fun t ↦ (g t)⁻¹ • u t := huc.smul_left
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h
    exact (h.filter_mono atTop_le_cocompact).tendsto
  rw [scalarGreenIntegral_def, integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ ↦ hderiv t)
    (hcont.integrable_of_hasCompactSupport hsupp).integrableOn htendsto, zero_sub, smul_neg,
    neg_neg, smul_smul, mul_inv_cancel₀ (hpos s).ne', one_smul]

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

/-- The growth constant is at least `1`, by the growth bound at `s = t`. -/
private theorem one_le_of_growth (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) : 1 ≤ K := by
  have h := hK 0 0 le_rfl
  rw [sub_self, mul_zero, Real.exp_zero, mul_one] at h
  exact (le_mul_iff_one_le_left (hpos 0)).1 h

/-- Under the growth bound, `t ↦ f t / g t` is integrable on every half-line `(c, ∞)` for a
continuous bounded `f`. -/
private theorem integrableOn_inv_smul_Ioi (hgc : Continuous g) (hpos : ∀ s, 0 < g s)
    (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (hα : 0 < α)
    (hf : Continuous f) (hfM : ∀ t, ‖f t‖ ≤ M) (c : ℝ) :
    IntegrableOn (fun t ↦ (g t)⁻¹ • f t) (Ioi c) := by
  have hK0 : 0 ≤ K := zero_le_one.trans (one_le_of_growth hpos hK)
  have hcont : Continuous fun t ↦ (g t)⁻¹ • f t := (hgc.inv₀ fun t ↦ (hpos t).ne').smul hf
  refine ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hα) c).const_mul
    (K * Real.exp (α * c) * (g c)⁻¹ * M)).mono' hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hct : c ≤ t := le_of_lt ht
  calc ‖(g t)⁻¹ • f t‖ = (g t)⁻¹ * ‖f t‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hpos t).le)]
    _ ≤ K * Real.exp (-α * (t - c)) * (g c)⁻¹ * M :=
        mul_le_mul (inv_le_mul_exp_mul_inv hpos hK hct) (hfM t) (norm_nonneg _)
          (by have := hpos c; positivity)
    _ = K * Real.exp (α * c) * (g c)⁻¹ * M * Real.exp (-α * t) := by
        rw [show -α * (t - c) = α * c + -α * t by ring, Real.exp_add]
        ring

section Additivity

variable {f₁ f₂ : ℝ → E} {M₁ M₂ : ℝ} (hgc : Continuous g) (hpos : ∀ s, 0 < g s)
  (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (hα : 0 < α)
  (hf₁ : Continuous f₁) (hf₁M : ∀ t, ‖f₁ t‖ ≤ M₁) (hf₂ : Continuous f₂) (hf₂M : ∀ t, ‖f₂ t‖ ≤ M₂)
include hgc hpos hK hα hf₁ hf₁M hf₂ hf₂M

/-- Under the growth bound, the Green integral is additive on continuous bounded forcing
terms. -/
theorem scalarGreenIntegral_add (s : ℝ) :
    scalarGreenIntegral g (f₁ + f₂) s =
      scalarGreenIntegral g f₁ s + scalarGreenIntegral g f₂ s := by
  simp only [scalarGreenIntegral_def, Pi.add_apply, smul_add]
  rw [integral_add (integrableOn_inv_smul_Ioi hgc hpos hK hα hf₁ hf₁M s)
    (integrableOn_inv_smul_Ioi hgc hpos hK hα hf₂ hf₂M s), smul_add, neg_add]

/-- Under the growth bound, the Green integral commutes with subtraction of continuous bounded
forcing terms. -/
theorem scalarGreenIntegral_sub (s : ℝ) :
    scalarGreenIntegral g (f₁ - f₂) s =
      scalarGreenIntegral g f₁ s - scalarGreenIntegral g f₂ s := by
  rw [sub_eq_add_neg, scalarGreenIntegral_add hgc hpos hK hα hf₁ hf₁M hf₂.neg (M₂ := M₂)
    (by simpa using hf₂M), scalarGreenIntegral_neg, sub_eq_add_neg]

end Additivity

/-- **The Green integral solves the forced equation.** If `g` is a positive solution of
`v' = b v` with `g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`, then for a continuous
bounded forcing term `f` the Green integral solves `u' = b u + f`. -/
theorem hasDerivAt_scalarGreenIntegral [CompleteSpace E] (hg : ∀ s, HasDerivAt g (b s * g s) s)
    (hpos : ∀ s, 0 < g s) (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t)
    (hα : 0 < α) (hf : Continuous f) (hfM : ∀ t, ‖f t‖ ≤ M) (s : ℝ) :
    HasDerivAt (scalarGreenIntegral g f) (b s • scalarGreenIntegral g f s + f s) s := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s ↦ (hg s).continuousAt
  set h : ℝ → E := fun t ↦ (g t)⁻¹ • f t with h_def
  have hhc : Continuous h := (hgc.inv₀ fun t ↦ (hpos t).ne').smul hf
  have hint := integrableOn_inv_smul_Ioi hgc hpos hK hα hf hfM
  -- `∫_{t > x} h = ∫_{t > 0} h - ∫_0^x h`, whose derivative in `x` is `-h x`.
  have hI : (fun x ↦ ∫ t in Ioi x, h t) =
      fun x ↦ (∫ t in Ioi 0, h t) - ∫ t in (0 : ℝ)..x, h t := by
    funext x
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' (hint 0) (hint x), sub_sub_cancel]
  have hIderiv : HasDerivAt (fun x ↦ ∫ t in Ioi x, h t) (-h s) s := by
    rw [hI]
    exact (hhc.integral_hasStrictDerivAt 0 s).hasDerivAt.const_sub _
  refine ((hg s).smul hIderiv).neg.congr_deriv ?_
  simp only [scalarGreenIntegral_def, h_def, smul_neg, smul_smul, mul_inv_cancel₀ (hpos s).ne',
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

/-- **The Green integral is bounded on `Lᵖ`.** If `g` is a positive solution of `v' = b v` with
`g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`, then `‖G f‖_{Lᵖ} ≤ 2 K / α ‖f‖_{Lᵖ}` for
every continuous bounded `f` and every `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_scalarGreenIntegral_le [CompleteSpace E] (hg : ∀ s, HasDerivAt g (b s * g s) s)
    (hpos : ∀ s, 0 < g s) (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t)
    (hα : 0 < α) (hf : Continuous f) (hfM : ∀ t, ‖f t‖ ≤ M) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (scalarGreenIntegral g f) p volume ≤ ENNReal.ofReal (2 * K / α) * eLpNorm f p volume :=
  eLpNorm_le_of_enorm_le_lintegral_exp_neg_mul_abs hα K
    (continuous_scalarGreenIntegral hg hpos hK hα hf hfM).aestronglyMeasurable
    hf.aestronglyMeasurable (enorm_scalarGreenIntegral_le hpos hK f) hp

end Growth

end TauCeti

/-! ### The trajectory operator `d/ds - b(s)` on `W^{1,p}(ℝ, E)` -/

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {g b : ℝ → ℝ} {K α : ℝ}
  {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

section Growth

variable (hg : ∀ s, HasDerivAt g (b s * g s) s) (hpos : ∀ s, 0 < g s)
  (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (hα : 0 < α)
  (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
    fun s ↦ -b s • ContinuousLinearMap.id ℝ E)
include hg hpos hK hα hAL

/-- **The Green integral is a `W^{1,p}` solution.** If `g` is a positive solution of `v' = b v`
with `g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`, then for every continuous compactly
supported `f` and `1 ≤ p ≤ ∞`, some `u ∈ W^{1,p}(ℝ, E)` represented by the Green integral of `f`
solves `u' - b u = f`. The coefficient of the trajectory operator is any `L∞` class `AL` of
`-b(s) • id`. -/
theorem exists_prev_ae_eq_scalarGreenIntegral_and_trajectoryOperator_ae_eq [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ u : WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] scalarGreenIntegral g f ∧
        ⇑(trajectoryOperator AL u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hfp : MemLp f p volume := hf.memLp_of_hasCompactSupport hfc
  have hvp : MemLp (scalarGreenIntegral g f) p volume :=
    (eLpNorm_scalarGreenIntegral_le hg hpos hK hα hf hM Fact.out).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfp.eLpNorm_lt_top)
  obtain ⟨u, hu, hux⟩ := exists_trajectoryOperator_ae_eq_of_hasDerivAt hAL
    (fun s ↦ by simpa [add_comm] using hasDerivAt_scalarGreenIntegral hg hpos hK hα hf hM s)
    hvp hfp
  exact ⟨u, hux, hu⟩

variable [FiniteDimensional ℝ E]

/-- **The a priori estimate for `d/ds - b`.** Let `b` be continuous and essentially bounded, so
that `-b(s) • id` has an `L∞` class `AL`, and let `g` be a positive solution of `v' = b v` with
`g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`. Then for `1 ≤ p < ∞` every
`u ∈ W^{1,p}(ℝ, E)` satisfies `‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - b u‖_{Lᵖ}`. -/
theorem norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth (hb : Continuous b)
    (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖prev _ u‖ ≤ 2 * K / α * ‖trajectoryOperator AL u‖ := by
  have hK0 : 0 ≤ 2 * K / α :=
    div_nonneg (mul_nonneg zero_le_two (zero_le_one.trans (one_le_of_growth hpos hK))) hα.le
  -- On smooth compactly supported paths this is the `Lᵖ` bound for the Green integral.
  refine norm_prev_le_mul_norm_trajectoryOperator_of_forall_contDiff hp hAL hK0
    (fun φ hφ hφc ↦ ?_) u
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  set f : ℝ → E := fun s ↦ deriv φ s - b s • φ s with f_def
  have hfc : Continuous f := (hφ1.continuous_deriv le_rfl).sub (hb.smul hφ1.continuous)
  have hfs : HasCompactSupport f := hφc.deriv.sub hφc.smul_left
  have hG : scalarGreenIntegral g f = φ :=
    funext (scalarGreenIntegral_deriv_sub_eq hb hg hpos hφ1 hφc)
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have key := eLpNorm_scalarGreenIntegral_le hg hpos hK hα hfc hM (p := p) Fact.out
  have hf : (fun s ↦ deriv φ s + (-b s • ContinuousLinearMap.id ℝ E) (φ s)) = f := by
    funext s
    rw [f_def, smul_apply, ContinuousLinearMap.id_apply, neg_smul,
      ← sub_eq_add_neg]
  rwa [hG, ← hf] at key

/-- **The graph-norm estimate for `d/ds - b`.** Under the hypotheses of
`TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth`, every
`u ∈ W^{1,p}(ℝ, E)` satisfies `‖u‖ ≤ (1 + (1 + ‖AL‖) 2 K / α) ‖u' - b u‖_{Lᵖ}`, where `AL` is the
`L∞` class of `-b(s) • id`. -/
theorem norm_le_mul_norm_trajectoryOperator_of_scalarGrowth (hb : Continuous b) (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖u‖ ≤ (1 + (1 + ‖AL‖) * (2 * K / α)) * ‖trajectoryOperator AL u‖ :=
  norm_le_mul_norm_trajectoryOperator_of_norm_prev_le u
    (norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp u)

/-- **`d/ds - b` is injective.** Under the hypotheses of
`TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth`, `u' = b u` has
no nonzero solution in `W^{1,p}(ℝ, E)`. -/
theorem injective_trajectoryOperator_of_scalarGrowth (hb : Continuous b) (hp : p ≠ ∞) :
    Function.Injective (trajectoryOperator (p := p) AL) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu0 ↦ norm_le_zero_iff.1 ?_
  simpa [hu0] using norm_le_mul_norm_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp u

/-- **`d/ds - b` is surjective.** Under the hypotheses of
`TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth`, the equation
`u' - b u = f` has a solution `u ∈ W^{1,p}(ℝ, E)` for every `f ∈ Lᵖ(ℝ, E)`. -/
theorem surjective_trajectoryOperator_of_scalarGrowth (hb : Continuous b) (hp : p ≠ ∞) :
    Function.Surjective (trajectoryOperator (p := p) AL) :=
  surjective_trajectoryOperator_of_forall_norm_le hp
    (norm_le_mul_norm_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp) fun _ hf hfc ↦
      (exists_prev_ae_eq_scalarGreenIntegral_and_trajectoryOperator_ae_eq hg hpos hK hα hAL
        hf.continuous hfc).imp fun _ h ↦ h.2

/-- **`d/ds - b` is bijective.** Let `b` be continuous and essentially bounded, so that
`-b(s) • id` has an `L∞` class `AL`, and let `g` be a positive solution of `v' = b v` with
`g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`. Then for `1 ≤ p < ∞` the trajectory
operator `u ↦ u' - b u` with coefficient `AL` is a bijection from `W^{1,p}(ℝ, E)` onto
`Lᵖ(ℝ, E)`. -/
theorem bijective_trajectoryOperator_of_scalarGrowth (hb : Continuous b) (hp : p ≠ ∞) :
    Function.Bijective (trajectoryOperator (p := p) AL) :=
  ⟨injective_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp,
    surjective_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp⟩

/-- **The inverse of `d/ds - b` is the Green integral.** Under the hypotheses of
`TauCeti.WeakDerivStep.bijective_trajectoryOperator_of_scalarGrowth`, if `u ∈ W^{1,p}(ℝ, E)`
solves `u' - b u = f` for a continuous compactly supported `f`, then
`u s = -g s ∫_{t > s} f t / g t dt` for almost every `s`. -/
theorem prev_ae_eq_scalarGreenIntegral_of_trajectoryOperator_ae_eq (hb : Continuous b)
    (hp : p ≠ ∞) {f : ℝ → E} (hf : Continuous f) (hfc : HasCompactSupport f)
    {u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    (hu : ⇑(trajectoryOperator AL u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f) :
    ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] scalarGreenIntegral g f := by
  obtain ⟨v, hv, hTv⟩ :=
    exists_prev_ae_eq_scalarGreenIntegral_and_trajectoryOperator_ae_eq (p := p) hg hpos hK hα hAL
      hf hfc
  rw [injective_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp
    (Lp.ext (hu.trans hTv.symm))]
  exact hv

end Growth

end TauCeti.WeakDerivStep
