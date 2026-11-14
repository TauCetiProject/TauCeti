/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.LConvolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Convolution.Young

/-!
# Commutators of convolution operators with Lipschitz functions

Let `κ` be a scalar kernel on a seminormed additive group `G` and let `f` be a Lipschitz function
with constant `K`. The commutator of the convolution operator `g ↦ κ ⋆ g` with multiplication by
`f` is

`[κ ⋆ ·, f] g x = (κ ⋆ (f • g)) x - f x • (κ ⋆ g) x = ∫ (f (x - t) - f x) • κ t • g (x - t) dt`

(`MeasureTheory.convolution_smul_sub_smul_convolution`, at every point where both convolutions
exist). In the integrand on the right the factor `f (x - t) - f x` has size at most `K ‖t‖`, so the
commutator is dominated by `K` times the convolution of `‖g‖` with the first moment `‖t‖ ‖κ t‖` of
the kernel. Young's inequality then gives, for `1 ≤ p ≤ ∞`,

`‖[κ ⋆ ·, f] g‖_p ≤ K (∫ ‖t‖ ‖κ t‖ dt) ‖g‖_p`

(`MeasureTheory.eLpNorm_integral_sub_smul_smul_le`). When `κ` is concentrated at scale `ε`, its
first moment is of order `ε` times its `L¹` norm, which bounds `κ ⋆ ·` on `Lᵖ`. So the
commutator gains a factor `ε` over that bound: a derivative, for a frequency localization at
frequencies of size `ε⁻¹`. The estimate involves only the Lipschitz constant `K` of `f`, not the
size of `f`. This is the basic commutator estimate of Littlewood–Paley theory, used for paraproducts
and for transport equations.

The estimate is stated for the integral on the right, which is defined for every `x` and needs no
integrability or boundedness hypothesis on `f` or `g`: a Lipschitz function need not be bounded,
and then `f • g` need not be in any `Lᵖ`.

## Main declarations

* `MeasureTheory.convolution_smul_sub_smul_convolution`: the commutator as a single integral.
* `MeasureTheory.eNorm_integral_sub_smul_smul_le`: the pointwise bound by the convolution of `‖g‖`
  with the first moment of the kernel.
* `MeasureTheory.eLpNorm_integral_sub_smul_smul_le`: the `Lᵖ` bound.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Lemma 2.97.
-/

public section

open ContinuousLinearMap
open scoped ENNReal NNReal Convolution

namespace MeasureTheory

variable {𝕜 G F : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {μ : Measure G} {κ f : G → 𝕜} {g : G → F} {K : ℝ≥0}

/-- **The commutator of a convolution with a multiplication is a single integral.** At a point
where both convolutions exist,
`(κ ⋆ (f • g)) x - f x • (κ ⋆ g) x = ∫ (f (x - t) - f x) • κ t • g (x - t) dt`. -/
theorem convolution_smul_sub_smul_convolution [Sub G] [SMulCommClass ℝ 𝕜 F] {x : G}
    (hfg : ConvolutionExistsAt κ (fun y ↦ f y • g y) x (lsmul 𝕜 𝕜) μ)
    (hg : ConvolutionExistsAt κ g x (lsmul 𝕜 𝕜) μ) :
    (κ ⋆[lsmul 𝕜 𝕜, μ] fun y ↦ f y • g y) x - f x • (κ ⋆[lsmul 𝕜 𝕜, μ] g) x =
      ∫ t, (f (x - t) - f x) • κ t • g (x - t) ∂μ := by
  have hg' : Integrable (fun t ↦ f x • lsmul 𝕜 𝕜 (κ t) (g (x - t))) μ := hg.integrable.smul (f x)
  rw [convolution_def, convolution_def, ← integral_smul, ← integral_sub hfg.integrable hg']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [lsmul_apply, sub_smul, smul_comm (κ t) (f _)]

variable [SeminormedAddCommGroup G]

/-- **Pointwise bound for the commutator with a Lipschitz function.** If `f` is `K`-Lipschitz,
then `‖∫ (f (x - t) - f x) • κ t • g (x - t) dt‖` is at most `K` times the convolution of `‖g‖`
with the first moment `‖t‖ ‖κ t‖` of the kernel, at `x`. -/
theorem eNorm_integral_sub_smul_smul_le (hf : LipschitzWith K f) (x : G) :
    ‖∫ t, (f (x - t) - f x) • κ t • g (x - t) ∂μ‖ₑ ≤
      K * ((fun t ↦ ‖t‖ₑ * ‖κ t‖ₑ) ⋆ₗ[μ] fun y ↦ ‖g y‖ₑ) x := by
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  rw [lconvolution_def, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun t ↦ ?_
  have hft : ‖f (x - t) - f x‖ₑ ≤ K * ‖t‖ₑ := by
    simpa [eDist_eq_eNorm_sub] using hf.edist_le_mul (x - t) x
  calc ‖(f (x - t) - f x) • κ t • g (x - t)‖ₑ
      = ‖f (x - t) - f x‖ₑ * (‖κ t‖ₑ * ‖g (x - t)‖ₑ) := by rw [eNorm_smul, eNorm_smul]
    _ ≤ K * ‖t‖ₑ * (‖κ t‖ₑ * ‖g (x - t)‖ₑ) := by gcongr
    _ = K * (‖t‖ₑ * ‖κ t‖ₑ * ‖g (-t + x)‖ₑ) := by rw [neg_add_eq_sub]; ring

variable [SecondCountableTopology G] [BorelSpace G] [SFinite μ] [μ.IsAddLeftInvariant]
  [μ.IsNegInvariant]

/-- **The commutator of a convolution with a Lipschitz function on `Lᵖ`.** If `f` is
`K`-Lipschitz, then for `1 ≤ p ≤ ∞`,
`‖∫ (f (· - t) - f ·) • κ t • g (· - t) dt‖_p ≤ K (∫ ‖t‖ ‖κ t‖ dt) ‖g‖_p`.
At points where both convolutions exist, the integral is the commutator
`(κ ⋆ (f • g)) x - f x • (κ ⋆ g) x` (`MeasureTheory.convolution_smul_sub_smul_convolution`). -/
theorem eLpNorm_integral_sub_smul_smul_le (hf : LipschitzWith K f)
    (hκ : AEStronglyMeasurable κ μ) (hg : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫ t, (f (x - t) - f x) • κ t • g (x - t) ∂μ) p μ ≤
      K * (∫⁻ t, ‖t‖ₑ * ‖κ t‖ₑ ∂μ) * eLpNorm g p μ := by
  set w : G → ℝ≥0∞ := fun t ↦ ‖t‖ₑ * ‖κ t‖ₑ
  have hw : AEMeasurable w μ := (measurable_eNorm.aemeasurable).mul hκ.eNorm
  -- The commutator is measurable as a parametric integral of a jointly measurable integrand.
  have hmeas : AEStronglyMeasurable
      (fun x ↦ ∫ t, (f (x - t) - f x) • κ t • g (x - t) ∂μ) μ := by
    refine AEStronglyMeasurable.integral_prod_right' (f := fun z : G × G ↦
      (f (z.1 - z.2) - f z.1) • κ z.2 • g (z.1 - z.2)) ?_
    refine (Continuous.aestronglyMeasurable ?_).smul (hκ.comp_snd.smul ?_)
    · exact (hf.continuous.comp continuous_sub).sub (hf.continuous.comp continuous_fst)
    · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)
  calc eLpNorm (fun x ↦ ∫ t, (f (x - t) - f x) • κ t • g (x - t) ∂μ) p μ
      ≤ eLpNorm (fun x ↦ (K : ℝ≥0∞) * (w ⋆ₗ[μ] fun y ↦ ‖g y‖ₑ) x) p μ :=
        eLpNorm_mono_eNorm hmeas fun x ↦ by
          simpa only [eNorm_eq_self] using eNorm_integral_sub_smul_smul_le hf x
    _ = K * eLpNorm (w ⋆ₗ[μ] fun y ↦ ‖g y‖ₑ) p μ :=
        eLpNorm_const_mul_ennreal (aemeasurable_lconvolution hw hg.eNorm).aestronglyMeasurable
    _ ≤ K * (eLpNorm w 1 μ * eLpNorm (fun y ↦ ‖g y‖ₑ) p μ) := by
        gcongr
        exact eLpNorm_lconvolution_le le_rfl hp (by rw [inv_one]) hw hg.eNorm
    _ = K * (∫⁻ t, ‖t‖ₑ * ‖κ t‖ₑ ∂μ) * eLpNorm g p μ := by
        rw [eLpNorm_one_eq_lintegral_eNorm hw.aestronglyMeasurable, eLpNorm_eNorm g hg, mul_assoc]
        simp only [w, eNorm_eq_self]

end MeasureTheory
