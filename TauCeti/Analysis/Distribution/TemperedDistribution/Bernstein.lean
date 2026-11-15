/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# Bernstein's inequalities

Let `E` be a real inner product space of finite dimension `n`. A tempered distribution `u` is
*band-limited* to the closed ball of radius `R` when its Fourier transform vanishes outside it,
`Distribution.IsVanishingOn (𝓕 u) (closedBall 0 R)ᶜ`. **Bernstein's inequalities** say that if
such a `u` is an `Lᵖ` function `f`, then for `1 ≤ p ≤ q ≤ ∞` every derivative of `f` is an `Lᵠ`
function, with

`‖∂_{m₁} ⋯ ∂_{mₖ} f‖_q ≤ C ^ (k + 1) R ^ (k + n (1/p - 1/q)) ‖m₁‖ ⋯ ‖mₖ‖ ‖f‖_p`

for a constant `C` depending only on `E`, `p` and `q`
(`TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`). The case `k = 0`
is the gain of integrability `‖f‖_q ≤ C R ^ (n (1/p - 1/q)) ‖f‖_p` of a band-limited function
(`TauCeti.exists_eq_and_norm_le_of_isVanishingOn_fourier`), and
the case `p = q`, `k = 1` says that differentiating costs at most a factor `C R`.

If moreover `𝓕 u` vanishes on the ball of radius `R`, so that the spectrum of `f` lies in the
annulus `R ≤ ‖ξ‖ ≤ B R`, differentiation also loses at most a factor of order `R` in the other
direction: for an orthonormal basis `b` of `E` there is a constant `C`, depending only on `b` and
`B`, with

`‖f‖_p ≤ (C / R) ^ k ∑ᵢ ‖∂_{b_{i₀}} ⋯ ∂_{b_{iₖ₋₁}} f‖_p`

for every `1 ≤ p ≤ ∞`, the sum running over `i : Fin k → ι`
(`OrthonormalBasis.exists_norm_le_div_pow_mul_sum_norm_of_iteratedLineDerivOp_eq`).

These are the basic estimates for functions whose spectrum lies in a ball or an annulus, such as
the Littlewood–Paley blocks of a tempered distribution: they convert the frequency localization of
a block into bounds on its derivatives and on its higher Lebesgue norms, and, on an annulus, bound
the block by its derivatives. This is what makes a dyadic block of frequency `2 ^ j` behave as if
differentiation were multiplication by `2 ^ j`.

## The argument

Let `χ` be a smooth bump function equal to one on the ball of radius `2`, and `χ_R = χ (R⁻¹ •)`.
If `𝓕 u` vanishes outside the ball of radius `R`, then `χ_R • 𝓕 u = 𝓕 u`, so `u` is reproduced by
the Fourier multiplier with symbol `χ_R`
(`TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`). That multiplier is
convolution with the Schwartz kernel `𝓕⁻ χ_R`, which maps `Lᵖ` to `Lᵠ` with norm at most
`‖𝓕⁻ χ_R‖_r`, `1/p + 1/r = 1 + 1/q`, by Young's inequality
(`TemperedDistribution.exists_fourierMultiplierCLM_toTemperedDistribution_eq`). Similarly `∂_m u` is
reproduced by the symbol `2πi ⟪ξ, m⟫ χ_R ξ`, whose kernel is `∂_m (𝓕⁻ χ_R)`. Since
`𝓕⁻ χ_R x = R ^ n 𝓕⁻ χ (R • x)`, the `Lʳ` norm of the first kernel is `R ^ (n (1 - 1/r))` times
that of `𝓕⁻ χ` (`TauCeti.eLpNorm_fourierInv_comp_inv_smul`), and the `L¹` norm of the second is
`R` times that of `∂_m 𝓕⁻ χ`, which is at most a fixed multiple of `‖m‖`. Derivatives of a
band-limited distribution are again band-limited
(`TemperedDistribution.isVanishingOn_fourier_iteratedLineDerivOp`), so the bounds for one
derivative iterate.

For the reverse inequality, where we may assume `B ≥ 1`, let `φ` be a smooth compactly
supported function equal to one on `1/2 ≤ ‖ξ‖ ≤ 2 B` and to zero near the origin, and
`φ_R = φ (R⁻¹ •)`. Since `∑ᵢ ⟪ξ, bᵢ⟫² = ‖ξ‖²`, the smooth compactly supported symbols
`σᵢ ξ = φ_R ξ ⟪ξ, bᵢ⟫ / ‖ξ‖²` satisfy `∑ᵢ 2πi ⟪ξ, bᵢ⟫ σᵢ ξ = 2πi φ_R ξ`, so
`2πi u = ∑ᵢ T_{σᵢ} (∂_{bᵢ} u)` when the spectrum of `u` lies in the annulus. The kernel of `σᵢ`
has `L¹` norm `R⁻¹` times that of the corresponding kernel for `R = 1`, and Young's inequality
gives the bound for one derivative; it iterates since derivatives keep the spectrum in the
annulus.

## Main declarations

* `TauCeti.exists_eq_and_norm_le_of_isVanishingOn_fourier`: Bernstein's inequality without
  derivatives, the gain of integrability of a band-limited function.
* `TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`: Bernstein's
  inequalities.
* `TauCeti.exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`: Bernstein's inequality
  for one derivative, with a constant independent of the exponent `p`.
* `TauCeti.exists_iteratedLineDerivOp_smulLeftCLM_eq_and_norm_le`: the Leibniz rule with
  Bernstein's inequality, bounding the derivatives of the product of a band-limited function with a
  function with bounded derivatives.
* `OrthonormalBasis.exists_eq_sum_lineDerivOp_and_norm_le`: on an annulus of radius `R`, a
  function is a sum of derivatives of functions smaller by a factor of order `R⁻¹`.
* `OrthonormalBasis.exists_norm_le_div_mul_sum_norm_of_lineDerivOp_eq`,
  `OrthonormalBasis.exists_norm_le_div_pow_mul_sum_norm_of_iteratedLineDerivOp_eq`: the reverse
  Bernstein inequality on an annulus, for one derivative and for derivatives of every order.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Lemma 2.1.
-/

public section

noncomputable section

open SchwartzMap ContinuousLinearMap MeasureTheory Metric Distribution Module
open scoped ENNReal FourierTransform SchwartzMap LineDeriv Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TauCeti

open TemperedDistribution

/-- The bump function, equal to one on the ball of radius `2`, whose dilations reproduce
band-limited functions. -/
private def bump : ContDiffBump (0 : E) := ⟨2, 3, two_pos, by norm_num⟩

/-- The symbol `ξ ↦ χ (R⁻¹ • ξ)`, equal to one on the ball of radius `2 R`, as a Schwartz
function. -/
private def cutoff {R : ℝ} (hR : 0 < R) : 𝓢(E, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun ξ ↦ ((bump : ContDiffBump (0 : E)) (R⁻¹ • ξ) : ℂ))
    ((bump.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')).comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (bump.contDiff.comp (contDiff_const_smul _)))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem cutoff_apply {R : ℝ} (hR : 0 < R) (ξ : E) :
    cutoff hR ξ = ((bump : ContDiffBump (0 : E)) (R⁻¹ • ξ) : ℂ) :=
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- The cutoff at scale `R` equals one outside a closed set disjoint from the closed ball of
radius `R`. -/
private theorem tsupport_cutoff_sub_one_subset {R : ℝ} (hR : 0 < R) :
    tsupport (⇑(cutoff (E := E) hR) - 1) ⊆ (closedBall 0 R)ᶜ := by
  have hsupp : Function.support (⇑(cutoff (E := E) hR) - 1) ⊆ (ball 0 (2 * R))ᶜ := by
    intro ξ hξ hball
    apply hξ
    have : R⁻¹ • ξ ∈ closedBall (0 : E) 2 := by
      rw [mem_ball_zero_iff] at hball
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      rw [inv_mul_le_iff₀ hR]
      linarith
    simp [cutoff_apply, bump.one_of_mem_closedBall this]
  refine (closure_minimal hsupp isOpen_ball.isClosed_compl).trans ?_
  refine Set.compl_subset_compl.2 (closedBall_subset_ball ?_)
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- The cutoff at scale `R` is the dilation of the cutoff at scale `1`. -/
private theorem cutoff_eq_comp {R : ℝ} (hR : 0 < R) :
    ⇑(cutoff (E := E) hR) = fun ξ ↦ cutoff (E := E) one_pos (R⁻¹ • ξ) := by
  ext ξ
  simp [cutoff_apply]

variable [CompleteSpace F]

/-- **Bernstein's inequality without derivatives.** For `1 ≤ p ≤ q ≤ ∞` there is a constant `C`,
depending only on `E`, `p` and `q`, such that an `Lᵖ` function `f` whose Fourier transform vanishes
outside the closed ball of radius `R > 0` is an `Lᵠ` function `g`, with
`‖g‖_q ≤ C R ^ (n (1/p - 1/q)) ‖f‖_p`, where `n` is the dimension of `E` and `1/∞ = 0`. -/
theorem exists_eq_and_norm_le_of_isVanishingOn_fourier {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (hpq : p ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F q (volume : Measure E), (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R ^ ((finrank ℝ E : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹)) * ‖f‖ := by
  -- The exponent `r` of Young's inequality, with `1/p + 1/r = 1 + 1/q`.
  set r : ℝ≥0∞ := (1 + q⁻¹ - p⁻¹)⁻¹
  have hqp : q⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hpq
  have hp1 : p⁻¹ ≤ 1 + q⁻¹ := (ENNReal.inv_le_one.2 hp.out).trans le_self_add
  have hq1 : q⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (zero_lt_one.trans_le Fact.out).ne'
  have hr : 1 ≤ r := ENNReal.one_le_inv.2 (tsub_le_iff_right.2 (by gcongr))
  have hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹ := by rw [inv_inv, add_tsub_cancel_of_le hp1]
  have hrexp : (finrank ℝ E : ℝ) - finrank ℝ E / r.toReal =
      finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹) := by
    have : r.toReal⁻¹ = 1 + q.toReal⁻¹ - p.toReal⁻¹ := by
      rw [← ENNReal.toReal_inv, inv_inv, ENNReal.toReal_sub_of_le hp1
        (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hq1⟩),
        ENNReal.toReal_add ENNReal.one_ne_top hq1, ENNReal.toReal_inv, ENNReal.toReal_inv,
        ENNReal.toReal_one]
    rw [div_eq_mul_inv, this]
    ring
  refine ⟨(eLpNorm (𝓕⁻ (cutoff (E := E) one_pos : E → ℂ)) r volume).toReal,
    ENNReal.toReal_nonneg, fun {R} hR f hf ↦ ?_⟩
  obtain ⟨g, hg, -, hgf⟩ :=
    exists_fourierMultiplierCLM_toTemperedDistribution_eq (cutoff hR) f hr hpqr
  refine ⟨g, ?_, ?_⟩
  · rw [← hg, fourierMultiplierCLM_eq_self_of_isVanishingOn hf (cutoff hR).hasTemperateGrowth
      (tsupport_cutoff_sub_one_subset hR)]
  · rw [cutoff_eq_comp hR, eLpNorm_fourierInv_comp_inv_smul _ hR, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hrexp] at hgf
    linarith

/-- The symbol `ξ ↦ 2πi ⟪ξ, m⟫ χ (R⁻¹ • ξ)` of `∂_m` composed with the reproducing multiplier
at scale `R`. -/
private def derivSymbol {R : ℝ} (hR : 0 < R) (m : E) : 𝓢(E, ℂ) :=
  (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (inner ℝ · m) (cutoff hR)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem coe_derivSymbol {R : ℝ} (hR : 0 < R) (m : E) :
    ⇑(derivSymbol hR m) =
      (2 * Real.pi * Complex.I) • (⇑(cutoff hR) * fun ξ ↦ ((inner ℝ ξ m : ℝ) : ℂ)) := by
  ext ξ
  simp [derivSymbol, SchwartzMap.smulLeftCLM_apply_apply (g := (inner ℝ · m)) (by fun_prop),
    mul_comm]

/-- The kernel of `derivSymbol` has `L¹` norm at most `C R ‖m‖`: it is `R` times the dilation of
the kernel `∂_m 𝓕⁻ χ` at scale `1`, which is bounded by `‖m‖ ‖D 𝓕⁻ χ‖`. -/
private theorem toReal_eLpNorm_fourierInv_derivSymbol_le {R : ℝ} (hR : 0 < R) (m : E) :
    (eLpNorm (𝓕⁻ (derivSymbol hR m : E → ℂ)) 1 volume).toReal ≤
      (eLpNorm (fderiv ℝ (𝓕⁻ (cutoff (E := E) one_pos) : 𝓢(E, ℂ))) 1 volume).toReal * R *
        ‖m‖ := by
  set K : 𝓢(E, ℂ) := 𝓕⁻ (cutoff (E := E) one_pos)
  have hscale : ⇑(derivSymbol hR m) = fun ξ ↦ ((R : ℂ) • derivSymbol one_pos m) (R⁻¹ • ξ) := by
    ext ξ
    simp [coe_derivSymbol, cutoff_apply, real_inner_smul_left]
    have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  have hK : 𝓕⁻ (derivSymbol one_pos m) = ∂_{m} K :=
    (SchwartzMap.lineDerivOp_fourierInv_eq _ m).symm
  have hfin : eLpNorm (fderiv ℝ K) 1 volume ≠ ∞ := by
    have : fderiv ℝ ⇑K = ⇑(SchwartzMap.fderivCLM ℝ E ℂ K) := by
      ext1 x
      rw [SchwartzMap.fderivCLM_apply]
    rw [this]
    exact (SchwartzMap.eLpNorm_lt_top _ 1 volume).ne
  have hderiv : eLpNorm ⇑(∂_{m} K : 𝓢(E, ℂ)) 1 volume ≤ ‖m‖ₑ * eLpNorm (fderiv ℝ K) 1 volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 1 (∂_{m} K).continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]
        exact ContinuousLinearMap.le_opENorm _ _)
  have hsmul : ⇑((R : ℂ) • (∂_{m} K : 𝓢(E, ℂ))) = (R : ℂ) • ⇑(∂_{m} K : 𝓢(E, ℂ)) :=
    funext fun x ↦ smul_apply _ _ _
  calc (eLpNorm (𝓕⁻ (derivSymbol hR m : E → ℂ)) 1 volume).toReal
      = R * (eLpNorm ⇑(∂_{m} K : 𝓢(E, ℂ)) 1 volume).toReal := by
        rw [hscale, eLpNorm_fourierInv_comp_inv_smul _ hR, ← SchwartzMap.fourierInv_coe,
          FourierTransform.fourierInv_smul, hK, hsmul, eLpNorm_const_smul]
        simp [abs_of_pos hR]
    _ ≤ R * (‖m‖ * (eLpNorm (fderiv ℝ K) 1 volume).toReal) := by
        gcongr
        calc (eLpNorm ⇑(∂_{m} K : 𝓢(E, ℂ)) 1 volume).toReal
            ≤ (‖m‖ₑ * eLpNorm (fderiv ℝ K) 1 volume).toReal :=
              ENNReal.toReal_mono (ENNReal.mul_ne_top eNorm_ne_top hfin) hderiv
          _ = ‖m‖ * (eLpNorm (fderiv ℝ K) 1 volume).toReal := by
              rw [ENNReal.toReal_mul, toReal_eNorm]
    _ = (eLpNorm (fderiv ℝ K) 1 volume).toReal * R * ‖m‖ := by ring

/-- **Bernstein's inequality for one derivative.** There is a constant `C`, depending only on
`E`, with the following property. For `1 ≤ p ≤ ∞`, an `Lᵖ` function `f` whose Fourier transform
vanishes outside the closed ball of radius `R > 0` has its derivative `∂_m f` in `Lᵖ`, with
`‖∂_m f‖_p ≤ C R ‖m‖ ‖f‖_p`. -/
theorem exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : E,
      ∃ g : Lp F p (volume : Measure E), ∂_{m} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R * ‖m‖ * ‖f‖ := by
  refine ⟨(eLpNorm (fderiv ℝ (𝓕⁻ (cutoff (E := E) one_pos) : 𝓢(E, ℂ))) 1 volume).toReal,
    ENNReal.toReal_nonneg, fun {p} _ {R} hR f hf m ↦ ?_⟩
  have hinner : (fun ξ : E ↦ ((inner ℝ ξ m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hσ := (cutoff (E := E) hR).hasTemperateGrowth
  -- `∂_m f` is the multiplier with symbol `derivSymbol hR m`.
  have hdist : ∂_{m} (f : 𝓢'(E, F)) =
      fourierMultiplierCLM F (derivSymbol hR m) (f : 𝓢'(E, F)) := by
    conv_lhs => rw [← fourierMultiplierCLM_eq_self_of_isVanishingOn hf hσ
      (tsupport_cutoff_sub_one_subset hR)]
    rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM,
      TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hσ hinner,
      coe_derivSymbol, TemperedDistribution.fourierMultiplierCLM_smul (hσ.mul hinner),
      smul_apply]
  obtain ⟨g, hg, -, hgf⟩ := exists_fourierMultiplierCLM_toTemperedDistribution_eq
    (derivSymbol hR m) f (q := p) (r := 1) le_rfl (by rw [inv_one, add_comm])
  exact ⟨g, hdist.trans hg, hgf.trans (mul_le_mul_of_nonneg_right
    (toReal_eLpNorm_fourierInv_derivSymbol_le hR m) (norm_nonneg f))⟩

/-- **Bernstein's inequality for derivatives at a fixed exponent**, by induction on the number of
derivatives: `‖∂_{m₁} ⋯ ∂_{mₖ} f‖_p ≤ (C R) ^ k ‖m₁‖ ⋯ ‖mₖ‖ ‖f‖_p`. -/
private theorem exists_iteratedLineDerivOp_eq_and_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∀ (k : ℕ) (m : Fin k → E), ∃ g : Lp F p (volume : Measure E),
        ∂^{m} (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ (C * R) ^ k * (∏ i, ‖m i‖) * ‖f‖ := by
  obtain ⟨C, hC, h₁⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
  refine ⟨C, hC, fun {R} hR f hf k ↦ ?_⟩
  induction k with
  | zero => exact fun m ↦ ⟨f, by simp, by simp⟩
  | succ k ih =>
    intro m
    obtain ⟨g', hg', hg'n⟩ := ih (Fin.tail m)
    have hg'f : IsVanishingOn (𝓕 (g' : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ := by
      rw [← hg']
      exact isVanishingOn_fourier_iteratedLineDerivOp hf _
    obtain ⟨g, hg, hgn⟩ := h₁ hR g' hg'f (m 0)
    refine ⟨g, by rw [LineDeriv.iteratedLineDerivOp_succ_left, hg', hg], ?_⟩
    calc ‖g‖ ≤ C * R * ‖m 0‖ * ‖g'‖ := hgn
      _ ≤ C * R * ‖m 0‖ * ((C * R) ^ k * (∏ i, ‖Fin.tail m i‖) * ‖f‖) := by gcongr
      _ = (C * R) ^ (k + 1) * (∏ i, ‖m i‖) * ‖f‖ := by
        rw [Fin.prod_univ_succ]
        simp only [Fin.tail]
        ring

/-- **Bernstein's inequalities.** For `1 ≤ p ≤ q ≤ ∞` there is a constant `C`, depending only on
`E`, `p` and `q`, with the following property. Let `f ∈ Lᵖ` have Fourier transform vanishing
outside the closed ball of radius `R > 0`. Then for all directions `m₁, …, mₖ` the derivative
`∂_{m₁} ⋯ ∂_{mₖ} f` is an `Lᵠ` function `g` with

`‖g‖_q ≤ C ^ (k + 1) R ^ (k + n (1/p - 1/q)) ‖m₁‖ ⋯ ‖mₖ‖ ‖f‖_p`,

where `n` is the dimension of `E` and `1/∞ = 0`. -/
theorem exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (m : Fin k → E) {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F q (volume : Measure E), ∂^{m} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C ^ (k + 1) * R ^ ((k : ℝ) + finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) *
          (∏ i, ‖m i‖) * ‖f‖ := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F) hpq
  obtain ⟨C₁, hC₁, hderiv⟩ :=
    exists_iteratedLineDerivOp_eq_and_norm_le (E := E) (F := F) (p := p)
  -- The derivatives at the exponent `p`, then the gain of integrability from `p` to `q`.
  refine ⟨max C₀ C₁, le_max_of_le_left hC₀, fun k m {R} hR f hf ↦ ?_⟩
  obtain ⟨g, hg, hgn⟩ := hderiv hR f hf k m
  obtain ⟨h, hh, hhn⟩ := h₀ hR g (by
    rw [← hg]
    exact isVanishingOn_fourier_iteratedLineDerivOp hf m)
  refine ⟨h, hg.trans hh, ?_⟩
  set d : ℝ := finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)
  have hC : C₀ * C₁ ^ k ≤ max C₀ C₁ ^ (k + 1) := by
    rw [pow_succ']
    gcongr
    exacts [le_max_left _ _, le_max_right _ _]
  calc ‖h‖ ≤ C₀ * R ^ d * ‖g‖ := hhn
    _ ≤ C₀ * R ^ d * ((C₁ * R) ^ k * (∏ i, ‖m i‖) * ‖f‖) := by gcongr
    _ = C₀ * C₁ ^ k * R ^ ((k : ℝ) + d) * (∏ i, ‖m i‖) * ‖f‖ := by
        rw [Real.rpow_add hR, Real.rpow_natCast, mul_pow]
        ring
    _ ≤ max C₀ C₁ ^ (k + 1) * R ^ ((k : ℝ) + d) * (∏ i, ‖m i‖) * ‖f‖ := by gcongr

/-- **Leibniz bound for band-limited functions.** There is `C`, depending only on `E`, with the
following property. Let `g` be a function of temperate growth whose derivatives of order at most
`k` are bounded by `G`, and let `f ∈ Lᵖ` have Fourier transform vanishing outside the closed ball
of radius `R > 0`. Then `∂_{m₁} ⋯ ∂_{mₖ} (g f)` is an `Lᵖ` function of norm at most
`(2 max 1 (C R)) ^ k ‖m₁‖ ⋯ ‖mₖ‖ G ‖f‖_p`. -/
theorem exists_iteratedLineDerivOp_smulLeftCLM_eq_and_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ) {g : E → ℂ} {G : ℝ},
      g.HasTemperateGrowth → (∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : Fin k → E,
      ∃ v : Lp F p (volume : Measure E), ∂^{m} (smulLeftCLM F g (f : 𝓢'(E, F))) = v ∧
        ‖v‖ ≤ (2 * max 1 (C * R)) ^ k * (∏ i, ‖m i‖) * G * ‖f‖ := by
  obtain ⟨C, hC, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
  refine ⟨C, hC, fun {p} _ k ↦ ?_⟩
  induction k with
  | zero =>
    intro g G hg hgG R _ f _ m
    obtain ⟨v, hv, hvn⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le hg
      (fun x ↦ by simpa using hgG 0 le_rfl x) f
    exact ⟨v, by simpa [LineDeriv.iteratedLineDerivOp_zero] using hv, by simpa using hvn⟩
  | succ k ih =>
    intro g G hg hgG R hR f hf m
    set w := m (Fin.last k)
    -- `∂_w f` is band-limited to the same ball, and `∂_w (g f) = (∂_w g) f + g ∂_w f`.
    obtain ⟨f', hf', hf'n⟩ := hB hR f hf w
    have hf'v : IsVanishingOn (𝓕 (f' : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ := by
      rw [← hf']
      exact isVanishingOn_fourier_lineDerivOp hf w
    obtain ⟨v₁, hv₁, hv₁n⟩ := ih (hg.fderiv_apply w)
      (hg.1.norm_iteratedFDeriv_fderiv_apply_le_of_forall_le (by
        rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast le_top) hgG w) hR f hf
      (Fin.init m)
    obtain ⟨v₂, hv₂, hv₂n⟩ := ih hg (fun n hn ↦ hgG n (by omega)) hR f' hf'v (Fin.init m)
    refine ⟨v₁ + v₂, ?_, ?_⟩
    · rw [LineDeriv.iteratedLineDerivOp_succ_right, lineDerivOp_smulLeftCLM hg, hf',
        LineDeriv.iteratedLineDerivOp_add, hv₁, hv₂, Lp.toTemperedDistribution_add]
    · have hG : 0 ≤ G := (norm_nonneg _).trans (by simpa using hgG 0 (by omega) 0)
      set A := 2 * max 1 (C * R)
      have h1 : 1 + C * R ≤ A := by
        have := le_max_left 1 (C * R); have := le_max_right 1 (C * R); simp only [A]; linarith
      calc ‖v₁ + v₂‖ ≤ ‖v₁‖ + ‖v₂‖ := norm_add_le _ _
        _ ≤ A ^ k * (∏ i, ‖Fin.init m i‖) * (G * ‖w‖) * ‖f‖ +
            A ^ k * (∏ i, ‖Fin.init m i‖) * G * (C * R * ‖w‖ * ‖f‖) := by
          exact add_le_add hv₁n (hv₂n.trans (by gcongr))
        _ = A ^ k * (∏ i, ‖Fin.init m i‖) * ‖w‖ * G * ‖f‖ * (1 + C * R) := by ring
        _ ≤ A ^ k * (∏ i, ‖Fin.init m i‖) * ‖w‖ * G * ‖f‖ * A := by gcongr
        _ = A ^ (k + 1) * (∏ i, ‖m i‖) * G * ‖f‖ := by
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.init, w]
          ring

/-! ### The reverse inequality on annuli -/

/-- A smooth compactly supported annular cutoff, chosen by
`TauCeti.exists_contDiff_cutoff_annulus`: it equals one where `1/2 ≤ ‖ξ‖ ≤ 2 B` and vanishes on
the ball of radius `1/4`. -/
private def annularCutoff (B : ℝ) : E → ℝ :=
  (exists_contDiff_cutoff_annulus (E := E) (r := 1 / 2) (by norm_num) (2 * B)).choose

omit [MeasurableSpace E] [BorelSpace E] in
private theorem contDiff_annularCutoff (B : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (annularCutoff (E := E) B) :=
  (exists_contDiff_cutoff_annulus (E := E) (r := 1 / 2) (by norm_num) (2 * B)).choose_spec.1

omit [MeasurableSpace E] [BorelSpace E] in
private theorem hasCompactSupport_annularCutoff (B : ℝ) :
    HasCompactSupport (annularCutoff (E := E) B) :=
  (exists_contDiff_cutoff_annulus (E := E) (r := 1 / 2) (by norm_num) (2 * B)).choose_spec.2.1

omit [MeasurableSpace E] [BorelSpace E] in
private theorem annularCutoff_eq_zero (B : ℝ) {ξ : E} (hξ : ‖ξ‖ < 1 / 4) :
    annularCutoff B ξ = 0 :=
  (exists_contDiff_cutoff_annulus (E := E) (r := 1 / 2) (by norm_num) (2 * B)).choose_spec.2.2.1 ξ
    (by linarith)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem annularCutoff_eq_one (B : ℝ) {ξ : E} (h₁ : 1 / 2 ≤ ‖ξ‖) (h₂ : ‖ξ‖ ≤ 2 * B) :
    annularCutoff B ξ = 1 :=
  (exists_contDiff_cutoff_annulus (E := E) (r := 1 / 2) (by norm_num) (2 * B)).choose_spec.2.2.2.2
    ξ h₁ h₂

/-- The symbol `ξ ↦ φ (R⁻¹ • ξ) ⟪ξ, m⟫ / ‖ξ‖²`, where `φ` is the annular cutoff. Multiplying by
`⟪ξ, m⟫` and summing over an orthonormal basis gives back `φ (R⁻¹ • ξ)`. -/
private def annularSymbol (B : ℝ) (R : ℝ) (m ξ : E) : ℂ :=
  ((annularCutoff B (R⁻¹ • ξ) * (inner ℝ ξ m / ‖ξ‖ ^ 2) : ℝ) : ℂ)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem contDiff_annularSymbol (B : ℝ) {R : ℝ} (hR : 0 < R) (m : E) :
    ContDiff ℝ (⊤ : ℕ∞) (annularSymbol B R m) := by
  refine Complex.ofRealCLM.contDiff.comp (contDiff_iff_contDiffAt.2 fun ξ ↦ ?_)
  rcases eq_or_ne ξ 0 with rfl | hξ
  · -- The symbol vanishes on the ball of radius `R / 4`.
    have hR4 : 0 < R / 4 := by positivity
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) hR4] with η hη
    rw [mem_ball_zero_iff] at hη
    rw [annularCutoff_eq_zero B
      (by rw [norm_smul_of_nonneg (inv_nonneg.2 hR.le), inv_mul_lt_iff₀ hR]; linarith)]
    exact zero_mul _
  · exact ((contDiff_annularCutoff B).comp
      (contDiff_const_smul _)).contDiffAt.mul ((contDiffAt_id.inner ℝ contDiffAt_const).div
        (contDiff_norm_sq ℝ).contDiffAt (by simpa using hξ))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem hasCompactSupport_annularSymbol (B : ℝ) {R : ℝ} (hR : 0 < R)
    (m : E) : HasCompactSupport (annularSymbol B R m) :=
  (((hasCompactSupport_annularCutoff B).comp_smul
    (inv_ne_zero hR.ne')).mul_right).comp_left Complex.ofReal_zero

/-- The annular symbol as a Schwartz function. -/
private def annularSymbolSchwartz (B : ℝ) {R : ℝ} (hR : 0 < R) (m : E) :
    𝓢(E, ℂ) :=
  (hasCompactSupport_annularSymbol B hR m).toSchwartzMap (contDiff_annularSymbol B hR m)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem coe_annularSymbolSchwartz (B : ℝ) {R : ℝ} (hR : 0 < R) (m : E) :
    ⇑(annularSymbolSchwartz B hR m) = annularSymbol B R m :=
  rfl

/-- The kernel of the annular symbol at scale `R` has `L¹` norm `R⁻¹` times that at scale `1`. -/
private theorem toReal_eLpNorm_fourierInv_annularSymbol (B : ℝ) {R : ℝ}
    (hR : 0 < R) (m : E) :
    (eLpNorm (𝓕⁻ (annularSymbolSchwartz B hR m : E → ℂ)) 1 volume).toReal =
      R⁻¹ * (eLpNorm (𝓕⁻ (annularSymbolSchwartz B one_pos m : E → ℂ)) 1 volume).toReal := by
  set S := annularSymbolSchwartz (E := E) B one_pos m
  have hscale : ⇑(annularSymbolSchwartz B hR m) =
      fun ξ ↦ (((R⁻¹ : ℝ) : ℂ) • S) (R⁻¹ • ξ) := by
    ext ξ
    rcases eq_or_ne ξ 0 with rfl | _
    · simp [S, coe_annularSymbolSchwartz, annularSymbol]
    simp only [S, smul_apply, coe_annularSymbolSchwartz, annularSymbol, inv_one, one_smul,
      real_inner_smul_left, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, smul_eq_mul]
    have : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    push_cast
    field_simp
  have hsmul : ⇑(𝓕⁻ (((R⁻¹ : ℝ) : ℂ) • S) : 𝓢(E, ℂ)) =
      ((R⁻¹ : ℝ) : ℂ) • ⇑(𝓕⁻ S : 𝓢(E, ℂ)) := by
    rw [FourierTransform.fourierInv_smul]
    exact funext fun x ↦ smul_apply _ _ _
  rw [hscale, eLpNorm_fourierInv_comp_inv_smul _ hR, ← SchwartzMap.fourierInv_coe, hsmul,
    eLpNorm_const_smul, ← SchwartzMap.fourierInv_coe]
  simp [abs_of_pos hR]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Multiplied by the symbols `⟪ξ, bᵢ⟫` of the derivatives along an orthonormal basis and summed,
the annular symbols give back the annular cutoff `φ (R⁻¹ • ξ)`, since `∑ᵢ ⟪ξ, bᵢ⟫² = ‖ξ‖²`. -/
private theorem _root_.OrthonormalBasis.sum_inner_mul_annularSymbol {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (B R : ℝ) (ξ : E) :
    ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) * annularSymbol B R (b i) ξ =
      ((annularCutoff B (R⁻¹ • ξ) : ℝ) : ℂ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [annularCutoff_eq_zero B (ξ := (0 : E)) (by norm_num)]
  have hreal : ∑ i, inner ℝ ξ (b i) * (annularCutoff B (R⁻¹ • ξ) * (inner ℝ ξ (b i) / ‖ξ‖ ^ 2)) =
      annularCutoff B (R⁻¹ • ξ) := by
    have hξ2 : ‖ξ‖ ^ 2 ≠ 0 := by positivity
    calc _ = annularCutoff B (R⁻¹ • ξ) * (∑ i, inner ℝ ξ (b i) ^ 2) / ‖ξ‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ = _ := by rw [b.sum_sq_inner_left, mul_div_assoc, div_self hξ2, mul_one]
  simp only [annularSymbol]
  exact_mod_cast hreal

omit [CompleteSpace F] in
/-- **Reproducing formula on an annulus.** If `𝓕 u` vanishes on the ball of radius `R` and outside
the closed ball of radius `B R`, then `u` is recovered from its derivatives along an orthonormal
basis: `∑ᵢ T_{σᵢ} (∂_{bᵢ} u) = 2πi u`, where `σᵢ` is the annular symbol at scale `R` in the
direction `bᵢ`. -/
private theorem _root_.OrthonormalBasis.sum_fourierMultiplierCLM_annularSymbol_lineDerivOp
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {B : ℝ} (hB : 1 ≤ B) {R : ℝ} (hR : 0 < R)
    {u : 𝓢'(E, F)}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ)) :
    ∑ i, TemperedDistribution.fourierMultiplierCLM F (annularSymbol B R (b i)) (∂_{b i} u) =
      (2 * Real.pi * Complex.I) • u := by
  have hinner (i : ι) : (fun ξ : E ↦ ((inner ℝ ξ (b i) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  have hσ (i : ι) : (annularSymbol B R (b i)).HasTemperateGrowth :=
    (annularSymbolSchwartz B hR (b i)).hasTemperateGrowth
  have hφ : (fun ξ : E ↦ ((annularCutoff B (R⁻¹ • ξ) : ℝ) : ℂ)).HasTemperateGrowth :=
    (((hasCompactSupport_annularCutoff B).comp_smul
      (inv_ne_zero hR.ne')).comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp
        ((contDiff_annularCutoff B).comp (contDiff_const_smul _)))
  -- The cutoff `φ (R⁻¹ • ·)` equals one on `R / 2 ≤ ‖ξ‖ ≤ 2 B R`, a neighbourhood of the annulus.
  have hsupp : Function.support ((fun ξ : E ↦ ((annularCutoff B (R⁻¹ • ξ) : ℝ) : ℂ)) - 1) ⊆
      closedBall 0 (R / 2) ∪ (ball 0 (2 * B * R))ᶜ := by
    intro ξ hξ
    by_contra h
    simp only [Set.mem_union, mem_closedBall_zero_iff, Set.mem_compl_iff, mem_ball_zero_iff,
      not_or, not_le, not_not] at h
    apply hξ
    rw [Pi.sub_apply, annularCutoff_eq_one B
      (by rw [norm_smul_of_nonneg (inv_nonneg.2 hR.le), le_inv_mul_iff₀ hR]; linarith)
      (by rw [norm_smul_of_nonneg (inv_nonneg.2 hR.le), inv_mul_le_iff₀ hR]; linarith),
      Complex.ofReal_one, Pi.one_apply, sub_self]
  have hBR : B * R < 2 * B * R := by nlinarith
  have hts : tsupport ((fun ξ : E ↦ ((annularCutoff B (R⁻¹ • ξ) : ℝ) : ℂ)) - 1) ⊆
      ball 0 R ∪ (closedBall 0 (B * R))ᶜ :=
    (closure_minimal hsupp (isClosed_closedBall.union isOpen_ball.isClosed_compl)).trans
      (Set.union_subset_union (closedBall_subset_ball (by linarith))
        (Set.compl_subset_compl.2 (closedBall_subset_ball hBR)))
  calc ∑ i, TemperedDistribution.fourierMultiplierCLM F (annularSymbol B R (b i)) (∂_{b i} u)
      = ∑ i, (2 * Real.pi * Complex.I) • TemperedDistribution.fourierMultiplierCLM F
          (fun ξ ↦ ((inner ℝ ξ (b i) : ℝ) : ℂ) * annularSymbol B R (b i) ξ) u := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM, map_smul,
          TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply (hinner i) (hσ i),
          Pi.mul_def]
    _ = (2 * Real.pi * Complex.I) • TemperedDistribution.fourierMultiplierCLM F
          (fun ξ ↦ ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) * annularSymbol B R (b i) ξ) u := by
        rw [← Finset.smul_sum, TemperedDistribution.fourierMultiplierCLM_sum F
          (g := fun i ξ ↦ ((inner ℝ ξ (b i) : ℝ) : ℂ) * annularSymbol B R (b i) ξ)
          (fun i _ ↦ (hinner i).mul (hσ i)), sum_apply]
    _ = (2 * Real.pi * Complex.I) • u := by
        simp_rw [b.sum_inner_mul_annularSymbol B R]
        rw [fourierMultiplierCLM_eq_self_of_isVanishingOn hu hφ hts]

/-- The multipliers of the reproducing formula on an annulus, divided by `2πi`, are bounded on
`Lᵖ` with norm `C / R` at scale `R`, where `C` depends only on `b` and `B`. -/
private theorem _root_.OrthonormalBasis.exists_smul_fourierMultiplierCLM_annularSymbol_eq
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R →
      ∀ (g : Lp F p (volume : Measure E)) (i : ι), ∃ h : Lp F p (volume : Measure E),
      (2 * Real.pi * Complex.I)⁻¹ • TemperedDistribution.fourierMultiplierCLM F
        (annularSymbol B R (b i)) (g : 𝓢'(E, F)) = h ∧ ‖h‖ ≤ C / R * ‖g‖ := by
  -- The `L¹` norms of the kernels of the annular symbols at scale `1`.
  set K : ι → ℝ := fun i ↦
    (eLpNorm (𝓕⁻ (annularSymbolSchwartz B one_pos (b i) : E → ℂ)) 1 volume).toReal
  have hK (i : ι) : 0 ≤ K i := ENNReal.toReal_nonneg
  refine ⟨(2 * Real.pi)⁻¹ * ∑ i, K i, by positivity, fun {p} _ {R} hR g i ↦ ?_⟩
  -- `T_{σᵢ} g` is an `Lᵖ` function `h` with `‖h‖ ≤ R⁻¹ Kᵢ ‖g‖`.
  obtain ⟨h, hh, -, hhn⟩ := exists_fourierMultiplierCLM_toTemperedDistribution_eq
    (annularSymbolSchwartz B hR (b i)) g (q := p) (r := 1) le_rfl (by rw [inv_one, add_comm])
  refine ⟨(2 * Real.pi * Complex.I)⁻¹ • h, ?_, ?_⟩
  · rw [← coe_annularSymbolSchwartz B hR, hh, Lp.toTemperedDistribution_smul]
  · calc ‖(2 * Real.pi * Complex.I)⁻¹ • h‖ = (2 * Real.pi)⁻¹ * ‖h‖ := by
          rw [norm_smul]
          simp [abs_of_pos Real.pi_pos]
      _ ≤ (2 * Real.pi)⁻¹ * (R⁻¹ * K i * ‖g‖) := by
          gcongr
          exact hhn.trans_eq (by rw [toReal_eLpNorm_fourierInv_annularSymbol B hR])
      _ ≤ (2 * Real.pi)⁻¹ * (R⁻¹ * (∑ j, K j) * ‖g‖) := by
          gcongr
          exact Finset.single_le_sum (fun j _ ↦ hK j) (Finset.mem_univ i)
      _ = (2 * Real.pi)⁻¹ * (∑ j, K j) / R * ‖g‖ := by ring

/-- **Reproducing formula on an annulus.** Let `b` be an orthonormal basis of `E` and `B` a real
number. There is a constant `C`, depending only on `b` and `B`, with the following property. Let
`1 ≤ p ≤ ∞` and let `f ∈ Lᵖ` have Fourier transform vanishing on the ball of radius `R > 0` and
outside the closed ball of radius `B R`. Then `f = ∑ᵢ ∂_{bᵢ} hᵢ` for `Lᵖ` functions `hᵢ` whose
Fourier transforms vanish on the same set, with `‖hᵢ‖_p ≤ C R⁻¹ ‖f‖_p`.

So on an annulus every function is a sum of derivatives of functions smaller by a factor of order
`R⁻¹`; applied `k` times, this writes `f` as a sum of derivatives of order `k` of functions of
size `R⁻ᵏ ‖f‖_p`. -/
theorem _root_.OrthonormalBasis.exists_eq_sum_lineDerivOp_and_norm_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) →
      ∃ h : ι → Lp F p (volume : Measure E), (f : 𝓢'(E, F)) = ∑ i, ∂_{b i} (h i : 𝓢'(E, F)) ∧
        ∀ i, IsVanishingOn (𝓕 (h i : 𝓢'(E, F)) : 𝓢'(E, F))
          (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) ∧ ‖h i‖ ≤ C / R * ‖f‖ := by
  have hB : 1 ≤ max B 1 := le_max_right _ _
  obtain ⟨C, hC, hT⟩ := b.exists_smul_fourierMultiplierCLM_annularSymbol_eq (F := F) (max B 1)
  refine ⟨C, hC, fun {p} _ {R} hR f hf ↦ ?_⟩
  have hf' : IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F))
      (ball 0 R ∪ (closedBall 0 (max B 1 * R))ᶜ) :=
    hf.mono (Set.union_subset_union_right _ (Set.compl_subset_compl.2
      (closedBall_subset_closedBall (by gcongr; exact le_max_left _ _))))
  -- `hᵢ = (2πi)⁻¹ T_{σᵢ} f`, and `∂_{bᵢ}` commutes with `T_{σᵢ}`.
  choose h hh hhn using hT hR f
  refine ⟨h, ?_, fun i ↦ ⟨?_, hhn i⟩⟩
  · have h2π : (2 * Real.pi * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    have hcomm (i : ι) : ∂_{b i} (TemperedDistribution.fourierMultiplierCLM F
        (annularSymbol (max B 1) R (b i)) (f : 𝓢'(E, F))) =
          TemperedDistribution.fourierMultiplierCLM F (annularSymbol (max B 1) R (b i))
            (∂_{b i} (f : 𝓢'(E, F))) := by
      rw [← coe_annularSymbolSchwartz (max B 1) hR]
      exact TemperedDistribution.lineDerivOp_fourierMultiplierCLM
        (annularSymbolSchwartz (max B 1) hR (b i)).hasTemperateGrowth _ _
    simp_rw [← hh, LineDeriv.lineDerivOp_smul, hcomm, ← Finset.smul_sum,
      b.sum_fourierMultiplierCLM_annularSymbol_lineDerivOp hB hR hf', smul_smul,
      inv_mul_cancel₀ h2π, one_smul]
  · rw [← hh i, FourierTransform.fourier_smul, ← coe_annularSymbolSchwartz (max B 1) hR,
      TemperedDistribution.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
    exact fun ψ hψ ↦ by
      rw [smul_apply, Distribution.TemperedDistribution.IsVanishingOn.smulLeftCLM hf
        (annularSymbolSchwartz (max B 1) hR (b i)).hasTemperateGrowth ψ hψ, smul_zero]

/-- **The reverse Bernstein inequality for one derivative.** Let `b` be an orthonormal basis of
`E` and `B` a real number. There is a constant `C`, depending only on `b` and `B`, with the
following property. Let `1 ≤ p ≤ ∞` and let `f ∈ Lᵖ` have Fourier transform vanishing on the
ball of radius `R > 0` and outside the closed ball of radius `B R`. If the derivatives `∂_{bᵢ} f`
are the `Lᵖ` functions `gᵢ`, then

`‖f‖_p ≤ C R⁻¹ ∑ᵢ ‖gᵢ‖_p`.

So on an annulus differentiation loses at most a factor of order `R`, in both directions:
Bernstein's inequality `TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`
bounds `‖∂_{bᵢ} f‖_p` by a constant multiple of `R ‖f‖_p`, and provides the functions `gᵢ`. -/
theorem _root_.OrthonormalBasis.exists_norm_le_div_mul_sum_norm_of_lineDerivOp_eq
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R →
      ∀ (f : Lp F p (volume : Measure E)) (g : ι → Lp F p (volume : Measure E)),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) →
      (∀ i, ∂_{b i} (f : 𝓢'(E, F)) = g i) → ‖f‖ ≤ C / R * ∑ i, ‖g i‖ := by
  have hB : 1 ≤ max B 1 := le_max_right _ _
  obtain ⟨C, hC, hT⟩ := b.exists_smul_fourierMultiplierCLM_annularSymbol_eq (F := F) (max B 1)
  refine ⟨C, hC, fun {p} _ {R} hR f g hf hg ↦ ?_⟩
  have hf' : IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F))
      (ball 0 R ∪ (closedBall 0 (max B 1 * R))ᶜ) :=
    hf.mono (Set.union_subset_union_right _ (Set.compl_subset_compl.2
      (closedBall_subset_closedBall (by gcongr; exact le_max_left _ _))))
  -- `hᵢ = (2πi)⁻¹ T_{σᵢ} gᵢ`, and `f = ∑ᵢ hᵢ` by the reproducing formula.
  choose h hh hhn using fun i ↦ hT hR (g i) i
  have hdist : (f : 𝓢'(E, F)) = ((∑ i, h i : Lp F p (volume : Measure E)) : 𝓢'(E, F)) := by
    have h2π : (2 * Real.pi * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    have := b.sum_fourierMultiplierCLM_annularSymbol_lineDerivOp hB hR hf'
    simp_rw [hg] at this
    rw [Lp.toTemperedDistribution_sum]
    simp_rw [← hh]
    rw [← Finset.smul_sum, this, smul_smul, inv_mul_cancel₀ h2π, one_smul]
  have hfh : f = ∑ i, h i :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F)
      (μ := (volume : Measure E)) (p := p)) hdist
  calc ‖f‖ ≤ ∑ i, ‖h i‖ := hfh ▸ norm_sum_le _ _
    _ ≤ ∑ i, C / R * ‖g i‖ := Finset.sum_le_sum fun i _ ↦ hhn i
    _ = C / R * ∑ i, ‖g i‖ := by rw [Finset.mul_sum]

/-- **The reverse Bernstein inequality.** Let `b` be an orthonormal basis of `E` and `B` a real
number. There is a constant `C`, depending only on `b` and `B`, with the following property. Let
`1 ≤ p ≤ ∞` and let `f ∈ Lᵖ` have Fourier transform vanishing on the ball of radius `R > 0` and
outside the closed ball of radius `B R`. If for every `i : Fin k → ι` the derivative
`∂_{b_{i₀}} ⋯ ∂_{b_{iₖ₋₁}} f` of order `k` is the `Lᵖ` function `gᵢ`, then

`‖f‖_p ≤ (C / R) ^ k ∑ᵢ ‖gᵢ‖_p`.

Bernstein's inequality `TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`
provides the functions `gᵢ`, and bounds each of them by a constant multiple of `R ^ k ‖f‖_p`. -/
theorem _root_.OrthonormalBasis.exists_norm_le_div_pow_mul_sum_norm_of_iteratedLineDerivOp_eq
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (k : ℕ) {R : ℝ}, 0 < R →
      ∀ (f : Lp F p (volume : Measure E)) (g : (Fin k → ι) → Lp F p (volume : Measure E)),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) →
      (∀ i, ∂^{⇑b ∘ i} (f : 𝓢'(E, F)) = g i) → ‖f‖ ≤ (C / R) ^ k * ∑ i, ‖g i‖ := by
  obtain ⟨C, hC, h₁⟩ := b.exists_norm_le_div_mul_sum_norm_of_lineDerivOp_eq (F := F) B
  refine ⟨C, hC, fun {p} _ k {R} hR f ↦ ?_⟩
  induction k with
  | zero =>
    intro g _ hg
    have hfg : f = g default := LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := F) (μ := (volume : Measure E)) (p := p)) (by simpa using hg default)
    simp [hfg]
  | succ k ih =>
    intro g hf hg
    -- The derivatives of order `k` are `Lᵖ` functions by Bernstein's inequality, with spectra in
    -- the same annulus.
    obtain ⟨C', -, hderiv⟩ :=
      exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
        (p := p) (q := p) le_rfl
    have hfball : IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (max B 1 * R))ᶜ :=
      hf.mono (Set.subset_union_of_subset_right (Set.compl_subset_compl.2
        (closedBall_subset_closedBall (by gcongr; exact le_max_left _ _))) _)
    choose h hh _ using fun i : Fin k → ι ↦ hderiv k (⇑b ∘ i) (by positivity) f hfball
    have hhf (i : Fin k → ι) : IsVanishingOn (𝓕 (h i : 𝓢'(E, F)) : 𝓢'(E, F))
        (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) := by
      rw [← hh i]
      exact isVanishingOn_fourier_iteratedLineDerivOp hf _
    -- One more derivative of `hᵢ` along `b j` is the derivative `g (Fin.cons j i)` of `f`.
    have hhg (i : Fin k → ι) (j : ι) : ∂_{b j} (h i : 𝓢'(E, F)) = g (Fin.cons j i) := by
      rw [← hh i, ← hg, LineDeriv.iteratedLineDerivOp_succ_left, Fin.comp_cons, Fin.cons_zero,
        Fin.tail_cons]
    calc ‖f‖ ≤ (C / R) ^ k * ∑ i, ‖h i‖ := ih h hf hh
      _ ≤ (C / R) ^ k * ∑ i, C / R * ∑ j, ‖g (Fin.cons j i)‖ := by
        gcongr with i
        exact h₁ hR (h i) (fun j ↦ g (Fin.cons j i)) (hhf i) (hhg i)
      _ = (C / R) ^ (k + 1) * ∑ i, ‖g i‖ := by
        rw [← Finset.mul_sum, ← mul_assoc, ← pow_succ, Finset.sum_comm,
          ← Fintype.sum_prod_type', Fintype.sum_equiv (Fin.consEquiv fun _ ↦ ι)
            (fun x ↦ ‖g (Fin.cons x.1 x.2)‖) (fun i ↦ ‖g i‖)
            fun x ↦ by rw [Fin.consEquiv_apply]]

end TauCeti
