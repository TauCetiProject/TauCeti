/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Dilation

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
is the gain of integrability `‖f‖_q ≤ C R ^ (n (1/p - 1/q)) ‖f‖_p` of a band-limited function, and
the case `p = q`, `k = 1` says that differentiating costs at most a factor `C R`.

These are the basic estimates for functions whose spectrum lies in a ball, such as the
Littlewood–Paley blocks of a tempered distribution: they convert the frequency localization of a
block into bounds on its derivatives and on its higher Lebesgue norms.

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
that of `𝓕⁻ χ`, and the `L¹` norm of the second is `R` times that of `∂_m 𝓕⁻ χ`, which is at most
a fixed multiple of `‖m‖`. Derivatives of a band-limited distribution are again band-limited
(`TemperedDistribution.isVanishingOn_fourier_iteratedLineDerivOp`), so the bounds for one
derivative iterate.

## Main declarations

* `TauCeti.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`: Bernstein's
  inequalities.

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

/-- **Dilating a symbol rescales the `Lʳ` norm of its kernel:** the kernel of `ξ ↦ g (R⁻¹ • ξ)`
has `Lʳ` norm `R ^ (n - n / r)` times that of the kernel of `g`. -/
private theorem eLpNorm_fourierInv_comp_inv_smul (g : E → ℂ) {R : ℝ} (hR : 0 < R)
    (r : ℝ≥0∞) :
    eLpNorm (𝓕⁻ fun ξ ↦ g (R⁻¹ • ξ)) r volume =
      ENNReal.ofReal (R ^ ((finrank ℝ E : ℝ) - finrank ℝ E / r.toReal)) *
        eLpNorm (𝓕⁻ g) r volume := by
  have h : (𝓕⁻ fun ξ ↦ g (R⁻¹ • ξ)) =
      (R ^ finrank ℝ E : ℝ) • fun x ↦ 𝓕⁻ g ((R⁻¹)⁻¹ • x) := by
    ext x
    simp [fourierInv_comp_smul g (inv_ne_zero hR.ne'), abs_of_pos hR]
  rw [h, eLpNorm_const_smul, Measure.eLpNorm_comp_inv_smul volume _ (inv_pos.2 hR), ← mul_assoc,
    ← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity), Real.inv_rpow hR.le, ← Real.rpow_natCast,
    ← Real.rpow_neg hR.le, ← Real.rpow_add hR, sub_eq_add_neg]

variable [CompleteSpace F]

/-- **Bernstein's inequality without derivatives.** For `1 ≤ p ≤ q ≤ ∞`, an `Lᵖ` function whose
Fourier transform vanishes outside the ball of radius `R` is in `Lᵠ`, with
`‖f‖_q ≤ C R ^ (n (1/p - 1/q)) ‖f‖_p`. -/
private theorem exists_eq_and_norm_le {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) :
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
              ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hfin) hderiv
          _ = ‖m‖ * (eLpNorm (fderiv ℝ K) 1 volume).toReal := by
              rw [ENNReal.toReal_mul, toReal_enorm]
    _ = (eLpNorm (fderiv ℝ K) 1 volume).toReal * R * ‖m‖ := by ring

/-- **Bernstein's inequality for one derivative.** An `Lᵖ` function whose Fourier transform
vanishes outside the ball of radius `R` has derivatives in `Lᵖ`, with
`‖∂_m f‖_p ≤ C R ‖m‖ ‖f‖_p`. -/
private theorem exists_lineDerivOp_eq_and_norm_le {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ → ∀ m : E,
      ∃ g : Lp F p (volume : Measure E), ∂_{m} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R * ‖m‖ * ‖f‖ := by
  refine ⟨(eLpNorm (fderiv ℝ (𝓕⁻ (cutoff (E := E) one_pos) : 𝓢(E, ℂ))) 1 volume).toReal,
    ENNReal.toReal_nonneg, fun {R} hR f hf m ↦ ?_⟩
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
  obtain ⟨C, hC, h₁⟩ := exists_lineDerivOp_eq_and_norm_le (E := E) (F := F) (p := p)
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
  obtain ⟨C₀, hC₀, h₀⟩ := exists_eq_and_norm_le (E := E) (F := F) hpq
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

end TauCeti
