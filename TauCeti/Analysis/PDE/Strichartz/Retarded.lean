/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.ChristKiselev
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Retarded estimates from two dual estimates

Let `V(s) : L²(X, μ) → H`, `s ∈ ℝ`, be a family of bounded operators into a Hilbert space, for
instance the adjoints `V(s) = U(s)*` of a propagator `U(s)`, so that `V(s) = exp(-isΔ)` for the
Schrödinger group. A *dual estimate* for `V` with exponents `(p, r)` is a bound

`‖∫ V(s) F(s) ds‖ ≤ B ‖F‖_{L^p_t L^r_x}`

for every `F : ℝ → L²(X, μ)`, where the mixed norm of `F` is
`eLpNorm (fun s ↦ eLpNorm (F s) r μ) p volume`. For a unitary group `U`, two such estimates control
the untruncated Duhamel pairing

`∫∫ ⟪U(t - s) F(s), G(t)⟫ ds dt = ⟪∫ U(s)* F(s) ds, ∫ U(t)* G(t) dt⟫`

with `F` and `G` measured in the two (possibly different) mixed norms. The inhomogeneous
Strichartz estimate is about the *retarded* pairing, restricted to `s < t`, which does not factor.

This file proves that the retarded pairing obeys the same bound, up to a constant depending only on
the time exponents, whenever `1 / p₁ + 1 / p₂ > 1` and `1 ≤ p₂`
(`TauCeti.enorm_integral_setIntegral_Iio_inner_le`):

`|∫ ∫_{s < t} ⟪V(s) F(s), V(t) G(t)⟫ ds dt| ≤ C B₁ B₂ ‖F‖_{L^{p₁} L^{r₁}} ‖G‖_{L^{p₂} L^{r₂}}`,

with `C = (1 - 2^{-δ})⁻¹` and `δ = 1 / p₁ + 1 / p₂ - 1`. For Strichartz estimates the time
exponents are the Hölder conjugates `q₁'` and `q₂'` of two admissible exponents `q₁, q₂ > 2`, so the
condition holds. The dual estimates themselves come from the `TT*` argument of
`TauCeti.Analysis.PDE.Strichartz.TTStar`, or from the energy bound at the pair `(1, 2)`.

## The argument

On a rectangle `I × J` the pairing factors as `⟪∫_I V(s) F(s) ds, ∫_J V(t) G(t) dt⟫`, and the two
dual estimates applied to `1_I F` and `1_J G` bound it by `B₁ B₂ ‖1_I F‖ ‖1_J G‖`. The
Christ–Kiselev lemma (`TauCeti.eNorm_setIntegral_fst_lt_snd_le`) passes from rectangles with `I`
to the left of `J` to the whole region `s < t`.

## Main declarations

* `TauCeti.enorm_integral_setIntegral_Iio_inner_le`: the retarded estimate from two dual
  estimates.

## References

* M. Christ and A. Kiselev, *Maximal functions associated to filtrations*, J. Funct. Anal. **179**
  (2001), 409–425.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Lemma 2.4 and the proof of Theorem 2.3.
-/

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {𝕜 X E H : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [NormedSpace ℝ H]

/-- Replacing a function `n` with values in `[0, ∞]` and finite `Lᵖ` norm by its real part does
not change the `Lᵖ` norm of any of its restrictions. -/
private theorem eLpNorm_indicator_toReal {n : ℝ → ℝ≥0∞} {p : ℝ≥0∞} (hn : eLpNorm n p ≠ ∞)
    {I : Set ℝ} (hI : MeasurableSet I) :
    eLpNorm (I.indicator fun s ↦ (n s).toReal) p = eLpNorm (I.indicator n) p := by
  have h : (I.indicator fun s ↦ (n s).toReal) = fun s ↦ (I.indicator n s).toReal := by
    ext s
    by_cases hs : s ∈ I <;> simp [hs]
  rw [h, eLpNorm_toReal (ne_top_of_le_ne_top hn (eLpNorm_indicator_le n hI.nullMeasurableSet))]

omit [CompleteSpace H] in
/-- A dual estimate restricted to a measurable set of times `I`: the integral of `V(s) F(s)` over
`I` is bounded by the mixed norm of `F` restricted to `I`. -/
private theorem enorm_setIntegral_le_of_dual {V : ℝ → Lp E 2 μ →L[𝕜] H} {p r B : ℝ≥0∞}
    (hB : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ V s (F s)) →
      ‖∫ s, V s (F s)‖ₑ ≤ B * eLpNorm (fun s ↦ eLpNorm (F s) r μ) p)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hVF : Integrable (fun s ↦ V s (F s)))
    {I : Set ℝ} (hI : MeasurableSet I) :
    ‖∫ s in I, V s (F s)‖ₑ ≤ B * eLpNorm (I.indicator fun s ↦ eLpNorm (F s) r μ) p := by
  have hV : (fun s ↦ V s (I.indicator F s)) = I.indicator fun s ↦ V s (F s) := by
    ext s
    by_cases hs : s ∈ I <;> simp [hs]
  have hn : (fun s ↦ eLpNorm (⇑(I.indicator F s)) r μ) =
      I.indicator fun s ↦ eLpNorm (F s) r μ := by
    ext s
    by_cases hs : s ∈ I
    · simp [hs]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs,
        eLpNorm_congr_ae (Lp.coeFn_zero E 2 μ), eLpNorm_zero]
  have h := hB (I.indicator F) (hF.indicator hI) (by rw [hV]; exact hVF.indicator hI)
  rwa [hV, hn, integral_indicator hI] at h

/-- **The rectangle bound.** Over a rectangle of times `I × J` the pairing
`⟪V(s) F(s), V(t) G(t)⟫` integrates to `⟪∫_I V(s) F(s) ds, ∫_J V(t) G(t) dt⟫`, so the two dual
estimates bound it by the mixed norms of `1_I F` and `1_J G`. -/
private theorem enorm_setIntegral_prod_inner_le {V : ℝ → Lp E 2 μ →L[𝕜] H}
    {p₁ p₂ r₁ r₂ B₁ B₂ : ℝ≥0∞}
    (hB₁ : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ V s (F s)) →
      ‖∫ s, V s (F s)‖ₑ ≤ B₁ * eLpNorm (fun s ↦ eLpNorm (F s) r₁ μ) p₁)
    (hB₂ : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ V t (G t)) →
      ‖∫ t, V t (G t)‖ₑ ≤ B₂ * eLpNorm (fun t ↦ eLpNorm (G t) r₂ μ) p₂)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G)
    (hVF : Integrable (fun s ↦ V s (F s))) (hVG : Integrable (fun t ↦ V t (G t)))
    {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    ‖∫ z in I ×ˢ J, ⟪V z.1 (F z.1), V z.2 (G z.2)⟫_𝕜‖ₑ ≤
      B₁ * eLpNorm (I.indicator fun s ↦ eLpNorm (F s) r₁ μ) p₁ *
        (B₂ * eLpNorm (J.indicator fun t ↦ eLpNorm (G t) r₂ μ) p₂) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_inner hVF.integrableOn
    hVG.integrableOn]
  exact (eNorm_inner_le_eNorm _ _).trans (mul_le_mul'
    (enorm_setIntegral_le_of_dual hB₁ hF hVF hI) (enorm_setIntegral_le_of_dual hB₂ hG hVG hJ))

/-- **The retarded estimate from two dual estimates.** Let `V(s) : L²(X, μ) → H` be bounded
operators satisfying the dual estimates `‖∫ V(s) F(s) ds‖ ≤ B₁ ‖F‖_{L^{p₁} L^{r₁}}` and
`‖∫ V(s) G(s) ds‖ ≤ B₂ ‖G‖_{L^{p₂} L^{r₂}}` for every almost everywhere strongly measurable
`F, G : ℝ → L²(X, μ)` for which `s ↦ V(s) F(s)`, respectively `s ↦ V(s) G(s)`, is integrable.
If `1 ≤ p₂` and `1 / p₁ + 1 / p₂ > 1`, then for all such `F` and `G`

`|∫ ∫_{s < t} ⟪V(s) F(s), V(t) G(t)⟫ ds dt| ≤ C B₁ B₂ ‖F‖_{L^{p₁} L^{r₁}} ‖G‖_{L^{p₂} L^{r₂}}`,

where `C = (1 - 2^{-δ})⁻¹` and `δ = 1 / p₁ + 1 / p₂ - 1 > 0`.

For `V(s) = U(s)*` with a unitary group `U`, the integrand is the Duhamel pairing
`⟪U(t - s) F(s), G(t)⟫`, and this is the retarded (inhomogeneous) estimate
`‖∫_{s < t} U(t - s) F(s) ds‖_{L^{p₂'} L^{r₂'}} ≲ ‖F‖_{L^{p₁} L^{r₁}}` tested against `G`. -/
theorem enorm_integral_setIntegral_Iio_inner_le {V : ℝ → Lp E 2 μ →L[𝕜] H}
    {p₁ p₂ r₁ r₂ B₁ B₂ : ℝ≥0∞} (hp₂ : 1 ≤ p₂) (hp : 1 < p₁⁻¹ + p₂⁻¹)
    (hB₁ : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ V s (F s)) →
      ‖∫ s, V s (F s)‖ₑ ≤ B₁ * eLpNorm (fun s ↦ eLpNorm (F s) r₁ μ) p₁)
    (hB₂ : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ V t (G t)) →
      ‖∫ t, V t (G t)‖ₑ ≤ B₂ * eLpNorm (fun t ↦ eLpNorm (G t) r₂ μ) p₂)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G)
    (hVF : Integrable (fun s ↦ V s (F s))) (hVG : Integrable (fun t ↦ V t (G t))) :
    ‖∫ t, ∫ s in Set.Iio t, ⟪V s (F s), V t (G t)⟫_𝕜‖ₑ ≤
      (1 - 2 ^ (-(p₁⁻¹ + p₂⁻¹ - 1).toReal))⁻¹ * B₁ * B₂ *
        eLpNorm (fun s ↦ eLpNorm (F s) r₁ μ) p₁ * eLpNorm (fun t ↦ eLpNorm (G t) r₂ μ) p₂ := by
  set nF := fun s ↦ eLpNorm (F s) r₁ μ
  set nG := fun t ↦ eLpNorm (G t) r₂ μ
  set c : ℝ≥0∞ := (1 - 2 ^ (-(p₁⁻¹ + p₂⁻¹ - 1).toReal))⁻¹
  set β := fun z : ℝ × ℝ ↦ ⟪V z.1 (F z.1), V z.2 (G z.2)⟫_𝕜
  have hβ' : Integrable β (volume.prod volume) := hVF.inner_prod hVG
  have hβ : Integrable β := by rwa [Measure.volume_eq_prod]
  -- The iterated integral is the integral of `β` over the region `s < t`.
  have hregion := integral_setIntegral_Iio_eq_setIntegral hβ'
  simp only [β] at hregion
  rw [hregion, ← Measure.volume_eq_prod]
  have hrect {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J) :=
    enorm_setIntegral_prod_inner_le hB₁ hB₂ hF hG hVF hVG hI hJ
  by_cases hfin : eLpNorm nF p₁ ≠ ∞ ∧ eLpNorm nG p₂ ≠ ∞
  · -- Both mixed norms are finite: apply the Christ–Kiselev lemma to the real parts of the
    -- spatial norms, which have the same restricted `Lᵖ` norms.
    have h := eNorm_setIntegral_fst_lt_snd_le hp₂ hp hβ.integrableOn (fun s ↦ (nF s).toReal)
      (fun t ↦ (nG t).toReal) (A := B₁ * B₂) fun I J hI hJ _ ↦ by
        rw [eLpNorm_indicator_toReal hfin.1 hI.measurableSet,
          eLpNorm_indicator_toReal hfin.2 hJ.measurableSet]
        exact (hrect hI.measurableSet hJ.measurableSet).trans_eq (by ring)
    rw [eLpNorm_toReal hfin.1, eLpNorm_toReal hfin.2] at h
    exact h.trans_eq (by ring)
  by_cases h0 : B₁ * eLpNorm nF p₁ = 0 ∨ B₂ * eLpNorm nG p₂ = 0
  · -- One side of every rectangle bound vanishes, so the integral vanishes.
    have h := eNorm_setIntegral_fst_lt_snd_le hp₂ hp hβ.integrableOn (fun _ ↦ (0 : ℝ))
      (fun _ ↦ (0 : ℝ)) (A := 0) fun I J hI hJ _ ↦ by
        rw [zero_mul, zero_mul]
        refine (hrect hI.measurableSet hJ.measurableSet).trans (le_of_eq ?_)
        rcases h0 with h0 | h0
        · rw [nonpos_iff_eq_zero.1 ((mul_le_mul' le_rfl (eLpNorm_indicator_le nF
            hI.measurableSet.nullMeasurableSet)).trans h0.le), zero_mul]
        · rw [nonpos_iff_eq_zero.1 ((mul_le_mul' le_rfl (eLpNorm_indicator_le nG
            hJ.measurableSet.nullMeasurableSet)).trans h0.le), mul_zero]
    rw [mul_zero, zero_mul, zero_mul] at h
    exact h.trans bot_le
  · -- Otherwise one mixed norm is infinite and no factor vanishes, so the bound is infinite.
    push Not at hfin h0
    have hc : c ≠ 0 := ENNReal.inv_ne_zero.2 (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    have htop : B₁ * eLpNorm nF p₁ = ∞ ∨ B₂ * eLpNorm nG p₂ = ∞ := by
      by_cases hF' : eLpNorm nF p₁ = ∞
      · exact Or.inl (by rw [hF', ENNReal.mul_top (left_ne_zero_of_mul h0.1)])
      · exact Or.inr (by rw [hfin hF', ENNReal.mul_top (left_ne_zero_of_mul h0.2)])
    have hrhs : c * (B₁ * eLpNorm nF p₁) * (B₂ * eLpNorm nG p₂) = ∞ := by
      rcases htop with h | h
      · rw [h, ENNReal.mul_top hc, ENNReal.top_mul h0.2]
      · rw [h, ENNReal.mul_top (mul_ne_zero hc h0.1)]
    calc _ ≤ ∞ := le_top
      _ = _ := by rw [← hrhs]; ring

end TauCeti
