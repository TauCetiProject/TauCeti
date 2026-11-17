/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LpSpace
public import TauCeti.MeasureTheory.Integral.RieszThorin
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# The Hausdorff–Young inequality

On a finite-dimensional real inner product space `E` with the normalization
`𝓕 f ξ = ∫ 𝐞(-⟪x, ξ⟫) f x` of the Fourier transform, the Fourier integral of an integrable complex
function `f` satisfies, for `1 ≤ p ≤ 2` and the conjugate exponent `p'` (`1 / p + 1 / p' = 1`),

`‖𝓕 f‖_{p'} ≤ ‖f‖_p`

(`MeasureTheory.Integrable.eLpNorm_fourier_le`). In particular `𝓕 f ∈ L^{p'}` whenever
`f ∈ L¹ ∩ Lᵖ` (`MeasureTheory.Integrable.memLp_fourier`). The constant is `1`, with no dependence
on the dimension, because the `2π` in the exponent makes both endpoint bounds exact.

The inequality interpolates its two endpoints, `‖𝓕 f‖_∞ ≤ ‖f‖₁`
(`TauCeti.eLpNorm_fourier_top_le`) and Plancherel's theorem `‖𝓕 f‖₂ = ‖f‖₂` on `L¹ ∩ L²`
(`TauCeti.Analysis.Fourier.LpSpace`), by the Riesz–Thorin theorem
(`TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm`) with `1 / p = (1 - θ) + θ / 2` and
`1 / p' = θ / 2`. Riesz–Thorin needs an operator that is linear on all simple functions, and the
Fourier integral is only additive on integrable functions; so it is applied to `g ↦ 𝓕 (1_s g)` for
a set `s` of finite measure, which is linear on simple functions. Taking for `s` the support of an
integrable simple function gives the inequality on integrable simple functions. A general
integrable `f ∈ Lᵖ` is the limit of integrable simple functions `gₙ` both in `L¹` and in `Lᵖ`
(`MeasureTheory.SimpleFunc.approxOn`); the `L¹` convergence makes `𝓕 gₙ → 𝓕 f` uniformly
(`MeasureTheory.Integrable.tendstoUniformly_fourier`), and
Fatou's lemma for `L^{p'}` norms passes the inequality to the limit.

## Main declarations

* `MeasureTheory.Integrable.eLpNorm_fourier_le`: **the Hausdorff–Young inequality**
  `‖𝓕 f‖_{p'} ≤ ‖f‖_p` for integrable `f` and `1 ≤ p ≤ 2`.
* `MeasureTheory.Integrable.memLp_fourier`: the Fourier integral of `f ∈ L¹ ∩ Lᵖ`,
  `1 ≤ p ≤ 2`, lies in `L^{p'}`.

## References

* F. Hausdorff, *Eine Ausdehnung des Parsevalschen Satzes über Fourierreihen*, Math. Z. 16
  (1923).
* W. H. Young, *On the determination of the summability of a function by means of its Fourier
  constants*, Proc. London Math. Soc. 12 (1913).
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Proposition 2.2.16.
* E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter V,
  Theorem 2.1.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TauCeti.HausdorffYoung

/-- The Fourier integral of simple functions cut off to a set `s` of finite measure, as a linear
map into almost-everywhere classes. It is the operator to which Riesz–Thorin is applied. -/
private noncomputable def fourierIndicator {s : Set E} (hs : MeasurableSet s)
    (hsfin : volume s ≠ ∞) : (SimpleFunc E ℂ) →ₗ[ℂ] (E →ₘ[volume] ℂ) where
  toFun g := AEEqFun.mk (𝓕 (s.indicator g))
    (g.integrable_indicator hs hsfin).continuous_fourier.aestronglyMeasurable
  map_add' g h := by
    rw [AEEqFun.mk_add_mk]
    congr 1
    rw [FunLike.coe_add, indicator_add',
      (g.integrable_indicator hs hsfin).fourier_add (h.integrable_indicator hs hsfin)]
  map_smul' c g := by
    rw [AEEqFun.smul_mk]
    congr 1
    rw [FunLike.coe_smul, ← Real.fourier_const_smul]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx]

/-- The norms of `fourierIndicator` are those of the Fourier integral of the cut-off function. -/
private theorem eLpNorm_fourierIndicator {s : Set E} (hs : MeasurableSet s)
    (hsfin : volume s ≠ ∞) (g : SimpleFunc E ℂ) (q : ℝ≥0∞) :
    eLpNorm (fourierIndicator hs hsfin g) q volume = eLpNorm (𝓕 (s.indicator g)) q volume :=
  eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)

/-- The Hausdorff–Young inequality for a simple function cut off to a set of finite measure. -/
private theorem eLpNorm_fourier_indicator_le {s : Set E} (hs : MeasurableSet s)
    (hsfin : volume s ≠ ∞) (g : SimpleFunc E ℂ) {p : ℝ≥0∞} (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2) :
    eLpNorm (𝓕 (s.indicator g)) p.conjExponent volume ≤ eLpNorm (s.indicator g) p volume := by
  have hc₁ : (1 : ℝ≥0∞).conjExponent = ∞ :=
    ENNReal.HolderConjugate.conjExponent_eq (h := .one_top)
  have hc₂ : (2 : ℝ≥0∞).conjExponent = 2 := ENNReal.HolderConjugate.conjExponent_eq
  rcases hp₁.eq_or_lt with rfl | hp₁
  · rw [hc₁]
    exact eLpNorm_fourier_top_le _
  rcases hp₂.eq_or_lt with rfl | hp₂
  · rw [hc₂, (g.integrable_indicator hs hsfin).eLpNorm_fourier_two_eq (g.memLp_indicator hs hsfin)]
  -- Interpolate between `(1, ∞)` and `(2, 2)`.
  obtain ⟨θ, hθ, hpθ⟩ := exists_inv_eq_of_mem_Ioo one_ne_zero ⟨hp₁, hp₂⟩
  have hqθ : p.conjExponent⁻¹ = ENNReal.ofReal (1 - θ) * (∞ : ℝ≥0∞)⁻¹ +
      ENNReal.ofReal θ * 2⁻¹ := by
    rw [← hc₁, ← hc₂]
    exact inv_conjExponent_eq_of_inv_eq le_rfl one_le_two (Ioo_subset_Icc_self hθ) hpθ
  have key := eLpNorm_le_rpow_mul_rpow_mul_eLpNorm (μ := volume.restrict s) (ν := volume)
    (T := fourierIndicator hs hsfin) (M₀ := 1) (M₁ := 1) le_top one_le_two hθ hpθ hqθ
    (fun g' => ?_) (fun g' => ?_) g
  · rwa [eLpNorm_fourierIndicator, NNReal.one_rpow, NNReal.one_rpow, mul_one, ENNReal.coe_one,
      one_mul, ← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet] at key
  · rw [eLpNorm_fourierIndicator, ENNReal.coe_one, one_mul,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
    exact eLpNorm_fourier_top_le _
  · rw [eLpNorm_fourierIndicator, ENNReal.coe_one, one_mul,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
      (g'.integrable_indicator hs hsfin).eLpNorm_fourier_two_eq (g'.memLp_indicator hs hsfin)]

/-- The Hausdorff–Young inequality for an integrable simple function. -/
private theorem eLpNorm_fourier_simpleFunc_le (g : SimpleFunc E ℂ) (hg : Integrable g) {p : ℝ≥0∞}
    (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2) :
    eLpNorm (𝓕 ⇑g) p.conjExponent volume ≤ eLpNorm g p volume := by
  simpa only [indicator_support] using eLpNorm_fourier_indicator_le g.measurableSet_support
    (g.measure_support_lt_top_of_integrable hg).ne g hp₁ hp₂

end TauCeti.HausdorffYoung

namespace MeasureTheory.Integrable

open TauCeti.HausdorffYoung in
/-- **The Hausdorff–Young inequality.** For `1 ≤ p ≤ 2` the Fourier integral of an integrable
complex function satisfies `‖𝓕 f‖_{p'} ≤ ‖f‖_p`, where `p' = p.conjExponent` is the conjugate
exponent. -/
theorem eLpNorm_fourier_le {f : E → ℂ} (hf : Integrable f) {p : ℝ≥0∞} (hp₁ : 1 ≤ p)
    (hp₂ : p ≤ 2) : eLpNorm (𝓕 f) p.conjExponent volume ≤ eLpNorm f p volume := by
  -- Pass to a strongly measurable representative `f'`, which has the same Fourier integral.
  have hfm := hf.aestronglyMeasurable
  set f' := hfm.mk f
  have hff' : f =ᵐ[volume] f' := hfm.ae_eq_mk
  have hf'i : Integrable f' := hf.congr hff'
  have hf'm : StronglyMeasurable f' := hfm.stronglyMeasurable_mk
  rw [show 𝓕 f = 𝓕 f' from funext (Real.fourier_congr_ae hff'), eLpNorm_congr_ae hff']
  rcases eq_or_ne (eLpNorm f' p volume) ∞ with h | h
  · rw [h]
    exact le_top
  have hp_top : p ≠ ∞ := (hp₂.trans_lt ENNReal.ofNat_lt_top).ne
  -- Integrable simple functions `gₙ` converging to `f'` in `L¹` and in `Lᵖ`.
  set g : ℕ → SimpleFunc E ℂ := fun n =>
    SimpleFunc.approxOn f' hf'm.measurable (range f' ∪ {0}) 0 (by simp) n
  have hg (n : ℕ) : Integrable (g n) :=
    SimpleFunc.integrable_approxOn hf'm.measurable hf'i _ (integrable_zero _ _ _) n
  have hcl : ∀ᵐ x ∂volume, f' x ∈ closure (range f' ∪ {0}) :=
    ae_of_all _ fun x => subset_closure (Or.inl (mem_range_self x))
  have hg₁ : Tendsto (fun n => eLpNorm (⇑(g n) - f') 1 volume) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_Lp_eLpNorm hf'm.measurable _ ENNReal.one_ne_top hcl
      (by simpa using (memLp_one_iff_integrable.2 hf'i).eLpNorm_lt_top)
  have hgp : Tendsto (fun n => eLpNorm (⇑(g n) - f') p volume) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_Lp_eLpNorm hf'm.measurable _ hp_top hcl (by simpa using h.lt_top)
  -- The `L¹` convergence makes the Fourier integrals converge at every point.
  have hlim (ξ : E) : Tendsto (fun n => 𝓕 ⇑(g n) ξ) atTop (𝓝 (𝓕 f' ξ)) :=
    (hf'i.tendstoUniformly_fourier hg hg₁).tendsto_at ξ
  -- Fatou's lemma and the inequality for the simple functions `gₙ`.
  calc eLpNorm (𝓕 f') p.conjExponent volume
      ≤ atTop.liminf fun n => eLpNorm (𝓕 ⇑(g n)) p.conjExponent volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hg n).continuous_fourier.aestronglyMeasurable)
          _ hf'i.continuous_fourier.aestronglyMeasurable (ae_of_all _ hlim)
    _ ≤ atTop.liminf fun n => eLpNorm f' p volume + eLpNorm (⇑(g n) - f') p volume := by
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
        refine (eLpNorm_fourier_simpleFunc_le (g n) (hg n) hp₁ hp₂).trans ?_
        calc eLpNorm (g n) p volume = eLpNorm (f' + (⇑(g n) - f')) p volume := by
              rw [add_sub_cancel]
          _ ≤ _ := eLpNorm_add_le hp₁
    _ = eLpNorm f' p volume := by simpa using (tendsto_const_nhds.add hgp).liminf_eq

/-- For `1 ≤ p ≤ 2` the Fourier integral of a function in `L¹ ∩ Lᵖ` lies in `L^{p'}`, where
`p' = p.conjExponent` is the conjugate exponent. -/
theorem memLp_fourier {f : E → ℂ} (hf : Integrable f) {p : ℝ≥0∞} (hfp : MemLp f p)
    (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2) : MemLp (𝓕 f) p.conjExponent :=
  memLp_iff.2 ((hf.eLpNorm_fourier_le hp₁ hp₂).trans_lt hfp.eLpNorm_lt_top)

end MeasureTheory.Integrable
