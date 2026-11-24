/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.Lp.MixedNorm
import TauCeti.MeasureTheory.Integral.ChristKiselev
import TauCeti.MeasureTheory.Integral.Kernel.Pairing
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Retarded Strichartz estimates from dual estimates

Let `U(t) : H → L²(X, μ)`, `t ∈ ℝ`, be a family of bounded operators from a Hilbert space into an
`L²` space, for instance a unitary propagator `exp(itΔ)` on `H = L²(ℝⁿ)`. The solution of the
inhomogeneous equation is given by Duhamel's formula `∫_{s < t} U(t) U(s)* F(s) ds`, and its
Strichartz estimates in weak form bound the retarded pairings

`∫ ∫_{s < t} ⟪U(s)* F(s), U(t)* G(t)⟫ ds dt`.

This file deduces such bounds from the dual estimates

`‖∫ U(s)* F(s) ds‖ ≤ C₁ ‖F‖_{L^{p₁}_t L^{a₁}_x}` and `‖∫ U(t)* G(t) dt‖ ≤ C ‖G‖_{L^p_t L^a_x}`,

which may hold with two different pairs of exponents, as for two different admissible pairs of a
dispersive equation. Without the restriction `s < t` the double integral factors as
`⟪∫ U(s)* F(s) ds, ∫ U(t)* G(t) dt⟫`, so the two dual estimates bound it, and they bound its
restriction to every rectangle of times in the same way. When `1 / p₁ + 1 / p > 1`, the
Christ–Kiselev lemma (`TauCeti.eNorm_setIntegral_fst_lt_snd_le`) passes this bound to the
retarded region `s < t`:

`|∫ ∫_{s < t} ⟪U(s)* F(s), U(t)* G(t)⟫ ds dt|
  ≤ (1 - 2^{-δ})⁻¹ C₁ C ‖F‖_{L^{p₁} L^{a₁}} ‖G‖_{L^p L^a}`,

where `δ = 1 / p₁ + 1 / p - 1`. For a dispersive equation with admissible pairs `(q, r)` and
`(q₁, r₁)` the time exponents are `p = q'` and `p₁ = q₁'`, and the condition reads `q₁' < q`. It
fails only when both pairs are at the endpoint `q = q₁ = 2`, which needs the Keel–Tao argument
instead (`TauCeti.exists_enorm_integral_setIntegral_Iio_inner_adjoint_le_of_endpoint`).

The mixed norm of a function `F : ℝ → L²(X, μ)` is written
`eLpNorm (fun s ↦ eLpNorm (F s) a μ) p volume`, as in `TauCeti.Analysis.PDE.Strichartz.TTStar`.

## Main declarations

* `TauCeti.enorm_setIntegral_adjoint_le`: a dual estimate restricted to a set of times.
* `TauCeti.enorm_integral_adjoint_neg_le`: a dual estimate for the time-reversed operators
  `U(-t)`.
* `TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le`: the retarded estimate from the two
  dual estimates.
* `TauCeti.one_lt_inv_add_inv_of_holderConjugate`: two time exponents, at most one of them at
  the endpoint `2`, satisfy the Christ–Kiselev condition `q₁' < q`.
* `TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le_of_holderConjugate`: the retarded
  estimate for the Hölder conjugates of two such time exponents, with a finite constant.

## References

* M. Christ and A. Kiselev, *Maximal functions associated to filtrations*, J. Funct. Anal. **179**
  (2001), 409–425.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 and Lemma 2.4.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

variable {𝕜 X E H : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [NormedSpace ℝ H]

/-- Time exponents `2 < q ≤ ∞` and `2 ≤ q₁ ≤ ∞`, at most one of them at the endpoint `2`, satisfy
the Christ–Kiselev condition of `TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le` for their
Hölder conjugates `p = q'` and `p₁ = q₁'`: `1 / p₁ + 1 / p > 1`, that is `q₁' < q`. -/
theorem one_lt_inv_add_inv_of_holderConjugate {p q p₁ q₁ : ℝ≥0∞} [p.HolderConjugate q]
    [p₁.HolderConjugate q₁] (hq : 2 < q) (hq₁ : 2 ≤ q₁) : 1 < p₁⁻¹ + p⁻¹ := by
  have h := ENNReal.HolderConjugate.inv_add_inv_eq_one p q
  have h₁ := ENNReal.HolderConjugate.inv_add_inv_eq_one p₁ q₁
  -- Otherwise `2 = (p₁⁻¹ + p⁻¹) + (q₁⁻¹ + q⁻¹) < 1 + (2⁻¹ + 2⁻¹) = 2`.
  by_contra hle
  rw [not_lt] at hle
  have hq' : q₁⁻¹ + q⁻¹ < 1 := by
    rw [← ENNReal.inv_two_add_inv_two]
    exact ENNReal.add_lt_add_of_le_of_lt (ENNReal.inv_ne_top.2 (by positivity))
      (ENNReal.inv_le_inv.2 hq₁) (ENNReal.inv_lt_inv.2 hq)
  have h2 : (2 : ℝ≥0∞) < 2 :=
    calc (2 : ℝ≥0∞) = (p₁⁻¹ + p⁻¹) + (q₁⁻¹ + q⁻¹) := by
          rw [add_add_add_comm, h₁, h, one_add_one_eq_two]
      _ < 1 + 1 := ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
          hle hq'
      _ = 2 := one_add_one_eq_two
  exact lt_irrefl _ h2

/-- A dual estimate applies to the restriction of `F` to a set of times `I`, and bounds
`∫_I U(s)* F(s) ds` by the mixed norm of `1_I F`. -/
theorem enorm_setIntegral_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {a p C : ℝ≥0∞}
    (hC : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ C * eLpNorm (fun s ↦ eLpNorm (F s) a μ) p)
    {F : ℝ → Lp E 2 μ} {I : Set ℝ} (hI : MeasurableSet I)
    (hF : AEStronglyMeasurable F (volume.restrict I))
    (hUF : IntegrableOn (fun s ↦ ((U s)†) (F s)) I) :
    ‖∫ s in I, ((U s)†) (F s)‖ₑ ≤ C * eLpNorm (I.indicator fun s ↦ eLpNorm (F s) a μ) p := by
  have hind : (fun s ↦ ((U s)†) (I.indicator F s)) = I.indicator fun s ↦ ((U s)†) (F s) := by
    funext s
    by_cases hs : s ∈ I <;> simp [hs]
  have hnorm : (fun s ↦ eLpNorm (⇑(I.indicator F s)) a μ) =
      I.indicator fun s ↦ eLpNorm (F s) a μ := by
    funext s
    by_cases hs : s ∈ I
    · simp [hs]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs,
        eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
  rw [← integral_indicator hI, ← hnorm, ← hind]
  exact hC _ ((aestronglyMeasurable_indicator_iff hI).2 hF)
    (by rw [hind]; exact (integrable_indicator_iff hI).2 hUF)

/-- **Reversing time in a dual estimate.** If the operators `U(t) : H → L²(X, μ)` satisfy the dual
estimate `‖∫ U(s)* F(s) ds‖ ≤ C ‖F‖_{L^p_t L^a_x}` for every almost everywhere strongly measurable
`F : ℝ → L²(X, μ)` with `s ↦ U(s)* F(s)` integrable, then so do the time-reversed operators
`U(-t)`: `‖∫ U(-s)* F(s) ds‖ ≤ C ‖F‖_{L^p_t L^a_x}` whenever `s ↦ U(-s)* F(s)` is integrable. The
substitution `s ↦ -s` preserves the integral and the mixed norm. -/
theorem enorm_integral_adjoint_neg_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {a p C : ℝ≥0∞}
    (hC : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ C * eLpNorm (fun s ↦ eLpNorm (F s) a μ) p)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F)
    (hUF : Integrable (fun s ↦ ((U (-s))†) (F s))) :
    ‖∫ s, ((U (-s))†) (F s)‖ₑ ≤ C * eLpNorm (fun s ↦ eLpNorm (F s) a μ) p := by
  have hneg := Measure.measurePreserving_neg (volume : Measure ℝ)
  have h := hC (fun s ↦ F (-s)) (hF.comp_measurePreserving hneg)
    (by simpa only [neg_neg] using hUF.comp_neg)
  have hint := integral_neg_eq_self (fun s ↦ ((U (-s))†) (F s)) volume
  simp only [neg_neg] at hint
  rwa [hF.eLpNorm_eLpNorm_comp_neg, hint] at h

/-- **The retarded estimate from two dual estimates.** Let `U(t) : H → L²(X, μ)` be bounded
operators satisfying the dual estimates

`‖∫ U(s)* F(s) ds‖ ≤ C₁ ‖F‖_{L^{p₁}_t L^{a₁}_x}` and `‖∫ U(s)* F(s) ds‖ ≤ C ‖F‖_{L^p_t L^a_x}`

for every almost everywhere strongly measurable `F : ℝ → L²(X, μ)` with `s ↦ U(s)* F(s)`
integrable, and let `1 ≤ p` and `1 / p₁ + 1 / p > 1`. Then for all such `F` and `G`,

`|∫ ∫_{s < t} ⟪U(s)* F(s), U(t)* G(t)⟫ ds dt|
  ≤ (1 - 2^{-δ})⁻¹ C₁ C ‖F‖_{L^{p₁} L^{a₁}} ‖G‖_{L^p L^a}`,

where `δ = 1 / p₁ + 1 / p - 1 > 0`. When `U(t)` is a unitary group, the pairing is the Duhamel
pairing `⟪U(t - s) F(s), G(t)⟫`, and this is the inhomogeneous Strichartz estimate
`‖∫_{s < t} U(t - s) F(s) ds‖_{L^{p'}_t L^{a'}_x} ≤ C' ‖F‖_{L^{p₁}_t L^{a₁}_x}` tested against
`G`. -/
theorem enorm_integral_setIntegral_Iio_inner_adjoint_le {p₁ p a₁ a : ℝ≥0∞} (hp : 1 ≤ p)
    (hpp : 1 < p₁⁻¹ + p⁻¹) {U : ℝ → H →L[𝕜] Lp E 2 μ} {C₁ C : ℝ≥0∞}
    (hC₁ : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ C₁ * eLpNorm (fun s ↦ eLpNorm (F s) a₁ μ) p₁)
    (hC : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ C * eLpNorm (fun s ↦ eLpNorm (F s) a μ) p)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G)
    (hUF : Integrable (fun s ↦ ((U s)†) (F s))) (hUG : Integrable (fun t ↦ ((U t)†) (G t))) :
    ‖∫ t, ∫ s in Set.Iio t, ⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
      (1 - 2 ^ (-(p₁⁻¹ + p⁻¹ - 1).toReal))⁻¹ * C₁ * C *
        eLpNorm (fun s ↦ eLpNorm (F s) a₁ μ) p₁ * eLpNorm (fun t ↦ eLpNorm (G t) a μ) p := by
  set u := fun s ↦ ((U s)†) (F s)
  set w := fun t ↦ ((U t)†) (G t)
  -- The pairing is integrable on the plane, so the integral over `s < t` is the integral over
  -- the region `{(s, t) | s < t}`.
  have hβ : Integrable (fun z : ℝ × ℝ ↦ ⟪u z.1, w z.2⟫_𝕜) (volume.prod volume) :=
    hUF.inner_fst_snd hUG
  rw [integral_setIntegral_Iio_eq_setIntegral hβ.integrableOn, ← Measure.volume_eq_prod]
  -- On every rectangle of times the pairing factors as `⟪∫_I u, ∫_J w⟫`, and the dual estimates
  -- bound the two factors; the Christ–Kiselev lemma passes the bound to `s < t`.
  refine (eNorm_setIntegral_fst_lt_snd_le hp hpp
    (by rw [Measure.volume_eq_prod]; exact hβ.integrableOn) _ _ (A := C₁ * C)
    fun I J hI hJ _ ↦ ?_).trans_eq (by ring)
  have hfac : ∫ z in I ×ˢ J, ⟪u z.1, w z.2⟫_𝕜 = ⟪∫ s in I, u s, ∫ t in J, w t⟫_𝕜 := by
    rw [inner_integral_integral_eq_integral_prod hUF.integrableOn hUG.integrableOn,
      Measure.prod_restrict, Measure.volume_eq_prod]
  rw [hfac]
  calc _ ≤ ‖∫ s in I, u s‖ₑ * ‖∫ t in J, w t‖ₑ := eNorm_inner_le_eNorm _ _
    _ ≤ C₁ * eLpNorm (I.indicator fun s ↦ eLpNorm (F s) a₁ μ) p₁ *
          (C * eLpNorm (J.indicator fun t ↦ eLpNorm (G t) a μ) p) := by
        gcongr
        exacts [enorm_setIntegral_adjoint_le hC₁ hI.measurableSet hF.restrict hUF.integrableOn,
          enorm_setIntegral_adjoint_le hC hJ.measurableSet hG.restrict hUG.integrableOn]
    _ = _ := by ring

/-- **The retarded estimate for time exponents above `2`.** Let `U(t) : H → L²(X, μ)` satisfy the
dual estimates of `TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le` with time exponents
`p₁ = q₁'` and `p = q'`, the Hölder conjugates of `2 ≤ q₁ ≤ ∞` and `2 < q ≤ ∞`. Then the
Christ–Kiselev condition holds (`TauCeti.one_lt_inv_add_inv_of_holderConjugate`), the constant
`K = (1 - 2^{-δ})⁻¹`, `δ = 1 / p₁ + 1 / p - 1`, is finite, and

`|∫ ∫_{s < t} ⟪U(s)* F(s), U(t)* G(t)⟫ ds dt| ≤ K C₁ C ‖F‖_{L^{p₁} L^{a₁}} ‖G‖_{L^p L^a}`. -/
theorem enorm_integral_setIntegral_Iio_inner_adjoint_le_of_holderConjugate
    {p q p₁ q₁ a₁ a : ℝ≥0∞} [p.HolderConjugate q] [p₁.HolderConjugate q₁] (hq : 2 < q)
    (hq₁ : 2 ≤ q₁) {U : ℝ → H →L[𝕜] Lp E 2 μ} {C₁ C : ℝ≥0∞}
    (hC₁ : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ C₁ * eLpNorm (fun s ↦ eLpNorm (F s) a₁ μ) p₁)
    (hC : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ C * eLpNorm (fun s ↦ eLpNorm (F s) a μ) p)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G)
    (hUF : Integrable (fun s ↦ ((U s)†) (F s))) (hUG : Integrable (fun t ↦ ((U t)†) (G t))) :
    ‖∫ t, ∫ s in Set.Iio t, ⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
      ((1 - (2 : ℝ≥0∞) ^ (-(p₁⁻¹ + p⁻¹ - 1).toReal))⁻¹).toNNReal * C₁ * C *
        eLpNorm (fun s ↦ eLpNorm (F s) a₁ μ) p₁ * eLpNorm (fun t ↦ eLpNorm (G t) a μ) p := by
  have hp : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  have hpp := one_lt_inv_add_inv_of_holderConjugate (p := p) (p₁ := p₁) hq hq₁
  rw [ENNReal.coe_toNNReal
    (inv_one_sub_two_rpow_neg_ne_top (ENNReal.HolderConjugate.ne_zero p₁ q₁) hp hpp)]
  exact enorm_integral_setIntegral_Iio_inner_adjoint_le hp hpp hC₁ hC hF hG hUF hUG

end TauCeti
