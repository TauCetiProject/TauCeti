/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow

/-!
# Poincaré estimates with transverse linear boundary conditions

A path whose endpoints lie in two disjoint finite-dimensional linear subspaces has its
squared norm controlled by the integral of its squared speed. Applying this estimate on
vertical slices gives a Poincaré estimate on the infinite strip. Unlike a zero-boundary
estimate, this allows both endpoint values to be nonzero.

The analytic step is the usual fundamental-theorem-of-calculus proof of the Poincaré
inequality (see L. C. Evans, *Partial Differential Equations*, Chapter 5), followed by
Cauchy–Schwarz. It uses Mathlib's
`enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc` and
`TauCeti.rpow_lintegral_le_measure_univ_rpow_mul`. The additional endpoint estimate comes from
the bounded-below property of the injective subtraction map on the product of the subspaces.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On the unit interval, the squared displacement of a continuously differentiable path is
bounded by its squared-speed integral. -/
theorem norm_sub_sq_le_integral_norm_deriv_sq {v : ℝ → V} (hv : ContDiff ℝ 1 v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖v t - v 0‖ ^ 2 ≤ ∫ r in Icc (0 : ℝ) 1, ‖deriv v r‖ ^ 2 := by
  have hd : Continuous (deriv v) := hv.continuous_deriv (by norm_num)
  have hFTC : ‖v t - v 0‖ₑ ≤ ∫⁻ r in Icc (0 : ℝ) 1, ‖deriv v r‖ₑ :=
    (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hv.contDiffOn ht.1).trans
      (lintegral_mono_set (Icc_subset_Icc_right ht.2))
  have hHolder : (∫⁻ r in Icc (0 : ℝ) 1, ‖deriv v r‖ₑ) ^ 2 ≤
      ∫⁻ r in Icc (0 : ℝ) 1, ‖deriv v r‖ₑ ^ 2 := by
    simpa using rpow_lintegral_le_measure_univ_rpow_mul
      (μ := volume.restrict (Icc (0 : ℝ) 1)) hd.enorm.measurable.aemeasurable
      (r := 2) (by norm_num)
  have hi : IntegrableOn (fun r ↦ ‖deriv v r‖ ^ 2) (Icc (0 : ℝ) 1) :=
    (hd.norm.pow 2).continuousOn.integrableOn_Icc
  have hbound := (pow_le_pow_left' hFTC 2).trans hHolder
  have hconv : (∫⁻ r in Icc (0 : ℝ) 1, ‖deriv v r‖ₑ ^ 2) =
      ENNReal.ofReal (∫ r in Icc (0 : ℝ) 1, ‖deriv v r‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun r ↦ sq_nonneg _)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hconv, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun r ↦ sq_nonneg _)).mp hbound

end TauCeti

namespace Submodule

open MeasureTheory Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Disjoint linear endpoint conditions control a path's squared norm uniformly throughout
the unit interval. The constant depends only on the two subspaces. -/
theorem exists_norm_sq_le_mul_integral_norm_deriv_sq_of_disjoint
    (L₀ L₁ : Submodule ℝ V) [FiniteDimensional ℝ L₀] [FiniteDimensional ℝ L₁]
    (hL : Disjoint L₀ L₁) :
    ∃ C > 0, ∀ (v : ℝ → V), ContDiff ℝ 1 v → v 0 ∈ L₀ → v 1 ∈ L₁ →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖v t‖ ^ 2 ≤ C * ∫ r in Icc (0 : ℝ) 1, ‖deriv v r‖ ^ 2 := by
  let f : L₀ × L₁ →ₗ[ℝ] V :=
    L₁.subtype.comp (LinearMap.snd ℝ L₀ L₁) -
      L₀.subtype.comp (LinearMap.fst ℝ L₀ L₁)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have heq : (x.2 : V) = x.1 := sub_eq_zero.mp hx
    have hx₀ : (x.1 : V) = 0 :=
      Submodule.disjoint_def.mp hL _ x.1.property (heq ▸ x.2.property)
    apply Prod.ext <;> apply Subtype.ext
    · exact hx₀
    · exact heq.trans hx₀
  obtain ⟨K, hK, hbound⟩ := f.injective_iff_antilipschitz.mp hf
  refine ⟨((K : ℝ) + 1) ^ 2, by positivity, ?_⟩
  intro v hv hv₀ hv₁ t ht
  let E := ∫ r in Icc (0 : ℝ) 1, ‖deriv v r‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg fun r ↦ sq_nonneg _
  have ht' : ‖v t - v 0‖ ≤ Real.sqrt E :=
    (Real.le_sqrt (norm_nonneg _) hE).mpr (TauCeti.norm_sub_sq_le_integral_norm_deriv_sq hv ht)
  have h1 : ‖v 1 - v 0‖ ≤ Real.sqrt E :=
    (Real.le_sqrt (norm_nonneg _) hE).mpr
      (TauCeti.norm_sub_sq_le_integral_norm_deriv_sq hv ⟨by norm_num, le_rfl⟩)
  have h0 : ‖v 0‖ ≤ (K : ℝ) * ‖v 1 - v 0‖ := by
    let x : L₀ × L₁ := (⟨v 0, hv₀⟩, ⟨v 1, hv₁⟩)
    exact (norm_fst_le x).trans (ZeroHomClass.bound_of_antilipschitz f hbound x)
  have hvbound : ‖v t‖ ≤ ((K : ℝ) + 1) * Real.sqrt E := by
    calc ‖v t‖ ≤ ‖v t - v 0‖ + ‖v 0‖ := by
          simpa only [sub_add_cancel] using norm_add_le (v t - v 0) (v 0)
      _ ≤ Real.sqrt E + (K : ℝ) * Real.sqrt E :=
        add_le_add ht' (h0.trans (mul_le_mul_of_nonneg_left h1 K.coe_nonneg))
      _ = ((K : ℝ) + 1) * Real.sqrt E := by ring
  calc ‖v t‖ ^ 2 ≤ (((K : ℝ) + 1) * Real.sqrt E) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hvbound 2
    _ = ((K : ℝ) + 1) ^ 2 * E := by rw [mul_pow, Real.sq_sqrt hE]

/-- The Poincaré inequality on the infinite unit strip for compactly supported continuously
differentiable maps with disjoint linear boundary conditions. Its constant is uniform in the
map and only the derivative in the bounded direction is needed. -/
theorem exists_integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_disjoint
    (L₀ L₁ : Submodule ℝ V) [FiniteDimensional ℝ L₀] [FiniteDimensional ℝ L₁]
    (hL : Disjoint L₀ L₁) :
    ∃ C > 0, ∀ (u : ℝ × ℝ → V), ContDiff ℝ 1 u → HasCompactSupport u →
      (∀ s, u (s, 0) ∈ L₀) → (∀ s, u (s, 1) ∈ L₁) →
      (∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖u z‖ ^ 2) ≤
        C * ∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ u z (0, 1)‖ ^ 2 := by
  obtain ⟨C, hC, hpath⟩ := L₀.exists_norm_sq_le_mul_integral_norm_deriv_sq_of_disjoint L₁ hL
  refine ⟨C, hC, fun u hu hc hbottom htop ↦ ?_⟩
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hi : Integrable (fun z ↦ ‖u z‖ ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp))
  have hdi : Integrable (fun z ↦ ‖fderiv ℝ u z (0, 1)‖ ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      ((hc.fderiv_apply (𝕜 := ℝ) (0, 1)).comp_left
        (g := fun v ↦ ‖v‖ ^ 2) (by simp))
  have hline (s : ℝ) : (∫ t in Icc (0 : ℝ) 1, ‖u (s, t)‖ ^ 2) ≤
      C * ∫ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (s, t) (0, 1)‖ ^ 2 := by
    have hv : ContDiff ℝ 1 (fun t ↦ u (s, t)) :=
      hu.comp (contDiff_const.prodMk contDiff_id)
    have hd (t : ℝ) : deriv (fun r ↦ u (s, r)) t = fderiv ℝ u (s, t) (0, 1) := by
      have hp : HasDerivAt (fun r : ℝ ↦ ((s, r) : ℝ × ℝ)) (0, 1) t :=
        (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
      exact ((hu.differentiable one_ne_zero (s, t)).hasFDerivAt.comp_hasDerivAt t hp).deriv
    have htbound := hpath (fun t ↦ u (s, t)) hv (hbottom s) (htop s)
    simp_rw [hd] at htbound
    calc (∫ t in Icc (0 : ℝ) 1, ‖u (s, t)‖ ^ 2) ≤
        ∫ _t in Icc (0 : ℝ) 1,
          C * ∫ r in Icc (0 : ℝ) 1, ‖fderiv ℝ u (s, r) (0, 1)‖ ^ 2 := by
            apply setIntegral_mono_on (hv.continuous.norm.pow 2).integrableOn_Icc
              (integrableOn_const (by simp)) measurableSet_Icc
            exact htbound
      _ = C * ∫ r in Icc (0 : ℝ) 1, ‖fderiv ℝ u (s, r) (0, 1)‖ ^ 2 := by simp
  have hmeasure : volume.prod (volume.restrict (Icc (0 : ℝ) 1)) =
      (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Icc (0 : ℝ) 1) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hi' : Integrable (fun z ↦ ‖u z‖ ^ 2)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [hmeasure]
    exact hi.integrableOn
  have hdi' : Integrable (fun z ↦ ‖fderiv ℝ u z (0, 1)‖ ^ 2)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [hmeasure]
    exact hdi.integrableOn
  rw [Measure.volume_eq_prod] at hi hdi ⊢
  rw [setIntegral_prod _ hi.integrableOn, setIntegral_prod _ hdi.integrableOn,
    setIntegral_univ, setIntegral_univ, ← integral_const_mul]
  exact integral_mono hi'.integral_prod_left (hdi'.integral_prod_left.const_mul C) hline

end Submodule
