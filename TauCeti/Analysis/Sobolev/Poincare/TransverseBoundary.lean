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
import TauCeti.MeasureTheory.Function.LocallyIntegrable
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

/-- On a closed interval, the squared displacement of a continuously differentiable path is
bounded by the interval length times its squared-speed integral. -/
theorem norm_sub_sq_le_integral_norm_deriv_sq {v : ℝ → V} {a b t : ℝ}
    (hv : ContDiffOn ℝ 1 v (Icc a b)) (hab : a ≤ b) (ht : t ∈ Icc a b) :
    ‖v t - v a‖ ^ 2 ≤ (b - a) * ∫ r in Icc a b, ‖deriv v r‖ ^ 2 := by
  obtain rfl | hab' := hab.eq_or_lt
  · obtain rfl : t = a := le_antisymm ht.2 ht.1
    simp
  have hd := hv.continuousOn_derivWithin (uniqueDiffOn_Icc hab') le_rfl
  have heq : derivWithin v (Icc a b) =ᵐ[volume.restrict (Icc a b)] deriv v := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)
  have hm : AEMeasurable (fun r ↦ ‖deriv v r‖ₑ) (volume.restrict (Icc a b)) :=
    (hd.enorm.aemeasurable measurableSet_Icc).congr (heq.fun_comp enorm)
  have hFTC : ‖v t - v a‖ₑ ≤ ∫⁻ r in Icc a b, ‖deriv v r‖ₑ :=
    (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
      (hv.mono (Icc_subset_Icc_right ht.2)) ht.1).trans
      (lintegral_mono_set (Icc_subset_Icc_right ht.2))
  have hHolder : (∫⁻ r in Icc a b, ‖deriv v r‖ₑ) ^ 2 ≤
      ENNReal.ofReal (b - a) * ∫⁻ r in Icc a b, ‖deriv v r‖ₑ ^ 2 := by
    have h := rpow_lintegral_le_measure_univ_rpow_mul
      (μ := volume.restrict (Icc a b)) hm
      (r := 2) (by norm_num)
    norm_num at h
    exact h
  have hi : IntegrableOn (fun r ↦ ‖deriv v r‖ ^ 2) (Icc a b) :=
    (hd.norm.pow 2).integrableOn_Icc.congr (by
      filter_upwards [heq] with r hr
      change ‖derivWithin v (Icc a b) r‖ ^ 2 = ‖deriv v r‖ ^ 2
      rw [hr])
  have hbound := (pow_le_pow_left' hFTC 2).trans hHolder
  have hconv : (∫⁻ r in Icc a b, ‖deriv v r‖ₑ ^ 2) =
      ENNReal.ofReal (∫ r in Icc a b, ‖deriv v r‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun r ↦ sq_nonneg _)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hconv, ← ENNReal.ofReal_mul (sub_nonneg.mpr hab),
    ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (sub_nonneg.mpr hab) (integral_nonneg fun r ↦ sq_nonneg _))).mp hbound

end TauCeti

namespace Submodule

open MeasureTheory Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Disjoint linear endpoint conditions control a path's squared norm uniformly throughout
the unit interval. The constant depends only on the two subspaces. -/
theorem exists_norm_sq_le_mul_integral_norm_deriv_sq_of_disjoint
    (L₀ L₁ : Submodule ℝ V) [FiniteDimensional ℝ L₀] [FiniteDimensional ℝ L₁]
    (hL : Disjoint L₀ L₁) :
    ∃ C > 0, ∀ (v : ℝ → V), ContDiffOn ℝ 1 v (Icc 0 1) → v 0 ∈ L₀ → v 1 ∈ L₁ →
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
    (Real.le_sqrt (norm_nonneg _) hE).mpr
      (by simpa using TauCeti.norm_sub_sq_le_integral_norm_deriv_sq hv zero_le_one ht)
  have h1 : ‖v 1 - v 0‖ ≤ Real.sqrt E :=
    (Real.le_sqrt (norm_nonneg _) hE).mpr
      (by
        simpa using TauCeti.norm_sub_sq_le_integral_norm_deriv_sq hv
          (a := 0) (b := 1) (t := 1) zero_le_one ⟨zero_le_one, le_rfl⟩)
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
    hu.continuous.integrable_norm_sq_of_hasCompactSupport hc
  have hdi : Integrable (fun z ↦ ‖fderiv ℝ u z (0, 1)‖ ^ 2) :=
    (hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (0, 1))
  have hline (s : ℝ) : (∫ t in Icc (0 : ℝ) 1, ‖u (s, t)‖ ^ 2) ≤
      C * ∫ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (s, t) (0, 1)‖ ^ 2 := by
    have hv : ContDiff ℝ 1 (fun t ↦ u (s, t)) :=
      hu.comp (contDiff_const.prodMk contDiff_id)
    have hd (t : ℝ) : deriv (fun r ↦ u (s, r)) t = fderiv ℝ u (s, t) (0, 1) := by
      have hp : HasDerivAt (fun r : ℝ ↦ ((s, r) : ℝ × ℝ)) (0, 1) t :=
        (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
      exact ((hu.differentiable one_ne_zero (s, t)).hasFDerivAt.comp_hasDerivAt t hp).deriv
    have htbound := hpath (fun t ↦ u (s, t)) hv.contDiffOn (hbottom s) (htop s)
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
