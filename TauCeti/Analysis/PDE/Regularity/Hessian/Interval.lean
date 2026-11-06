/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Analysis.Sobolev.W1p.Interval
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The `W^{2,p}` Dirichlet problem on an interval

Let `a < b`, `1 ≤ p < ∞`, and let `σ` be a measurable coefficient on `(a, b)` with `λ ≤ σ` almost
everywhere for some `λ > 0`. This file proves that for every `f ∈ Lᵖ(a, b)` the Dirichlet problem

`-σ u'' = f` on `(a, b)`, `u ∈ W^{2,p}(a, b) ∩ W^{1,p}_0(a, b)`,

has exactly one strong solution
(`TauCeti.PDE.existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo`),
and that every strong solution satisfies the global estimate

`‖u‖_{W^{2,p}(a, b)} ≤ (1 + 2 (b - a) + 2 (b - a)²) / λ · ‖f‖_{Lᵖ(a, b)}`

(`TauCeti.PDE.norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo`), which holds for `p = ∞` as well.
Here `u''` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` evaluated in the direction `1`.

This is the one-dimensional case of the global `W^{2,p}` theory of non-divergence-form equations
`-aⁱʲ ∂ᵢ∂ⱼ u = f` on bounded domains. In higher dimensions that theory needs a regularity
hypothesis on the coefficients, such as continuity or vanishing mean oscillation, and a
Calderón–Zygmund estimate. On an interval it needs neither: the coefficient need only be bounded
below, not bounded above or continuous, and the constant depends on `σ` only through `λ`. The
reason is that the equation is the ordinary differential equation `u'' = -f / σ`, and
`|f / σ| ≤ |f| / λ`.

## The argument

The solution is written down by integrating twice: with `g = -f / σ ∈ Lᵖ(a, b)`, the function
`w t = ∫ s in a..t, g s - k` has weak derivative `g`, where the constant `k` makes the integral
of `w` over `(a, b)` vanish, and `u t = ∫ s in a..t, w s` then vanishes at both endpoints. So it
lies in `W^{1,p}_0(a, b)` (`TauCeti.W1p.mem_w1p0Submodule_of_continuousOn_closure`), and
uniqueness of weak derivatives identifies `u'' = g`.

For the estimate, a solution `u` has `|u''| ≤ |f| / λ`. Its weak derivative `u'` is a constant
`k` plus the primitive of `u''`, and has integral zero because `u ∈ W^{1,p}_0(a, b)`
(`TauCeti.W1p.intervalIntegral_gradient_eq_zero_of_mem_w1p0Submodule`), which bounds `|k|` and
hence `|u'| ≤ 2 ‖u''‖_{L¹}`. Since `u` is the primitive of `u'` from `a`
(`TauCeti.W1p.value_ae_eq_intervalIntegral_gradient_of_mem_w1p0Submodule`),
`|u| ≤ 2 (b - a) ‖u''‖_{L¹}`. Hölder's inequality `‖u''‖_{L¹} ≤ (b - a)^{1 - 1/p} ‖u''‖_{Lᵖ}`
turns these pointwise bounds into the `Lᵖ` bounds `‖u'‖ ≤ 2 (b - a) ‖u''‖` and
`‖u‖ ≤ 2 (b - a)² ‖u''‖`. Uniqueness follows from the estimate applied to the difference of two
solutions.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 9, for the `W^{2,p}` theory of strong solutions in higher dimensions.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4, for the one-dimensional boundary value problem.
-/

public section

open MeasureTheory Set Filter TopologicalSpace intervalIntegral

namespace TauCeti

namespace PDE

variable {a b : ℝ} {p : ENNReal} [Fact (1 ≤ p)]

/-- The weak gradient of the first-order part of `u ∈ W^{2,p}` of an open subset of the line has
weak derivative the weak Hessian evaluated in the direction `1`. -/
private theorem hasWeakLineDerivOn_gradient_lowerOrder {Omega : Opens ℝ}
    (u : Wkp volume Omega p 2) :
    HasWeakLineDerivOn volume Omega (W1p.gradient (Wkp.lowerOrder 1 u))
      (fun x => Wkp.iteratedGradient 1 u x 1) 1 := by
  rw [← Wkp.iteratedGradient_zero]
  exact (Wkp.hasWeakFDerivOn_iteratedGradient 0 u).hasWeakLineDerivOn 1

/-- **Hölder's inequality on an interval.** The `L¹` norm of `g ∈ Lᵖ(a, b)` is at most
`(b - a)^{1 - 1/p}` times its `Lᵖ` norm. -/
private theorem intervalIntegral_norm_le_rpow_mul_norm {F : Type*} [NormedAddCommGroup F]
    (hab : a ≤ b) (g : Lp F p (volume.restrict (Ioo a b))) :
    ∫ x in a..b, ‖g x‖ ≤ (b - a) ^ (1 - p.toReal⁻¹) * ‖g‖ := by
  have hs : 0 ≤ 1 - p.toReal⁻¹ := by
    rcases eq_or_ne p ⊤ with rfl | hp
    · simp
    · exact sub_nonneg.2 (inv_le_one_of_one_le₀
        (ENNReal.toReal_one ▸ ENNReal.toReal_mono hp Fact.out))
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Ioo a b))
    (p := 1) (q := p) Fact.out (Lp.aestronglyMeasurable g)
  rw [Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.toReal_one, div_one,
    one_div] at h
  rw [integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable g),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable g), Lp.norm_def, mul_comm]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top g)
    (ENNReal.rpow_ne_top_of_nonneg hs ENNReal.ofReal_ne_top)) h).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]

omit [Fact (1 ≤ p)] in
/-- An almost everywhere bound `C` on `h ∈ Lᵖ(a, b)` bounds its `Lᵖ` norm by
`(b - a)^{1/p} C`. -/
private theorem norm_le_rpow_mul_of_ae_norm_le {F : Type*} [NormedAddCommGroup F]
    (hab : a ≤ b) {h : Lp F p (volume.restrict (Ioo a b))} {C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ᵐ x ∂volume.restrict (Ioo a b), ‖h x‖ ≤ C) :
    ‖h‖ ≤ (b - a) ^ p.toReal⁻¹ * C := by
  refine (Lp.norm_le_of_ae_bound hC hh).trans_eq ?_
  rw [measureUnivNNReal, ENNReal.coe_toNNReal_eq_toReal,
    Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]

/-- The weak derivative of `u ∈ W^{2,p}(a, b)` with first-order part in `W^{1,p}_0(a, b)` is
bounded almost everywhere by twice the `L¹` norm of the weak Hessian: it is a constant plus the
primitive of `u''`, and its integral vanishes. -/
private theorem ae_norm_gradient_lowerOrder_le (hab : a < b)
    (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2)
    (hu0 : Wkp.lowerOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ‖W1p.gradient (Wkp.lowerOrder 1 u) t‖ ≤
      2 * ∫ x in a..b, ‖Wkp.iteratedGradient 1 u x‖ := by
  set D := Wkp.iteratedGradient 1 u
  set N := ∫ x in a..b, ‖D x‖
  have hL : 0 < b - a := sub_pos.2 hab
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo a b
  -- `u'` is a constant `k` plus the primitive of `u''`, and that primitive is bounded by `N`.
  have hDint : IntegrableOn (fun x => D x 1) (Ioo a b) :=
    ((Lp.memLp D).integrable Fact.out).apply_continuousLinearMap 1
  obtain ⟨k, hk⟩ :=
    (hasWeakLineDerivOn_gradient_lowerOrder u).exists_ae_eq_add_intervalIntegral_left hDint
  have hDn : IntervalIntegrable (fun x => ‖D x‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2
      ((Lp.memLp D).integrable Fact.out).norm
  have hD1 : IntervalIntegrable (fun x => D x 1) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hDint
  have hprim : ∀ t ∈ Icc a b, ‖∫ s in a..t, D s 1‖ ≤ N := fun t ht => by
    have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc_left (Icc_subset_uIcc ht)
    calc ‖∫ s in a..t, D s 1‖ ≤ ∫ s in a..t, ‖D s 1‖ := norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t, ‖D s‖ := integral_mono_on ht.1 (hD1.mono_set hsub).norm
          (hDn.mono_set hsub) fun s _ => by simpa using (D s).le_opNorm 1
      _ ≤ N := integral_mono_interval le_rfl ht.1 ht.2 (ae_of_all _ fun _ => norm_nonneg _) hDn
  -- `u'` has integral zero, which bounds the constant: `|k| ≤ N`.
  have hGint : IntegrableOn (fun t => ∫ s in a..t, D s 1) (Ioo a b) :=
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hDint
      (left_mem_Icc.2 hab.le)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hk0 : (b - a) * k + ∫ t in Ioo a b, ∫ s in a..t, D s 1 = 0 := by
    rw [← W1p.intervalIntegral_gradient_eq_zero_of_mem_w1p0Submodule hab.le hu0,
      integral_of_le hab.le, integral_Ioc_eq_integral_Ioo, integral_congr_ae hk,
      integral_add (integrable_const k) hGint, setIntegral_const,
      Real.volume_real_Ioo_of_le hab.le, smul_eq_mul]
  have hkN : |k| ≤ N := by
    have h := norm_setIntegral_le_of_norm_le_const
      (measure_Ioo_lt_top (μ := volume) (a := a) (b := b))
      fun t ht => hprim t (Ioo_subset_Icc_self ht)
    rw [eq_neg_of_add_eq_zero_right hk0, norm_neg,
      Real.norm_eq_abs, abs_mul, abs_of_pos hL, Real.volume_real_Ioo_of_le hab.le] at h
    exact le_of_mul_le_mul_left (by linarith) hL
  filter_upwards [hk, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [ht]
  calc ‖k + ∫ s in a..t, D s 1‖ ≤ ‖k‖ + ‖∫ s in a..t, D s 1‖ := norm_add_le _ _
    _ ≤ N + N := add_le_add hkN (hprim t (Ioo_subset_Icc_self htI))
    _ = 2 * N := by ring

/-- On `W^{2,p}(a, b)` with first-order part in `W^{1,p}_0(a, b)`, the weak Hessian controls the
first-order part: `‖u‖_{W^{1,p}} ≤ (2 (b - a) + 2 (b - a)²) ‖u''‖_{Lᵖ}`. -/
private theorem norm_lowerOrder_le_of_mem_w1p0Submodule (hab : a < b)
    (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2)
    (hu0 : Wkp.lowerOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ‖Wkp.lowerOrder 1 u‖ ≤ (2 * (b - a) + 2 * (b - a) ^ 2) * ‖Wkp.iteratedGradient 1 u‖ := by
  set w := Wkp.lowerOrder 1 u
  set D := Wkp.iteratedGradient 1 u
  set N := ∫ x in a..b, ‖D x‖
  have hL : 0 < b - a := sub_pos.2 hab
  have hN0 : 0 ≤ N := integral_nonneg hab.le fun _ _ => norm_nonneg _
  -- Pointwise, `|u'| ≤ 2 N` and, since `u` is the primitive of `u'` from `a`, `|u| ≤ 2 N (b - a)`.
  have hw' := ae_norm_gradient_lowerOrder_le hab u hu0
  have hv : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖W1p.value w t‖ ≤ 2 * N * (b - a) := by
    have hw'' := (ae_restrict_iff' measurableSet_Ioo).1 hw'
    filter_upwards [W1p.value_ae_eq_intervalIntegral_gradient_of_mem_w1p0Submodule hu0,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [ht]
    refine (norm_integral_le_of_norm_le_const_ae (C := 2 * N) ?_).trans ?_
    · filter_upwards [hw''] with s hs hsI
      rw [uIoc_of_le htI.1.le] at hsI
      exact hs ⟨hsI.1, hsI.2.trans_lt htI.2⟩
    · rw [abs_of_nonneg (sub_nonneg.2 htI.1.le)]
      exact mul_le_mul_of_nonneg_left (by linarith [htI.2]) (by positivity)
  -- The `Lᵖ` bounds follow by Hölder's inequality `N ≤ (b - a)^{1 - 1/p} ‖u''‖`.
  have hHolder : (b - a) ^ p.toReal⁻¹ * N ≤ (b - a) * ‖D‖ := by
    calc (b - a) ^ p.toReal⁻¹ * N
        ≤ (b - a) ^ p.toReal⁻¹ * ((b - a) ^ (1 - p.toReal⁻¹) * ‖D‖) :=
          mul_le_mul_of_nonneg_left (intervalIntegral_norm_le_rpow_mul_norm hab.le D)
            (by positivity)
      _ = (b - a) * ‖D‖ := by
          rw [← mul_assoc, ← Real.rpow_add hL, add_sub_cancel, Real.rpow_one]
  have hgw : ‖W1p.gradient w‖ ≤ 2 * (b - a) * ‖D‖ := by
    refine (norm_le_rpow_mul_of_ae_norm_le hab.le (by positivity) hw').trans ?_
    linarith
  have hvw : ‖W1p.value w‖ ≤ 2 * (b - a) ^ 2 * ‖D‖ := by
    refine (norm_le_rpow_mul_of_ae_norm_le hab.le (by positivity) hv).trans ?_
    nlinarith
  have hlow : ‖w‖ ≤ ‖W1p.value w‖ + ‖W1p.gradient w‖ :=
    W1p.norm_le_norm_value_add_norm_gradient w
  linarith

/-- **The global `W^{2,p}` estimate for the Dirichlet problem on an interval.** Let `a < b`,
`1 ≤ p ≤ ∞` and `λ > 0`, and let `σ ≥ λ` almost everywhere on `(a, b)`. If
`u ∈ W^{2,p}(a, b)` has first-order part in `W^{1,p}_0(a, b)` and solves `-σ u'' = f` almost
everywhere, with `f ∈ Lᵖ(a, b)` and `u''` the weak Hessian in the direction `1`, then

`‖u‖_{W^{2,p}(a, b)} ≤ (1 + 2 (b - a) + 2 (b - a)²) / λ · ‖f‖_{Lᵖ(a, b)}`.

No upper bound, continuity or measurability of `σ` is needed. -/
theorem norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo (hab : a < b) {σ : ℝ → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x)
    {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2} {f : Lp ℝ p (volume.restrict (Ioo a b))}
    (hu0 : Wkp.firstOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p)
    (hu : ∀ᵐ x ∂volume.restrict (Ioo a b), -(σ x * Wkp.iteratedGradient 1 u x 1) = f x) :
    ‖u‖ ≤ (1 + 2 * (b - a) + 2 * (b - a) ^ 2) / lam * ‖f‖ := by
  rw [Wkp.firstOrder_succ, Wkp.firstOrder_zero] at hu0
  set D := Wkp.iteratedGradient 1 u
  -- Pointwise `|u''| = |f| / σ ≤ |f| / λ`, hence `‖u''‖ ≤ ‖f‖ / λ` in `Lᵖ`.
  have hD : ‖D‖ ≤ lam⁻¹ * ‖f‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hσ, hu] with x hσx hx
    rw [← (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).symm.norm_map,
      ContinuousLinearMap.toSpanSingletonLIE_symm_apply, ← hx, norm_neg, norm_mul,
      Real.norm_of_nonneg (hlam.trans_le hσx).le, ← mul_assoc]
    exact le_mul_of_one_le_left (norm_nonneg _) ((one_le_inv_mul₀ hlam).2 hσx)
  have hlow := norm_lowerOrder_le_of_mem_w1p0Submodule hab u hu0
  -- `‖u‖² = ‖u‖_{W^{1,p}}² + ‖u''‖²`, so `‖u‖ ≤ ‖u‖_{W^{1,p}} + ‖u''‖`.
  have hu2 := Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ 0 u
  have hu1 : ‖u‖ ≤ ‖Wkp.lowerOrder 1 u‖ + ‖D‖ := by
    nlinarith [norm_nonneg u, norm_nonneg (Wkp.lowerOrder 1 u), norm_nonneg D]
  calc ‖u‖ ≤ (1 + 2 * (b - a) + 2 * (b - a) ^ 2) * ‖D‖ := by linarith
    _ ≤ (1 + 2 * (b - a) + 2 * (b - a) ^ 2) * (lam⁻¹ * ‖f‖) :=
        mul_le_mul_of_nonneg_left hD (by nlinarith)
    _ = (1 + 2 * (b - a) + 2 * (b - a) ^ 2) / lam * ‖f‖ := by ring

/-- Every `g ∈ Lᵖ(a, b)`, `p < ∞`, is the second weak derivative of some `u ∈ W^{2,p}(a, b)` with
first-order part in `W^{1,p}_0(a, b)`: integrate twice, adjusting the first primitive by a
constant so that the second vanishes at both endpoints. -/
private theorem exists_firstOrder_mem_w1p0Submodule_and_iteratedGradient_ae_eq
    (hp : p ≠ ⊤) (hab : a < b) {g : ℝ → ℝ} (hgm : MemLp g p (volume.restrict (Ioo a b))) :
    ∃ u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2,
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p ∧
        (fun x => Wkp.iteratedGradient 1 u x 1) =ᵐ[volume.restrict (Ioo a b)] g := by
  have hL : 0 < b - a := sub_pos.2 hab
  have hgi : IntegrableOn g (Ioo a b) := hgm.integrable Fact.out
  -- `w = G - k` has weak derivative `g` and integral zero, where `G` is the primitive of `g`.
  set G : ℝ → ℝ := fun t => ∫ s in a..t, g s
  have hGc : ContinuousOn G (Icc a b) :=
    TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hgi
      (left_mem_Icc.2 hab.le)
  set w : ℝ → ℝ := fun t => G t - (∫ s in a..b, G s) / (b - a)
  have hwc : ContinuousOn w (Icc a b) := hGc.sub continuousOn_const
  have hwi : IntegrableOn w (Ioo a b) := hwc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hw0 : ∫ t in a..b, w t = 0 := by
    rw [integral_sub (hGc.intervalIntegrable_of_Icc hab.le) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, mul_div_cancel₀ _ hL.ne', sub_self]
  have hdw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ w g 1 :=
    ((hasWeakLineDerivOn_intervalIntegral_left hgi).sub
      (hasWeakLineDerivOn_const _)).congr_ae_deriv (EventuallyEq.of_eq (sub_zero g))
  -- `v`, the primitive of `w`, vanishes at both endpoints.
  set v : ℝ → ℝ := fun t => ∫ s in a..t, w s
  have hvc : ContinuousOn v (Icc a b) :=
    TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hwi
      (left_mem_Icc.2 hab.le)
  have hdv : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ v w 1 :=
    hasWeakLineDerivOn_intervalIntegral_left hwi
  -- Assemble `v` into an element `u` of `W^{2,p}(a, b)`.
  obtain ⟨d, hd⟩ := Wkp.exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn (mu := volume)
    (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
    (hwc.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self p)
    (fun c x => c * g x) (fun c => hgm.const_mul c) fun c => by
      have h := hdw.smul_direction c
      rw [smul_eq_mul, mul_one] at h
      exact h
  obtain ⟨u, hu⟩ := Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn (mu := volume)
    (Omega := ⟨Ioo a b, isOpen_Ioo⟩) 1
    (hvc.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self p)
    (fun c => c • d) fun c => by
      rw [Wkp.value_smul]
      simpa using ((hdv.congr_ae_deriv hd.symm).smul_direction c).congr_ae_deriv
        (Lp.coeFn_smul c (Wkp.value 1 d)).symm
  refine ⟨u, ?_, ?_⟩
  · -- The first-order part of `u` vanishes continuously on the boundary.
    refine W1p.mem_w1p0Submodule_of_continuousOn_closure hp
      (by simpa using Metric.isBounded_Ioo a b) (g := v) (by simpa [closure_Ioo hab.ne] using hvc)
      (fun t ht => ?_) (by rw [Wkp.value_firstOrder]; exact hu)
    simp only [Opens.coe_mk, frontier_Ioo hab, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact integral_same
    · exact hw0
  · -- By uniqueness of weak derivatives, `u' = w` and `u'' = g`.
    have hlow : W1p.value (Wkp.lowerOrder 1 u) =ᵐ[volume.restrict (Ioo a b)] v := by
      rw [← Wkp.value_one, ← Wkp.value_succ]
      exact hu
    have hval : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
        (W1p.value (Wkp.lowerOrder 1 u)) (W1p.gradient (Wkp.lowerOrder 1 u)) 1 := by
      simpa using (W1p.hasWeakFDerivOn (Wkp.lowerOrder 1 u)).hasWeakLineDerivOn (1 : ℝ)
    exact ((hasWeakLineDerivOn_gradient_lowerOrder u).congr_ae
      ((hval.congr_ae hlow).ae_eq hdv)).ae_eq hdw

/-- **The Dirichlet problem on an interval.** Let `a < b`, `1 ≤ p < ∞` and `λ > 0`, and let `σ`
be measurable on `(a, b)` with `σ ≥ λ` almost everywhere. For every `f ∈ Lᵖ(a, b)` there is
exactly one `u ∈ W^{2,p}(a, b)` whose first-order part lies in `W^{1,p}_0(a, b)` and which solves
`-σ u'' = f` almost everywhere on `(a, b)`, where `u''` is the weak Hessian in the direction `1`.
It satisfies the bound of `TauCeti.PDE.norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo`. -/
theorem existsUnique_firstOrder_mem_w1p0Submodule_and_neg_mul_iteratedGradient_eq_of_Ioo
    (hp : p ≠ ⊤) (hab : a < b) {σ : ℝ → ℝ}
    (hσm : AEStronglyMeasurable σ (volume.restrict (Ioo a b))) {lam : ℝ} (hlam : 0 < lam)
    (hσ : ∀ᵐ x ∂volume.restrict (Ioo a b), lam ≤ σ x) (f : Lp ℝ p (volume.restrict (Ioo a b))) :
    ∃! u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2,
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p ∧
        ∀ᵐ x ∂volume.restrict (Ioo a b), -(σ x * Wkp.iteratedGradient 1 u x 1) = f x := by
  -- Existence: `u'' = -f / σ` lies in `Lᵖ(a, b)`, since `|f / σ| ≤ |f| / λ`.
  have hgm : MemLp (fun x => -(f x / σ x)) p (volume.restrict (Ioo a b)) := by
    refine ((Lp.memLp f).const_mul lam⁻¹).of_le ((Lp.aestronglyMeasurable f).div₀ hσm).neg ?_
    filter_upwards [hσ] with x hx
    rw [norm_neg, norm_div, norm_mul, Real.norm_of_nonneg (hlam.trans_le hx).le, norm_inv,
      Real.norm_of_nonneg hlam.le, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hlam hx) (norm_nonneg _)
  obtain ⟨u, hu0, hug⟩ :=
    exists_firstOrder_mem_w1p0Submodule_and_iteratedGradient_ae_eq hp hab hgm
  have hu : ∀ᵐ x ∂volume.restrict (Ioo a b), -(σ x * Wkp.iteratedGradient 1 u x 1) = f x := by
    filter_upwards [hug, hσ] with x hx hσx
    rw [hx]
    field_simp [(hlam.trans_le hσx).ne']
  refine ⟨u, ⟨hu0, hu⟩, fun v ⟨hv0, hv⟩ => ?_⟩
  -- Uniqueness: the difference of two solutions solves the problem with `f = 0`.
  have hd0 : Wkp.firstOrder 1 (v - u) ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p := by
    rw [← Wkp.firstOrderL_apply, map_sub, Wkp.firstOrderL_apply, Wkp.firstOrderL_apply]
    exact (w1p0Submodule _ _ p).toSubmodule.sub_mem hv0 hu0
  have hd : ∀ᵐ x ∂volume.restrict (Ioo a b),
      -(σ x * Wkp.iteratedGradient 1 (v - u) x 1) = (0 : Lp ℝ p (volume.restrict (Ioo a b))) x := by
    rw [← Wkp.iteratedGradientL_apply, map_sub, Wkp.iteratedGradientL_apply,
      Wkp.iteratedGradientL_apply]
    filter_upwards [Lp.coeFn_sub (Wkp.iteratedGradient 1 v) (Wkp.iteratedGradient 1 u),
      Lp.coeFn_zero ℝ p (volume.restrict (Ioo a b)), hv, hu] with x hx hx0 hvx hux
    rw [hx, hx0, Pi.sub_apply, sub_apply, Pi.zero_apply]
    linear_combination hvx - hux
  have h0 := norm_le_of_neg_mul_iteratedGradient_eq_of_Ioo hab hlam hσ hd0 hd
  rw [norm_zero, mul_zero] at h0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end PDE

end TauCeti
