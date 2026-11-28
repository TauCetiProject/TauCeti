/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Sobolev.W1p.Interval.Basic
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary
import TauCeti.Analysis.Sobolev.Wkp.Nonseparable
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Higher-order Sobolev functions on a bounded interval

On an interval `(a, b)`, consider `u ∈ W^{2,p}(a, b)` whose first-order part lies in
`W^{1,p}_0(a, b)`. Its weak derivative `u'` is a constant plus the primitive of the weak second
derivative `u''`, and has integral zero, so `|u'| ≤ 2 ‖u''‖_{L¹}`; since `u` is the primitive of
`u'` from `a`, also `|u| ≤ 2 (b - a) ‖u''‖_{L¹}`. Hölder's inequality
`‖u''‖_{L¹} ≤ (b - a)^{1 - 1/p} ‖u''‖_{Lᵖ}` turns these into the Poincaré-type bound

`‖u‖_{W^{1,p}(a, b)} ≤ (2 (b - a) + 2 (b - a)²) ‖u''‖_{Lᵖ(a, b)}`.

Conversely, for `p < ∞` every `g ∈ Lᵖ(a, b)` is `u''` for such a `u`: integrate twice, adjusting
the first primitive by a constant so that the second vanishes at both endpoints.

Every `u ∈ W^{2,p}(a, b)`, with no boundary condition, is `C¹` on the open interval: its precise
representative `ū` is continuously differentiable on `(a, b)`, `ū'` agrees almost everywhere with
the weak derivative `u'`, and `ū'(y) - ū'(x) = ∫_x^y u''`. This is the one-dimensional Sobolev
embedding `W^{2,1} ⊆ C¹`, used to turn bounds on `u''` into bounds on the classical derivative.

For all `a, b : ℝ`, every `1 ≤ p ≤ ∞`, and every order `k`, integrating from `a` (or using that
`W^{k,p}(∅)` is zero when `b ≤ a`) shows that weak differentiation
`lineDerivL 1 k : W^{k+1,p}(a, b) →L[ℝ] W^{k,p}(a, b)` is surjective. At `p = ∞`, smooth
representatives fail to be dense in `W^{k,∞}(a, b)` at every order `k` whenever `a < b`, as a
special case of the failure on every nonempty open set
(`TauCeti.Wkp.not_dense_contDiffOn_representatives_top`).

## Main declarations

* `TauCeti.Wkp.ae_norm_gradient_lowerOrder_le_of_mem_w1p0Submodule`: the pointwise bound
  `|u'| ≤ 2 ‖u''‖_{L¹}`.
* `TauCeti.Wkp.norm_lowerOrder_le_of_mem_w1p0Submodule`: the weak second derivative controls
  the first-order part in `W^{1,p}(a, b)`.
* `TauCeti.Wkp.exists_firstOrder_mem_w1p0Submodule_and_iteratedGradient_ae_eq`: every
  `g ∈ Lᵖ(a, b)`, `p < ∞`, is the weak second derivative of such a `u`.
* `TauCeti.Wkp.contDiffOn_preciseRepresentative_Ioo`,
  `TauCeti.Wkp.deriv_preciseRepresentative_ae_eq_gradient_lowerOrder`,
  `TauCeti.Wkp.deriv_preciseRepresentative_sub_deriv_eq_integral`: the precise
  representative of `u ∈ W^{2,p}(a, b)` is `C¹` on `(a, b)`, its derivative is the weak
  derivative, and the increments of the derivative are the integrals of `u''`; in particular
  the derivative is affine where `u''` is constant
  (`TauCeti.Wkp.deriv_preciseRepresentative_eq_add_mul_of_iteratedGradient_eq`).
* `TauCeti.Wkp.lineDerivL_one_surjective_Ioo`: weak differentiation
  `W^{k+1,p}(a, b) → W^{k,p}(a, b)` is surjective for `1 ≤ p ≤ ∞`.
* `TauCeti.Wkp.not_dense_contDiff_representatives_Ioo_top`,
  `TauCeti.Wkp.dense_contDiff_representatives_Ioo_top_iff`: smooth representatives are dense in
  `W^{k,∞}(a, b)` if and only if `b ≤ a`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Section 8.4.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3.16.
-/

public section

open MeasureTheory Set Filter TopologicalSpace intervalIntegral TauCeti.MeasureTheory
open scoped ContDiff

namespace TauCeti

namespace Wkp

variable {a b : ℝ} {p : ENNReal} [Fact (1 ≤ p)]

/-- The weak second derivative `u''` of `u ∈ W^{2,p}(a, b)` is integrable on `(a, b)`. -/
theorem integrableOn_iteratedGradient_one_Ioo (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2) :
    IntegrableOn (fun t => iteratedGradient 1 u t 1) (Ioo a b) := by
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo a b
  exact ((Lp.memLp (iteratedGradient 1 u)).integrable Fact.out).apply_continuousLinearMap 1

/-- The weak derivative of `u ∈ W^{2,p}(a, b)` with first-order part in `W^{1,p}_0(a, b)` is
bounded almost everywhere by twice the `L¹` norm of the weak Hessian: it is a constant plus the
primitive of `u''`, and its integral vanishes. -/
theorem ae_norm_gradient_lowerOrder_le_of_mem_w1p0Submodule (hab : a < b)
    (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2)
    (hu0 : lowerOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ‖W1p.gradient (lowerOrder 1 u) t‖ ≤
      2 * ∫ x in a..b, ‖iteratedGradient 1 u x‖ := by
  set D := iteratedGradient 1 u
  set N := ∫ x in a..b, ‖D x‖
  have hL : 0 < b - a := sub_pos.2 hab
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo a b
  -- `u'` is a constant `k` plus the primitive of `u''`, and that primitive is bounded by `N`.
  have hDint : IntegrableOn (fun x => D x 1) (Ioo a b) := integrableOn_iteratedGradient_one_Ioo u
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
    TauCeti.intervalIntegral.integrableOn_primitive_of_integrableOn_Ioo hDint
      (left_mem_Icc.2 hab.le)
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
theorem norm_lowerOrder_le_of_mem_w1p0Submodule (hab : a < b)
    (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2)
    (hu0 : lowerOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ‖lowerOrder 1 u‖ ≤ (2 * (b - a) + 2 * (b - a) ^ 2) * ‖iteratedGradient 1 u‖ := by
  set w := lowerOrder 1 u
  set D := iteratedGradient 1 u
  set N := ∫ x in a..b, ‖D x‖
  have hL : 0 < b - a := sub_pos.2 hab
  have hN0 : 0 ≤ N := integral_nonneg hab.le fun _ _ => norm_nonneg _
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo a b
  have hmeas : (measureUnivNNReal
      (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) : ℝ) = b - a := by
    rw [measureUnivNNReal, ENNReal.coe_toNNReal_eq_toReal, Measure.restrict_apply_univ,
      Opens.coe_mk, Real.volume_Ioo, ENNReal.toReal_ofReal hL.le]
  -- Pointwise, `|u'| ≤ 2 N` and, since `u` is the primitive of `u'` from `a`, `|u| ≤ 2 N (b - a)`.
  have hw' := ae_norm_gradient_lowerOrder_le_of_mem_w1p0Submodule hab u hu0
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
  have hN : N ≤ (b - a) ^ (1 - p.toReal⁻¹) * ‖D‖ := by
    have h := Lp.integral_norm_le_mul_norm D
    simp only [Measure.restrict_apply_univ, Opens.coe_mk] at h
    rwa [Real.volume_Ioo, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hL.le, one_div, ← integral_Ioc_eq_integral_Ioo,
      ← integral_of_le hab.le] at h
  have hHolder : (b - a) ^ p.toReal⁻¹ * N ≤ (b - a) * ‖D‖ := by
    calc (b - a) ^ p.toReal⁻¹ * N
        ≤ (b - a) ^ p.toReal⁻¹ * ((b - a) ^ (1 - p.toReal⁻¹) * ‖D‖) :=
          mul_le_mul_of_nonneg_left hN (by positivity)
      _ = (b - a) * ‖D‖ := by
          rw [← mul_assoc, ← Real.rpow_add hL, add_sub_cancel, Real.rpow_one]
  have hgw : ‖W1p.gradient w‖ ≤ 2 * (b - a) * ‖D‖ := by
    refine (Lp.norm_le_of_ae_bound (by positivity) hw').trans ?_
    rw [hmeas]
    linarith
  have hvw : ‖W1p.value w‖ ≤ 2 * (b - a) ^ 2 * ‖D‖ := by
    refine (Lp.norm_le_of_ae_bound (by positivity) hv).trans ?_
    rw [hmeas]
    nlinarith
  have hlow : ‖w‖ ≤ ‖W1p.value w‖ + ‖W1p.gradient w‖ :=
    W1p.norm_le_norm_value_add_norm_gradient w
  linarith

/-- Uniqueness of weak derivatives: if `u ∈ W^{2,p}(a, b)` has value `v`, where
`v' = w` and `w' = g` weakly, then the weak Hessian of `u` equals `g` almost everywhere. -/
private theorem iteratedGradient_one_ae_eq_of_value_firstOrder
    {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2} {v w g : ℝ → ℝ}
    (hu : Wkp.value 2 u =ᵐ[volume.restrict (Ioo a b)] v)
    (hdv : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ v w 1)
    (hdw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ w g 1) :
    (fun x => iteratedGradient 1 u x 1) =ᵐ[volume.restrict (Ioo a b)] g := by
  have hlow : W1p.value (lowerOrder 1 u) =ᵐ[volume.restrict (Ioo a b)] v := by
    rw [← value_one, ← value_succ]
    exact hu
  have hval : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (W1p.value (lowerOrder 1 u)) (W1p.gradient (lowerOrder 1 u)) 1 := by
    simpa using (W1p.hasWeakFDerivOn (lowerOrder 1 u)).hasWeakLineDerivOn (1 : ℝ)
  exact ((hasWeakLineDerivOn_gradient_lowerOrder u).congr_ae
    ((hval.congr_ae hlow).ae_eq hdv)).ae_eq hdw

/-- Every `g ∈ Lᵖ(a, b)`, `p < ∞`, is the second weak derivative of some `u ∈ W^{2,p}(a, b)` with
first-order part in `W^{1,p}_0(a, b)`: integrate twice, adjusting the first primitive by a
constant so that the second vanishes at both endpoints. -/
theorem exists_firstOrder_mem_w1p0Submodule_and_iteratedGradient_ae_eq
    (hp : p ≠ ⊤) (hab : a < b) {g : ℝ → ℝ} (hgm : MemLp g p (volume.restrict (Ioo a b))) :
    ∃ u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2,
      firstOrder 1 u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p ∧
        (fun x => iteratedGradient 1 u x 1) =ᵐ[volume.restrict (Ioo a b)] g := by
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
  obtain ⟨d, hd⟩ := exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn (mu := volume)
    (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
    (hwc.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self p)
    (fun c x => c * g x) (fun c => hgm.const_mul c) fun c => by
      have h := hdw.smul_direction c
      rw [smul_eq_mul, mul_one] at h
      exact h
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_forall_hasWeakLineDerivOn (mu := volume)
    (Omega := ⟨Ioo a b, isOpen_Ioo⟩) 1
    (TauCeti.intervalIntegral.memLp_primitive hwi (left_mem_Icc.2 hab.le))
    (fun c => c • d) fun c => by
      rw [value_smul]
      simpa using ((hdv.congr_ae_deriv hd.symm).smul_direction c).congr_ae_deriv
        (Lp.coeFn_smul c (value 1 d)).symm
  refine ⟨u, ?_, ?_⟩
  · -- The first-order part of `u` vanishes continuously on the boundary.
    refine W1p.mem_w1p0Submodule_of_continuousOn_closure hp
      (by simpa using Metric.isBounded_Ioo a b) (g := v) (by simpa [closure_Ioo hab.ne] using hvc)
      (fun t ht => ?_) (by rw [value_firstOrder]; exact hu)
    simp only [Opens.coe_mk, frontier_Ioo hab, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact integral_same
    · exact hw0
  · exact iteratedGradient_one_ae_eq_of_value_firstOrder hu hdv hdw

/-! ### `W^{2,p}` functions are `C¹` on an open interval -/

/-- The derivative of the precise representative of `u ∈ W^{2,p}(a, b)`: it is
`t ↦ k + ∫_a^t u''` for a constant `k`, which is continuous on `[a, b]` and agrees almost
everywhere with the weak derivative `u'`. -/
private theorem exists_hasDerivAt_preciseRepresentative_Ioo (hab : a < b)
    (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2) :
    ∃ k : ℝ, ContinuousOn (fun t => k + ∫ s in a..t, iteratedGradient 1 u s 1) (Icc a b) ∧
      (W1p.gradient (lowerOrder 1 u) =ᵐ[volume.restrict (Ioo a b)]
        fun t => k + ∫ s in a..t, iteratedGradient 1 u s 1) ∧
      ∀ x ∈ Ioo a b, HasDerivAt (preciseRepresentative volume (value 2 u))
        (k + ∫ s in a..x, iteratedGradient 1 u s 1) x := by
  have hDint := integrableOn_iteratedGradient_one_Ioo u
  -- The weak derivative `u'` is a constant `k` plus the primitive `G` of `u''`.
  obtain ⟨k, hk⟩ :=
    (hasWeakLineDerivOn_gradient_lowerOrder u).exists_ae_eq_add_intervalIntegral_left hDint
  set G : ℝ → ℝ := fun t => k + ∫ s in a..t, iteratedGradient 1 u s 1
  have hGc : ContinuousOn G (Icc a b) := continuousOn_const.add
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hDint
      (left_mem_Icc.2 hab.le))
  have hGi : IntegrableOn G (Ioo a b) := hGc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- So `u` has weak derivative `G`, and is a constant `c` plus the primitive `U` of `G`.
  have hv : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (value 2 u) G 1 := by
    have h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (W1p.value (lowerOrder 1 u))
        (W1p.gradient (lowerOrder 1 u)) 1 := by
      simpa using (W1p.hasWeakFDerivOn (lowerOrder 1 u)).hasWeakLineDerivOn (1 : ℝ)
    rw [value_lowerOrder_one] at h
    exact h.congr_ae_deriv hk
  obtain ⟨c, hc⟩ := hv.exists_ae_eq_add_intervalIntegral_left hGi
  have hU (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt (fun t => c + ∫ s in a..t, G s) (G x) x :=
    (hGc.integral_hasDerivAt_of_mem_Ioo hx).const_add c
  -- The precise representative agrees with the continuous function `U` on `(a, b)`.
  have heq : EqOn (preciseRepresentative volume (value 2 u)) (fun t => c + ∫ s in a..t, G s)
      (Ioo a b) :=
    eqOn_preciseRepresentative_of_continuousOn isOpen_Ioo
      (by simpa using Lp.locallyIntegrableOn (value 2 u) Fact.out) hc
      fun x hx => (hU x hx).continuousAt.continuousWithinAt
  exact ⟨k, hGc, hk, fun x hx =>
    (hU x hx).congr_of_eventuallyEq (eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx) heq)⟩

/-- **`W^{2,p}` functions are differentiable on an open interval.** The precise representative of
`u ∈ W^{2,p}(a, b)` is differentiable at every point of `(a, b)`. -/
theorem differentiableOn_preciseRepresentative_Ioo (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2) :
    DifferentiableOn ℝ (preciseRepresentative volume (value 2 u)) (Ioo a b) := by
  rcases le_or_gt b a with hba | hab
  · exact fun x hx => absurd (hx.1.trans hx.2) (not_lt.2 hba)
  obtain ⟨k, -, -, h⟩ := exists_hasDerivAt_preciseRepresentative_Ioo hab u
  exact fun x hx => (h x hx).differentiableAt.differentiableWithinAt

/-- The classical derivative of the precise representative of `u ∈ W^{2,p}(a, b)` agrees almost
everywhere on `(a, b)` with the weak derivative `u'`. -/
theorem deriv_preciseRepresentative_ae_eq_gradient_lowerOrder
    (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2) :
    deriv (preciseRepresentative volume (value 2 u)) =ᵐ[volume.restrict (Ioo a b)]
      W1p.gradient (lowerOrder 1 u) := by
  rcases le_or_gt b a with hba | hab
  · simp [EventuallyEq, Ioo_eq_empty_of_le hba]
  obtain ⟨k, -, hk, h⟩ := exists_hasDerivAt_preciseRepresentative_Ioo hab u
  filter_upwards [hk, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [(h t htI).deriv, ht]

/-- **The fundamental theorem of calculus for the derivative of a `W^{2,p}` function.** For
`u ∈ W^{2,p}(a, b)` and `x, y ∈ (a, b)`, the derivative of the precise representative `ū` of `u`
satisfies `ū'(y) - ū'(x) = ∫_x^y u''`, where `u''` is the weak second derivative. -/
theorem deriv_preciseRepresentative_sub_deriv_eq_integral
    (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2) {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    deriv (preciseRepresentative volume (value 2 u)) y -
        deriv (preciseRepresentative volume (value 2 u)) x =
      ∫ t in x..y, iteratedGradient 1 u t 1 := by
  have hab : a < b := hx.1.trans hx.2
  have hD (z : ℝ) (hz : z ∈ Ioo a b) :
      IntervalIntegrable (fun t => iteratedGradient 1 u t 1) volume a z :=
    (integrableOn_iteratedGradient_one_Ioo u).intervalIntegrable_of_mem_Icc
      (left_mem_Icc.2 hab.le) (Ioo_subset_Icc_self hz)
  obtain ⟨k, -, -, h⟩ := exists_hasDerivAt_preciseRepresentative_Ioo hab u
  rw [(h y hy).deriv, (h x hx).deriv, add_sub_add_left_eq_sub,
    integral_interval_sub_left (hD y hy) (hD x hx)]

/-- If the weak second derivative of `u ∈ W^{2,p}(a, b)` equals a constant `c` almost everywhere
between two points `x, y ∈ (a, b)`, then the derivative of the precise representative `ū` of `u`
is affine there: `ū'(y) = ū'(x) + c (y - x)`. -/
theorem deriv_preciseRepresentative_eq_add_mul_of_iteratedGradient_eq
    (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2) {x y c : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (h : ∀ᵐ t, t ∈ uIoc x y → iteratedGradient 1 u t 1 = c) :
    deriv (preciseRepresentative volume (value 2 u)) y =
      deriv (preciseRepresentative volume (value 2 u)) x + c * (y - x) := by
  have hFTC := deriv_preciseRepresentative_sub_deriv_eq_integral u hx hy
  rw [integral_congr_ae (g := fun _ => c) h, intervalIntegral.integral_const, smul_eq_mul,
    mul_comm] at hFTC
  linarith

/-- **`W^{2,p}` functions are `C¹` on an open interval.** The precise representative of
`u ∈ W^{2,p}(a, b)` is continuously differentiable on `(a, b)`. -/
theorem contDiffOn_preciseRepresentative_Ioo (u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ p 2) :
    ContDiffOn ℝ 1 (preciseRepresentative volume (value 2 u)) (Ioo a b) := by
  rcases le_or_gt b a with hba | hab
  · exact fun x hx => absurd (hx.1.trans hx.2) (not_lt.2 hba)
  obtain ⟨k, hGc, -, h⟩ := exists_hasDerivAt_preciseRepresentative_Ioo hab u
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioo).2
    ⟨differentiableOn_preciseRepresentative_Ioo u, by simp, ?_⟩
  exact contDiffOn_zero.2 ((hGc.mono Ioo_subset_Icc_self).congr fun x hx => (h x hx).deriv)

/-- On any bounded open interval `(a, b)`, weak differentiation
`lineDerivL 1 k : W^{k+1,p}(a, b) →L[ℝ] W^{k,p}(a, b)` is surjective for every `1 ≤ p ≤ ∞` and
every natural order `k`. -/
theorem lineDerivL_one_surjective_Ioo (k : ℕ) :
    Function.Surjective
      (lineDerivL (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩) (p := p) (1 : ℝ) k) := by
  intro d
  rcases lt_or_ge a b with hab | hba
  · have : IsFiniteMeasure (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
      Real.isFiniteMeasure_restrict_Ioo a b
    have hgi : IntegrableOn (value k d : ℝ → ℝ) (Ioo a b) :=
      (Lp.memLp (value k d)).integrable Fact.out
    set v : ℝ → ℝ := fun t => ∫ s in a..t, value k d s
    have hvm : MemLp v p (volume.restrict (Ioo a b)) :=
      TauCeti.intervalIntegral.memLp_primitive hgi (left_mem_Icc.2 hab.le)
    have hdv : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ v (value k d) 1 :=
      hasWeakLineDerivOn_intervalIntegral_left hgi
    cases k with
    | zero =>
      obtain ⟨u, hu⟩ := exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn (mu := volume)
        (Omega := ⟨Ioo a b, isOpen_Ioo⟩) hvm (fun c => c • (value 0 d : ℝ → ℝ))
        (fun c => (Lp.memLp (value 0 d)).const_smul c) fun c => by
          have h := hdv.smul_direction c
          rwa [smul_eq_mul, mul_one] at h
      exact ⟨u, lineDerivL_eq_of_hasWeakLineDerivOn (hdv.congr_ae hu.symm)⟩
    | succ k =>
      obtain ⟨u, hu⟩ := exists_value_ae_eq_of_forall_hasWeakLineDerivOn (mu := volume)
        (Omega := ⟨Ioo a b, isOpen_Ioo⟩) (k + 1) hvm (fun c => c • d) fun c => by
          rw [value_smul]
          have h := hdv.smul_direction c
          rw [smul_eq_mul, mul_one] at h
          exact h.congr_ae_deriv (Lp.coeFn_smul c (value (k + 1) d)).symm
      exact ⟨u, lineDerivL_eq_of_hasWeakLineDerivOn (hdv.congr_ae hu.symm)⟩
  · refine ⟨0, ?_⟩
    rw [map_zero]
    exact (ext k (Lp.ext (by simp [EventuallyEq, Ioo_eq_empty_of_le hba]))).symm

/-- Smooth representatives fail to be dense in `W^{k,∞}(a, b)` for every natural order `k`
whenever `a < b`: a special case of `TauCeti.Wkp.not_dense_contDiffOn_representatives_top`. -/
theorem not_dense_contDiff_representatives_Ioo_top (hab : a < b) :
    ∀ k : ℕ, ¬ Dense {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤ k |
      ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (value k u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] f} :=
  fun k hd => not_dense_contDiffOn_representatives_top (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
    (nonempty_Ioo.2 hab) k
    (hd.mono fun _ hu => by
      obtain ⟨f, hf, huf⟩ := hu
      exact ⟨f, (hf.of_le (mod_cast le_top)).contDiffOn, huf⟩)

/-- Smooth representatives are dense in `W^{k,∞}(a, b)` if and only if `b ≤ a`. -/
theorem dense_contDiff_representatives_Ioo_top_iff (k : ℕ) :
    Dense {u : Wkp volume ⟨Ioo a b, isOpen_Ioo⟩ ⊤ k |
      ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (value k u : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)] f} ↔
        b ≤ a := by
  refine ⟨fun hd => le_of_not_gt fun hab =>
    not_dense_contDiff_representatives_Ioo_top hab k hd, fun hba u => ?_⟩
  have hu0 : u = 0 := ext k (Lp.ext (by simp [EventuallyEq, Ioo_eq_empty_of_le hba]))
  rw [hu0]
  exact subset_closure ⟨0, contDiff_const, by simp [EventuallyEq, Ioo_eq_empty_of_le hba]⟩

end Wkp

end TauCeti
