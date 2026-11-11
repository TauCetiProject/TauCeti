/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Membership and non-membership examples for local Sobolev classes

This file tests `TauCeti.MemWkpLoc` against explicit planar functions.

* The identity of `ℂ` is in every local Sobolev class, although it is not globally `Lᵖ` for
  `0 < p`.
* The map `z ↦ ‖z‖` is in every local `W^{1,p}` class, as a Lipschitz map
  (`LipschitzWith.memWkpLoc_one`).
* The map `z ↦ ‖z‖` is not in the local class `W^{2,p}` near the origin for `p ≥ 2`: away from
  the origin its second derivative has norm at least `‖z‖⁻¹`, and `‖z‖ ^ (-2)` is not integrable
  near the origin of the plane.
* The indicator of the half-plane `{z | 0 < z.re}` has no weak derivative on any open set
  meeting the imaginary axis, so it is in every local `Lᵖ` class but in no local `W^{k,p}` class
  of positive order there.
* On the closed upper half-disc `D⁺ = ball 0 1 ∩ {z | 0 ≤ z.im}`, the map `z ↦ √z.im` is in the
  local class `W^{1,p}` exactly when `p < 2`, because the `Lᵖ` bounds reach the real axis. On the
  open half-disc it is in that class for every `p`, although it is continuous up to the axis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Topology Distributions

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set ℂ}

/-! ### The identity and the norm -/

/-- The identity of `ℂ` is in every local Sobolev class on every set, although for `0 < p` it is
not in `Lᵖ` of the whole plane: the local class imposes no bound at infinity. -/
theorem memWkpLoc_id (p : ENNReal) (U : Set ℂ) (k : ℕ) : MemWkpLoc p U k (fun z : ℂ => z) :=
  (contDiff_id.contDiffOn : ContDiffOn ℝ k id ((⊤ : Opens ℂ) : Set ℂ)).memWkpLoc (subset_univ U)

/-- The norm `z ↦ ‖z‖` is in the local class `W^{1,p}` on every set, for every exponent: its
weak gradient `z / ‖z‖` is bounded. -/
theorem memWkpLoc_one_norm : MemWkpLoc p U 1 (fun z : ℂ => ‖z‖) :=
  lipschitzWith_one_norm.memWkpLoc_one

/-! ### The norm is not in `W^{2,p}` for `p ≥ 2` -/

/-- The norm `z ↦ ‖z‖` is not in the local class `W^{2,p}` on any set whose interior contains the
origin, for `p ≥ 2`. Its second weak derivative has size `‖z‖⁻¹`, and `‖z‖ ^ (-2)` is not
integrable near the origin of the plane. A definition omitting the `Lᵖ` bound on the top
derivative would accept it. -/
theorem not_memWkpLoc_two_norm (hp : 2 ≤ p) (h0 : (0 : ℂ) ∈ interior U) :
    ¬ MemWkpLoc p U 2 (fun z : ℂ => ‖z‖) := by
  intro h
  obtain ⟨-, D₁, hD₁, h₁⟩ := memWkpLoc_succ_iff.1 h
  obtain ⟨-, D₂, hD₂, h₂⟩ := memWkpLoc_succ_iff.1 h₁
  have hL := memWkpLoc_zero_iff.1 h₂
  set Ω : Opens ℂ := Opens.interior U
  set N : ℂ → ℂ →L[ℝ] ℝ := fderiv ℝ fun y : ℂ => ‖y‖
  -- The first weak derivative is the classical derivative of the norm.
  have hN : HasWeakFDerivOn volume Ω (fun y : ℂ => ‖y‖) N :=
    lipschitzWith_one_norm.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv
  have hD₂N : HasWeakFDerivOn volume Ω N D₂ := hD₂.congr_ae (hD₁.ae_eq hN)
  -- Away from the origin, `N` is smooth.
  set Ω' : Opens ℂ := Ω ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hNsmooth : ContDiffOn ℝ 1 N (Ω' : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := hz.2
    exact ((contDiffAt_norm ℝ hz0 : ContDiffAt ℝ 2 (fun y : ℂ => ‖y‖) z).fderiv_right
      (by norm_num)).contDiffWithinAt
  have hNw : HasWeakFDerivOn volume Ω' N (fderiv ℝ N) := by
    apply hasWeakFDerivOn_of_differentiableOn
    · exact (hNsmooth.continuousOn_fderiv_of_isOpen Ω'.isOpen le_rfl).locallyIntegrableOn
        Ω'.isOpen.measurableSet
    · exact fun z hz => (hNsmooth.differentiableOn one_ne_zero).differentiableAt
        (Ω'.isOpen.mem_nhds hz)
  have hae : D₂ =ᵐ[volume.restrict Ω'] fderiv ℝ N := (hD₂N.mono inf_le_left).ae_eq hNw
  -- Integrate on a small ball around the origin.
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hK : closedBall (0 : ℂ) (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans (hrU.trans interior_subset)
  have hfin : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) (r / 2))) :=
    ⟨by simpa using (isCompact_closedBall (0 : ℂ) (r / 2)).measure_lt_top⟩
  have hD₂2 := ((memLpLoc_iff.1 hL _ hK (isCompact_closedBall 0 _)).mono_exponent hp).mono_measure
    (Measure.restrict_mono ball_subset_closedBall le_rfl :
      volume.restrict (ball (0 : ℂ) (r / 2)) ≤ volume.restrict (closedBall (0 : ℂ) (r / 2)))
  have hball : ball (0 : ℂ) (r / 2) ⊆ Ω ∪ {0} := fun z hz =>
    Or.inl (interior_mono subset_rfl (hrU (ball_subset_ball (by linarith) hz)))
  have hnull : ∀ᵐ z ∂volume, z ≠ (0 : ℂ) := by
    simp [ae_iff, measure_singleton]
  have hae' : D₂ =ᵐ[volume.restrict (ball (0 : ℂ) (r / 2))] fderiv ℝ N := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    have h1 := (ae_restrict_iff' Ω'.isOpen.measurableSet).1 hae
    filter_upwards [h1, hnull] with z hz hz0 hzb
    rcases hball hzb with hzΩ | hz
    · exact hz ⟨hzΩ, hz0⟩
    · exact absurd hz hz0
  have hG := hD₂2.ae_eq hae'
  have hint := (integrable_norm_rpow_iff hG.norm.aestronglyMeasurable two_ne_zero
    ENNReal.ofNat_ne_top).2 hG.norm
  have hsing : IntegrableOn (fun z : ℂ => ‖z‖ ^ (-2 : ℝ)) (ball (0 : ℂ) (r / 2)) := by
    refine hint.mono' (by fun_prop : Measurable fun z : ℂ => ‖z‖ ^ (-2 : ℝ)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_ball).2 ?_)
    filter_upwards [hnull] with z hz0 _
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), Real.rpow_neg (norm_nonneg z),
      ← Real.inv_rpow (norm_nonneg z)]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    rw [norm_norm]
    -- The tangential direction `I * z` is orthogonal to `z`.
    refine inv_norm_le_norm_fderiv_fderiv_norm hz0 (mul_ne_zero Complex.I_ne_zero hz0) ?_
    simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have := (integrableOn_norm_rpow_ball_iff (E := ℂ) (mu := volume) (s := -2)
    (half_pos hr)).1 hsing
  simp [Complex.finrank_real_complex] at this

/-! ### A jump across a line -/

/-- The indicator of the right half-plane is locally `Lᵖ` on every set, for every exponent. -/
theorem memLpLoc_indicator_re_pos :
    MemLpLoc p U ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) := by
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_indicator_const p
    (measurableSet_lt measurable_const Complex.measurable_re).nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

/-- The indicator of the right half-plane has no weak derivative on any open set meeting the
imaginary axis: its distributional derivative is a measure carried by the axis. -/
theorem not_hasWeakFDerivOn_indicator_re_pos {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hre : z₀.re = 0) (D : ℂ → ℂ →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  set u : ℂ → ℝ := {z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ) with hu
  -- On each open half of `Ω` the indicator is constant, so `D` vanishes almost everywhere.
  set Ωp : Opens ℂ := Ω ⊓ ⟨{z | 0 < z.re}, isOpen_lt continuous_const Complex.continuous_re⟩
  set Ωn : Opens ℂ := Ω ⊓ ⟨{z | z.re < 0}, isOpen_lt Complex.continuous_re continuous_const⟩
  have hconst : HasWeakFDerivOn volume Ωp (fun _ => (1 : ℝ)) 0 := hasWeakFDerivOn_iff.2 fun v => by
    simpa using (hasWeakLineDerivOn_const (1 : ℝ) :
      HasWeakLineDerivOn volume Ωp (fun _ => (1 : ℝ)) (fun _ => 0) v)
  have hp : HasWeakFDerivOn volume Ωp u 0 := hconst.congr_ae <|
    (ae_restrict_iff' Ωp.isOpen.measurableSet).2 <| Eventually.of_forall fun z hz => by
      simp [hu, Set.indicator_of_mem (show z ∈ {z : ℂ | 0 < z.re} from hz.2)]
  have hn : HasWeakFDerivOn volume Ωn u 0 := (hasWeakFDerivOn_zero (μ := volume)).congr_ae <|
    (ae_restrict_iff' Ωn.isOpen.measurableSet).2 <| Eventually.of_forall fun z hz => by
      have hz' : ¬ 0 < z.re := not_lt.2 (le_of_lt hz.2)
      simp [hu, hz']
  have hDp := (ae_restrict_iff' Ωp.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hp)
  have hDn := (ae_restrict_iff' Ωn.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hn)
  have hD0 : D =ᵐ[volume.restrict Ω] 0 := by
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
    filter_upwards [hDp, hDn, measure_eq_zero_iff_ae_notMem.1 (Complex.volume_setOf_re_eq 0)]
      with z hzp hzn hz0 hzΩ
    rcases lt_or_gt_of_ne hz0 with h | h
    · exact hzn ⟨hzΩ, h⟩
    · exact hzp ⟨hzΩ, h⟩
  have hline := (hD.congr_ae_deriv hD0).hasWeakLineDerivOn 1
  -- Test against a product of bump functions centred at `z₀`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  let a : ContDiffBump (0 : ℝ) := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  let b : ContDiffBump z₀.im := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  let f : ℂ → ℝ := ((a : ℝ → ℝ) ∘ Complex.re) * ((b : ℝ → ℝ) ∘ Complex.im)
  have hfs : tsupport f ⊆ closedBall z₀ (2 * ε / 3) := by
    intro z hz
    have hzr : z ∈ Complex.re ⁻¹' tsupport a :=
      tsupport_comp_subset_preimage (a : ℝ → ℝ) Complex.continuous_re (tsupport_mul_subset_left hz)
    have hzi : z ∈ Complex.im ⁻¹' tsupport b :=
      tsupport_comp_subset_preimage (b : ℝ → ℝ) Complex.continuous_im (tsupport_mul_subset_right hz)
    rw [mem_preimage, a.tsupport_eq, mem_closedBall, Real.dist_eq, sub_zero] at hzr
    rw [mem_preimage, b.tsupport_eq, mem_closedBall, Real.dist_eq] at hzi
    rw [mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, hre, sub_zero]
    simp only [a, b] at hzr hzi
    linarith
  have hfΩ : tsupport f ⊆ Ω := fun z hz =>
    hball (closedBall_subset_ball (by linarith) (hfs hz))
  let φ : 𝓓(Ω, ℝ) := ⟨f, (a.contDiff.comp Complex.reCLM.contDiff).mul
      (b.contDiff.comp Complex.imCLM.contDiff),
    (isCompact_closedBall z₀ _).of_isClosed_subset (isClosed_tsupport f) hfs, hfΩ⟩
  have hφ : (φ : ℂ → ℝ) = f := TestFunction.coe_mk
  have hkey := hline.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [Pi.zero_apply, zero_apply, smul_zero, integral_zero, neg_zero] at hkey
  -- Compute the pairing by Fubini.
  have hda : ∀ x, HasDerivAt a (deriv a x) x := fun x =>
    ((a.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have hldf : ∀ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 = deriv a z.re * b z.im := by
    intro z
    refine HasLineDerivAt.lineDeriv
      (?_ : HasDerivAt (fun t : ℝ => (φ : ℂ → ℝ) (z + t • (1 : ℂ))) _ 0)
    have h := ((hda (z.re + 0)).comp_const_add z.re 0).mul_const (b z.im)
    simp only [add_zero] at h
    convert h using 1
    funext t
    simp [hφ, f]
  have hint : ∫ z : ℂ, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z =
      ∫ q : ℝ × ℝ, (deriv a q.1 * (Ioi (0 : ℝ)).indicator 1 q.1) * b q.2 := by
    rw [← Complex.volume_preserving_equiv_real_prod.integral_comp
      Complex.measurableEquivRealProd.measurableEmbedding]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hldf, smul_eq_mul, hu, Complex.measurableEquivRealProd]
    by_cases hz : 0 < z.re <;> simp [Set.indicator, hz]
  have hprod := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x => deriv a x * (Ioi (0 : ℝ)).indicator 1 x) (fun y => b y)
  rw [hint, Measure.volume_eq_prod, hprod] at hkey
  have hIoi : ∫ x : ℝ, deriv a x * (Ioi (0 : ℝ)).indicator 1 x = -1 := by
    have hfun : (fun x : ℝ => deriv a x * (Ioi (0 : ℝ)).indicator 1 x) =
        (Ioi (0 : ℝ)).indicator (deriv a) := by
      funext x
      by_cases hx : 0 < x <;> simp [Set.indicator, hx]
    rw [hfun, integral_indicator measurableSet_Ioi]
    have hdc : Continuous (deriv a) := (a.contDiff (n := 1)).continuous_deriv le_rfl
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (m := 0) a.continuous.continuousWithinAt
      (fun x _ => hda x)
      (hdc.integrable_of_hasCompactSupport a.hasCompactSupport.deriv).integrableOn ?_,
      a.one_of_mem_closedBall (mem_closedBall_self (by simp only [a]; positivity))]
    · simp
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (ε / 3)] with x hx
      refine (a.zero_of_le_dist ?_).symm
      simp only [a, Real.dist_eq, sub_zero]
      exact hx.trans (le_abs_self x)
  rw [hIoi] at hkey
  have hb := b.integral_pos (μ := volume)
  linarith

/-- The indicator of the right half-plane is in no local Sobolev class of positive order on a
set whose interior meets the imaginary axis, although it is locally `Lᵖ` there. -/
theorem not_memWkpLoc_indicator_re_pos {k : ℕ} {z₀ : ℂ} (hz₀ : z₀ ∈ interior U)
    (hre : z₀.re = 0) :
    ¬ MemWkpLoc p U (k + 1) ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) := fun h => by
  obtain ⟨-, D, hD, -⟩ := memWkpLoc_succ_iff.1 h
  exact not_hasWeakFDerivOn_indicator_re_pos (Ω := Opens.interior U) hz₀ hre D hD

/-! ### A square-root profile on the half-disc -/

/-- The open upper half-plane. -/
private def openUpperHalfPlane : Opens ℂ := ⟨{z | 0 < z.im}, isOpen_lt continuous_const
  Complex.continuous_im⟩

private theorem hasWeakFDerivOn_sqrt_im :
    HasWeakFDerivOn volume openUpperHalfPlane (fun z : ℂ => √z.im)
      (fun z => (1 / (2 * √z.im)) • Complex.imCLM) := by
  have hD : ContinuousOn (fun z : ℂ => (1 / (2 * √z.im)) • Complex.imCLM) {z | 0 < z.im} := by
    fun_prop (disch := exact fun z hz => mul_ne_zero two_ne_zero (Real.sqrt_pos.2 hz).ne')
  exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
    (by fun_prop : Continuous fun z : ℂ => √z.im).continuousOn
    (hD.locallyIntegrableOn openUpperHalfPlane.isOpen.measurableSet)
    fun z hz => Complex.imCLM.hasFDerivAt.sqrt hz.1.ne'

/-- On the closed upper half-disc `ball 0 1 ∩ {z | 0 ≤ z.im}`, the map `z ↦ √z.im` is in the
local class `W^{1,p}` exactly when `p < 2`. The `Lᵖ` bounds are imposed on compact sets reaching
the real axis, where the derivative `(2 √(Im z))⁻¹` is not square integrable. A definition that
only tested compact subsets of the open half-disc would accept it for every `p`. -/
theorem memWkpLoc_sqrt_im_iff :
    MemWkpLoc p (ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}) 1 (fun z : ℂ => √z.im) ↔ p < 2 := by
  set U : Set ℂ := ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}
  set D : ℂ → ℂ →L[ℝ] ℝ := fun z => (1 / (2 * √z.im)) • Complex.imCLM
  have hint : interior U = ball (0 : ℂ) 1 ∩ {z | 0 < z.im} := by
    rw [interior_inter, isOpen_ball.interior_eq, Complex.interior_setOfPred_le_im]
  have hDU : HasWeakFDerivOn volume (Opens.interior U) (fun z : ℂ => √z.im) D :=
    hasWeakFDerivOn_sqrt_im.mono fun z hz => by
      rw [Opens.mem_interior, hint] at hz
      exact hz.2
  constructor
  · intro h
    by_contra hp
    have hp : 2 ≤ p := not_lt.1 hp
    obtain ⟨-, D', hD', h₀⟩ := memWkpLoc_succ_iff.1 h
    have hL := memWkpLoc_zero_iff.1 h₀
    have hae := (ae_restrict_iff' (Opens.interior U).isOpen.measurableSet).1 (hD'.ae_eq hDU)
    set K : Set ℂ := Icc (-1 / 2) (1 / 2) ×ℂ Icc 0 (1 / 4)
    have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
    have hKU : K ⊆ U := fun z hz => by
      obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hz
      have h1 : |z.re| ≤ 1 / 2 := abs_le.2 ⟨by linarith, hr2⟩
      have h2 : |z.im| ≤ 1 / 4 := abs_le.2 ⟨by linarith, hi2⟩
      exact ⟨mem_ball_zero_iff.2 ((Complex.norm_le_abs_re_add_abs_im z).trans_lt
        (by linarith)), hi1⟩
    have hfinK : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hKc.measure_lt_top⟩
    have hD'2 := (memLpLoc_iff.1 hL K hKU hKc).mono_exponent hp
    have haeK : D' =ᵐ[volume.restrict K] D := by
      rw [EventuallyEq, ae_restrict_iff' hKc.isClosed.measurableSet]
      filter_upwards [hae, measure_eq_zero_iff_ae_notMem.1 (Complex.volume_setOf_im_eq 0)]
        with z hz hz0 hzK
      refine hz ?_
      rw [Opens.coe_interior, hint]
      exact ⟨(hKU hzK).1, lt_of_le_of_ne (hKU hzK).2 (Ne.symm hz0)⟩
    have hgK : MemLp (fun z : ℂ => 1 / (2 * √z.im)) 2 (volume.restrict K) :=
      (hD'2.ae_eq haeK).congr_norm
        (by fun_prop : Measurable fun z : ℂ => 1 / (2 * √z.im)).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [norm_smul, Complex.imCLM_norm, mul_one])
    have hiK := (integrable_norm_rpow_iff hgK.aestronglyMeasurable two_ne_zero
      ENNReal.ofNat_ne_top).2 hgK
    have hg : IntegrableOn (fun t : ℝ => ‖1 / (2 * √t)‖ ^ (2 : ENNReal).toReal)
        (Icc 0 (1 / 4)) :=
      Complex.integrableOn_of_integrableOn_comp_im_reProdIm measurableSet_Icc measurableSet_Icc
        (by simp [Real.volume_Icc]; norm_num) hiK
    have hinv : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 (1 / 4)) := by
      refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioo).1
        ((hg.mono_set Ioo_subset_Icc_self).const_mul 4)
      have ht0 : 0 < t := ht.1
      rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_of_nonneg (by positivity), div_pow,
        mul_pow, Real.sq_sqrt ht0.le, Real.rpow_neg_one]
      field_simp
      norm_num
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1 / 4)).1 hinv
    linarith
  · intro hp
    refine memWkpLoc_succ_iff.2
      ⟨(by fun_prop : Continuous fun z : ℂ => √z.im).continuousOn.memLpLoc, D, hDU,
        memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKU hK => ?_)⟩
    have hKR : K ⊆ Icc (-1) 1 ×ℂ Icc 0 1 := fun z hz => by
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (hKU hz).1
      have hre := (Complex.abs_re_le_norm z).trans hz1.le
      have him := (Complex.abs_im_le_norm z).trans hz1.le
      exact ⟨abs_le.1 hre, (hKU hz).2, (abs_le.1 him).2⟩
    have : IsFiniteMeasure (volume.restrict (Icc (-1 : ℝ) 1)) := ⟨by simp⟩
    have hp' : p ≠ ⊤ := ne_top_of_lt hp
    have hp2 : p.toReal < 2 := by
      simpa using (ENNReal.toReal_lt_toReal hp' (by simp)).2 hp
    -- The derivative profile `t ↦ (2 √t)⁻¹` is in `Lᵖ(0, 1)` for `p < 2`.
    have hsq : MemLp (fun t : ℝ => 1 / (2 * √t)) p (volume.restrict (Icc 0 1)) := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
      refine ((memLp_rpow_neg_restrict_Ioo one_pos hp' (by linarith : 1 / 2 * p.toReal < 1))
        |>.const_mul (1 / 2)).ae_eq
        ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_))
      dsimp only
      rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.1.le]
      field_simp
    have hR : MemLp (fun z : ℂ => 1 / (2 * √z.im)) p
        (volume.restrict (Icc (-1) 1 ×ℂ Icc 0 1)) :=
      (hsq.comp_snd (volume.restrict (Icc (-1 : ℝ) 1)))
        |>.comp_measurePreserving
          (Complex.measurePreserving_measurableEquivRealProd_reProdIm measurableSet_Icc
            measurableSet_Icc)
    refine (hR.congr_norm ?_ (Eventually.of_forall fun z => by
      rw [norm_smul, Complex.imCLM_norm, mul_one]))
      |>.mono_measure (Measure.restrict_mono hKR le_rfl)
    exact ((by fun_prop : Measurable fun z : ℂ => 1 / (2 * √z.im)).smul_const
      Complex.imCLM).aestronglyMeasurable

/-- On the open upper half-disc, the map `z ↦ √z.im` is in the local class `W^{1,p}` for every
exponent, although it extends continuously to the real axis. Together with
`TauCeti.memWkpLoc_sqrt_im_iff`, a map can be continuous on the closed half-disc and locally
`W^{1,p}` on the open half-disc, with `p > 2`, without being locally `W^{1,p}` on the closed one. -/
theorem memWkpLoc_sqrt_im_ball_inter_im_pos :
    MemWkpLoc p (ball (0 : ℂ) 1 ∩ {z | 0 < z.im}) 1 (fun z : ℂ => √z.im) := by
  set V : Set ℂ := ball (0 : ℂ) 1 ∩ {z | 0 < z.im}
  refine memWkpLoc_succ_iff.2
    ⟨(by fun_prop : Continuous fun z : ℂ => √z.im).continuousOn.memLpLoc, _,
      hasWeakFDerivOn_sqrt_im.mono fun z hz => (interior_subset (s := V) hz).2,
      memWkpLoc_zero_iff.2 (ContinuousOn.memLpLoc ?_)⟩
  fun_prop (disch := exact fun z hz => mul_ne_zero two_ne_zero (Real.sqrt_pos.2 hz.2).ne')

end TauCeti
