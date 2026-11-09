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
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Membership and non-membership examples for local Sobolev classes

This file tests `TauCeti.MemWkpLoc` against explicit planar functions.

* The identity of `ℂ` is in every local Sobolev class, although it is not globally `Lᵖ`.
* A globally Lipschitz map into a finite-dimensional space is in every local `W^{1,p}` class,
  with its Fréchet derivative as weak derivative. In particular `z ↦ ‖z‖` is.
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

/-! ### The identity and Lipschitz maps -/

/-- The identity of `ℂ` is in every local Sobolev class on every set, although it is not in
`Lᵖ` of the whole plane: the local class imposes no bound at infinity. -/
theorem memWkpLoc_id (p : ENNReal) (U : Set ℂ) (k : ℕ) : MemWkpLoc p U k (fun z : ℂ => z) :=
  (contDiff_id.contDiffOn : ContDiffOn ℝ k id ((⊤ : Opens ℂ) : Set ℂ)).memWkpLoc (subset_univ U)

/-- A globally Lipschitz map from the plane into a finite-dimensional space is in the local
class `W^{1,p}` on every set, for every exponent: its Fréchet derivative is a weak derivative
bounded by the Lipschitz constant. -/
theorem _root_.LipschitzWith.memWkpLoc_one [FiniteDimensional ℝ F] {K : NNReal} {u : ℂ → F}
    (hu : LipschitzWith K u) : MemWkpLoc p U 1 u := by
  refine memWkpLoc_succ_iff.2 ⟨hu.continuous.continuousOn.memLpLoc, fderiv ℝ u, ?_,
    memWkpLoc_zero_iff.2 ?_⟩
  · have hΩ : LocallyLipschitzOn ((⊤ : Opens ℂ) : Set ℂ) u :=
      hu.locallyLipschitz.locallyLipschitzOn
    exact (hΩ.hasWeakFDerivOn_fderiv (μ := volume)).mono le_top
  · refine memLpLoc_iff.2 fun L _ hL => ?_
    have : IsFiniteMeasure (volume.restrict L) := ⟨by simpa using hL.measure_lt_top⟩
    exact MemLp.of_bound (measurable_fderiv ℝ u).aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ hu)

/-- The norm `z ↦ ‖z‖` is in the local class `W^{1,p}` on every set, for every exponent: its
weak gradient `z / ‖z‖` is bounded. -/
theorem memWkpLoc_one_norm : MemWkpLoc p U 1 (fun z : ℂ => ‖z‖) :=
  lipschitzWith_one_norm.memWkpLoc_one

/-! ### The norm is not in `W^{2,p}` for `p ≥ 2` -/

/-- Away from the origin the derivative of the norm is `‖z‖⁻¹ • innerSL ℝ z`. -/
private theorem hasFDerivAt_norm_complex {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun y : ℂ => ‖y‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
  have hsq := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hpos : 0 < ‖z‖ ^ 2 := by positivity
  have h := (Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt z hsq
  have hfun : (fun x => √x) ∘ (fun y : ℂ => ‖y‖ ^ 2) = fun y => ‖y‖ := by
    funext y
    simp [Real.sqrt_sq (norm_nonneg y)]
  rw [hfun] at h
  convert h using 1
  rw [Real.sqrt_sq (norm_nonneg z)]
  ext w
  simp only [smul_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
  field_simp

/-- The derivative of the norm, as a map into `ℂ →L[ℝ] ℝ`, has derivative of norm at least
`‖z‖⁻¹` away from the origin: in the tangential direction `I * z` it is `‖z‖⁻¹ • innerSL ℝ`. -/
private theorem inv_norm_le_norm_fderiv_fderiv_norm {z : ℂ} (hz : z ≠ 0) :
    ‖z‖⁻¹ ≤ ‖fderiv ℝ (fderiv ℝ fun y : ℂ => ‖y‖) z‖ := by
  set N : ℂ → ℂ →L[ℝ] ℝ := fun y => ‖y‖⁻¹ • innerSL ℝ y
  have hN : fderiv ℝ (fun y : ℂ => ‖y‖) =ᶠ[𝓝 z] N := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    exact (hasFDerivAt_norm_complex hy).fderiv
  have hinv : HasFDerivAt (fun y : ℂ => ‖y‖⁻¹)
      ((-(‖z‖ ^ 2)⁻¹) • (‖z‖⁻¹ • innerSL ℝ z)) z :=
    (hasDerivAt_inv (norm_ne_zero_iff.2 hz)).comp_hasFDerivAt z (hasFDerivAt_norm_complex hz)
  have hlin : HasFDerivAt (fun y : ℂ => innerSL ℝ y) (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) z :=
    (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).hasFDerivAt
  have hD := (hinv.smul hlin).congr_of_eventuallyEq hN
  set v : ℂ := Complex.I * z
  have hv : ‖v‖ = ‖z‖ := by simp [v]
  have hzv : inner ℝ z v = 0 := by
    simp only [v, Complex.inner, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    ring
  obtain ⟨L, hDL, hLv⟩ : ∃ L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
      HasFDerivAt (fderiv ℝ fun y : ℂ => ‖y‖) L z ∧ L v = ‖z‖⁻¹ • innerSL ℝ v :=
    ⟨_, hD, by simp [hzv]⟩
  rw [hDL.fderiv]
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  refine le_of_mul_le_mul_right ?_ hz0
  have hle := L.le_opNorm v
  rw [hLv, norm_smul, innerSL_apply_norm, hv, norm_inv, norm_norm] at hle
  exact hle

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
    exact inv_norm_le_norm_fderiv_fderiv_norm hz0
  have := (integrableOn_norm_rpow_ball_iff (E := ℂ) (mu := volume) (s := -2)
    (half_pos hr)).1 hsing
  simp [Complex.finrank_real_complex] at this

/-! ### A jump across a line -/

/-- The imaginary axis is a null set of the plane. -/
private theorem ae_re_ne_zero : ∀ᵐ z : ℂ, z.re ≠ 0 := by
  have hset : {z : ℂ | z.re = 0} = (LinearMap.ker Complex.reLm : Set ℂ) := by
    ext z
    simp
  have hnull : volume {z : ℂ | z.re = 0} = 0 := by
    rw [hset]
    refine Measure.addHaar_submodule _ _ fun h => ?_
    have h1 : (1 : ℂ) ∈ LinearMap.ker Complex.reLm := h ▸ Submodule.mem_top
    simp at h1
  exact measure_eq_zero_iff_ae_notMem.1 hnull

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
    filter_upwards [hDp, hDn, ae_re_ne_zero] with z hzp hzn hz0 hzΩ
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
    change f (z + t • (1 : ℂ)) = _
    simp [f]
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

/-- The real axis is a null set of the plane. -/
private theorem ae_im_ne_zero : ∀ᵐ z : ℂ, z.im ≠ 0 := by
  have hset : {z : ℂ | z.im = 0} = (LinearMap.ker Complex.imLm : Set ℂ) := by
    ext z
    simp
  have hnull : volume {z : ℂ | z.im = 0} = 0 := by
    rw [hset]
    refine Measure.addHaar_submodule _ _ fun h => ?_
    have hI : Complex.I ∈ LinearMap.ker Complex.imLm := h ▸ Submodule.mem_top
    simp at hI
  exact measure_eq_zero_iff_ae_notMem.1 hnull

/-- Restricted to a rectangle, Lebesgue measure on `ℂ` is the product of the restrictions to
its sides. -/
private theorem measurePreserving_reProdIm {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    MeasurePreserving Complex.measurableEquivRealProd (volume.restrict (s ×ℂ t))
      ((volume.restrict s).prod (volume.restrict t)) := by
  have h := Complex.volume_preserving_equiv_real_prod.restrict_preimage (hs.prod ht)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  exact h

/-- A function of `Im z` integrable on a rectangle of positive width is integrable on the
vertical side. -/
private theorem integrable_of_integrable_comp_im {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hs0 : volume s ≠ 0) (hsfin : volume s ≠ ⊤) {g : ℝ → ℝ}
    (h : Integrable (fun z : ℂ => g z.im) (volume.restrict (s ×ℂ t))) :
    Integrable g (volume.restrict t) := by
  have : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hsfin.lt_top⟩
  have h2 := ((measurePreserving_reProdIm hs ht).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (g := fun q : ℝ × ℝ => g q.2)).1
    (by
      convert h using 1
      funext z
      simp [Complex.measurableEquivRealProd])
  exact (Integrable.comp_snd_iff (μ := volume.restrict s) (by simpa using hs0)).1 h2

/-- The derivative of `z ↦ √z.im` in the open upper half-plane. -/
private theorem hasFDerivAt_sqrt_im {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (fun y : ℂ => √y.im) ((1 / (2 * √z.im)) • Complex.imCLM) z := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_sqrt hz.ne').comp_hasFDerivAt z Complex.imCLM.hasFDerivAt

private theorem continuous_sqrt_im : Continuous fun z : ℂ => √z.im := by fun_prop

/-- The open upper half-plane. -/
private def openUpperHalfPlane : Opens ℂ := ⟨{z | 0 < z.im}, isOpen_lt continuous_const
  Complex.continuous_im⟩

private theorem continuousOn_sqrt_im_deriv :
    ContinuousOn (fun z : ℂ => (1 / (2 * √z.im)) • Complex.imCLM) (openUpperHalfPlane : Set ℂ) := by
  refine ContinuousOn.smul (ContinuousOn.div continuousOn_const
    (continuous_const.mul (Real.continuous_sqrt.comp Complex.continuous_im)).continuousOn
    fun z hz => ?_) continuousOn_const
  have hz : 0 < z.im := hz
  exact mul_ne_zero two_ne_zero (Real.sqrt_pos.2 hz).ne'

private theorem hasWeakFDerivOn_sqrt_im :
    HasWeakFDerivOn volume openUpperHalfPlane (fun z : ℂ => √z.im)
      (fun z => (1 / (2 * √z.im)) • Complex.imCLM) :=
  hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty continuous_sqrt_im.continuousOn
    (continuousOn_sqrt_im_deriv.locallyIntegrableOn openUpperHalfPlane.isOpen.measurableSet)
    fun _ hz => hasFDerivAt_sqrt_im hz.1

private theorem norm_sqrt_im_deriv (z : ℂ) :
    ‖(1 / (2 * √z.im)) • Complex.imCLM‖ = ‖1 / (2 * √z.im)‖ := by
  rw [norm_smul, Complex.imCLM_norm, mul_one]

/-- The function `t ↦ (2 √t)⁻¹` is in `Lᵖ(0, c)` for `p < 2`. -/
private theorem memLp_inv_two_sqrt (hp : p < 2) {c : ℝ} (hc : 0 < c) :
    MemLp (fun t : ℝ => 1 / (2 * √t)) p (volume.restrict (Icc 0 c)) := by
  have : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) c)) := ⟨by simp⟩
  set q : ENNReal := max p 1
  have hq1 : 1 ≤ q := le_max_right _ _
  have hq2 : q < 2 := max_lt hp ENNReal.one_lt_two
  have hqtop : q ≠ ⊤ := ne_top_of_lt hq2
  have hr2 : q.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal hqtop (by simp)).2 hq2
  have hr0 : 0 ≤ q.toReal := ENNReal.toReal_nonneg
  refine MemLp.mono_exponent ?_ (le_max_left p 1)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => 1 / (2 * √t)) (volume.restrict (Icc 0 c)) :=
    (by fun_prop : Measurable fun t : ℝ => 1 / (2 * √t)).aestronglyMeasurable
  refine (integrable_norm_rpow_iff hmeas (zero_lt_one.trans_le hq1).ne' hqtop).1 ?_
  rw [← IntegrableOn, integrableOn_Icc_iff_integrableOn_Ioo]
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-(q.toReal / 2))) (Ioo 0 c) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hc).2 (by linarith)
  refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioo).1
    (hpow.const_mul ((1 / 2 : ℝ) ^ q.toReal))
  have ht0 : 0 < t := ht.1
  rw [Real.norm_of_nonneg (by positivity), Real.sqrt_eq_rpow]
  conv_rhs => rw [Real.div_rpow zero_le_one (by positivity), Real.one_rpow,
    Real.mul_rpow zero_le_two (by positivity), ← Real.rpow_mul ht0.le]
  rw [Real.div_rpow zero_le_one zero_le_two, Real.one_rpow, Real.rpow_neg ht0.le,
    show (1 / 2 : ℝ) * q.toReal = q.toReal / 2 by ring]
  field_simp

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
      change z ∈ interior U at hz
      rw [hint] at hz
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
      filter_upwards [hae, ae_im_ne_zero] with z hz hz0 hzK
      refine hz ?_
      change z ∈ interior U
      rw [hint]
      exact ⟨(hKU hzK).1, lt_of_le_of_ne (hKU hzK).2 (Ne.symm hz0)⟩
    have hgK : MemLp (fun z : ℂ => 1 / (2 * √z.im)) 2 (volume.restrict K) :=
      (hD'2.ae_eq haeK).congr_norm
        (by fun_prop : Measurable fun z : ℂ => 1 / (2 * √z.im)).aestronglyMeasurable
        (Eventually.of_forall fun z => norm_sqrt_im_deriv z)
    have hiK := (integrable_norm_rpow_iff hgK.aestronglyMeasurable two_ne_zero
      ENNReal.ofNat_ne_top).2 hgK
    have hg : IntegrableOn (fun t : ℝ => ‖1 / (2 * √t)‖ ^ (2 : ENNReal).toReal)
        (Icc 0 (1 / 4)) :=
      integrable_of_integrable_comp_im measurableSet_Icc measurableSet_Icc
        (by simp [Real.volume_Icc]; norm_num) (by simp [Real.volume_Icc]) hiK
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
    refine memWkpLoc_succ_iff.2 ⟨continuous_sqrt_im.continuousOn.memLpLoc, D, hDU,
      memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKU hK => ?_)⟩
    have hKR : K ⊆ Icc (-1) 1 ×ℂ Icc 0 1 := fun z hz => by
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (hKU hz).1
      have hre := (Complex.abs_re_le_norm z).trans hz1.le
      have him := (Complex.abs_im_le_norm z).trans hz1.le
      exact ⟨abs_le.1 hre, (hKU hz).2, (abs_le.1 him).2⟩
    have : IsFiniteMeasure (volume.restrict (Icc (-1 : ℝ) 1)) := ⟨by simp⟩
    have hR : MemLp (fun z : ℂ => 1 / (2 * √z.im)) p
        (volume.restrict (Icc (-1) 1 ×ℂ Icc 0 1)) :=
      ((memLp_inv_two_sqrt hp one_pos).comp_snd (volume.restrict (Icc (-1 : ℝ) 1)))
        |>.comp_measurePreserving (measurePreserving_reProdIm measurableSet_Icc measurableSet_Icc)
    refine (hR.congr_norm ?_ (Eventually.of_forall fun z => (norm_sqrt_im_deriv z).symm))
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
  refine memWkpLoc_succ_iff.2 ⟨continuous_sqrt_im.continuousOn.memLpLoc, _,
    hasWeakFDerivOn_sqrt_im.mono fun z hz => (interior_subset (s := V) hz).2,
    memWkpLoc_zero_iff.2 (continuousOn_sqrt_im_deriv.mono fun z hz => ?_).memLpLoc⟩
  exact (hz : z ∈ V).2

end TauCeti
