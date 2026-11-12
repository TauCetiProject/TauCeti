/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Reflection
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.Analysis.SpecialFunctions.Pow.NormSqAdd
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Limit
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
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
* Polynomials are in every local Sobolev class on every set, as holomorphic maps on the plane
  (`DifferentiableOn.memWkpLoc`).
* The map `z ↦ ‖z‖` is in the local class `W^{2,p}` exactly when `p < 2`, on every set whose
  interior contains the origin: away from the origin its second derivative has norm between
  `‖z‖⁻¹` and `2 ‖z‖⁻¹`, and `‖z‖ ^ (-p)` is integrable near the origin of the plane exactly when
  `p < 2`. For `p < 2` the weak second derivative across the origin is obtained by approximating
  the coordinates of `z / ‖z‖` by those of `z / (‖z‖ ^ 2 + c) ^ (1 / 2)`.
* The indicator of the half-plane `{z | 0 < z.re}` has no weak derivative on any open set
  meeting the imaginary axis, so it is in every local `Lᵖ` class but in no local `W^{k,p}` class
  of positive order there.
* On the closed upper half-disc `D⁺ = ball 0 1 ∩ {z | 0 ≤ z.im}`, the map `z ↦ √z.im` is in the
  local class `W^{1,p}` exactly when `p < 2`, because the `Lᵖ` bounds reach the real axis. On the
  open half-disc it is in that class for every `p`, although it is continuous up to the axis.
* The even reflection does not extend `u = Im z` from the upper half-disc to a local `W^{2,p}`
  map, for any exponent: it gives `|Im z|`, whose first derivative jumps across the real axis. The
  order-two reflection `u(s, -t) = -3 u(s, t) + 4 u(s, t / 2)` gives `Im z` back.

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

/-! ### Polynomials -/

/-- Every complex polynomial is in every local Sobolev class on every set. -/
theorem _root_.Polynomial.memWkpLoc_eval (P : Polynomial ℂ) (U : Set ℂ) (k : ℕ) :
    MemWkpLoc p U k (fun z => P.eval z) :=
  P.differentiable.differentiableOn.memWkpLoc (Ω := ⊤) (subset_univ U) k

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

/-! ### The norm is in `W^{2,p}` for `p < 2` -/

/-- The regularised coordinate `z ↦ (‖z‖ ^ 2 + c) ^ (-1 / 2) ⟪e, z⟫` of the unit radial field. -/
private def unitRadialCoord (c : ℝ) (e z : ℂ) : ℝ :=
  (‖z‖ ^ 2 + c) ^ (-(1 / 2) : ℝ) * innerSL ℝ e z

/-- The derivative of `TauCeti.unitRadialCoord c e`. -/
private def unitRadialCoordDeriv (c : ℝ) (e z : ℂ) : ℂ →L[ℝ] ℝ :=
  (‖z‖ ^ 2 + c) ^ (-(1 / 2) : ℝ) • innerSL ℝ e -
    ((‖z‖ ^ 2 + c) ^ (-(3 / 2) : ℝ) * innerSL ℝ e z) • innerSL ℝ z

private theorem hasFDerivAt_unitRadialCoord {c : ℝ} (e : ℂ) {z : ℂ} (hz : 0 < ‖z‖ ^ 2 + c) :
    HasFDerivAt (unitRadialCoord c e) (unitRadialCoordDeriv c e z) z := by
  have hr := ((hasFDerivAt_id z).norm_sq.add_const c).rpow_const (p := -(1 / 2))
    (Or.inl hz.ne')
  convert hr.mul (innerSL ℝ e).hasFDerivAt using 1
  · rfl
  ext v
  simp only [unitRadialCoordDeriv, sub_apply, add_apply, smul_apply, smul_eq_mul, id,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply]
  norm_num [nsmul_eq_mul]
  ring

private theorem norm_unitRadialCoord_le {c : ℝ} (hc : 0 ≤ c) (e z : ℂ) :
    ‖unitRadialCoord c e z‖ ≤ ‖e‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [unitRadialCoord]
  rw [unitRadialCoord, norm_mul, Real.norm_of_nonneg (by positivity)]
  calc _ ≤ ‖z‖⁻¹ * (‖e‖ * ‖z‖) := by
        gcongr
        · exact rpow_norm_sq_add_neg_half_le hc hz
        · exact (innerSL ℝ e).le_of_opNorm_le (innerSL_apply_norm ℝ e).le z
    _ = ‖e‖ := by field_simp [norm_ne_zero_iff.2 hz]

private theorem norm_unitRadialCoordDeriv_le {c : ℝ} (hc : 0 ≤ c) (e : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ‖unitRadialCoordDeriv c e z‖ ≤ 2 * ‖e‖ * ‖z‖⁻¹ := by
  have hs : 0 < ‖z‖ ^ 2 + c := by have := norm_pos_iff.2 hz; positivity
  have h3 : (‖z‖ ^ 2 + c) ^ (-(3 / 2) : ℝ) * ‖z‖ ^ 2 ≤ (‖z‖ ^ 2 + c) ^ (-(1 / 2) : ℝ) := by
    calc _ ≤ (‖z‖ ^ 2 + c) ^ (-(3 / 2) : ℝ) * (‖z‖ ^ 2 + c) := by gcongr; linarith
      _ = _ := by rw [← Real.rpow_add_one hs.ne']; norm_num
  have h1 := rpow_norm_sq_add_neg_half_le hc hz
  have hez : ‖innerSL ℝ e z‖ ≤ ‖e‖ * ‖z‖ :=
    (innerSL ℝ e).le_of_opNorm_le (innerSL_apply_norm ℝ e).le z
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_mul, innerSL_apply_norm, innerSL_apply_norm,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc _ ≤ (‖z‖ ^ 2 + c) ^ (-(1 / 2) : ℝ) * ‖e‖ +
        (‖z‖ ^ 2 + c) ^ (-(3 / 2) : ℝ) * (‖e‖ * ‖z‖) * ‖z‖ := by gcongr
    _ = ‖e‖ * ((‖z‖ ^ 2 + c) ^ (-(1 / 2) : ℝ) + (‖z‖ ^ 2 + c) ^ (-(3 / 2) : ℝ) * ‖z‖ ^ 2) := by
        ring
    _ ≤ ‖e‖ * (2 * ‖z‖⁻¹) := by gcongr; linarith
    _ = _ := by ring

private theorem continuous_unitRadialCoord {c : ℝ} (hc : 0 < c) (e : ℂ) :
    Continuous (unitRadialCoord c e) :=
  (continuous_rpow_norm_sq_add hc _).mul (innerSL ℝ e).continuous

private theorem continuous_unitRadialCoordDeriv {c : ℝ} (hc : 0 < c) (e : ℂ) :
    Continuous (unitRadialCoordDeriv c e) :=
  ((continuous_rpow_norm_sq_add hc _).smul continuous_const).sub
    (((continuous_rpow_norm_sq_add hc _).mul (innerSL ℝ e).continuous).smul
      (innerSL ℝ (E := ℂ)).continuous)

private theorem measurable_unitRadialCoord (c : ℝ) (e : ℂ) : Measurable (unitRadialCoord c e) := by
  unfold unitRadialCoord
  fun_prop

private theorem measurable_unitRadialCoordDeriv (c : ℝ) (e : ℂ) :
    Measurable (unitRadialCoordDeriv c e) := by
  unfold unitRadialCoordDeriv
  fun_prop


private theorem tendsto_unitRadialCoord (e : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => unitRadialCoord c e z) (𝓝 0) (𝓝 (unitRadialCoord 0 e z)) :=
  ((continuousAt_rpow_norm_sq_add hz _).mul continuousAt_const).tendsto

private theorem tendsto_unitRadialCoordDeriv (e : ℂ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c => unitRadialCoordDeriv c e z) (𝓝 0) (𝓝 (unitRadialCoordDeriv 0 e z)) :=
  (((continuousAt_rpow_norm_sq_add hz _).smul continuousAt_const).sub
    (((continuousAt_rpow_norm_sq_add hz _).mul continuousAt_const).smul
      continuousAt_const)).tendsto

private theorem locallyIntegrable_unitRadialCoord {c : ℝ} (hc : 0 ≤ c) (e : ℂ) :
    LocallyIntegrable (unitRadialCoord c e) volume :=
  (locallyIntegrable_const ‖e‖).mono (measurable_unitRadialCoord c e).aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa using norm_unitRadialCoord_le hc e z)

private theorem norm_unitRadialCoordDeriv_le_rpow (e : ℂ) :
    ∀ᵐ z : ℂ ∂volume, ‖unitRadialCoordDeriv 0 e z‖ ≤ 2 * ‖e‖ * ‖z‖ ^ (-1 : ℝ) := by
  filter_upwards [volume.ae_ne 0] with z hz
  rw [Real.rpow_neg_one]
  exact norm_unitRadialCoordDeriv_le le_rfl e hz

private theorem locallyIntegrable_unitRadialCoordDeriv (e : ℂ) :
    LocallyIntegrable (unitRadialCoordDeriv 0 e) volume := by
  have h := (locallyIntegrable_norm_sub_rpow (mu := (volume : Measure ℂ)) (s := -1)
    (by simp [Complex.finrank_real_complex]) 0).smul (2 * ‖e‖)
  refine h.mono (measurable_unitRadialCoordDeriv 0 e).aestronglyMeasurable ?_
  filter_upwards [norm_unitRadialCoordDeriv_le_rpow e] with z hz
  rw [Pi.smul_apply, zero_sub, norm_neg, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact hz


/-- The unit disc as an open set. -/
private def unitBall : Opens ℂ := ⟨ball 0 1, isOpen_ball⟩

private theorem hasWeakFDerivOn_unitRadialCoord_unitBall (e : ℂ) :
    HasWeakFDerivOn volume unitBall (unitRadialCoord 0 e) (unitRadialCoordDeriv 0 e) := by
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hc : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc0 : ∀ n, 0 < c n := fun n => Nat.one_div_pos_of_nat
  refine hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub (l := atTop)
    (u := fun n => unitRadialCoord (c n) e) (U := fun n => unitRadialCoordDeriv (c n) e)
    ((locallyIntegrable_unitRadialCoord le_rfl e).locallyIntegrableOn _)
    (fun v => by
      simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
        (ContinuousLinearMap.apply ℝ ℝ v).locallyIntegrableOn_comp
          ((locallyIntegrable_unitRadialCoordDeriv e).locallyIntegrableOn _))
    (fun n => ?_) ?_ ?_
  · exact hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (continuous_unitRadialCoord (hc0 n) e).continuousOn
      ((continuous_unitRadialCoordDeriv (hc0 n) e).locallyIntegrable.locallyIntegrableOn _)
      fun z _ => hasFDerivAt_unitRadialCoord e (by have := hc0 n; positivity)
  · simpa only [ofReal_norm, unitBall, Opens.coe_mk] using
      tendsto_lintegral_norm_of_dominated_convergence
        (μ := volume.restrict (ball (0 : ℂ) 1)) (bound := fun _ => ‖e‖)
        (fun n => (measurable_unitRadialCoord _ e).aestronglyMeasurable)
        (integrableOn_const (C := ‖e‖)).hasFiniteIntegral
        (fun n => Eventually.of_forall fun z => norm_unitRadialCoord_le (hc0 n).le e z)
        (ae_restrict_of_ae <| by
          filter_upwards [volume.ae_ne 0] with z hz
          exact (tendsto_unitRadialCoord e hz).comp hc)
  · simpa only [ofReal_norm, unitBall, Opens.coe_mk] using
      tendsto_lintegral_norm_of_dominated_convergence
        (μ := volume.restrict (ball (0 : ℂ) 1)) (bound := fun z => 2 * ‖e‖ * ‖z‖ ^ (-1 : ℝ))
        (fun n => (measurable_unitRadialCoordDeriv _ e).aestronglyMeasurable)
        ((integrableOn_norm_rpow_ball (by simp [Complex.finrank_real_complex])).const_mul
          (2 * ‖e‖)).hasFiniteIntegral
        (fun n => ae_restrict_of_ae <| by
          filter_upwards [volume.ae_ne 0] with z hz
          rw [Real.rpow_neg_one]
          exact norm_unitRadialCoordDeriv_le (hc0 n).le e hz)
        (ae_restrict_of_ae <| by
          filter_upwards [volume.ae_ne 0] with z hz
          exact (tendsto_unitRadialCoordDeriv e hz).comp hc)


private theorem hasWeakFDerivOn_unitRadialCoord (e : ℂ) :
    HasWeakFDerivOn volume ⊤ (unitRadialCoord 0 e) (unitRadialCoordDeriv 0 e) := by
  have hcompl : HasWeakFDerivOn volume ⟨{0}ᶜ, isOpen_compl_singleton⟩ (unitRadialCoord 0 e)
      (unitRadialCoordDeriv 0 e) :=
    hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
      (fun z hz => (hasFDerivAt_unitRadialCoord e (by have := norm_pos_iff.2 hz; positivity)
        ).continuousAt.continuousWithinAt)
      ((locallyIntegrable_unitRadialCoordDeriv e).locallyIntegrableOn _)
      fun z hz => hasFDerivAt_unitRadialCoord e (by have := norm_pos_iff.2 hz.1; positivity)
  refine ((hasWeakFDerivOn_unitRadialCoord_unitBall e).sup hcompl).mono fun z _ => ?_
  rcases eq_or_ne z 0 with rfl | hz
  · exact Or.inl (mem_ball_self one_pos)
  · exact Or.inr hz

private theorem memWkpLoc_one_unitRadialCoord (hp : p < 2) (e : ℂ) :
    MemWkpLoc p U 1 (unitRadialCoord 0 e) := by
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, unitRadialCoordDeriv 0 e,
    (hasWeakFDerivOn_unitRadialCoord e).mono le_top, memWkpLoc_zero_iff.2
      (memLpLoc_iff.2 fun K _ hK => ?_)⟩
  · have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact MemLp.of_bound (measurable_unitRadialCoord 0 e).aestronglyMeasurable ‖e‖
      (Eventually.of_forall (norm_unitRadialCoord_le le_rfl e))
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
    have hp2 : p.toReal < 2 := by
      simpa using (ENNReal.toReal_lt_toReal (ne_top_of_lt hp) (by simp)).2 hp
    have hker : MemLp (fun z : ℂ => ‖z‖ ^ (-1 : ℝ)) p (volume.restrict (ball 0 R)) :=
      memLp_norm_rpow_ball (ne_top_of_lt hp) (by simp [Complex.finrank_real_complex]; linarith)
    refine ((hker.const_mul (2 * ‖e‖)).mono_measure
      (Measure.restrict_mono hR le_rfl)).of_le
      (measurable_unitRadialCoordDeriv 0 e).aestronglyMeasurable
      (ae_restrict_of_ae ((norm_unitRadialCoordDeriv_le_rpow e).mono fun z hz => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    exact hz


/-- The derivative of the norm of `ℂ` away from the origin, in the coordinates `re` and `im`. -/
private def normDeriv (z : ℂ) : ℂ →L[ℝ] ℝ :=
  unitRadialCoord 0 1 z • Complex.reCLM + unitRadialCoord 0 Complex.I z • Complex.imCLM

private theorem hasFDerivAt_norm_normDeriv {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun y : ℂ => ‖y‖) (normDeriv z) z := by
  convert hasFDerivAt_norm_of_ne hz using 1
  have h : (‖z‖ ^ 2 + 0) ^ (-(1 / 2) : ℝ) = ‖z‖⁻¹ := by
    rw [add_zero, Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  ext v
  simp only [normDeriv, unitRadialCoord, h, add_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply, Complex.reCLM_apply, Complex.imCLM_apply, Complex.inner]
  simp
  ring

private theorem memWkpLoc_one_normDeriv (hp : p < 2) : MemWkpLoc p U 1 normDeriv := by
  have h := ((memWkpLoc_one_unitRadialCoord (U := U) hp 1).clm_comp
    ((1 : ℝ →L[ℝ] ℝ).smulRight Complex.reCLM)).add
    ((memWkpLoc_one_unitRadialCoord (U := U) hp Complex.I).clm_comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight Complex.imCLM))
  convert h using 1
  funext z
  ext v
  simp [normDeriv]

private theorem locallyIntegrable_normDeriv : LocallyIntegrable normDeriv volume := by
  have h1 := measurable_unitRadialCoord 0 1
  have hI := measurable_unitRadialCoord 0 Complex.I
  refine (locallyIntegrable_const (2 : ℝ)).mono (by unfold normDeriv; fun_prop)
    (Eventually.of_forall fun z => ?_)
  have h1 := norm_unitRadialCoord_le le_rfl 1 z
  have hI := norm_unitRadialCoord_le le_rfl Complex.I z
  simp only [norm_one, Complex.norm_I] at h1 hI
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.reCLM_norm, Complex.imCLM_norm, Real.norm_two]
  linarith

/-- The norm `z ↦ ‖z‖` is in the local class `W^{2,p}` on every set for `p < 2`: its second
weak derivative has size `‖z‖⁻¹`, which is `Lᵖ` near the origin of the plane exactly when
`p < 2`. -/
theorem memWkpLoc_two_norm (hp : p < 2) : MemWkpLoc p U 2 (fun z : ℂ => ‖z‖) := by
  have hD : HasWeakFDerivOn volume ⊤ (fun z : ℂ => ‖z‖) normDeriv :=
    hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0)
      continuous_norm.continuousOn
      (locallyIntegrable_normDeriv.locallyIntegrableOn _)
      fun z hz => hasFDerivAt_norm_normDeriv hz.2
  exact memWkpLoc_succ_iff.2 ⟨continuous_norm.continuousOn.memLpLoc, normDeriv,
    hD.mono le_top, memWkpLoc_one_normDeriv hp⟩

/-- The norm `z ↦ ‖z‖` is in the local class `W^{2,p}` on a set whose interior contains the
origin exactly when `p < 2`. -/
theorem memWkpLoc_two_norm_iff (h0 : (0 : ℂ) ∈ interior U) :
    MemWkpLoc p U 2 (fun z : ℂ => ‖z‖) ↔ p < 2 :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_two_norm hp h0 h, memWkpLoc_two_norm⟩

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
        memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKU _ => ?_)⟩
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

/-! ### The even reflection fails at order two -/

/-- The even extension `z ↦ |Im z|` of the normal coordinate `Im z` is not in the local class
`W^{2,p}` on any set whose interior meets the real axis, for any exponent: its first derivative
jumps from `-Im` to `Im` across the axis, so its second derivative is a measure carried by the
axis. -/
theorem not_memWkpLoc_two_abs_im {z₀ : ℂ} (hz₀ : z₀ ∈ interior U) (him : z₀.im = 0) :
    ¬ MemWkpLoc p U 2 (fun z : ℂ => |z.im|) := by
  intro h
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior z₀ hz₀
  -- Rotate by a quarter turn, so that the axis becomes the imaginary axis.
  let A : ℂ ≃L[ℝ] ℂ := ((LinearEquiv.smulOfNeZero ℂ ℂ Complex.I Complex.I_ne_zero).restrictScalars
    ℝ).toContinuousLinearEquiv
  have hA : ∀ z, A z = Complex.I * z := fun z => rfl
  have hmaps : MapsTo (fun z => A z + z₀) (ball 0 r) U := fun z hz => by
    refine interior_subset (hrU ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right, hA, norm_mul, Complex.norm_I, one_mul]
    simpa using hz
  have h' : MemWkpLoc p (ball 0 r) 2 (fun z : ℂ => |z.re|) := by
    convert h.comp_continuousLinearEquiv_add A z₀ hmaps using 2 with z
    simp [hA, him]
  obtain ⟨-, D, hD, hD1⟩ := memWkpLoc_succ_iff.1 h'
  -- The weak derivative is the classical one, `± re`, off the imaginary axis.
  have hlip : LipschitzWith 1 (fun z : ℂ => |z.re|) := LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by simpa using Complex.abs_re_le_norm (a - b))
  have hae := (ae_restrict_iff' (Opens.interior (ball (0 : ℂ) r)).isOpen.measurableSet).1
    (hD.ae_eq hlip.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv)
  have hpos : ∀ z : ℂ, 0 < z.re → fderiv ℝ (fun z : ℂ => |z.re|) z 1 = 1 := fun z hz => by
    have : (fun w : ℂ => |w.re|) =ᶠ[𝓝 z] fun w => Complex.reCLM w :=
      eventuallyEq_of_mem ((Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (mem_preimage.2 (mem_Ioi.2 hz))) fun w hw => abs_of_pos hw
    rw [this.fderiv_eq, Complex.reCLM.fderiv]
    simp
  have hneg : ∀ z : ℂ, z.re < 0 → fderiv ℝ (fun z : ℂ => |z.re|) z 1 = -1 := fun z hz => by
    have : (fun w : ℂ => |w.re|) =ᶠ[𝓝 z] fun w => (-Complex.reCLM) w :=
      eventuallyEq_of_mem ((Complex.continuous_re.isOpen_preimage _ isOpen_Iio).mem_nhds
        (mem_preimage.2 (mem_Iio.2 hz))) fun w hw => abs_of_neg hw
    rw [this.fderiv_eq, ContinuousLinearMap.fderiv]
    simp
  -- So `(D · 1 + 1) / 2` is the indicator of the right half-plane, which is not `W^{1,p}`.
  have hind : MemWkpLoc p (ball 0 r) 1 ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) := by
    refine (((hD1.clm_comp (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ))).add
      (memWkpLoc_const (1 : ℝ))).const_smul (1 / 2)).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hae, measure_eq_zero_iff_ae_notMem.1 (Complex.volume_setOf_re_eq 0)]
      with z hz hz0 hzb
    rw [Opens.coe_interior, isOpen_ball.interior_eq] at hz
    simp only [Pi.smul_apply, Pi.add_apply, ContinuousLinearMap.apply_apply, hz hzb, smul_eq_mul]
    rcases lt_or_gt_of_ne hz0 with h | h
    · rw [hneg z h, indicator_of_notMem (s := {z : ℂ | 0 < z.re}) (not_lt.2 h.le)]
      norm_num
    · rw [hpos z h, indicator_of_mem (s := {z : ℂ | 0 < z.re}) h]
      norm_num
  exact not_memWkpLoc_indicator_re_pos (k := 0) (z₀ := 0)
    (by rw [isOpen_ball.interior_eq]; exact mem_ball_self hr) rfl hind


/-- The order-one reflection across the real axis is the even reflection, and it does not extend
the normal coordinate `u = Im z` from the upper half-disc to a `W^{2,p}` map on the unit disc, for
any exponent: it gives `|Im z|`. -/
theorem not_memWkpLoc_two_planarReflection_one_im :
    ¬ MemWkpLoc p (ball (0 : ℂ) 1) 2
      (planarReflection (higherReflectionCoeff 1) fun z => z.im) := by
  have h : planarReflection (higherReflectionCoeff 1) (fun z : ℂ => z.im) = fun z => |z.im| :=
    funext fun z => planarReflection_higherReflectionCoeff_one _ z
  rw [h]
  exact not_memWkpLoc_two_abs_im (by rw [isOpen_ball.interior_eq]; exact mem_ball_self one_pos) rfl

/-- The order-two reflection `u(s, -t) = -3 u(s, t) + 4 u(s, t / 2)` extends the normal coordinate
`u = Im z` to itself, which is in every local Sobolev class on every set. -/
theorem memWkpLoc_planarReflection_two_im (U : Set ℂ) (k : ℕ) :
    MemWkpLoc p U k (planarReflection (higherReflectionCoeff 2) fun z => z.im) := by
  rw [planarReflection_higherReflectionCoeff_two_im]
  exact (Complex.imCLM.contDiff.contDiffOn : ContDiffOn ℝ k _ ((⊤ : Opens ℂ) : Set ℂ)).memWkpLoc
    (subset_univ U)

end TauCeti
