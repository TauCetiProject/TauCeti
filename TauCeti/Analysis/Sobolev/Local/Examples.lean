/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Reflection
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Holomorphic
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Membership and non-membership examples for local Sobolev classes

This file tests `TauCeti.MemWkpLoc`, `TauCeti.MemLpLoc`, and `TauCeti.MemW1pLoc` against explicit
functions on planar and general finite-dimensional Euclidean domains, including infinite-dimensional
Banach targets.

* Linear and continuous affine maps into complete spaces, and in particular the identity of `E`, lie
  in `MemW1pLoc p Ω` for all `p`, whereas the identity is not in `Lᵖ(E)` for `0 < p < ∞` on any
  nontrivial space (`TauCeti.memW1pLoc_id`, `TauCeti.not_memLp_id`).
* The norm `x ↦ ‖x‖` on any finite-dimensional real normed space lies in `MemW1pLoc p Ω` for every
  `p` (`TauCeti.memW1pLoc_norm`); on `ℝ × ℝ` with the `max` norm its derivative at `(1, 1 / 2)` in
  direction `(0, 1)` vanishes (`TauCeti.fderiv_norm_prod_apply_snd_eq_zero`), unlike the
  inner-product formula. On `ℂ`, `z ↦ ‖z‖` lies in `W^{2,p}_loc` near `0` iff `p < 2`.
* Polynomials on `ℂ` lie in every local Sobolev class (`Polynomial.memWkpLoc`).
* On a nontrivial finite-dimensional space `E`, `x ↦ ‖x‖⁻¹` lies in `MemLpLoc p U` near `0` iff
  `p < dim E` (`TauCeti.memLpLoc_norm_inv_iff_of_mem_nhds`, giving `p < 3` on `ℝ³`).
* On a finite-dimensional inner product space `E`, for `α > -1` the radial map `x ↦ ‖x‖ ^ α • x`
  lies in `MemW1pLoc p Ω` iff `x ↦ ‖x‖ ^ α` lies in `MemLpLoc p Ω`
  (`TauCeti.memW1pLoc_norm_rpow_smul_self_iff`), and when `dim E ≥ 2` and `0 ∈ Ω` the unit radial
  map `x ↦ ‖x‖⁻¹ • x` lies in `MemW1pLoc p Ω` iff `p < dim E` (`TauCeti.memW1pLoc_unitRadial_iff`,
  specializing on `ℂ` to `z ↦ z / ‖z‖` iff `p < 2`).
* The indicator of a half-space `{x | 0 < ℓ x}` lies in `MemLpLoc p U` for every `p` and in no
  `MemW1pLoc p Ω` meeting `{x | ℓ x = 0}` (`TauCeti.memLpLoc_indicator_pos`,
  `TauCeti.not_memW1pLoc_indicator_pos`).
* For a scalar map `a ∈ MemW1pLoc p Ω` and a vector `v ∈ ℓ²(ℕ)`, `x ↦ a x • v` lies in
  `MemW1pLoc p Ω` with weak derivative `h ↦ Da x h • v` (`TauCeti.MemW1pLoc.smul_const_lp_two`).
* Planar half-disc and logarithmic profiles (`z ↦ √z.im`, `z ↦ log ‖z‖`, and reflection examples).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299, §2.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Topology Distributions RealInnerProductSpace

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
protected theorem _root_.Polynomial.memWkpLoc (P : Polynomial ℂ) (U : Set ℂ) (k : ℕ) :
    MemWkpLoc p U k (fun z => P.eval z) :=
  P.differentiable.memWkpLoc

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

/-- For `p < 2`, the coordinate `z ↦ ‖z‖⁻¹ ⟪z, e⟫` of the weak gradient `z / ‖z‖` of the norm is in
the local class `W^{1,p}` on every set: it is bounded, and its weak derivative has size at most
`2 ‖e‖ ‖z‖⁻¹`. -/
private theorem memWkpLoc_one_norm_rpow_neg_one_mul_inner (hp : p < 2) (e : ℂ) :
    MemWkpLoc p U 1 (fun z : ℂ => ‖z‖ ^ (-1 : ℝ) * ⟪z, e⟫) := by
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, _,
    hasWeakFDerivOn_norm_rpow_neg_one_mul_inner (by simp [Complex.finrank_real_complex]) e _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K _ hK => ?_)⟩
  · have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable ‖e‖
      (Eventually.of_forall fun z => abs_norm_rpow_neg_one_mul_inner_le e z)
  · have hker : MemLp (fun z : ℂ => ‖z‖⁻¹) p (volume.restrict K) :=
      hK.memLp_norm_inv_restrict (by simpa [Complex.finrank_real_complex] using hp)
    refine (hker.const_mul (2 * ‖e‖)).of_le (by fun_prop : Measurable _).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
    exact norm_norm_rpow_neg_one_smul_innerSL_sub_le e z

/-- The norm `z ↦ ‖z‖` is in the local class `W^{2,p}` on every set for `p < 2`: its second
weak derivative has size `‖z‖⁻¹`, which is `Lᵖ` near the origin of the plane exactly when
`p < 2`. -/
theorem memWkpLoc_two_norm (hp : p < 2) : MemWkpLoc p U 2 (fun z : ℂ => ‖z‖) := by
  have hD := hasWeakFDerivOn_norm_rpow (μ := volume) (s := 1)
    (by norm_num [Complex.finrank_real_complex]) (Opens.interior U)
  norm_num only [Real.rpow_one, one_mul] at hD
  refine continuous_norm.continuousOn.memLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn hD ?_ ?_
  · simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul] using
      memWkpLoc_one_norm_rpow_neg_one_mul_inner (U := U) hp 1
  · simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul] using
      memWkpLoc_one_norm_rpow_neg_one_mul_inner (U := U) hp Complex.I

/-- The norm `z ↦ ‖z‖` is in the local class `W^{2,p}` on a set whose interior contains the
origin exactly when `p < 2`. -/
theorem memWkpLoc_two_norm_iff (h0 : (0 : ℂ) ∈ interior U) :
    MemWkpLoc p U 2 (fun z : ℂ => ‖z‖) ↔ p < 2 :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_two_norm hp h0 h, memWkpLoc_two_norm⟩

/-! ### A jump across a hyperplane -/

/-- Integrating `deriv a` on `(0, ∞)` for a smooth bump `a` equal to `1` near `0` gives `-1`. -/
private theorem integral_deriv_bump_mul_indicator_Ioi (a : ContDiffBump (0 : ℝ)) :
    ∫ t : ℝ, deriv a t * (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t = -1 := by
  have hfun : (fun t : ℝ => deriv a t * (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t) =
      (Ioi (0 : ℝ)).indicator (deriv a) := by
    funext t; by_cases ht : 0 < t <;> simp [Set.indicator, ht]
  have hda : ∀ t, HasDerivAt a (deriv a t) t := fun t =>
    ((a.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have hdc : Continuous (deriv a) := (a.contDiff (n := 1)).continuous_deriv le_rfl
  rw [hfun, integral_indicator measurableSet_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto (m := 0) a.continuous.continuousWithinAt
      (fun t _ => hda t)
      (hdc.integrable_of_hasCompactSupport a.hasCompactSupport.deriv).integrableOn,
    a.one_of_mem_closedBall (mem_closedBall_self a.rIn_pos.le)]
  · simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop a.rOut] with t ht
    refine (a.zero_of_le_dist ?_).symm
    rw [Real.dist_eq, sub_zero]
    exact ht.trans (le_abs_self t)

/-- On `ℝ × EuclideanSpace ℝ (Fin m)`, the indicator of `{q | 0 < q.1}` does not have weak
directional derivative `0` in direction `(1, 0)` on any open set containing `(0, y₀)`. -/
private theorem not_hasWeakLineDerivOn_indicator_fst_pos {m : ℕ}
    {Ω' : Opens (ℝ × EuclideanSpace ℝ (Fin m))} {y₀ : EuclideanSpace ℝ (Fin m)}
    (hy₀ : ((0 : ℝ), y₀) ∈ Ω') :
    ¬ HasWeakLineDerivOn volume Ω'
        (fun q : ℝ × EuclideanSpace ℝ (Fin m) => (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) q.1)
        0 (1, 0) := by
  intro hline
  have : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω'.isOpen (0, y₀) hy₀
  let a : ContDiffBump (0 : ℝ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let b : ContDiffBump y₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let f : ℝ × EuclideanSpace ℝ (Fin m) → ℝ := ((a : ℝ → ℝ) ∘ Prod.fst) * ((b : _ → ℝ) ∘ Prod.snd)
  have hfs : tsupport f ⊆ closedBall (0, y₀) (ε / 2) := fun q hq => by
    have hq1 := tsupport_comp_subset_preimage (a : ℝ → ℝ) continuous_fst
      (tsupport_mul_subset_left hq)
    have hq2 := tsupport_comp_subset_preimage (b : _ → ℝ) continuous_snd
      (tsupport_mul_subset_right hq)
    rw [mem_preimage, a.tsupport_eq, mem_closedBall] at hq1
    rw [mem_preimage, b.tsupport_eq, mem_closedBall] at hq2
    rw [mem_closedBall, Prod.dist_eq]
    exact max_le hq1 hq2
  let φ : 𝓓(Ω', ℝ) := ⟨f, (a.contDiff.comp contDiff_fst).mul (b.contDiff.comp contDiff_snd),
    (isCompact_closedBall (0, y₀) _).of_isClosed_subset (isClosed_tsupport f) hfs,
    fun q hq => hball (closedBall_subset_ball (half_lt_self hε) (hfs hq))⟩
  have hφ : (φ : _ → ℝ) = f := TestFunction.coe_mk
  have hda : ∀ t, HasDerivAt a (deriv a t) t := fun t =>
    ((a.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have hldf : ∀ q, lineDeriv ℝ (φ : _ → ℝ) q (1, 0) = deriv a q.1 * b q.2 := fun q => by
    refine HasLineDerivAt.lineDeriv
      (?_ : HasDerivAt (fun t : ℝ => (φ : _ → ℝ) (q + t • ((1 : ℝ), (0 : _)))) _ 0)
    have h := ((hda (q.1 + 0)).comp_const_add q.1 0).mul_const (b q.2)
    simp only [add_zero] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => by simp [hφ, f])
  have hkey := hline.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [Pi.zero_apply, smul_zero, integral_zero, neg_zero] at hkey
  have hkey' : ∫ q : ℝ × EuclideanSpace ℝ (Fin m),
      (deriv a q.1 * (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) q.1) * b q.2 = 0 := by
    simpa only [hldf, smul_eq_mul, mul_right_comm] using hkey
  have hprod := integral_prod_mul (μ := volume) (ν := volume)
    (fun t => deriv a t * (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t) (fun y => b y)
  rw [Measure.volume_eq_prod, hprod, integral_deriv_bump_mul_indicator_Ioi a] at hkey'
  linarith [b.integral_pos (μ := volume)]

section HalfSpaceIndicator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The indicator of an open half-space `{x | 0 < ℓ x}` is in `MemLpLoc p V` on every set `V` and
for every exponent `p`. -/
theorem memLpLoc_indicator_pos [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] (ℓ : E →L[ℝ] ℝ) (p : ENNReal) (V : Set E) :
    MemLpLoc p V ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := by
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_indicator_const p
    (measurableSet_lt measurable_const ℓ.continuous.measurable).nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

/-- Any nonzero continuous linear functional `ℓ : E →L[ℝ] ℝ` on a finite-dimensional real normed
space admits a continuous linear equivalence `ℝ × EuclideanSpace ℝ (Fin m) ≃L[ℝ] E` under which `ℓ`
is the first coordinate. -/
private theorem exists_cle_prod_of_ne_zero [FiniteDimensional ℝ E] {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ∃ (m : ℕ) (e : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] E), ∀ q, ℓ (e q) = q.1 := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hℓ
  let w : E := (ℓ v)⁻¹ • v
  have hℓw : ℓ w = 1 := by simp [w, inv_mul_cancel₀ hv]
  let K := LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)
  let m := Module.finrank ℝ K
  let bK : K ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (Module.finBasis ℝ K).equivFun.trans (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.equivFun.symm
  let L : (ℝ × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] E :=
    { toFun := fun q => q.1 • w + (bK.symm q.2 : E)
      map_add' := fun q₁ q₂ => by simp [add_smul, add_add_add_comm]
      map_smul' := fun c q => by simp [smul_add, mul_smul]
      invFun := fun x => (ℓ x, bK ⟨x - ℓ x • w, by simp [K, LinearMap.mem_ker, hℓw]⟩)
      left_inv := fun q => by
        have hq2 : ℓ (bK.symm q.2 : E) = 0 := LinearMap.mem_ker.1 (bK.symm q.2).2
        ext <;> simp [hℓw, hq2]
      right_inv := fun x => by simp }
  refine ⟨m, L.toContinuousLinearEquiv, fun q => ?_⟩
  have hq2 : ℓ (bK.symm q.2 : E) = 0 := LinearMap.mem_ker.1 (bK.symm q.2).2
  simp [L, hℓw, hq2]

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

/-- The indicator of a half-space `{x | 0 < ℓ x}` for a nonzero functional `ℓ` has no weak Fréchet
derivative on any open set `Ω` meeting the hyperplane `{x | ℓ x = 0}`. -/
theorem not_hasWeakFDerivOn_indicator_pos {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {Ω : Opens E} {x₀ : E}
    (hx₀ : x₀ ∈ Ω) (hx₀0 : ℓ x₀ = 0) (D : E → E →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  set u : E → ℝ := {x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ) with hu
  set Ωp : Opens E := Ω ⊓ ⟨{x | 0 < ℓ x}, isOpen_lt continuous_const ℓ.continuous⟩
  set Ωn : Opens E := Ω ⊓ ⟨{x | ℓ x < 0}, isOpen_lt ℓ.continuous continuous_const⟩
  have hconst : HasWeakFDerivOn volume Ωp (fun _ => (1 : ℝ)) 0 :=
    hasWeakFDerivOn_iff.2 fun v => by simpa using (hasWeakLineDerivOn_const (1 : ℝ))
  have hp : HasWeakFDerivOn volume Ωp u 0 := hconst.congr_ae <|
    (ae_restrict_iff' Ωp.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx => by
      simp [hu, Set.indicator_of_mem (show x ∈ {x : E | 0 < ℓ x} from hx.2)]
  have hn : HasWeakFDerivOn volume Ωn u 0 := (hasWeakFDerivOn_zero (μ := volume)).congr_ae <|
    (ae_restrict_iff' Ωn.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx => by
      have hz' : ¬ 0 < ℓ x := not_lt.2 (le_of_lt hx.2)
      simp [hu, hz']
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hℓ
  have hker_ne : LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) ≠ ⊤ := fun htop =>
    hv (LinearMap.mem_ker.1 (htop ▸ Submodule.mem_top))
  have hnull : volume (LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) : Set E) = 0 :=
    Measure.addHaar_submodule volume _ hker_ne
  have hD0 : D =ᵐ[volume.restrict Ω] 0 := by
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
    filter_upwards [(ae_restrict_iff' Ωp.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hp),
      (ae_restrict_iff' Ωn.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hn),
      measure_eq_zero_iff_ae_notMem.1 hnull] with x hxp hxn hx0 hxΩ
    rcases lt_or_gt_of_ne (show ℓ x ≠ 0 from hx0) with h | h
    · exact hxn ⟨hxΩ, h⟩
    · exact hxp ⟨hxΩ, h⟩
  obtain ⟨m, e, hℓe⟩ := exists_cle_prod_of_ne_zero hℓ
  have : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  let Ω' : Opens (ℝ × EuclideanSpace ℝ (Fin m)) := Ω.comap ⟨e, e.continuous⟩
  have hpull :=
    ((hD.congr_ae_deriv hD0).comp_continuousLinearEquiv (μ := volume) (U := Ω') e
      fun _ hx => hx).hasWeakLineDerivOn (1, 0)
  have hu_eq : u ∘ e = fun q => (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) q.1 := by
    funext q; by_cases hq : 0 < q.1 <;> simp [u, Function.comp_apply, Set.indicator, hℓe, hq]
  have hy₀ : ((0 : ℝ), (e.symm x₀).2) ∈ Ω' := by
    have he0 : ((0 : ℝ), (e.symm x₀).2) = e.symm x₀ :=
      Prod.ext (by simp [← hℓe (e.symm x₀), hx₀0]) rfl
    change e (0, (e.symm x₀).2) ∈ Ω
    simpa [he0] using hx₀
  rw [hu_eq] at hpull
  exact not_hasWeakLineDerivOn_indicator_fst_pos hy₀
    (hpull.congr_ae_deriv (Eventually.of_forall fun _ => by simp))

/-- The indicator of a half-space `{x | 0 < ℓ x}` for a nonzero functional `ℓ` lies in no
`MemW1pLoc p Ω` when `Ω` meets `{x | ℓ x = 0}`. -/
theorem not_memW1pLoc_indicator_pos {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {Ω : Opens E} {x₀ : E}
    (hx₀ : x₀ ∈ Ω) (hx₀0 : ℓ x₀ = 0) :
    ¬ MemW1pLoc p Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := fun h => by
  obtain ⟨D, hD, -⟩ := h.exists_hasWeakFDerivOn
  exact not_hasWeakFDerivOn_indicator_pos hℓ hx₀ hx₀0 D hD

end HalfSpaceIndicator

/-- The indicator of the right half-plane is locally `Lᵖ` on every set, for every exponent. -/
theorem memLpLoc_indicator_re_pos :
    MemLpLoc p U ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) :=
  memLpLoc_indicator_pos Complex.reCLM p U

/-- The indicator of the right half-plane has no weak derivative on any open set meeting the
imaginary axis: its distributional derivative is a measure carried by the axis. -/
theorem not_hasWeakFDerivOn_indicator_re_pos {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hre : z₀.re = 0) (D : ℂ → ℂ →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn volume Ω ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) D :=
  not_hasWeakFDerivOn_indicator_pos (ℓ := Complex.reCLM)
    (fun h => (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using DFunLike.congr_fun h (1 : ℂ)))
    hz₀ hre D

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

/-! ### The logarithm of the norm and its gradient -/

/-- **`‖z‖⁻¹` is locally `Lᵖ` near the origin exactly for `p < 2`.** -/
theorem memLpLoc_norm_inv_iff (hU : U ∈ 𝓝 0) :
    MemLpLoc p U (fun z : ℂ => ‖z‖⁻¹) ↔ p < 2 := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK =>
    hK.memLp_norm_inv_restrict (by simpa [Complex.finrank_real_complex] using h)⟩
  by_contra! hp2
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε (by simpa [Complex.finrank_real_complex] using hp2)
    (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

/-- **The components of the gradient of `log ‖z‖` are locally `Lᵖ` near the origin exactly for
`p < 2`.** These are `Re z / ‖z‖²` and `Im z / ‖z‖²`, the divergence-form data of `log ‖z‖`. -/
theorem memLpLoc_re_div_and_im_div_iff (hU : U ∈ 𝓝 0) :
    (MemLpLoc p U (fun z : ℂ => z.re / ‖z‖ ^ 2) ∧ MemLpLoc p U fun z : ℂ => z.im / ‖z‖ ^ 2) ↔
      p < 2 := by
  rw [← memLpLoc_norm_inv_iff hU]
  have hdiv (a : ℝ) (z : ℂ) (hz : |a| ≤ ‖z‖) :
      ‖a / ‖z‖ ^ 2‖ ≤ ‖‖z‖⁻¹‖ := by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    rw [norm_div, norm_pow, norm_norm, Real.norm_eq_abs,
      Real.norm_of_nonneg (inv_nonneg.2 hn.le), div_le_iff₀ (pow_pos hn 2)]
    calc |a| ≤ ‖z‖ := hz
      _ = ‖z‖⁻¹ * ‖z‖ ^ 2 := by field_simp
  constructor
  · rintro ⟨hf, hg⟩
    refine memLpLoc_iff.2 fun K hKU hK => ?_
    refine ((memLpLoc_iff.1 hf K hKU hK).norm.add
      (memLpLoc_iff.1 hg K hKU hK).norm).of_le (by fun_prop) ?_
    filter_upwards with z
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have key : ‖z‖⁻¹ ≤ |z.re| / ‖z‖ ^ 2 + |z.im| / ‖z‖ ^ 2 := by
      rw [← add_div, le_div_iff₀ (pow_pos hn 2)]
      calc ‖z‖⁻¹ * ‖z‖ ^ 2 = ‖z‖ := by field_simp
        _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [Real.norm_of_nonneg (inv_nonneg.2 hn.le), Pi.add_apply,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    simpa only [Real.norm_eq_abs, abs_div, abs_pow, abs_norm] using key
  · intro h
    exact ⟨memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 h K hKU hK).of_le
        (by fun_prop : Measurable fun z : ℂ => z.re / ‖z‖ ^ 2).aestronglyMeasurable
        (ae_of_all _ fun z => hdiv _ z (Complex.abs_re_le_norm z)),
      memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 h K hKU hK).of_le
        (by fun_prop : Measurable fun z : ℂ => z.im / ‖z‖ ^ 2).aestronglyMeasurable
        (ae_of_all _ fun z => hdiv _ z (Complex.abs_im_le_norm z))⟩

/-- **`log ‖z‖` is locally `W^{1,p}` near the origin exactly for `p < 2`.** -/
theorem memWkpLoc_one_log_norm_iff {Ω : Opens ℂ} (h0 : (0 : ℂ) ∈ Ω) :
    MemWkpLoc p Ω 1 (fun z : ℂ => Real.log ‖z‖) ↔ p < 2 := by
  have hU : (Ω : Set ℂ) ∈ 𝓝 0 := Ω.isOpen.mem_nhds h0
  have hmeas : AEStronglyMeasurable (fun z : ℂ => (‖z‖ ^ 2)⁻¹ • innerSL ℝ z) := by
    fun_prop
  -- Pointwise, the weak derivative of `log ‖z‖` has norm `‖z‖⁻¹`, both sides being `0` at `0`.
  have hnorm (z : ℂ) : ‖(‖z‖ ^ 2)⁻¹ • innerSL ℝ z‖ = ‖z‖⁻¹ := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    rw [← (hasFDerivAt_log_norm_of_ne hz).fderiv, norm_fderiv_log_norm_of_ne hz]
  simp only [memWkpLoc_succ_iff_of_isOpen, memWkpLoc_zero_iff]
  rw [← memLpLoc_norm_inv_iff hU]
  constructor
  · rintro ⟨-, D, hD, hDp⟩
    have hae := hD.ae_eq (hasWeakFDerivOn_log_norm Ω)
    refine memLpLoc_iff.2 fun K hKU hK => ?_
    have := (memLpLoc_iff.1 (hDp.congr_ae hae) K hKU hK).norm
    simpa only [hnorm] using this
  · intro h
    refine ⟨memLpLoc_iff.2 fun K hKU hK => ?_, _, hasWeakFDerivOn_log_norm Ω,
      memLpLoc_iff.2 fun K hKU hK => ?_⟩
    · have hn : MemLp (fun z : ℂ => ‖z‖) p (volume.restrict K) :=
        memLpLoc_iff.1 (continuous_norm.continuousOn.memLpLoc (p := p)) K subset_rfl hK
      refine ((memLpLoc_iff.1 h K hKU hK).add hn).of_le
        (Real.measurable_log.comp measurable_norm).aestronglyMeasurable (ae_of_all _ fun z => ?_)
      rw [Pi.add_apply, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
      rcases eq_or_ne z 0 with rfl | hz0
      · simp
      have hn0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
      rw [abs_le]
      constructor
      · have := Real.log_le_sub_one_of_pos (inv_pos.2 hn0)
        rw [Real.log_inv] at this
        linarith
      · linarith [Real.log_le_sub_one_of_pos hn0, inv_pos.2 hn0]
    · exact (memLpLoc_iff.1 h K hKU hK).of_le hmeas.restrict
        (ae_of_all _ fun z => by
          rw [hnorm, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg z))])

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
  have hA : ∀ z, A z = Complex.I * z := fun z => by simp [A]
  have hmaps : MapsTo (fun z => A z + z₀) (ball 0 r) U := fun z hz => by
    refine interior_subset (hrU ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right, hA, norm_mul, Complex.norm_I, one_mul]
    simpa using hz
  have h' : MemWkpLoc p (ball 0 r) 2 (fun z : ℂ => |z.re|) := by
    convert h.comp_continuousLinearEquiv_add A z₀ hmaps using 2 with z
    simp [hA, him]
  obtain ⟨-, D, hD, hD1⟩ := memWkpLoc_succ_iff.1 h'
  -- `|Re z|` is Lipschitz, so its weak derivative is the classical one, `± re`, off the
  -- imaginary axis.
  have hlip : LocallyLipschitz fun z : ℂ => |z.re| :=
    (lipschitzWith_one_norm.comp (RCLike.lipschitzWith_re (K := ℂ))).locallyLipschitz
  have hae := (ae_restrict_iff' (Opens.interior (ball (0 : ℂ) r)).isOpen.measurableSet).1
    (hD.ae_eq hlip.locallyLipschitzOn.hasWeakFDerivOn_fderiv)
  -- So `(D · 1 + 1) / 2` is the indicator of the right half-plane, which is not `W^{1,p}`.
  have hind : MemWkpLoc p (ball 0 r) 1 ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) := by
    refine (((hD1.clm_comp (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ))).add
      (memWkpLoc_const (1 : ℝ))).const_smul (1 / 2)).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hae, measure_eq_zero_iff_ae_notMem.1 (Complex.volume_setOf_re_eq 0)]
      with z hz hz0 hzb
    rw [Opens.coe_interior, isOpen_ball.interior_eq] at hz
    simp only [Pi.smul_apply, Pi.add_apply, ContinuousLinearMap.apply_apply, hz hzb, smul_eq_mul]
    have hre : HasFDerivAt Complex.re Complex.reCLM z := Complex.reCLM.hasFDerivAt
    rcases lt_or_gt_of_ne hz0 with h | h
    · rw [(hre.abs_of_neg h).fderiv,
        indicator_of_notMem (s := {z : ℂ | 0 < z.re}) (not_lt.2 h.le)]
      norm_num
    · rw [(hre.abs_of_pos h).fderiv,
        indicator_of_mem (s := {z : ℂ | 0 < z.re}) h]
      norm_num
  exact not_memWkpLoc_indicator_re_pos (k := 0) (z₀ := 0)
    (by rw [isOpen_ball.interior_eq]; exact mem_ball_self hr) rfl hind


/-- The order-one reflection across the real axis is the even reflection, and it does not extend
the normal coordinate `u = Im z` from the upper half-disc to a `W^{2,p}` map on the unit disc, for
any exponent: it gives `|Im z|`. -/
theorem not_memWkpLoc_two_planarReflection_higherReflectionCoeff_one_im :
    ¬ MemWkpLoc p (ball (0 : ℂ) 1) 2
      (planarReflection (higherReflectionCoeff 1) fun z => z.im) := by
  have h : planarReflection (higherReflectionCoeff 1) (fun z : ℂ => z.im) = fun z => |z.im| :=
    funext fun z => planarReflection_higherReflectionCoeff_one _ z
  rw [h]
  exact not_memWkpLoc_two_abs_im (by rw [isOpen_ball.interior_eq]; exact mem_ball_self one_pos) rfl

/-- The order-two reflection `u(s, -t) = -3 u(s, t) + 4 u(s, t / 2)` extends the normal coordinate
`u = Im z` to itself, which is in every local Sobolev class on every set. -/
theorem memWkpLoc_planarReflection_higherReflectionCoeff_two_im (U : Set ℂ) (k : ℕ) :
    MemWkpLoc p U k (planarReflection (higherReflectionCoeff 2) fun z => z.im) := by
  rw [planarReflection_higherReflectionCoeff_two_im]
  exact Complex.imCLM.contDiff.memWkpLoc

/-! ### Euclidean and Banach-valued examples for `MemLpLoc` and `MemW1pLoc` -/

section EuclideanNormed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every continuous linear map into a Banach space lies in `MemW1pLoc p Ω` on every open set and
for every exponent `p`. -/
protected theorem _root_.ContinuousLinearMap.memW1pLoc [CompleteSpace F]
    (L : E →L[ℝ] F) (p : ENNReal) (Ω : Opens E) :
    MemW1pLoc p Ω L :=
  L.contDiff.memW1pLoc le_rfl

/-- Every continuous affine map into a Banach space lies in `MemW1pLoc p Ω` on every open set and
for every exponent `p`. -/
protected theorem _root_.ContinuousAffineMap.memW1pLoc [CompleteSpace F]
    (A : E →ᴬ[ℝ] F) (p : ENNReal) (Ω : Opens E) :
    MemW1pLoc p Ω A :=
  A.contDiff.memW1pLoc le_rfl

/-- The identity of `E` lies in `MemW1pLoc p Ω` for every open set `Ω` and every exponent `p`. -/
theorem memW1pLoc_id (p : ENNReal) (Ω : Opens E) :
    MemW1pLoc p Ω (id : E → E) :=
  contDiff_id.memW1pLoc le_rfl

/-- On a nontrivial finite-dimensional real normed space, the identity is not globally in `Lᵖ` for
any `0 < p < ∞`: `MemW1pLoc` is genuinely local. -/
theorem not_memLp_id [Nontrivial E] (hp₀ : p ≠ 0) (hp : p ≠ ⊤) :
    ¬ MemLp (id : E → E) p volume := fun h => by
  have hint := (integrable_norm_rpow_iff h.aestronglyMeasurable hp₀ hp).2 h
  refine (volume : Measure E).not_integrable_norm_sub_rpow p.toReal 0 ?_
  simpa only [sub_zero, id_eq] using hint

/-- The norm `x ↦ ‖x‖` on any finite-dimensional real normed space lies in `MemW1pLoc p Ω` on every
open set and for every exponent `p`. -/
theorem memW1pLoc_norm (p : ENNReal) (Ω : Opens E) :
    MemW1pLoc p Ω (fun x : E => ‖x‖) :=
  lipschitzWith_one_norm.memW1pLoc

/-- On `ℝ × ℝ` with its `max` norm `‖(x₁, x₂)‖ = max |x₁| |x₂|`, the derivative of the norm at
`(1, 1 / 2)` in direction `(0, 1)` is `0`, whereas the inner-product formula `⟪x / ‖x‖, (0, 1)⟫`
would be nonzero. -/
theorem fderiv_norm_prod_apply_snd_eq_zero :
    fderiv ℝ (fun y : ℝ × ℝ => ‖y‖) (1, 1 / 2) (0, 1) = 0 := by
  have ho : IsOpen {y : ℝ × ℝ | |y.2| < y.1} :=
    isOpen_lt (continuous_abs.comp continuous_snd) continuous_fst
  have hmem : ((1 : ℝ), (1 / 2 : ℝ)) ∈ {y : ℝ × ℝ | |y.2| < y.1} := by norm_num
  have heq : (fun y : ℝ × ℝ => ‖y‖) =ᶠ[𝓝 (1, 1 / 2)] Prod.fst := by
    filter_upwards [ho.mem_nhds hmem] with y hy
    have hy0 : 0 ≤ y.1 := (abs_nonneg y.2).trans hy.le
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hy0, max_eq_left hy.le]
  have hd : HasFDerivAt (fun y : ℝ × ℝ => ‖y‖) (ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 1 / 2) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.congr_of_eventuallyEq heq
  rw [hd.fderiv]
  rfl

/-- On a nontrivial finite-dimensional real normed space, `x ↦ ‖x‖⁻¹` lies in `MemLpLoc p U` near
the origin if and only if `p < dim E`. -/
theorem memLpLoc_norm_inv_iff_of_mem_nhds [Nontrivial E] {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK => hK.memLp_norm_inv_restrict h⟩
  by_contra! hp
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hp (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

/-- On `ℝ³` (`EuclideanSpace ℝ (Fin 3)`), `x ↦ ‖x‖⁻¹` is locally `Lᵖ` on the whole space if and only
if `p < 3`. -/
theorem memLpLoc_norm_inv_euclideanFinThree_iff :
    MemLpLoc p (univ : Set (EuclideanSpace ℝ (Fin 3)))
      (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) ↔ p < 3 := by
  simpa [finrank_euclideanSpace_fin] using
    memLpLoc_norm_inv_iff_of_mem_nhds (E := EuclideanSpace ℝ (Fin 3)) (p := p) univ_mem

/-! #### Infinite-dimensional `ℓ²(ℕ)` target -/

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
/-- For a scalar Sobolev function `a ∈ MemW1pLoc p Ω` with weak derivative `Da` and a fixed element
`v ∈ ℓ²(ℕ)`, the map `x ↦ a x • v` lies in `MemW1pLoc p Ω` with weak derivative `h ↦ Da x h • v`;
no basis of the target is used. -/
theorem MemW1pLoc.smul_const_lp_two {Ω : Opens E} {a : E → ℝ} {Da : E → E →L[ℝ] ℝ}
    (ha : MemW1pLoc p Ω a) (haD : HasWeakFDerivOn volume Ω a Da) (v : lp (fun _ : ℕ => ℝ) 2) :
    MemW1pLoc p Ω (fun x => a x • v) ∧
      HasWeakFDerivOn volume Ω (fun x => a x • v)
        (fun x => ((ContinuousLinearMap.id ℝ ℝ).smulRight v).comp (Da x)) :=
  ⟨ha.smul_const v, haD.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)⟩

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- For `α > -1`, `x ↦ ‖x‖ ^ α • x` is continuous on the whole space `E`, including at `0`. -/
private theorem continuous_norm_rpow_smul_self {α : ℝ} (hα : -1 < α) :
    Continuous (fun x : E => ‖x‖ ^ α • x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, norm_zero, smul_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hc : Continuous fun y : E => ‖y‖ ^ (α + 1) :=
      continuous_norm.rpow_const fun _ => Or.inr (by linarith)
    have hlim : Tendsto (fun y : E => ‖y‖ ^ (α + 1)) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow (by linarith : α + 1 ≠ 0)] using hc.tendsto 0
    refine hlim.congr' (Eventually.of_forall fun y => ?_)
    dsimp only
    rcases eq_or_ne y 0 with rfl | hy
    · simp [Real.zero_rpow (by linarith : α + 1 ≠ 0)]
    · rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _),
        Real.rpow_add_one (norm_ne_zero_iff.2 hy)]
  · exact (continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.2 hx))).smul
      continuousAt_id

end EuclideanNormed

section EuclideanInnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pointwise operator-norm bounds for the classical derivative
`Dα x = ‖x‖ ^ α • id + (α * ‖x‖ ^ (α - 2)) • (innerSL ℝ x).smulRight x` of `x ↦ ‖x‖ ^ α • x`. -/
private theorem norm_deriv_norm_rpow_smul_self_bounds {α : ℝ} (hα : -1 < α) (x : E) :
    ‖‖x‖ ^ α • ContinuousLinearMap.id ℝ E +
        (α * ‖x‖ ^ (α - 2)) • (innerSL ℝ x).smulRight x‖ ≤ (1 + |α|) * ‖x‖ ^ α ∧
      (x ≠ 0 → (1 + α) * ‖x‖ ^ α ≤
        ‖‖x‖ ^ α • ContinuousLinearMap.id ℝ E +
          (α * ‖x‖ ^ (α - 2)) • (innerSL ℝ x).smulRight x‖) := by
  set Dx : E →L[ℝ] E :=
    ‖x‖ ^ α • ContinuousLinearMap.id ℝ E + (α * ‖x‖ ^ (α - 2)) • (innerSL ℝ x).smulRight x
  constructor
  · rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_ne α 0 with rfl | hα0
      · simpa [Dx] using ContinuousLinearMap.norm_id_le
      · simp [Dx, Real.zero_rpow hα0]
    · have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hpow : ‖x‖ ^ (α - 2) * (‖x‖ * ‖x‖) = ‖x‖ ^ α := by
        rw [← sq, ← Real.rpow_natCast, ← Real.rpow_add hx']
        norm_num
      calc ‖Dx‖ ≤ ‖‖x‖ ^ α • ContinuousLinearMap.id ℝ E‖ +
            ‖(α * ‖x‖ ^ (α - 2)) • (innerSL ℝ x).smulRight x‖ := norm_add_le _ _
        _ ≤ ‖x‖ ^ α * 1 + |α| * ‖x‖ ^ (α - 2) * (‖innerSL ℝ x‖ * ‖x‖) := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hx'.le _),
            Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx'.le _),
            (innerSL ℝ x).norm_smulRight_apply x]
          gcongr
          exact ContinuousLinearMap.norm_id_le
        _ = (1 + |α|) * ‖x‖ ^ α := by
          rw [innerSL_apply_norm, mul_assoc, hpow]
          ring
  · intro hx
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hpow : ‖x‖ ^ (α - 2) * ‖x‖ ^ 2 = ‖x‖ ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx']
      norm_num
    have happ : Dx x = ((1 + α) * ‖x‖ ^ α) • x := by
      simp only [Dx, add_apply, smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
        smul_smul, ← add_smul]
      congr 1
      linear_combination α * hpow
    have hle := Dx.le_opNorm x
    have h1α : 0 ≤ (1 + α) * ‖x‖ ^ α := mul_nonneg (by linarith) (Real.rpow_nonneg hx'.le _)
    rw [happ, norm_smul, Real.norm_of_nonneg h1α] at hle
    exact le_of_mul_le_mul_right hle hx'

/-- Trace identity for the classical derivatives of the coordinates of `x ↦ ‖x‖⁻¹ • x`:
their divergence in an orthonormal basis equals `(dim E - 1) ‖x‖⁻¹`. -/
private theorem sum_unitRadialCoordDeriv_apply_self [FiniteDimensional ℝ E] (x : E) :
    ∑ i : Fin (Module.finrank ℝ E),
        (‖x‖ ^ (-1 : ℝ) • innerSL ℝ (stdOrthonormalBasis ℝ E i) -
          (‖x‖ ^ (-3 : ℝ) * ⟪x, stdOrthonormalBasis ℝ E i⟫) • innerSL ℝ x)
          (stdOrthonormalBasis ℝ E i) =
      ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖⁻¹ := by
  let b := stdOrthonormalBasis ℝ E
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h3 : ‖x‖ ^ (-3 : ℝ) * ‖x‖ ^ 2 = ‖x‖⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx', ← Real.rpow_neg_one]
    norm_num
  have hbi : ∀ i, ⟪b i, b i⟫ = 1 := fun i =>
    real_inner_self_eq_norm_mul_norm (b i) |>.trans (by simp [b.norm_eq_one])
  have hterm : ∀ i,
      (‖x‖ ^ (-1 : ℝ) • innerSL ℝ (b i) - (‖x‖ ^ (-3 : ℝ) * ⟪x, b i⟫) • innerSL ℝ x) (b i) =
        ‖x‖⁻¹ - ‖x‖ ^ (-3 : ℝ) * ⟪x, b i⟫ ^ 2 := fun i => by
    simp only [sub_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, hbi, mul_one,
      Real.rpow_neg_one, sq, mul_assoc]
  simp_rw [show stdOrthonormalBasis ℝ E = b from rfl, hterm, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul, ← Finset.mul_sum, b.sum_sq_inner_left, h3]
  ring

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] {p : ENNReal} {Ω : Opens E}

/-- For `α > -1` on a nontrivial finite-dimensional inner product space, `x ↦ ‖x‖ ^ α • x` lies in
`MemW1pLoc p Ω` if and only if `x ↦ ‖x‖ ^ α` lies in `MemLpLoc p Ω`. -/
theorem memW1pLoc_norm_rpow_smul_self_iff [Nontrivial E] {α : ℝ} (hα : -1 < α) :
    MemW1pLoc p Ω (fun x : E => ‖x‖ ^ α • x) ↔ MemLpLoc p Ω (fun x : E => ‖x‖ ^ α) := by
  let D : E → E →L[ℝ] E := fun x =>
    ‖x‖ ^ α • ContinuousLinearMap.id ℝ E + (α * ‖x‖ ^ (α - 2)) • (innerSL ℝ x).smulRight x
  have hmeasD : Measurable D :=
    ((measurable_norm.pow_const α).smul_const (ContinuousLinearMap.id ℝ E)).add
      ((measurable_const.mul (measurable_norm.pow_const (α - 2))).smul
        (isBoundedBilinearMap_smulRight.continuous.comp₂
          (innerSL ℝ (E := E)).continuous continuous_id).measurable)
  have hd : ∀ x : E, x ≠ 0 → HasFDerivAt (fun y : E => ‖y‖ ^ α • y) (D x) x := fun x hx =>
    ((hasFDerivAt_norm_rpow_of_ne α hx).smul (hasFDerivAt_id x)).congr_fderiv
      (by ext v; simp [D, mul_smul])
  have hlocD : LocallyIntegrableOn D Ω volume := by
    have hpos : -(Module.finrank ℝ E : ℝ) < α := by
      have : (1 : ℝ) ≤ Module.finrank ℝ E := Nat.one_le_cast.2 Module.finrank_pos
      linarith
    have hker := (locallyIntegrable_norm_sub_rpow (mu := volume) hpos 0).smul (1 + |α|)
    refine (hker.mono hmeasD.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)).locallyIntegrableOn _
    simp only [Pi.smul_apply, zero_sub, norm_neg, smul_eq_mul]
    rw [Real.norm_of_nonneg (by positivity)]
    exact (norm_deriv_norm_rpow_smul_self_bounds hα x).1
  have hweak : HasWeakFDerivOn volume Ω (fun x : E => ‖x‖ ^ α • x) D :=
    hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0)
      (continuous_norm_rpow_smul_self hα).continuousOn hlocD fun x hx => hd x hx.2
  rw [(continuous_norm_rpow_smul_self hα).continuousOn.memW1pLoc_iff]
  constructor
  · rintro ⟨Du, hDu, hDuLp⟩
    have hDLp := hDuLp.congr_ae (hDu.ae_eq hweak)
    refine memLpLoc_iff.2 fun K hKΩ hK => ?_
    have h1α : 0 < 1 + α := by linarith
    refine (((memLpLoc_iff.1 hDLp K hKΩ hK).norm.const_mul (1 + α)⁻¹).of_le
      (measurable_norm.pow_const α).aestronglyMeasurable ?_)
    filter_upwards [ae_restrict_of_ae (volume.ae_ne 0)] with x hx0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 h1α.le) (norm_nonneg _)),
      le_inv_mul_iff₀ h1α]
    exact (norm_deriv_norm_rpow_smul_self_bounds hα x).2 hx0
  · intro hLp
    refine ⟨D, hweak, memLpLoc_iff.2 fun K hKΩ hK => ?_⟩
    refine ((memLpLoc_iff.1 hLp K hKΩ hK).const_mul (1 + |α|)).of_le
      hmeasD.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg x) _))]
    exact (norm_deriv_norm_rpow_smul_self_bounds hα x).1

/-- **The unit radial map `x ↦ ‖x‖⁻¹ • x` is in `W^{1,p}_loc` near `0` iff `p < dim E`.**
When `dim E ≥ 2` and `0 ∈ Ω`, the coordinate weak derivatives exist across `0` and have size
`O(‖x‖⁻¹)`, while their divergence equals `(dim E - 1) ‖x‖⁻¹`. -/
theorem memW1pLoc_unitRadial_iff (hd : 1 < Module.finrank ℝ E) (h0 : (0 : E) ∈ Ω) :
    MemW1pLoc p Ω (fun x : E => ‖x‖⁻¹ • x) ↔ p < Module.finrank ℝ E := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hd)
  let b := stdOrthonormalBasis ℝ E
  let D : Fin (Module.finrank ℝ E) → E → E →L[ℝ] ℝ := fun i x =>
    ‖x‖ ^ (-1 : ℝ) • innerSL ℝ (b i) - (‖x‖ ^ (-3 : ℝ) * ⟪x, b i⟫) • innerSL ℝ x
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      (fun x : E => b.toBasis.repr (‖x‖⁻¹ • x) i) = fun x => ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫ := by
    funext x
    rw [OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply, real_inner_smul_right,
      real_inner_comm, Real.rpow_neg_one]
  rw [b.toBasis.memW1pLoc_iff, ← memLpLoc_norm_inv_iff_of_mem_nhds (Ω.isOpen.mem_nhds h0)]
  constructor
  · intro h
    have hDi : ∀ i, MemLpLoc p Ω (D i) := fun i => by
      have hi : MemW1pLoc p Ω (fun x : E => ‖x‖ ^ (-1 : ℝ) * ⟪x, b i⟫) := hcoord i ▸ h i
      exact hi.memLpLoc_of_hasWeakFDerivOn (hasWeakFDerivOn_norm_rpow_neg_one_mul_inner hd (b i) Ω)
    have hdiv : MemLpLoc p Ω (fun x : E => ∑ i, D i x (b i)) :=
      MemLpLoc.sum Finset.univ fun i _ =>
        (hDi i).clm_comp (ContinuousLinearMap.apply ℝ ℝ (b i))
    have hd1 : ((Module.finrank ℝ E : ℝ) - 1) ≠ 0 := by
      linarith [show (1 : ℝ) < Module.finrank ℝ E from Nat.one_lt_cast.2 hd]
    exact (hdiv.const_smul ((Module.finrank ℝ E : ℝ) - 1)⁻¹).congr fun x _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (∑ i, D i x (b i)) = ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖⁻¹ from
        sum_unitRadialCoordDeriv_apply_self x, inv_mul_cancel_left₀ hd1]
  · intro hinv i
    rw [hcoord i]
    refine memW1pLoc_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, D i,
      hasWeakFDerivOn_norm_rpow_neg_one_mul_inner hd (b i) Ω, memLpLoc_iff.2 fun K hKΩ hK => ?_⟩
    · have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
      exact MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable ‖b i‖
        (Eventually.of_forall fun x => abs_norm_rpow_neg_one_mul_inner_le (b i) x)
    · refine ((memLpLoc_iff.1 hinv K hKΩ hK).const_mul (2 * ‖b i‖)).of_le
        (by fun_prop : Measurable _).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
      exact norm_norm_rpow_neg_one_smul_innerSL_sub_le (b i) x

end EuclideanInnerProduct

/-- On the complex plane, `z ↦ z / ‖z‖` lies in `MemW1pLoc p Ω` near `0` if and only if `p < 2`. -/
theorem memW1pLoc_div_norm_iff {Ω : Opens ℂ} (h0 : (0 : ℂ) ∈ Ω) :
    MemW1pLoc p Ω (fun z : ℂ => z / ‖z‖) ↔ p < 2 := by
  have heq : (fun z : ℂ => z / ‖z‖) = fun z : ℂ => ‖z‖⁻¹ • z := by
    funext z; simp [div_eq_inv_mul, Complex.real_smul]
  rw [heq]
  simpa [Complex.finrank_real_complex] using
    memW1pLoc_unitRadial_iff (E := ℂ) (p := p) (by simp [Complex.finrank_real_complex]) h0

end TauCeti
