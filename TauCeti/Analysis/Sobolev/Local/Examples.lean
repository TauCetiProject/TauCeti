/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Reflection
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.FirstOrder.Examples
import TauCeti.Analysis.Sobolev.Local.Haar
import TauCeti.Analysis.Sobolev.Local.Holomorphic
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.Local.W1p
import TauCeti.Analysis.Sobolev.WeakDeriv.Hyperplane
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Function.MemLpLoc.NormInv
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Membership and non-membership examples for local Sobolev classes

This file tests `TauCeti.MemWkpLoc` across finite-dimensional real normed domains `E` (including
`ℂ`, non-inner-product norms, and arbitrary additive Haar measures) and Banach codomains `F`.

* **Identity, affine maps, and norm:** on any finite-dimensional real normed space `E` with an
  additive Haar measure `μ`, the identity (`TauCeti.memWkpLoc_id`) and affine maps
  (`ContinuousLinearMap.memWkpLoc_affine`) belong to every local Sobolev class, although `id` is
  not globally `Lᵖ` on a nontrivial space for `p ≠ 0` (`TauCeti.not_memLp_id`). The norm
  `x ↦ ‖x‖` is in every local `W^{1,p}` class as a Lipschitz map (`TauCeti.memWkpLoc_one_norm`),
  with weak derivative bounded in operator norm by `1` almost everywhere
  (`TauCeti.ae_norm_le_one_of_hasWeakFDerivOn_norm`).
* **Haar scaling and non-inner-product model norm (`ℝ × ℝ` vs `EuclideanSpace ℝ (Fin 2)`):**
  `example` checks confirm scaling invariance under `(2 : ℝ≥0∞) • μ` for `MemLpLoc` and
  `MemWkpLoc`. The equivalence `TauCeti.prodEquivEuclideanSpaceFin2` carries `MemLpLoc` and
  `MemWkpLoc` between `ℝ × ℝ` (with the supremum norm `max |x₁| |x₂|`) and
  `EuclideanSpace ℝ (Fin 2)` (`TauCeti.memLpLoc_prod_iff_euclideanSpaceFin2`,
  `TauCeti.memWkpLoc_prod_iff_euclideanSpaceFin2`), while their norm derivatives differ at
  `(1, 1/2)` in direction `(0, 1)`.
* **Infinite-dimensional Banach targets without a basis and strong measurability counterexample:**
  `example` checks verify `x ↦ a x • v` via `MemWkpLoc.smul_const` and
  `HasWeakFDerivOn.smul_const`. Composing `t ↦ lp.single 2 t 1` with any continuous linear
  functional on `ℓ²(ℝ)` gives a map in `MemWkpLoc p U k` (`StrongDual.memWkpLoc_comp_lpSingle`),
  while `t ↦ lp.single 2 t 1` itself lies in no `MemWkpLoc p U k` when `interior U` is nonempty
  (`TauCeti.not_memWkpLoc_lpSingle`).
* **Unit radial field and radial power maps:** on a real inner product space `E` of dimension at
  least `2`, `x ↦ ‖x‖⁻¹ • x` belongs to `MemWkpLoc p U 1 μ` near `0` exactly when
  `p < Module.finrank ℝ E` (`TauCeti.memWkpLoc_one_unitRadial_iff`). For `α > -1`,
  `x ↦ ‖x‖ ^ α • x` lies in `MemWkpLoc p U 1 μ` whenever `x ↦ ‖x‖ ^ α` lies in `MemLpLoc p U μ`
  (`TauCeti.memWkpLoc_one_norm_rpow_smul_id`).
* **Polynomials:** polynomials are in every local Sobolev class on every set in `ℂ`, as holomorphic
  maps (`Differentiable.memWkpLoc`).
* **The norm `z ↦ ‖z‖` at order two:** `z ↦ ‖z‖` is in the local class `W^{2,p}` on `ℂ` exactly
  when `p < 2` on every set whose interior contains the origin (`TauCeti.memWkpLoc_two_norm_iff`).
* **Half-space indicators:** for nonzero `ℓ : E →L[ℝ] ℝ`, the indicator of `{x | 0 < ℓ x}` lies in
  every local `Lᵖ` class (`StrongDual.memLpLoc_indicator_pos`) but in no local `W^{k,p}` class of
  positive order when `interior U` meets `ker ℓ` (`TauCeti.not_memWkpLoc_indicator_clm_pos`,
  `TauCeti.not_memWkpLoc_indicator_re_pos`).
* **The rotation `z ↦ i z` on half-discs:** the indicator of `{z | 0 < z.im}` is in every local
  Sobolev class on `ball 0 1 ∩ {z | 0 ≤ z.im}`, while its composition with `z ↦ i z` is not.
* **Square-root profile on the half-disc:** `z ↦ √z.im` is in `W^{1,p}` on the closed upper
  half-disc exactly when `p < 2`, while on the open half-disc it is in `W^{1,p}` for all `p`.
* **Logarithmic fundamental solution:** `Re z / ‖z‖²`, `Im z / ‖z‖²`, and `log ‖z‖` are locally
  `Lᵖ` / `W^{1,p}` near the origin in `ℂ` exactly when `p < 2`.
* **Reflections:** the even reflection does not extend `Im z` from the upper half-disc to a local
  `W^{2,p}` map, while the order-two reflection gives `Im z` back.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2, pp. 2–3.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set ℂ}

/-! ### The identity and the norm -/

section IdentityAndNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {q : ENNReal} {S : Set E} {k : ℕ}

/-- The identity map on any finite-dimensional real normed space lies in `MemWkpLoc q S k` for
every exponent `q`, order `k`, and additive Haar measure `μ`, although for `q ≠ 0` on a
nontrivial space it is not in global `L^q`: the local class imposes no bound at infinity. -/
theorem memWkpLoc_id (q : ENNReal) (S : Set E) (k : ℕ) : MemWkpLoc q S k (id : E → E) μ :=
  (contDiff_id.contDiffOn : ContDiffOn ℝ k id ((⊤ : Opens E) : Set E)).memWkpLoc (subset_univ S)

example [Nontrivial E] (hq : q ≠ 0) : ¬ MemLp (id : E → E) q μ :=
  not_memLp_id hq

/-- On any finite-dimensional real normed space `E`, the norm `x ↦ ‖x‖` is Lipschitz and therefore
lies in `MemWkpLoc q S 1` for every exponent `q` and additive Haar measure `μ`. -/
theorem memWkpLoc_one_norm : MemWkpLoc q S 1 (fun x : E => ‖x‖) μ :=
  lipschitzWith_one_norm.memWkpLoc_one

example {Ω : Opens E} {D : E → E →L[ℝ] ℝ} (hD : HasWeakFDerivOn μ Ω (fun x : E => ‖x‖) D) :
    ∀ᵐ x ∂μ.restrict Ω, ‖D x‖ ≤ 1 :=
  ae_norm_le_one_of_hasWeakFDerivOn_norm hD

end IdentityAndNorm

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
    hasWeakFDerivOn_norm_rpow_mul_inner (by norm_num [Complex.finrank_real_complex]) e _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K _ hK => ?_)⟩
  · have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable ‖e‖
      (Eventually.of_forall fun z => by simpa using abs_norm_rpow_mul_inner_le (-1) e z)
  · have hker : MemLp (fun z : ℂ => ‖z‖⁻¹) p (volume.restrict K) :=
      hK.isBounded.memLp_norm_inv_restrict (by simpa [Complex.finrank_real_complex] using hp)
    refine (hker.const_mul ((1 + |(-1 : ℝ)|) * ‖e‖)).of_le
      (by fun_prop : Measurable _).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
    exact norm_norm_rpow_smul_innerSL_add_le (-1) e z

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

/-! ### A jump across a hyperplane or line -/

/-- The indicator of the open half-space `{x : E | 0 < ℓ x}` for a nonzero `ℓ : E →L[ℝ] ℝ` lies in
no positive-order local Sobolev class `MemWkpLoc q S (k + 1) μ` whenever `interior S` meets
`ker ℓ`. -/
theorem not_memWkpLoc_indicator_clm_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {q : ENNReal} {S : Set E} {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {k : ℕ}
    {x₀ : E} (hx₀ : x₀ ∈ interior S) (hker : ℓ x₀ = 0) :
    ¬ MemWkpLoc q S (k + 1) ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) μ := by
  intro h
  obtain ⟨D, hD, -⟩ := h.exists_weakFDeriv
  exact not_hasWeakFDerivOn_indicator_pos hℓ hx₀ hker D hD

/-- The indicator of the right half-plane is in no local Sobolev class of positive order on a
set whose interior meets the imaginary axis, although it is locally `Lᵖ` there
(`StrongDual.memLpLoc_indicator_pos`). -/
theorem not_memWkpLoc_indicator_re_pos {k : ℕ} {z₀ : ℂ} (hz₀ : z₀ ∈ interior U)
    (hre : z₀.re = 0) :
    ¬ MemWkpLoc p U (k + 1) ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) :=
  not_memWkpLoc_indicator_clm_pos (ℓ := Complex.reCLM) (fun h0 =>
    (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using congrArg (fun f : StrongDual ℝ ℂ => f 1) h0))
    hz₀ hre

/-! ### The rotation `z ↦ i z` on the half-disc -/

/-- The indicator of the open upper half-plane is in every local Sobolev class on the closed upper
half-disc `ball 0 1 ∩ {z | 0 ≤ z.im}`: there it agrees with `1` off the real axis. -/
theorem memWkpLoc_ball_inter_setOf_im_nonneg_indicator_im_pos (k : ℕ) :
    MemWkpLoc p (ball 0 1 ∩ {z : ℂ | 0 ≤ z.im}) k
      ({z : ℂ | 0 < z.im}.indicator fun _ => (1 : ℝ)) := by
  have h : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 ≤ z.im}), 0 < z.im := by
    rw [Measure.restrict_congr_set (Complex.setOf_le_im_ae_eq 0)]
    exact ae_restrict_mem (measurableSet_lt measurable_const Complex.measurable_im)
  refine (memWkpLoc_const (1 : ℝ)).congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right h] with z hz
  simp [Set.indicator, hz]

/-- **The rotation `z ↦ i z` does not preserve the half-disc classes.** The indicator of the open
upper half-plane is in every local Sobolev class on the closed upper half-disc
(`TauCeti.memWkpLoc_ball_inter_setOf_im_nonneg_indicator_im_pos`), but its composition with
`z ↦ i z` is the indicator of the right half-plane, which is in no class of positive order there:
the interior of the half-disc meets the imaginary axis at `i / 2`. -/
theorem not_memWkpLoc_ball_inter_setOf_im_nonneg_indicator_im_pos_comp_I_mul (k : ℕ) :
    ¬ MemWkpLoc p (ball 0 1 ∩ {z : ℂ | 0 ≤ z.im}) (k + 1)
      (fun z => {z : ℂ | 0 < z.im}.indicator (fun _ => (1 : ℝ)) (Complex.I * z)) := by
  have hfun : (fun z => {z : ℂ | 0 < z.im}.indicator (fun _ => (1 : ℝ)) (Complex.I * z)) =
      {z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ) := by
    funext z
    simp [Set.indicator]
  have hz₀ : Complex.I / 2 ∈ interior (ball (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im}) := by
    rw [interior_inter, isOpen_ball.interior_eq, Complex.interior_setOfPred_le_im]
    exact ⟨by norm_num [Complex.norm_div], by simp⟩
  rw [hfun]
  exact not_memWkpLoc_indicator_re_pos hz₀ (by simp)

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
      filter_upwards [hae, Complex.ae_im_ne_zero]
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

/-- Planar specialization of `TauCeti.memLpLoc_norm_inv_iff_lt_finrank`: `‖z‖⁻¹` is locally `Lᵖ`
near the origin in `ℂ` if and only if `p < 2`. -/
private theorem memLpLoc_norm_inv_iff (hU : U ∈ 𝓝 0) :
    MemLpLoc p U (fun z : ℂ => ‖z‖⁻¹) ↔ p < 2 := by
  simpa [Complex.finrank_real_complex] using memLpLoc_norm_inv_iff_lt_finrank (p := p) hU

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

/-! ### Haar scaling check -/

section HaarScaling

example {α G : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [NormedAddCommGroup G] {μ : Measure α} {q : ENNReal} {S : Set α} {f : α → G} :
    MemLpLoc q S f ((2 : ENNReal) • μ) ↔ MemLpLoc q S f μ :=
  memLpLoc_smul_measure_iff (c := 2) two_ne_zero ENNReal.ofNat_ne_top

example {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] {μ : Measure E} {q : ENNReal}
    {S : Set E} {k : ℕ} {f : E → G} :
    MemWkpLoc q S k f ((2 : ENNReal) • μ) ↔ MemWkpLoc q S k f μ :=
  memWkpLoc_smul_measure_iff (c := 2) two_ne_zero ENNReal.ofNat_ne_top

end HaarScaling

/-! ### Non-inner-product model norm: `ℝ × ℝ` vs `EuclideanSpace ℝ (Fin 2)` -/

section NonInnerProductModel

/-- Local `Lᵖ` membership on `ℝ × ℝ` (with the supremum norm and product Lebesgue measure) matches
`EuclideanSpace ℝ (Fin 2)` under `TauCeti.prodEquivEuclideanSpaceFin2`. -/
theorem memLpLoc_prod_iff_euclideanSpaceFin2 {G : Type*} [NormedAddCommGroup G]
    {q : ENNReal} {V : Set (EuclideanSpace ℝ (Fin 2))} {u : EuclideanSpace ℝ (Fin 2) → G} :
    MemLpLoc q (prodEquivEuclideanSpaceFin2 ⁻¹' V) (u ∘ prodEquivEuclideanSpaceFin2) volume ↔
      MemLpLoc q V u volume := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact prodEquivEuclideanSpaceFin2.memLpLoc_comp_right_iff volume volume

/-- Local Sobolev membership on `ℝ × ℝ` (with the supremum norm and product Lebesgue measure)
matches `EuclideanSpace ℝ (Fin 2)` under `TauCeti.prodEquivEuclideanSpaceFin2`. -/
theorem memWkpLoc_prod_iff_euclideanSpaceFin2 {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {q : ENNReal} {V : Set (EuclideanSpace ℝ (Fin 2))} {k : ℕ}
    {u : EuclideanSpace ℝ (Fin 2) → G} :
    MemWkpLoc q (prodEquivEuclideanSpaceFin2 ⁻¹' V) k (u ∘ prodEquivEuclideanSpaceFin2) volume ↔
      MemWkpLoc q V k u volume := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact prodEquivEuclideanSpaceFin2.memWkpLoc_comp_preimage_iff

-- At `(1, 1/2)`, the derivative of the supremum norm on `ℝ × ℝ` in direction `(0, 1)` vanishes,
-- whereas the Euclidean gradient does not.
example : fderiv ℝ (fun y : ℝ × ℝ => ‖y‖) (1, (1 / 2 : ℝ)) (0, 1) = 0 := by
  have h := hasFDerivAt_norm_prod_of_abs_snd_lt_abs_fst (y := (1, (1 / 2 : ℝ))) (by norm_num)
  rw [h.fderiv]
  simp

example :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖)
      (prodEquivEuclideanSpaceFin2 (1, (1 / 2 : ℝ)))
      (prodEquivEuclideanSpaceFin2 (0, 1)) ≠ 0 := by
  set x : EuclideanSpace ℝ (Fin 2) := prodEquivEuclideanSpaceFin2 (1, (1 / 2 : ℝ))
  set v : EuclideanSpace ℝ (Fin 2) := prodEquivEuclideanSpaceFin2 (0, 1)
  have hx : x ≠ 0 := by
    intro h
    have h0 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h
    norm_num [x] at h0
  have hd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x :=
    hasFDerivAt_norm_of_ne hx
  rw [hd.fderiv, smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hinner : ⟪x, v⟫ = (1 / 2 : ℝ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Fin.sum_univ_two, x, v, dotProduct]
  rw [hinner]
  exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hx)) (by norm_num)

end NonInnerProductModel

/-! ### Infinite-dimensional Banach targets without a basis -/

section BanachTarget

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure E} {q : ENNReal} {S : Set E}

-- Banach-valued scalar products `x ↦ a x • v` need no basis, separability, or inner product on `G`.
example {a : E → ℝ} (ha : MemWkpLoc q S 1 a μ) (v : G) :
    MemWkpLoc q S 1 (fun x => a x • v) μ :=
  ha.smul_const v

example {Ω : Opens E} {a : E → ℝ} {Da : E → E →L[ℝ] ℝ}
    (hDa : HasWeakFDerivOn μ Ω a Da) (v : G) :
    HasWeakFDerivOn μ Ω (fun x => a x • v) (fun x => (Da x).smulRight v) :=
  hDa.smul_const v

-- Specialization to the infinite-dimensional Hilbert space `ℓ²(ℕ, ℝ)`.
example {a : E → ℝ} {Da : E → E →L[ℝ] ℝ} (ha : MemWkpLoc q S 1 a μ)
    (hDa : HasWeakFDerivOn μ (Opens.interior S) a Da) (v : lp (fun _ : ℕ => ℝ) 2) :
    MemWkpLoc q S 1 (fun x => a x • v) μ ∧
      HasWeakFDerivOn μ (Opens.interior S) (fun x => a x • v)
        (fun x => (Da x).smulRight v) :=
  ⟨ha.smul_const v, hDa.smul_const v⟩

end BanachTarget

/-! ### Strong measurability counterexample: weakly zero a.e., not locally `Lᵖ` -/

section WeaklyZeroCounterexample

/-- Every continuous scalar composition of `t ↦ lp.single 2 t 1` lies in `MemWkpLoc q S k` for
every exponent `q`, set `S`, and order `k`. -/
theorem _root_.StrongDual.memWkpLoc_comp_lpSingle
    (ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) 2)) (q : ENNReal) (S : Set ℝ) (k : ℕ) :
    MemWkpLoc q S k (fun t : ℝ => ℓ (lp.single 2 t (1 : ℝ))) volume :=
  (memWkpLoc_zero_fun (μ := volume)).congr_ae
    (ae_restrict_of_ae ℓ.comp_lpSingle_ae_eq_zero.symm)

/-- `t ↦ lp.single 2 t 1` lies in no `MemWkpLoc q S k` for every exponent `q` (even `q = 0`) on
any set `S ⊆ ℝ` with nonempty interior: weak scalar membership does not imply strong
measurability. -/
theorem not_memWkpLoc_lpSingle (q : ENNReal) {S : Set ℝ} (k : ℕ) (hS : (interior S).Nonempty) :
    ¬ MemWkpLoc q S k (fun t : ℝ => lp.single 2 t (1 : ℝ)) volume :=
  fun h => not_memLpLoc_lpSingle q hS h.memLpLoc

end WeaklyZeroCounterexample

/-! ### The inverse norm `x ↦ ‖x‖⁻¹` on general finite-dimensional spaces -/

section InverseNorm

-- In dimension `3`, `x ↦ ‖x‖⁻¹` belongs to `MemLpLoc q S volume` near `0` iff `q < 3`.
example {q : ENNReal} {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : S ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 3))) :
    MemLpLoc q S (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) volume ↔ q < 3 := by
  simpa [finrank_euclideanSpace_fin] using memLpLoc_norm_inv_iff_lt_finrank (μ := volume) hS

end InverseNorm

/-! ### Unit radial field `x ↦ ‖x‖⁻¹ • x` on inner product spaces of dimension `≥ 2` -/

section UnitRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {q : ENNReal} {S : Set E}

/-- On a real inner product space `E` of dimension at least `2`, the unit radial field
`x ↦ ‖x‖⁻¹ • x` belongs to `MemWkpLoc q S 1 μ` for every `q < Module.finrank ℝ E`. -/
theorem memWkpLoc_one_unitRadial (hd : 1 < Module.finrank ℝ E) (hq : q < Module.finrank ℝ E) :
    MemWkpLoc q S 1 (fun x : E => ‖x‖⁻¹ • x) μ := by
  have hd2 : 2 ≤ Module.finrank ℝ E := hd
  have h1 := memWkpLoc_one_iff_memW1pLoc.2
    ((memW1pLoc_norm_inv_smul_iff (μ := μ) (Ω := (⊤ : Opens E)) hd2 trivial).2 hq)
  exact h1.mono (subset_univ S)

/-- On a real inner product space `E` of dimension at least `2`, the unit radial field
`x ↦ ‖x‖⁻¹ • x` does not belong to `MemWkpLoc q S 1 μ` when `Module.finrank ℝ E ≤ q` and
`(0 : E) ∈ interior S`. -/
theorem not_memWkpLoc_one_unitRadial (hd : 1 < Module.finrank ℝ E)
    (hq : Module.finrank ℝ E ≤ q) (h0 : (0 : E) ∈ interior S) :
    ¬ MemWkpLoc q S 1 (fun x : E => ‖x‖⁻¹ • x) μ := by
  intro h
  have hd2 : 2 ≤ Module.finrank ℝ E := hd
  have h1 : MemW1pLoc q (Opens.interior S) (fun x : E => ‖x‖⁻¹ • x) μ :=
    memWkpLoc_one_iff_memW1pLoc.1 (h.mono interior_subset)
  exact not_lt.2 hq ((memW1pLoc_norm_inv_smul_iff hd2 h0).1 h1)

/-- On a real inner product space `E` of dimension at least `2`, the unit radial field
`x ↦ ‖x‖⁻¹ • x` belongs to `MemWkpLoc q S 1 μ` on any set whose interior contains `0` exactly when
`q < Module.finrank ℝ E`. -/
theorem memWkpLoc_one_unitRadial_iff (hd : 1 < Module.finrank ℝ E) (h0 : (0 : E) ∈ interior S) :
    MemWkpLoc q S 1 (fun x : E => ‖x‖⁻¹ • x) μ ↔ q < Module.finrank ℝ E :=
  ⟨fun h => not_le.1 fun hq => not_memWkpLoc_one_unitRadial hd hq h0 h,
    memWkpLoc_one_unitRadial hd⟩

end UnitRadial

/-! ### Radial power maps `x ↦ ‖x‖ ^ α • x` for `α > -1` -/

section RadialPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {q : ENNReal} {S : Set E}

/-- For `α > -1`, the radial power map `x ↦ ‖x‖ ^ α • x` lies in `MemWkpLoc q S 1 μ` whenever
`x ↦ ‖x‖ ^ α` belongs to `MemLpLoc q S μ`. -/
theorem memWkpLoc_one_norm_rpow_smul_id {α : ℝ} (hα : -1 < α)
    (hp : MemLpLoc q S (fun x : E => ‖x‖ ^ α) μ) :
    MemWkpLoc q S 1 (fun x : E => ‖x‖ ^ α • x) μ := by
  refine memWkpLoc_succ_iff.2 ⟨(continuous_norm_rpow_smul_self hα).continuousOn.memLpLoc, _,
    hasWeakFDerivOn_norm_rpow_smul_self hα _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKS hK => ?_)⟩
  have hbase : MemLp (fun x : E => ‖x‖ ^ α) q (μ.restrict K) := memLpLoc_iff.1 hp K hKS hK
  refine (hbase.const_mul (1 + |α|)).of_le
    ((hasWeakFDerivOn_norm_rpow_smul_self (μ := μ) hα
      (⊤ : Opens E)).locallyIntegrableOn_deriv.mono_set (subset_univ K)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg x) _))]
  exact norm_rpow_smul_id_add_smulRight_le α x

end RadialPower

end TauCeti
