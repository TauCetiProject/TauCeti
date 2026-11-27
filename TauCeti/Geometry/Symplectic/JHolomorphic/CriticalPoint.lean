/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.ContDiffStructure
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak
import TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Complex.CauchyRiemann.RealBoundary.VariableStructure
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex

/-!
# Isolated critical points of J-holomorphic curves

Let `E` be a finite-dimensional real normed space and `u : ℂ → E` a map of class `C¹` on an open
set `Ω ⊆ ℂ` solving the Cauchy–Riemann equation

`∂ₜu = A(z) ∂ₛu`

on `Ω`, in the coordinate `z = s + i t`, for a `C¹` field `A : ℂ → E →L[ℝ] E` of complex
structures, `A(z)² = -1`. The main case is `A = J ∘ u` for an almost complex structure `J` on `E`
of class `C¹`, which makes `u` a `J`-holomorphic curve in local coordinates; a structure that also
depends on the domain point, such as `A(z) = J(z, u(z))`, is covered as well. This file shows that
the critical points of `u`, the points where its differential vanishes, behave like the zeros of
the derivative of a holomorphic function (McDuff–Salamon, Lemma 2.4.1, the part about critical
points):

* **unique continuation**: if `Ω` is connected and the differential of `u` vanishes near one point
  of `Ω`, or to infinite order at one point, then `u` is constant on `Ω`
  (`TauCeti.eqOn_const_of_cauchyRiemann_of_eventually_fderiv_eq_zero`,
  `TauCeti.eqOn_const_of_cauchyRiemann_of_forall_fderiv_isBigO`);
* **isolated critical points**: otherwise the critical points of `u` form a discrete subset of
  `Ω` (`TauCeti.setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann`), so finitely many of
  them lie in each compact subset of `Ω`
  (`TauCeti.finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann`);
* **order of a critical point**: at each critical point `z₀` the differential vanishes to a finite
  positive order `m`, `‖du_z‖ ≍ ‖z - z₀‖ ^ m` near `z₀`
  (`TauCeti.exists_isTheta_pow_fderiv_of_cauchyRiemann`).

The theorems with the suffix `_comp` state the two main results for `A = J ∘ u`, assuming `J` of
class `C¹` near the image of `u` and `J² = -1` along it. Combined with the finiteness of the fibres
of `u` on compact sets (`TauCeti.finite_inter_preimage_singleton_of_cauchyRiemann`), they give the
last assertion of McDuff–Salamon, Lemma 2.4.1: for compact subsets `K` and `K'` of `Ω`, only
finitely many points of `K` lie over the values of `u` at its critical points in `K'`, so a
nonconstant curve on a compact domain has finite `u⁻¹(u(Crit u))`
(`TauCeti.finite_inter_preimage_image_inter_setOf_fderiv_eq_zero_of_cauchyRiemann_comp`).

The argument applies the similarity principle to the differentiated equation. Since
`∂ₜu = A ∂ₛu` and `A² = -1`, the differential of `u` vanishes exactly where `∂ₛu` does
(`ContinuousLinearMap.eq_zero_iff_apply_one_eq_zero_of_apply_I_eq`), and exactly where
`ξ = ∂ₜu` does. A `C¹` solution is in `W^{2,p}_loc` for every finite `p`
(`TauCeti.memWkpLoc_two_of_contDiffOn_of_cauchyRiemann`), and differentiating the equation
`∂ₛu + A ∂ₜu = 0` in `t` shows that `ξ` is a weak solution of the linear Cauchy–Riemann equation

`∂ₛξ + A ∂ₜξ + (∂ₜA) ξ = 0`

with the continuous coefficient `∂ₜA`
(`TauCeti.isWeakLinearCauchyRiemannOn_fderiv_I_of_contDiffOn_of_cauchyRiemann`). Its structure
`A` genuinely varies, so the weak variable-structure unique continuation theorems of
`TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak` apply to `ξ`.

For a `C²` solution the same holds classically for `ξ = ∂ₛu`: differentiating the equation in `s`
and using the symmetry of the second derivative gives `∂ₜξ = (∂ₛA) ξ + A ∂ₛξ`, and applying `A`
turns this into the linear Cauchy–Riemann equation

`∂ₛξ + A ∂ₜξ - A (∂ₛA) ξ = 0`

with the continuous coefficient `-A ∘ ∂ₛA` (`TauCeti.cauchyRiemann_fderiv_one`; the same
computation for the equation `∂ₛu + A ∂ₜu = 0` on `ℝ × ℝ` is
`TauCeti.cauchyRiemann_fderiv_apply_eq_neg`). The order of a critical point
(`TauCeti.exists_isTheta_pow_fderiv_of_cauchyRiemann`) is proved from this classical equation, by
the `C¹` theorems of `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure`,
and still assumes `u` of class `C²`.

**Totally real boundary values.** Isolated critical points and unique continuation also hold up to
the boundary of a half-disc with totally real boundary values, the local model of a
pseudoholomorphic strip or disc with boundary on a totally real submanifold: `u` of class `C²` up
to the real axis on the closed upper part `Ω ∩ {0 ≤ im}` of an open set, solving `∂ₜu = A ∂ₛu`
off the axis, and a real-linear automorphism `R` of `E` which fixes the boundary values `u(s)` and
anticommutes with `A(s)` on `Ω ∩ ℝ`. In coordinates where the totally real submanifold is
`ℝⁿ ⊆ ℂⁿ` and the almost complex structure is `i` along it, `R` is complex conjugation. The
critical points are the zeros of the derivative of `u` within the closed upper half-plane. Since
the boundary values are fixed by `R`, so is their derivative `ξ = ∂ₛu` on the axis, and `ξ` is a
weak solution of the linearized equation up to the axis. The similarity principle for a variable
structure up to a totally real boundary
(`TauCeti.Analysis.Complex.CauchyRiemann.RealBoundary.VariableStructure`), proved by reflection
across the axis, then shows that the critical points of a nonconstant `u` are isolated in
`Ω ∩ {0 ≤ im}`, also at the points of the axis
(`TauCeti.setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg`).

## Main results

* `TauCeti.cauchyRiemann_fderiv_one`: `∂ₛu` solves the linearized Cauchy–Riemann equation.
* `TauCeti.eqOn_const_of_cauchyRiemann_of_eventually_fderiv_eq_zero`: a solution whose
  differential vanishes near one point of a connected domain is constant on the domain.
* `TauCeti.eqOn_const_of_cauchyRiemann_of_forall_fderiv_isBigO`: a solution whose differential
  vanishes to infinite order at one point of a connected domain is constant on the domain.
* `TauCeti.setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann`: the critical points of a
  nonconstant solution on a connected domain are isolated.
* `TauCeti.finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann`: a nonconstant solution on a
  connected domain has finitely many critical points in each compact subset.
* `TauCeti.exists_isTheta_pow_fderiv_of_cauchyRiemann`: the differential vanishes to a finite
  positive order at each critical point of a nonconstant solution.
* `TauCeti.finite_inter_preimage_image_inter_setOf_fderiv_eq_zero_of_cauchyRiemann_comp`: for
  compact `K, K' ⊆ Ω`, a nonconstant J-holomorphic curve has finitely many points of `K` over the
  values of `u` at its critical points in `K'`.
* `TauCeti.setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg` and
  `TauCeti.finite_inter_setOf_fderivWithin_eq_zero_of_cauchyRiemann_inter_im_nonneg`: the critical
  points of a nonconstant solution with totally real boundary values are isolated in
  `Ω ∩ {0 ≤ im}`, and finitely many lie in each of its compact subsets, also near the real axis;
  the theorems with the suffix `_comp` state them for `A = J ∘ u`.
* `TauCeti.eqOn_const_of_cauchyRiemann_inter_im_nonneg_of_forall_fderivWithin_isBigO` and
  `TauCeti.eqOn_const_of_cauchyRiemann_inter_im_nonneg_of_eventually_fderivWithin_eq_zero`: a
  solution with totally real boundary values whose differential vanishes to infinite order, or
  near one point, possibly on the real axis, is constant.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemma 2.4.1 and its proof via the similarity principle, Theorem 2.3.5, with the reflection
  across a totally real boundary of Appendix B.4.
-/

public section

open Asymptotics Complex Filter MeasureTheory Set Topology TopologicalSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : ℂ → E →L[ℝ] E} {u : ℂ → E} {Ω : Set ℂ} {z₀ : ℂ}

/-! ### The differentiated equation -/

/-- **The linearized equation of a Cauchy–Riemann solution.** Let `u` be of class `C²` on an open
set `Ω` and solve `∂ₜu = A ∂ₛu` there, for a differentiable field `A` of endomorphisms. At a
point `z ∈ Ω` where `A(z)² = -1`, the map `ξ = ∂ₛu` solves the linear Cauchy–Riemann equation
`∂ₛξ + A ∂ₜξ - A (∂ₛA) ξ = 0`. -/
theorem cauchyRiemann_fderiv_one (hΩ : IsOpen Ω) (hA : DifferentiableOn ℝ A Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) {z : ℂ}
    (hz : z ∈ Ω) (hAA : A z ∘L A z = -ContinuousLinearMap.id ℝ E) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y 1) z 1 + A z (fderiv ℝ (fun y ↦ fderiv ℝ u y 1) z I) +
      (-(A z ∘L fderiv ℝ A z 1)) (fderiv ℝ u z 1) = 0 := by
  have hzΩ : Ω ∈ 𝓝 z := hΩ.mem_nhds hz
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    ((hu.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).differentiableOn one_ne_zero).differentiableAt
      hzΩ
  have hAz : DifferentiableAt ℝ A z := hA.differentiableAt hzΩ
  have hξ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y 1) z :=
    hDu.clm_apply (differentiableAt_const _)
  -- differentiate `∂ₜu = A ∂ₛu` in the direction `1`
  have h := congrArg (fun L : ℂ →L[ℝ] E ↦ L 1)
    (EventuallyEq.fderiv_eq (𝕜 := ℝ) (Filter.mem_of_superset hzΩ fun y hy ↦ hCR y hy))
  simp only [fderiv_clm_apply hAz hξ, fderiv_clm_apply_const_apply hDu, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at h ⊢
  -- by the symmetry of the second derivative, the left side is `∂ₜξ`
  rw [(hu.contDiffAt hzΩ).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) 1 I]
    at h
  have hAA' (v : E) : A z (A z v) = -v := congr($hAA v)
  rw [h, map_add, hAA', neg_apply, ContinuousLinearMap.comp_apply]
  abel

/-! ### The zero structure of `∂ₛu` -/

/-- A solution with `∂ₛu ≡ 0` on a connected open set is constant there. -/
private theorem eqOn_const_of_cauchyRiemann_of_eqOn_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hu : DifferentiableOn ℝ u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (h₀ : EqOn (fun z ↦ fderiv ℝ u z 1) 0 Ω) (hz₀ : z₀ ∈ Ω) : EqOn u (fun _ ↦ u z₀) Ω :=
  fun _ hz ↦ hΩ.is_const_of_fderiv_eq_zero hΩc hu (fun y hy ↦
    (ContinuousLinearMap.eq_zero_iff_apply_one_eq_zero_of_apply_I_eq (K := ℂ) (hCR y hy)).2
      (h₀ hy)) hz hz₀

/-- A nonconstant solution on a connected open set has a point where `∂ₛu ≠ 0`. -/
private theorem exists_fderiv_one_ne_zero_of_cauchyRiemann (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hu : DifferentiableOn ℝ u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) : ∃ z ∈ Ω, fderiv ℝ u z 1 ≠ 0 := by
  obtain ⟨z, hz, w, hw, hzw⟩ := hne
  by_contra! h
  exact hzw (eqOn_const_of_cauchyRiemann_of_eqOn_zero hΩ hΩc hu hCR (fun y hy ↦ h y hy) hw hz)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The hypotheses of the variable-structure unique continuation theorems for `ξ = ∂ₛu`: `ξ` is
`C¹`, the coefficient `-A ∘ ∂ₛA` is measurable and locally bounded, since it is continuous, and `ξ`
solves the linearized equation. -/
private theorem linearizedCoeff_of_cauchyRiemann (hΩ : IsOpen Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 2 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) :
    ContDiffOn ℝ 1 (fun z ↦ fderiv ℝ u z 1) Ω ∧
      AEStronglyMeasurable (fun z ↦ -(A z ∘L fderiv ℝ A z 1)) (volume.restrict Ω) ∧
      (∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖-(A w ∘L fderiv ℝ A w 1)‖ ≤ M) ∧
      ∀ z ∈ Ω, fderiv ℝ (fun y ↦ fderiv ℝ u y 1) z 1 +
        A z (fderiv ℝ (fun y ↦ fderiv ℝ u y 1) z I) +
        (-(A z ∘L fderiv ℝ A z 1)) (fderiv ℝ u z 1) = 0 := by
  have hC : ContinuousOn (fun z ↦ -(A z ∘L fderiv ℝ A z 1)) Ω :=
    (hA.continuousOn.clm_comp
      ((hA.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const)).neg
  refine ⟨(hu.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).clm_apply contDiffOn_const,
    hC.aestronglyMeasurable hΩ.measurableSet,
    fun z hz ↦ ⟨‖-(A z ∘L fderiv ℝ A z 1)‖ + 1, ?_⟩,
    fun z hz ↦ cauchyRiemann_fderiv_one hΩ (hA.differentiableOn one_ne_zero) hu hCR hz (hAA z hz)⟩
  filter_upwards [(hC.continuousAt (hΩ.mem_nhds hz)).norm.eventually
    (gt_mem_nhds (lt_add_one _))] with w hw using hw.le

/-- The hypotheses of the weak unique continuation theorems for `ξ = ∂ₜu`, at the exponent `3`:
`A ∈ W^{1,3}_loc`, the coefficient `∂ₜA` is locally `L³`, and `ξ` solves the linearized equation
`∂ₛξ + A ∂ₜξ + (∂ₜA) ξ = 0` weakly
(`TauCeti.isWeakLinearCauchyRiemannOn_fderiv_I_of_contDiffOn_of_cauchyRiemann`). -/
private theorem weakLinearized_of_cauchyRiemann (hΩ : IsOpen Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) :
    MemWkpLoc 3 (⟨Ω, hΩ⟩ : Opens ℂ) 1 A ∧ MemLpLoc 3 Ω (fun z ↦ fderiv ℝ A z I) ∧
      IsWeakLinearCauchyRiemannOn 3 Ω A (fun z ↦ fderiv ℝ A z I) (fun z ↦ fderiv ℝ u z I) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  exact ⟨hA.memWkpLoc (Ω := ⟨Ω, hΩ⟩) subset_rfl,
    ((hA.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const).memLpLoc,
    isWeakLinearCauchyRiemannOn_fderiv_I_of_contDiffOn_of_cauchyRiemann (Ω := ⟨Ω, hΩ⟩) hA hAA hu
      hCR ENNReal.ofNat_ne_top⟩

/-- **Unique continuation for critical points.** Let `u` be of class `C¹` on a connected open set
`Ω` and solve the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of complex
structures, `A(z)² = -1`, on a finite-dimensional real normed space. If the differential of `u`
vanishes near one point `z₀ ∈ Ω`, then `u` is constant on `Ω`. -/
theorem eqOn_const_of_cauchyRiemann_of_eventually_fderiv_eq_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ᶠ z in 𝓝 z₀, fderiv ℝ u z = 0) : EqOn u (fun _ ↦ u z₀) Ω := by
  obtain ⟨hAw, hC, hξ⟩ := weakLinearized_of_cauchyRiemann hΩ hA hAA hu hCR
  obtain ⟨t, ht, hto, hz₀t⟩ := eventually_nhds_iff.1 h₀
  have h := eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_eqOn_zero (Ω := ⟨Ω, hΩ⟩) (by norm_num)
    hΩc hAw hA.continuousOn hAA hC hξ (hto.inter hΩ) ⟨z₀, hz₀t, hz₀⟩ inter_subset_right
    fun z hz ↦ by simp [ht z hz.1]
  refine eqOn_const_of_cauchyRiemann_of_eqOn_zero hΩ hΩc (hu.differentiableOn one_ne_zero) hCR
    (fun z hz ↦ (ContinuousLinearMap.apply_I_eq_zero_iff_apply_one_eq_zero_of_apply_I_eq
      (hAA z hz) (hCR z hz)).1 (h hz)) hz₀

/-- **Unique continuation for critical points of infinite order.** Let `u` be of class `C¹` on a
connected open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹`
field `A` of complex structures, `A(z)² = -1`, on a finite-dimensional real normed space. If the
differential of `u` is `O(‖z - z₀‖ⁿ)` at a point `z₀ ∈ Ω` for every `n`, then `u` is constant on
`Ω`. -/
theorem eqOn_const_of_cauchyRiemann_of_forall_fderiv_isBigO (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, (fun z ↦ fderiv ℝ u z) =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn u (fun _ ↦ u z₀) Ω := by
  obtain ⟨hAw, hC, hξ⟩ := weakLinearized_of_cauchyRiemann hΩ hA hAA hu hCR
  have h := eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO (Ω := ⟨Ω, hΩ⟩)
    (by norm_num) hΩc hAw hA.continuousOn hAA hC hξ hz₀
    fun n ↦ ((ContinuousLinearMap.apply ℝ E I).isBigO_comp _ _).trans (h₀ n)
  exact eqOn_const_of_cauchyRiemann_of_eqOn_zero hΩ hΩc (hu.differentiableOn one_ne_zero) hCR
    (fun z hz ↦ (ContinuousLinearMap.apply_I_eq_zero_iff_apply_one_eq_zero_of_apply_I_eq
      (hAA z hz) (hCR z hz)).1 (h hz)) hz₀

/-- **Isolated critical points.** Let `u` be of class `C¹` on a connected open set `Ω` and solve
the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of complex structures,
`A(z)² = -1`, on a finite-dimensional real normed space. If `u` is not constant on `Ω`, its
critical points form a discrete subset of `Ω`. -/
theorem setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) : {z | fderiv ℝ u z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨hAw, hC, hξ⟩ := weakLinearized_of_cauchyRiemann hΩ hA hAA hu hCR
  obtain ⟨z₁, hz₁, h₁⟩ :=
    exists_fderiv_one_ne_zero_of_cauchyRiemann hΩ hΩc (hu.differentiableOn one_ne_zero) hCR hne
  refine Filter.mem_of_superset
    (setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn (Ω := ⟨Ω, hΩ⟩)
      (by norm_num) hΩc hAw hA.continuousOn hAA hC hξ
      ⟨z₁, hz₁, fun h ↦ h₁ ((ContinuousLinearMap.apply_I_eq_zero_iff_apply_one_eq_zero_of_apply_I_eq
        (hAA z₁ hz₁) (hCR z₁ hz₁)).1 h)⟩)
    fun z hz h₀ ↦ ?_
  exact hz (by simp [h₀])

/-- **Finitely many critical points on compact sets.** Let `u` be of class `C¹` on a connected
open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of
complex structures, `A(z)² = -1`, on a finite-dimensional real normed space. If `u` is not
constant on `Ω`, each compact subset of `Ω` contains finitely many critical points of `u`. -/
theorem finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (K ∩ {z | fderiv ℝ u z = 0}).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono hKΩ
    (setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann hΩ hΩc hA hAA hu hCR hne))
  convert h using 1
  ext z
  simp

/-- **The order of a critical point.** Let `u` be of class `C²` on a connected open set `Ω` and
solve the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of complex
structures, `A(z)² = -1`, on a finite-dimensional real normed space. If `u` is not constant on
`Ω`, its differential vanishes to a finite positive order `m` at each critical point `z₀ ∈ Ω`:
`‖du_z‖` is comparable to `‖z - z₀‖ ^ m` near `z₀`. -/
theorem exists_isTheta_pow_fderiv_of_cauchyRiemann (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hA : ContDiffOn ℝ 1 A Ω) (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E)
    (hu : ContDiffOn ℝ 2 u Ω) (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) (hz₀ : z₀ ∈ Ω) (hcrit : fderiv ℝ u z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (fun z ↦ fderiv ℝ u z) =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m := by
  obtain ⟨hξ, hCm, hCb, hL⟩ := linearizedCoeff_of_cauchyRiemann hΩ hA hAA hu hCR
  obtain ⟨m, hm, hθ⟩ := exists_isTheta_pow_of_contDiffOn_of_complexStructure hΩ hΩc hA hAA hξ
    hCm hCb hL
    (exists_fderiv_one_ne_zero_of_cauchyRiemann hΩ hΩc (hu.differentiableOn two_ne_zero) hCR hne)
    hz₀ (by simp [hcrit])
  -- `∂ₛu` controls `du`, since `∂ₜu = A ∂ₛu` with `A` bounded near `z₀`
  have hAc : ContinuousAt A z₀ := hA.continuousOn.continuousAt (hΩ.mem_nhds hz₀)
  have hO : (fun z ↦ fderiv ℝ u z) =O[𝓝 z₀] fun z ↦ fderiv ℝ u z 1 := by
    refine IsBigO.of_bound (1 + (‖A z₀‖ + 1)) ?_
    filter_upwards [hΩ.mem_nhds hz₀, hAc.norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      hAz
    exact ContinuousLinearMap.norm_le_of_apply_I_eq (K := ℂ) _ (hCR z hz) hAz.le le_rfl
  exact ⟨m, hm, IsTheta.trans ⟨hO, (ContinuousLinearMap.apply ℝ E (1 : ℂ)).isBigO_comp _ _⟩ hθ⟩

/-! ### J-holomorphic curves in local coordinates -/

/-- **Isolated critical points of J-holomorphic curves.** Let `u` be of class `C¹` on a connected
open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` there, for a field `J` of
endomorphisms of a finite-dimensional real normed space which is `C¹` near the image of `u` and
satisfies `J(u)² = -1` along it. If `u` is not constant on `Ω`, its critical points form a
discrete subset of `Ω`. -/
theorem setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_comp {J : E → E →L[ℝ] E}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 J (u z))
    (hJJ : ∀ z ∈ Ω, J (u z) ∘L J (u z) = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) : {z | fderiv ℝ u z ≠ 0} ∈ codiscreteWithin Ω :=
  setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann (A := fun z ↦ J (u z)) hΩ hΩc
    (fun z hz ↦ (hJ z hz).comp_contDiffWithinAt z (hu z hz)) hJJ hu hCR hne

/-- **Finitely many critical points of J-holomorphic curves on compact sets.** Let `u` be of class
`C¹` on a connected open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` there,
for a field `J` of endomorphisms of a finite-dimensional real normed space which is `C¹` near the
image of `u` and satisfies `J(u)² = -1` along it. If `u` is not constant on `Ω`, each compact
subset of `Ω` contains finitely many critical points of `u`. -/
theorem finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann_comp {J : E → E →L[ℝ] E}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 J (u z))
    (hJJ : ∀ z ∈ Ω, J (u z) ∘L J (u z) = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (K ∩ {z | fderiv ℝ u z = 0}).Finite :=
  finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann (A := fun z ↦ J (u z)) hΩ hΩc
    (fun z hz ↦ (hJ z hz).comp_contDiffWithinAt z (hu z hz)) hJJ hu hCR hne hK hKΩ

/-! ### Fibres through critical points -/

/-- **Finitely many points over the critical values of a J-holomorphic curve.** Let `u` be of
class `C¹` on a connected open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu`
there, for a field `J` of endomorphisms of a finite-dimensional real normed space which is `C¹`
near the image of `u` and satisfies `J(u)² = -1` along it. If `u` is not constant on `Ω`, then for
compact subsets `K` and `K'` of `Ω`, only finitely many points of `K` are mapped by `u` to the
image of a critical point of `u` lying in `K'`. For `K = K'` this is the finiteness of
`u⁻¹(u(Crit u))` on a compact domain. -/
theorem finite_inter_preimage_image_inter_setOf_fderiv_eq_zero_of_cauchyRiemann_comp
    {J : E → E →L[ℝ] E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 J (u z))
    (hJJ : ∀ z ∈ Ω, J (u z) ∘L J (u z) = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 1 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) {K K' : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hK' : IsCompact K') (hK'Ω : K' ⊆ Ω) :
    (K ∩ u ⁻¹' (u '' (K' ∩ {z | fderiv ℝ u z = 0}))).Finite := by
  -- over each value `u c`, `c ∈ Ω`, there are finitely many points of `K`
  have hfib : ∀ c ∈ Ω, (K ∩ u ⁻¹' {u c}).Finite := by
    intro c hc
    -- one of the two distinct values of `u` differs from `u c`
    have hnec : ∃ z ∈ Ω, u z ≠ u c := by
      obtain ⟨z, hz, w, hw, hzw⟩ := hne
      by_cases hz' : u z = u c
      · exact ⟨w, hw, fun hw' ↦ hzw (hz'.trans hw'.symm)⟩
      · exact ⟨z, hz, hz'⟩
    exact finite_inter_preimage_singleton_of_cauchyRiemann (hJ c hc).exists_lipschitzOnWith
      (hJJ c hc) hΩ hΩc hu hCR hnec hK hKΩ
  -- and there are finitely many critical points in `K'`
  refine ((finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann_comp hΩ hΩc hJ hJJ hu hCR hne hK'
    hK'Ω).biUnion fun c hc ↦ hfib c (hK'Ω hc.1)).subset ?_
  rintro z ⟨hzK, c, hc, hcz⟩
  exact mem_biUnion hc ⟨hzK, hcz.symm⟩

/-! ### Critical points up to a totally real boundary -/

omit [FiniteDimensional ℝ E] in
/-- A map of class `C¹` up to the real axis on `Ω ∩ {0 ≤ im}`, solving `∂ₜu = A ∂ₛu` off the axis,
whose derivative `∂ₛu` within the closed upper half-plane vanishes on a preconnected
`Ω ∩ {0 ≤ im}`, is constant there. -/
private theorem eqOn_const_of_cauchyRiemann_of_eqOn_zero_inter_im_nonneg (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im})) (hu : ContDiffOn ℝ 1 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (h₀ : EqOn (fun z ↦ fderivWithin ℝ u {z | 0 ≤ z.im} z 1) 0 (Ω ∩ {z | 0 ≤ z.im}))
    (hz₀ : z₀ ∈ Ω ∩ {z | 0 ≤ z.im}) : EqOn u (fun _ ↦ u z₀) (Ω ∩ {z | 0 ≤ z.im}) := by
  have hS : UniqueDiffOn ℝ (Ω ∩ {z | 0 ≤ z.im}) := by
    simpa only [inter_comm] using (uniqueDiffOn_setOfPred_le_im 0).inter hΩ
  -- off the axis the derivative within `Ω ∩ {0 ≤ im}` is the classical one, and vanishes
  have hint : EqOn (fderivWithin ℝ u (Ω ∩ {z | 0 ≤ z.im})) 0 (Ω ∩ {z | 0 < z.im}) := by
    intro z hz
    have hzS : Ω ∩ {z | 0 ≤ z.im} ∈ 𝓝 z :=
      inter_mem (hΩ.mem_nhds hz.1) (setOfPred_le_im_mem_nhds hz.2)
    have h1 : fderiv ℝ u z 1 = 0 := by
      have h : fderivWithin ℝ u {z | 0 ≤ z.im} z 1 = 0 := h₀ ⟨hz.1, hz.2.out.le⟩
      rwa [← fderivWithin_inter (hΩ.mem_nhds hz.1), inter_comm, fderivWithin_of_mem_nhds hzS]
        at h
    rw [fderivWithin_of_mem_nhds hzS]
    exact (ContinuousLinearMap.eq_zero_iff_apply_one_eq_zero_of_apply_I_eq (K := ℂ)
      (hCR z hz.1 hz.2)).2 h1
  -- by continuity it vanishes up to the axis
  have hzero : EqOn (fderivWithin ℝ u (Ω ∩ {z | 0 ≤ z.im})) 0 (Ω ∩ {z | 0 ≤ z.im}) :=
    hint.of_subset_closure (hu.continuousOn_fderivWithin hS le_rfl) continuousOn_const
      (fun z hz ↦ ⟨hz.1, hz.2.out.le⟩)
      (interior_inter_setOf_im_nonneg hΩ ▸ subset_closure_interior_inter_setOf_im_nonneg hΩ)
  exact fun z hz ↦ (convex_halfSpace_im_ge 0).is_const_of_fderivWithin_inter_eq_zero hΩ hΩc
    (hu.differentiableOn one_ne_zero) hzero hz hz₀

omit [FiniteDimensional ℝ E] in
/-- Off the real axis, the derivative `ξ = ∂ₛu` within the closed upper half-plane of a `C²`
solution of `∂ₜu = A ∂ₛu` is a weak solution of `∂ₛξ + A ∂ₜξ - A (∂ₛA) ξ = 0` on
`Ω ∩ {0 < im}`, by the classical computation `TauCeti.cauchyRiemann_fderiv_one`. -/
private theorem isWeakLinearCauchyRiemannOn_fderivWithin_one_inter_im_pos [CompleteSpace E]
    (hΩ : IsOpen Ω) (hA : ContDiffOn ℝ 1 A (Ω ∩ {z | 0 ≤ z.im}))
    (hAA : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, A z ∘L A z = -ContinuousLinearMap.id ℝ E)
    (hu : ContDiffOn ℝ 2 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hξ : ContDiffOn ℝ 1 (fun z ↦ fderivWithin ℝ u {z | 0 ≤ z.im} z 1) (Ω ∩ {z | 0 ≤ z.im})) :
    IsWeakLinearCauchyRiemannOn 3 (Ω ∩ {z | 0 < z.im}) A
      (fun z ↦ -(A z ∘L fderivWithin ℝ A {z | 0 ≤ z.im} z 1))
      (fun z ↦ fderivWithin ℝ u {z | 0 ≤ z.im} z 1) := by
  -- off the axis, derivatives within the half-plane are classical derivatives
  have hDIu {z : ℂ} (hz : 0 < z.im) : fderivWithin ℝ u {z | 0 ≤ z.im} z = fderiv ℝ u z :=
    fderivWithin_of_mem_nhds (setOfPred_le_im_mem_nhds hz)
  have hDIA {z : ℂ} (hz : 0 < z.im) : fderivWithin ℝ A {z | 0 ≤ z.im} z = fderiv ℝ A z :=
    fderivWithin_of_mem_nhds (setOfPred_le_im_mem_nhds hz)
  have hOo : IsOpen (Ω ∩ {z | 0 < z.im}) := hΩ.inter (isOpen_lt continuous_const continuous_im)
  have hOS : Ω ∩ {z | 0 < z.im} ⊆ Ω ∩ {z | 0 ≤ z.im} := fun w hw ↦ ⟨hw.1, hw.2.out.le⟩
  refine isWeakCauchyRiemannOn_of_contDiffOn (Ω := ⟨_, hOo⟩) (hξ.mono hOS)
    fun z (hz : z ∈ Ω ∩ {z | 0 < z.im}) ↦ ?_
  -- near `z`, `ξ` is the classical derivative `∂ₛu`
  have hξz : (fun w ↦ fderivWithin ℝ u {z | 0 ≤ z.im} w 1) =ᶠ[𝓝 z] fun w ↦ fderiv ℝ u w 1 :=
    Filter.eventually_of_mem (hOo.mem_nhds hz) fun w hw ↦ by simp only [hDIu hw.2]
  have h := cauchyRiemann_fderiv_one hOo ((hA.mono hOS).differentiableOn one_ne_zero)
    (hu.mono hOS) (fun w hw ↦ hCR w hw.1 hw.2) hz (hAA z (hOS hz))
  beta_reduce
  rw [hξz.fderiv_eq, hDIA hz.2, hDIu hz.2, ← sub_eq_zero, sub_neg_eq_add]
  exact h

/-- **The linearized equation up to the boundary.** For `u` of class `C²` up to the real axis
solving `∂ₜu = A ∂ₛu` off the axis, with boundary values fixed by `R`, the derivative
`ξ = ∂ₛu` within the closed upper half-plane satisfies the hypotheses of the boundary similarity
principle at the exponent `3`: `A ∈ W^{1,3}_loc` up to the axis, the coefficient `-A ∘ ∂ₛA` is
locally `L³` up to the axis, `ξ` is a weak solution of `∂ₛξ + A ∂ₜξ - A (∂ₛA) ξ = 0` on
`Ω ∩ {0 ≤ im}`, and `R ξ(s) = ξ(s)` on the axis. -/
private theorem linearized_inter_im_nonneg {R : E ≃L[ℝ] E} (hΩ : IsOpen Ω)
    (hA : ContDiffOn ℝ 1 A (Ω ∩ {z | 0 ≤ z.im}))
    (hAA : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, A z ∘L A z = -ContinuousLinearMap.id ℝ E)
    (hu : ContDiffOn ℝ 2 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (u x) = u x) :
    MemWkpLoc 3 (Ω ∩ {z | 0 ≤ z.im}) 1 A ∧
      MemLpLoc 3 (Ω ∩ {z | 0 ≤ z.im})
        (fun z ↦ -(A z ∘L fderivWithin ℝ A {z | 0 ≤ z.im} z 1)) ∧
      IsWeakLinearCauchyRiemannOn 3 (Ω ∩ {z | 0 ≤ z.im}) A
        (fun z ↦ -(A z ∘L fderivWithin ℝ A {z | 0 ≤ z.im} z 1))
        (fun z ↦ fderivWithin ℝ u {z | 0 ≤ z.im} z 1) ∧
      ∀ x : ℝ, (x : ℂ) ∈ Ω →
        R (fderivWithin ℝ u {z | 0 ≤ z.im} x 1) = fderivWithin ℝ u {z | 0 ≤ z.im} x 1 := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hS : UniqueDiffOn ℝ (Ω ∩ {z | 0 ≤ z.im}) := by
    simpa only [inter_comm] using (uniqueDiffOn_setOfPred_le_im 0).inter hΩ
  -- derivatives within `Ω ∩ {0 ≤ im}` are derivatives within the half-plane
  have hDSu {z : ℂ} (hz : z ∈ Ω) :
      fderivWithin ℝ u (Ω ∩ {z | 0 ≤ z.im}) z = fderivWithin ℝ u {z | 0 ≤ z.im} z := by
    rw [inter_comm, fderivWithin_inter (hΩ.mem_nhds hz)]
  have hDSA {z : ℂ} (hz : z ∈ Ω) :
      fderivWithin ℝ A (Ω ∩ {z | 0 ≤ z.im}) z = fderivWithin ℝ A {z | 0 ≤ z.im} z := by
    rw [inter_comm, fderivWithin_inter (hΩ.mem_nhds hz)]
  have hξ : ContDiffOn ℝ 1 (fun z ↦ fderivWithin ℝ u {z | 0 ≤ z.im} z 1)
      (Ω ∩ {z | 0 ≤ z.im}) :=
    ((hu.fderivWithin hS (by norm_num)).clm_apply (contDiffOn_const (c := (1 : ℂ)))).congr
      fun z hz ↦ by rw [hDSu hz.1]
  have hDA : ContinuousOn (fun z ↦ fderivWithin ℝ A {z | 0 ≤ z.im} z) (Ω ∩ {z | 0 ≤ z.im}) :=
    (hA.continuousOn_fderivWithin hS le_rfl).congr fun z hz ↦ (hDSA hz.1).symm
  refine ⟨hA.memWkpLoc_of_uniqueDiffOn hS,
    (hA.continuousOn.clm_comp (hDA.clm_apply continuousOn_const)).neg.memLpLoc,
    isWeakCauchyRiemannOn_iff_continuousOn_memWkpLoc_interior.2
      ⟨hξ.continuousOn, hξ.memWkpLoc_of_uniqueDiffOn hS, ?_⟩, fun x hx ↦ ?_⟩
  · rw [interior_inter_setOf_im_nonneg hΩ]
    exact isWeakLinearCauchyRiemannOn_fderivWithin_one_inter_im_pos hΩ hA hAA hu hCR hξ
  · -- on the axis, `∂ₛu` is the derivative of the boundary values `s ↦ u s`, fixed by `R`
    have hT : ofReal ⁻¹' Ω ∈ 𝓝 x := (hΩ.preimage continuous_ofReal).mem_nhds hx
    have hd := HasFDerivWithinAt.hasDerivAt_comp_ofReal
      ((hu.differentiableOn two_ne_zero) x ⟨hx, by simp⟩).hasFDerivWithinAt
      (Filter.mem_of_superset hT fun t ht ↦ ⟨ht, by simp⟩)
    have hR := ((R : E →L[ℝ] E).hasFDerivAt.comp_hasDerivAt x hd).congr_of_eventuallyEq
      (Filter.mem_of_superset hT fun t ht ↦ (hbd t ht).symm)
    rw [← hDSu hx]
    exact hR.unique hd

/-- **Isolated critical points up to a totally real boundary.** Let `R` be a real-linear
automorphism of a finite-dimensional real normed space `E`, such as complex conjugation on `ℂⁿ`.
Let `Ω` be open with `Ω ∩ {0 ≤ im}` preconnected, and `u` a map of class `C²` up to the real
axis on `Ω ∩ {0 ≤ im}`, solving `∂ₜu = A ∂ₛu` off the axis, for a field `A` of class `C¹` up to
the axis with `A(z)² = -1`. Assume the totally real boundary condition: `R` fixes the boundary
values `u(s)` and anticommutes with `A(s)` on `Ω ∩ ℝ`. If `u` is not constant on `Ω ∩ {0 ≤ im}`,
the points where its derivative within the closed upper half-plane vanishes form a discrete
subset of `Ω ∩ {0 ≤ im}`, also near the real axis. -/
theorem setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg
    {R : E ≃L[ℝ] E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hA : ContDiffOn ℝ 1 A (Ω ∩ {z | 0 ≤ z.im}))
    (hAA : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, A z ∘L A z = -ContinuousLinearMap.id ℝ E)
    (hAR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (A x v) = -A x (R v))
    (hu : ContDiffOn ℝ 2 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (u x) = u x)
    (hne : ∃ z ∈ Ω ∩ {z | 0 ≤ z.im}, ∃ w ∈ Ω ∩ {z | 0 ≤ z.im}, u z ≠ u w) :
    {z | fderivWithin ℝ u {z | 0 ≤ z.im} z ≠ 0} ∈ codiscreteWithin (Ω ∩ {z | 0 ≤ z.im}) := by
  -- pass to a conjugation-invariant open set with the same closed upper part
  obtain ⟨Ω', hΩ', hΩs, heq⟩ := exists_isOpen_mapsTo_conj_inter_setOf_im_nonneg_eq hΩ
  have hsub {z : ℂ} (hz : z ∈ Ω') (h : 0 ≤ z.im) : z ∈ Ω := (heq.subset ⟨hz, h⟩).1
  have hCR' : ∀ z ∈ Ω', 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1) :=
    fun z hz h ↦ hCR z (hsub hz h.le) h
  rw [← heq] at hΩc hA hAA hu hne ⊢
  obtain ⟨hAw, hC, hξ, hξR⟩ :=
    linearized_inter_im_nonneg hΩ' hA hAA hu hCR' fun x hx ↦ hbd x (hsub hx (by simp))
  -- `∂ₛu` does not vanish identically, since `u` is not constant
  have hξne : ∃ z ∈ Ω' ∩ {z | 0 ≤ z.im}, fderivWithin ℝ u {z | 0 ≤ z.im} z 1 ≠ 0 := by
    by_contra! h
    obtain ⟨z, hz, w, hw, hzw⟩ := hne
    have hc := eqOn_const_of_cauchyRiemann_of_eqOn_zero_inter_im_nonneg hΩ' hΩc
      (hu.of_le one_le_two) hCR' h hz
    exact hzw (hc hw).symm
  refine Filter.mem_of_superset
    (setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg
      (Ω := ⟨Ω', hΩ'⟩) (by norm_num) hΩs hΩc hAw hA.continuousOn hAA
      (fun x hx ↦ hAR x (hsub hx (by simp))) hC hξ hξR hξne) fun z hz h₀ ↦ hz (by simp [h₀])

/-- **Unique continuation for critical points of infinite order, up to a totally real
boundary.** Let `Ω`, `u`, `A` and `R` be as in
`TauCeti.setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg`. If
the derivative of `u` within the closed upper half-plane is `O(‖z - z₀‖ⁿ)` within `{0 ≤ im}` for
every `n`, at a point `z₀ ∈ Ω ∩ {0 ≤ im}` possibly on the real axis, then `u` is constant on
`Ω ∩ {0 ≤ im}`. -/
theorem eqOn_const_of_cauchyRiemann_inter_im_nonneg_of_forall_fderivWithin_isBigO
    {R : E ≃L[ℝ] E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hA : ContDiffOn ℝ 1 A (Ω ∩ {z | 0 ≤ z.im}))
    (hAA : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, A z ∘L A z = -ContinuousLinearMap.id ℝ E)
    (hAR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (A x v) = -A x (R v))
    (hu : ContDiffOn ℝ 2 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (u x) = u x) (hz₀ : z₀ ∈ Ω ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, (fun z ↦ fderivWithin ℝ u {z | 0 ≤ z.im} z) =O[𝓝[{z | 0 ≤ z.im}] z₀]
      fun z ↦ (z - z₀) ^ n) :
    EqOn u (fun _ ↦ u z₀) (Ω ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨Ω', hΩ', hΩs, heq⟩ := exists_isOpen_mapsTo_conj_inter_setOf_im_nonneg_eq hΩ
  have hsub {z : ℂ} (hz : z ∈ Ω') (h : 0 ≤ z.im) : z ∈ Ω := (heq.subset ⟨hz, h⟩).1
  have hCR' : ∀ z ∈ Ω', 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1) :=
    fun z hz h ↦ hCR z (hsub hz h.le) h
  rw [← heq] at hΩc hA hAA hu hz₀ ⊢
  obtain ⟨hAw, hC, hξ, hξR⟩ :=
    linearized_inter_im_nonneg hΩ' hA hAA hu hCR' fun x hx ↦ hbd x (hsub hx (by simp))
  exact eqOn_const_of_cauchyRiemann_of_eqOn_zero_inter_im_nonneg hΩ' hΩc (hu.of_le one_le_two)
    hCR' (eqOn_zero_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg_of_forall_isBigO
      (Ω := ⟨Ω', hΩ'⟩) (by norm_num) hΩs hΩc hAw hA.continuousOn hAA
      (fun x hx ↦ hAR x (hsub hx (by simp))) hC hξ hξR hz₀
      fun n ↦ ((ContinuousLinearMap.apply ℝ E (1 : ℂ)).isBigO_comp _ _).trans (h₀ n)) hz₀

/-- **Unique continuation for critical points up to a totally real boundary.** Let `Ω`, `u`,
`A` and `R` be as in
`TauCeti.setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg`. If
the derivative of `u` within the closed upper half-plane vanishes at the points of `{0 ≤ im}`
near a point `z₀ ∈ Ω ∩ {0 ≤ im}`, possibly on the real axis, then `u` is constant on
`Ω ∩ {0 ≤ im}`. -/
theorem eqOn_const_of_cauchyRiemann_inter_im_nonneg_of_eventually_fderivWithin_eq_zero
    {R : E ≃L[ℝ] E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hA : ContDiffOn ℝ 1 A (Ω ∩ {z | 0 ≤ z.im}))
    (hAA : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, A z ∘L A z = -ContinuousLinearMap.id ℝ E)
    (hAR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (A x v) = -A x (R v))
    (hu : ContDiffOn ℝ 2 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (u x) = u x) (hz₀ : z₀ ∈ Ω ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ᶠ z in 𝓝[{z | 0 ≤ z.im}] z₀, fderivWithin ℝ u {z | 0 ≤ z.im} z = 0) :
    EqOn u (fun _ ↦ u z₀) (Ω ∩ {z | 0 ≤ z.im}) :=
  eqOn_const_of_cauchyRiemann_inter_im_nonneg_of_forall_fderivWithin_isBigO hΩ hΩc hA hAA hAR
    hu hCR hbd hz₀ fun _ ↦ (isBigO_zero _ _).congr' (h₀.mono fun _ h ↦ h.symm) .rfl

/-- **Finitely many critical points on compact sets, up to a totally real boundary.** Let `Ω`,
`u`, `A` and `R` be as in
`TauCeti.setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg`, with
`u` not constant on `Ω ∩ {0 ≤ im}`. Each compact subset of `Ω ∩ {0 ≤ im}`, which may meet the
real axis, contains finitely many points where the derivative of `u` within the closed upper
half-plane vanishes. -/
theorem finite_inter_setOf_fderivWithin_eq_zero_of_cauchyRiemann_inter_im_nonneg
    {R : E ≃L[ℝ] E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hA : ContDiffOn ℝ 1 A (Ω ∩ {z | 0 ≤ z.im}))
    (hAA : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, A z ∘L A z = -ContinuousLinearMap.id ℝ E)
    (hAR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (A x v) = -A x (R v))
    (hu : ContDiffOn ℝ 2 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (u x) = u x)
    (hne : ∃ z ∈ Ω ∩ {z | 0 ≤ z.im}, ∃ w ∈ Ω ∩ {z | 0 ≤ z.im}, u z ≠ u w) {K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω ∩ {z | 0 ≤ z.im}) :
    (K ∩ {z | fderivWithin ℝ u {z | 0 ≤ z.im} z = 0}).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono hKΩ
    (setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg hΩ hΩc hA
      hAA hAR hu hCR hbd hne))
  convert h using 1
  ext z
  simp

/-- **Isolated critical points of J-holomorphic curves up to a totally real boundary.** Let `R`
be a real-linear automorphism of a finite-dimensional real normed space `E`, and `J` a field of
endomorphisms of `E`. Let `Ω` be open with `Ω ∩ {0 ≤ im}` preconnected, and `u` a map of class
`C²` up to the real axis on `Ω ∩ {0 ≤ im}`, solving `∂ₜu = J(u) ∂ₛu` off the axis, with `J` of
class `C¹` near the image of `u` and `J(u)² = -1` along it. Assume that `R` fixes the boundary
values `u(s)` and anticommutes with `J(u(s))` on `Ω ∩ ℝ`; in coordinates where a totally real
submanifold is `ℝⁿ ⊆ ℂⁿ` and `J = i` along it, `R` is complex conjugation. If `u` is not constant
on `Ω ∩ {0 ≤ im}`, its critical points form a discrete subset of `Ω ∩ {0 ≤ im}`. -/
theorem setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg_comp
    {R : E ≃L[ℝ] E} {J : E → E →L[ℝ] E} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hJ : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, ContDiffAt ℝ 1 J (u z))
    (hJJ : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, J (u z) ∘L J (u z) = -ContinuousLinearMap.id ℝ E)
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J (u x) v) = -J (u x) (R v))
    (hu : ContDiffOn ℝ 2 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (u x) = u x)
    (hne : ∃ z ∈ Ω ∩ {z | 0 ≤ z.im}, ∃ w ∈ Ω ∩ {z | 0 ≤ z.im}, u z ≠ u w) :
    {z | fderivWithin ℝ u {z | 0 ≤ z.im} z ≠ 0} ∈ codiscreteWithin (Ω ∩ {z | 0 ≤ z.im}) :=
  setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg
    (A := fun z ↦ J (u z)) hΩ hΩc
    (fun z hz ↦ (hJ z hz).comp_contDiffWithinAt z ((hu z hz).of_le one_le_two)) hJJ hJR hu hCR
    hbd hne

/-- **Finitely many critical points of J-holomorphic curves on compact sets, up to a totally real
boundary.** Let `Ω`, `u`, `J` and `R` be as in
`TauCeti.setOf_fderivWithin_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_inter_im_nonneg_comp`,
with `u` not constant on `Ω ∩ {0 ≤ im}`. Each compact subset of `Ω ∩ {0 ≤ im}`, which may meet
the real axis, contains finitely many critical points of `u`. -/
theorem finite_inter_setOf_fderivWithin_eq_zero_of_cauchyRiemann_inter_im_nonneg_comp
    {R : E ≃L[ℝ] E} {J : E → E →L[ℝ] E} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected (Ω ∩ {z | 0 ≤ z.im}))
    (hJ : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, ContDiffAt ℝ 1 J (u z))
    (hJJ : ∀ z ∈ Ω ∩ {z | 0 ≤ z.im}, J (u z) ∘L J (u z) = -ContinuousLinearMap.id ℝ E)
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J (u x) v) = -J (u x) (R v))
    (hu : ContDiffOn ℝ 2 u (Ω ∩ {z | 0 ≤ z.im}))
    (hCR : ∀ z ∈ Ω, 0 < z.im → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hbd : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (u x) = u x)
    (hne : ∃ z ∈ Ω ∩ {z | 0 ≤ z.im}, ∃ w ∈ Ω ∩ {z | 0 ≤ z.im}, u z ≠ u w) {K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω ∩ {z | 0 ≤ z.im}) :
    (K ∩ {z | fderivWithin ℝ u {z | 0 ≤ z.im} z = 0}).Finite :=
  finite_inter_setOf_fderivWithin_eq_zero_of_cauchyRiemann_inter_im_nonneg
    (A := fun z ↦ J (u z)) hΩ hΩc
    (fun z hz ↦ (hJ z hz).comp_contDiffWithinAt z ((hu z hz).of_le one_le_two)) hJJ hJR hu hCR
    hbd hne hK hKΩ

end FiniteDimensional

end TauCeti
