/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.RCLike.OperatorNorm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Isolated critical points of J-holomorphic curves

Let `E` be a finite-dimensional real normed space and `u : ℂ → E` a map of class `C²` on an open
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
class `C¹` near the image of `u` and `J² = -1` along it.

The argument applies the similarity principle to the differentiated equation. Since
`∂ₜu = A ∂ₛu`, the differential of `u` vanishes exactly where `ξ = ∂ₛu` does
(`ContinuousLinearMap.eq_zero_iff_apply_one_eq_zero_of_apply_I_eq`). Differentiating the
equation in `s` and using the symmetry of the second derivative gives `∂ₜξ = (∂ₛA) ξ + A ∂ₛξ`,
and applying `A` turns this into the linear Cauchy–Riemann equation

`∂ₛξ + A ∂ₜξ - A (∂ₛA) ξ = 0`

with the continuous coefficient `-A ∘ ∂ₛA` (`TauCeti.cauchyRiemann_fderiv_one`; the same
computation for the equation `∂ₛu + A ∂ₜu = 0` on `ℝ × ℝ` is
`TauCeti.cauchyRiemann_fderiv_apply_eq_neg`). Its structure
`A` genuinely varies, so the variable-structure unique continuation theorems of
`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure` apply to `ξ`.

The `C²` hypothesis on `u` is what the differentiated equation needs classically. For a smooth
structure it holds for every `C¹` solution by elliptic regularity; a structure of class `C¹` only
gives `W^{2,p}` solutions, which are not treated here.

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

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemma 2.4.1 and its proof via the similarity principle, Theorem 2.3.5.
-/

public section

open Asymptotics Complex Filter MeasureTheory Set Topology

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

/-- **Unique continuation for critical points.** Let `u` be of class `C²` on a connected open set
`Ω` and solve the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of complex
structures, `A(z)² = -1`, on a finite-dimensional real normed space. If the differential of `u`
vanishes near one point `z₀ ∈ Ω`, then `u` is constant on `Ω`. -/
theorem eqOn_const_of_cauchyRiemann_of_eventually_fderiv_eq_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 2 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ᶠ z in 𝓝 z₀, fderiv ℝ u z = 0) : EqOn u (fun _ ↦ u z₀) Ω := by
  obtain ⟨hξ, hCm, hCb, hL⟩ := linearizedCoeff_of_cauchyRiemann hΩ hA hAA hu hCR
  obtain ⟨t, ht, hto, hz₀t⟩ := eventually_nhds_iff.1 h₀
  refine eqOn_const_of_cauchyRiemann_of_eqOn_zero hΩ hΩc (hu.differentiableOn two_ne_zero) hCR ?_
    hz₀
  exact eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure hΩ hΩc hA hAA hξ hCm hCb hL
    (hto.inter hΩ) ⟨z₀, hz₀t, hz₀⟩ inter_subset_right fun z hz ↦ by simp [ht z hz.1]

/-- **Unique continuation for critical points of infinite order.** Let `u` be of class `C²` on a
connected open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹`
field `A` of complex structures, `A(z)² = -1`, on a finite-dimensional real normed space. If the
differential of `u` is `O(‖z - z₀‖ⁿ)` at a point `z₀ ∈ Ω` for every `n`, then `u` is constant on
`Ω`. -/
theorem eqOn_const_of_cauchyRiemann_of_forall_fderiv_isBigO (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 2 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1)) (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, (fun z ↦ fderiv ℝ u z) =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn u (fun _ ↦ u z₀) Ω := by
  obtain ⟨hξ, hCm, hCb, hL⟩ := linearizedCoeff_of_cauchyRiemann hΩ hA hAA hu hCR
  exact eqOn_const_of_cauchyRiemann_of_eqOn_zero hΩ hΩc (hu.differentiableOn two_ne_zero) hCR
    (eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ hΩc hA hAA hξ hCm hCb hL hz₀
      fun n ↦ ((ContinuousLinearMap.apply ℝ E (1 : ℂ)).isBigO_comp _ _).trans (h₀ n)) hz₀

/-- **Isolated critical points.** Let `u` be of class `C²` on a connected open set `Ω` and solve
the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of complex structures,
`A(z)² = -1`, on a finite-dimensional real normed space. If `u` is not constant on `Ω`, its
critical points form a discrete subset of `Ω`. -/
theorem setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 2 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = A z (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) : {z | fderiv ℝ u z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨hξ, hCm, hCb, hL⟩ := linearizedCoeff_of_cauchyRiemann hΩ hA hAA hu hCR
  refine Filter.mem_of_superset
    (setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure hΩ hΩc hA hAA hξ hCm
      hCb hL (exists_fderiv_one_ne_zero_of_cauchyRiemann hΩ hΩc (hu.differentiableOn two_ne_zero)
        hCR hne)) fun z hz h₀ ↦ ?_
  exact hz (by simp [h₀])

/-- **Finitely many critical points on compact sets.** Let `u` be of class `C²` on a connected
open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = A ∂ₛu` there, for a `C¹` field `A` of
complex structures, `A(z)² = -1`, on a finite-dimensional real normed space. If `u` is not
constant on `Ω`, each compact subset of `Ω` contains finitely many critical points of `u`. -/
theorem finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hA : ContDiffOn ℝ 1 A Ω)
    (hAA : ∀ z ∈ Ω, A z ∘L A z = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 2 u Ω)
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

/-- **Isolated critical points of J-holomorphic curves.** Let `u` be of class `C²` on a connected
open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` there, for a field `J` of
endomorphisms of a finite-dimensional real normed space which is `C¹` near the image of `u` and
satisfies `J(u)² = -1` along it. If `u` is not constant on `Ω`, its critical points form a
discrete subset of `Ω`. -/
theorem setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_comp {J : E → E →L[ℝ] E}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 J (u z))
    (hJJ : ∀ z ∈ Ω, J (u z) ∘L J (u z) = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 2 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) : {z | fderiv ℝ u z ≠ 0} ∈ codiscreteWithin Ω :=
  setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann (A := fun z ↦ J (u z)) hΩ hΩc
    (fun z hz ↦ (hJ z hz).comp_contDiffWithinAt z ((hu z hz).of_le (by norm_num))) hJJ hu hCR hne

/-- **Finitely many critical points of J-holomorphic curves on compact sets.** Let `u` be of class
`C²` on a connected open set `Ω` and solve the Cauchy–Riemann equation `∂ₜu = J(u) ∂ₛu` there,
for a field `J` of endomorphisms of a finite-dimensional real normed space which is `C¹` near the
image of `u` and satisfies `J(u)² = -1` along it. If `u` is not constant on `Ω`, each compact
subset of `Ω` contains finitely many critical points of `u`. -/
theorem finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann_comp {J : E → E →L[ℝ] E}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJ : ∀ z ∈ Ω, ContDiffAt ℝ 1 J (u z))
    (hJJ : ∀ z ∈ Ω, J (u z) ∘L J (u z) = -ContinuousLinearMap.id ℝ E) (hu : ContDiffOn ℝ 2 u Ω)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hne : ∃ z ∈ Ω, ∃ w ∈ Ω, u z ≠ u w) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (K ∩ {z | fderiv ℝ u z = 0}).Finite :=
  finite_inter_setOf_fderiv_eq_zero_of_cauchyRiemann (A := fun z ↦ J (u z)) hΩ hΩc
    (fun z hz ↦ (hJ z hz).comp_contDiffWithinAt z ((hu z hz).of_le (by norm_num))) hJJ hu hCR hne
    hK hKΩ

end FiniteDimensional

end TauCeti
