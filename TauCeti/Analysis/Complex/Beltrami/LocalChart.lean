/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Beltrami.Chart
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Holder.Rescaling
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology

/-!
# Planar isothermal charts without a smallness hypothesis

Let `J` be a field of almost complex structures on the plane, of class `C¹` near `c`. There is a
local chart `e` of the plane around `c`, of class `C¹` with `C¹` inverse, whose differential
carries `J` to multiplication by `i` at every point of its source
(`TauCeti.Beltrami.exists_isComplexLinear_chart_of_contDiffAt`).

The planar Beltrami chart `TauCeti.Beltrami.exists_isComplexLinear_chart` needs a coefficient
that is small in the Hölder norm. The coefficient of `J` is reduced to this case in two steps,
following McDuff–Salamon, Appendix E.

* *Normalization.* A real-linear map `A` carries `J c` to the standard structure
  (`TauCeti.Beltrami.exists_transport_eq_std_and_contDiffAt`), so the coefficient `μ₁` of the
  structure `J` read through `w ↦ A (w - c)` vanishes at `0`.
* *Rescaling and cutoff.* Rescaling by `ε` does not change the structures, and with a fixed cutoff
  `χ`, equal to `1` on the unit disc and vanishing off the disc of radius `2`, the coefficient
  `ν(z) = χ(z) μ₁(ε z)` is small in Hölder norm for `ε` small, because `μ₁` is Lipschitz near `0`
  and vanishes there (`TauCeti.eventually_exists_holderSpace_cutoff_rescale`).

Restricting the chart of `ν` to the unit disc, where `ν` is the coefficient of the rescaled
structure, and composing it with `w ↦ ε⁻¹ A (w - c)` gives the chart of `J`
(`OpenPartialHomeomorph.isComplexLinear_chart_comp_affine`).

## Main results

* `TauCeti.Beltrami.exists_isComplexLinear_chart_of_contDiffAt`: a `C¹` structure has a `C¹`
  chart at `c`, with `C¹` inverse, in which it is the standard structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix E.
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
-/

public noncomputable section

open Complex Filter Metric Set Topology
open scoped NNReal Manifold ContDiff BoundedContinuousFunction

namespace TauCeti.Beltrami

/-- **Planar isothermal charts.** Let `J` be a field of almost complex structures on the plane,
with `z ↦ J z` of class `C¹` at `c` in the operator norm. Then there is an open
partial homeomorphism `e` of the plane with `c` in its source and `e c = 0`, of class `C¹` on its
source with `C¹` inverse on its target, whose real differential carries `J z` to multiplication by
`i` at every point `z` of its source. No smallness of the Beltrami coefficient of `J` is
assumed. -/
theorem exists_isComplexLinear_chart_of_contDiffAt {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ}
    (hJs : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) c) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e c = 0 ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧ (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, IsComplexLinear (J z).toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ e z).toLinearMap := by
  set J₀ := AlmostComplexStructure.ofComplexModule ℂ
  /- Step 1: normalize at `c`. Read `J` through `w ↦ A (w - c)`, where `A` carries `J c` to the
  standard structure; the coefficient `μ₁` of the new field `J₁` vanishes at `0`. -/
  obtain ⟨A, hA, hJ₁s⟩ := exists_transport_eq_std_and_contDiffAt hJs
  let J₁ : ℂ → AlmostComplexStructure ℂ := fun w ↦
    (J (c + A.symm w)).transport A.toLinearEquiv
  have hJ₁ : ∀ w v, J₁ w (A v) = A (J (c + A.symm w) v) := fun w v ↦ by
    simp [J₁, AlmostComplexStructure.transport_toLinearMap, LinearEquiv.conj_apply]
  have hJ₁0 : J₁ 0 = J₀ := by
    simp only [J₁, map_zero, add_zero]
    exact hA
  have htame₀ : stdComplexSymplecticForm.Tames (J₁ 0) := hJ₁0 ▸ stdComplexSymplecticForm_tames
  let μ₁ : ℂ → ℂ := fun w ↦ J₀.cayley (J₁ w) 1
  have hμ₁0 : μ₁ 0 = 0 := by simp [μ₁, hJ₁0]
  have hμ₁s : ContDiffAt ℝ 1 μ₁ 0 := by
    have h := stdComplexSymplecticForm_tames.contMDiffAt_cayley (I := 𝓘(ℝ, ℂ)) htame₀
      (contMDiffAt_iff_contDiffAt.2 hJ₁s)
    exact contMDiffAt_iff_contDiffAt.1 (h.clm_apply contMDiffAt_const)
  /- Step 2: near `0`, `μ₁` is Lipschitz and bounded, hence `½`-Hölder, and `J₁` is tame. -/
  obtain ⟨Kμ, t, ht, hKμ⟩ := hμ₁s.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hρ'⟩ : ∃ ρ > 0, ∀ w ∈ ball (0 : ℂ) ρ,
      w ∈ t ∧ ‖μ₁ w‖ ≤ 1 ∧ stdComplexSymplecticForm.Tames (J₁ w) :=
    Metric.eventually_nhds_iff_ball.1 (Filter.Eventually.and ht
      ((hμ₁s.continuousAt.norm.eventually (ge_mem_nhds (by simp [hμ₁0]))).and
        (SymplecticForm.Tames.eventually_of_continuousAt hJ₁s.continuousAt htame₀)))
  have hμ₁H : HolderOnWith (Kμ + 2 * 1) (1 / 2) μ₁ (ball 0 ρ) :=
    (hKμ.mono fun w hw ↦ (hρ' w hw).1).holderOnWith_of_norm_le
      (fun w hw ↦ by simpa using (hρ' w hw).2.1) (by norm_num)
  /- Step 3: the planar Beltrami chart with `C¹` inverse on the disc of radius `2`, applied to the
  rescaled cutoff coefficient `ν(z) = χ(z) μ₁(ε z)` for `ε` small. -/
  obtain ⟨δ, hδ, C, hchart⟩ := exists_isComplexLinear_chart (α := 1 / 2)
    (by norm_num) (by norm_num) 0 (r := 2) two_pos
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨ε, ⟨hε, hερ⟩, ν, hνmem, hνapp, hνη⟩ := ((eventually_mem_nhdsWithin.and
    ((eventually_lt_nhds hρ).filter_mono nhdsWithin_le_nhds)).and
    ((eventually_exists_holderSpace_cutoff_rescale (by norm_num) (by norm_num) hρ hμ₁H hμ₁0
      χ.contDiff χ.hasCompactSupport (lt_min hδ one_pos)).filter_mono nhdsWithin_le_nhds) :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).exists
  rw [χ.tsupport_eq] at hνmem
  have hν1 : ∀ z, ‖ν z‖ < 1 := fun z ↦
    (HolderSpace.norm_apply_le _ z).trans_lt (hνη.trans_le (min_le_right _ _))
  let J'' : ℂ → AlmostComplexStructure ℂ := fun z ↦ (coefficientEquiv.symm ⟨ν z, hν1 z⟩).val
  have hJ''t : ∀ z, stdComplexSymplecticForm.Tames (J'' z) := fun z ↦
    (coefficientEquiv.symm _).property
  have hJ''μ : ∀ z, ν z = (coefficientEquiv ⟨J'' z, hJ''t z⟩).val := fun z ↦ by
    simp [J'']
  obtain ⟨h, -, -, -, -, -, -, -, -, hφC1, -, -, hφlin, e, he, hce, hesub, hesC⟩ :=
    hchart J'' (fun z _ ↦ hJ''t z) ν hνmem (fun z _ ↦ hJ''μ z) (hνη.trans_le (min_le_left _ _))
  have heC : ∀ z ∈ e.source, ContDiffAt ℝ 1 e z := fun z hz ↦ by
    rw [he]
    exact hφC1.contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball (by norm_num) (hesub hz)))
  have helin : ∀ z ∈ e.source, IsComplexLinear (J'' z).toLinearMap J₀.toLinearMap
      (fderiv ℝ e z).toLinearMap := fun z hz ↦ by
    rw [he]
    exact hφlin z (ball_subset_closedBall (hesub hz))
  -- On the unit disc, `J''` is the rescaled normalized structure.
  have hJ''J₁ : ∀ z ∈ ball (0 : ℂ) 1, J'' z = J₁ (ε • z) := by
    intro z hz
    have hεz : ε • z ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hε.le]
      rw [mem_ball_zero_iff] at hz
      calc ε * ‖z‖ < ε * 1 := by gcongr
        _ < ρ := by linarith
    have hT := (hρ' _ hεz).2.2
    have hν' : ν z = μ₁ (ε • z) := by
      rw [hνapp, χ.one_of_mem_closedBall (ball_subset_closedBall hz), one_smul]
    have hc : coefficientEquiv ⟨J₁ (ε • z), hT⟩ = ⟨ν z, hν1 z⟩ :=
      Subtype.ext (by rw [coefficientEquiv_apply]; exact hν'.symm)
    simp only [J'', ← hc, Equiv.symm_apply_apply]
  /- Step 4: restrict the chart to the unit disc and compose it with `w ↦ ε⁻¹ A (w - c)`, which
  carries `J` to `J''` there. -/
  let e₁ := e.restrOpen (ball (0 : ℂ) 1) isOpen_ball
  have he₁s : ∀ z, z ∈ e₁.source ↔ z ∈ e.source ∧ z ∈ ball (0 : ℂ) 1 := fun z ↦ by
    rw [OpenPartialHomeomorph.restrOpen_source, mem_inter_iff]
  let B : ℂ ≃L[ℝ] ℂ := A.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 ε⁻¹ (inv_ne_zero hε.ne')))
  have hB : ∀ v, B v = ε⁻¹ • A v := fun v ↦ by simp [B, Units.smul_def]
  have hBJ : ∀ z, B (z - c) ∈ e₁.source → ∀ v, B (J z v) = J'' (B (z - c)) (B v) :=
    fun z hz v ↦ by
      have hεS : ε • B (z - c) = A (z - c) := by
        rw [hB, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
      have hzc : c + A.symm (A (z - c)) = z := by
        rw [ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel]
      rw [hJ''J₁ _ ((he₁s _).1 hz).2, hεS, hB, hB, map_smul, hJ₁, hzc]
  obtain ⟨he'C, he'sC, he'lin⟩ :=
    e₁.isComplexLinear_chart_comp_affine B c (fun z hz ↦ heC z ((he₁s z).1 hz).1)
      (fun z hz ↦ (hesC z hz.1).contDiffAt (e.open_target.mem_nhds hz.1))
      (fun z hz ↦ helin z ((he₁s z).1 hz).1) hBJ
  refine ⟨_, ?_, ?_, he'C, he'sC, he'lin⟩
  · simpa [he₁s] using hce
  · simp [e₁, he]

end TauCeti.Beltrami
