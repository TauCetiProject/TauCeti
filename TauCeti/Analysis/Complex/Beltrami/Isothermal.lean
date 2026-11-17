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
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.Topology.MetricSpace.Holder

/-!
# Isothermal coordinates for a field of complex structures on the plane

Let `J` be a field of real-linear endomorphisms of the plane which is `C¹` near a point `z₀` and
squares to `-1` there, a `C¹` almost complex structure near `z₀`. This file constructs an
*isothermal chart* for `J` at `z₀`: an open partial homeomorphism `e` of `ℂ` whose source
contains `z₀`, which is `C¹` with `C¹` inverse, and whose derivative carries `J` to multiplication
by `i` at every point of its source
(`TauCeti.Beltrami.exists_isothermal_chart`). No orientation is assumed: `J z₀` may induce either
orientation of the plane, and the chart then preserves or reverses the standard orientation.

The construction is the Beltrami argument of McDuff and Salamon.

* **Normalization.** A real-linear automorphism `B` carries multiplication by `i` to `J z₀`
  (`ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul`), so in the coordinates
  `u = B⁻¹ (z - z₀)` the field is `K u = B⁻¹ ∘ J (z₀ + B u) ∘ B`, with `K 0 = i`.
* **The coefficient.** A real-linear endomorphism `K` of the plane with `K² = -1` and
  `K 1 ≠ -i`, of either orientation, is conjugate to multiplication by `i` through the affine
  Beltrami normalizer `z ↦ z + ν conj z` of the coefficient `ν = (i - K 1) / (conj (K 1) - i)`.
  The coefficient `ν u` of `K u` is a `C¹` function of `u` near `0` with `ν 0 = 0`, hence Hölder
  near `0`.
* **Rescaling.** For a bump function `χ` equal to `1` on the unit disc and supported in the disc
  of radius `2`, the coefficient `w ↦ χ w ν (ε w)` is small in Hölder norm for small `ε > 0`
  (`TauCeti.eventually_exists_holderSpace_cutoff_rescale`).
* **The planar Beltrami chart.** For the structure with this small coefficient, the planar
  Beltrami chart `TauCeti.Beltrami.exists_isComplexLinear_chart` is a `C¹` chart at `0`, with
  `C¹` inverse, whose derivative carries the structure to `i` on the disc of radius `2`. On the
  unit disc that structure is `K (ε w)`.

Composing this chart with the real-affine map `z ↦ ε⁻¹ B⁻¹ (z - z₀)`, which carries `J` to
`w ↦ K (ε w)`, gives the isothermal chart of `J`.

## Main results

* `TauCeti.Beltrami.exists_isothermal_chart`: a `C¹` field of complex structures on the plane has
  a `C¹` isothermal chart, with `C¹` inverse, at every point.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
-/

public section

open Complex Filter Metric Set
open scoped ComplexConjugate NNReal Topology

namespace TauCeti.Beltrami

/-! ### Complex structures on the plane in either orientation -/

/-- **The coefficient of a complex structure on the plane, in either orientation.** If a
real-linear endomorphism `K` of the plane squares to `-1` and `μ (conj (K 1) - i) = i - K 1`, then
the affine Beltrami normalizer of `μ` carries `K` to multiplication by `i`. -/
private theorem linearMap_apply_eq_I_mul {K : ℂ →L[ℝ] ℂ} (hK : ∀ v, K (K v) = -v) {μ : ℂ}
    (hμ : μ * (conj (K 1) - I) = I - K 1) (v : ℂ) :
    linearMap μ (K v) = I * linearMap μ v := by
  -- `K 1` is off the real line, since `K (r • 1) = r • K 1` cannot square to `-1`.
  have ha : (K 1).im ≠ 0 := by
    intro h
    have hre : K 1 = (K 1).re • (1 : ℂ) := by
      apply Complex.ext <;> simp [h]
    have h1 := hK 1
    rw [hre, map_smul, hre, smul_smul] at h1
    have := congrArg Complex.re h1
    simp only [Complex.real_smul, Complex.re_ofReal_mul, Complex.one_re, Complex.neg_re,
      Complex.ofReal_mul, mul_one] at this
    nlinarith [mul_self_nonneg (K 1).re]
  -- Both sides are real-linear in `v`, and agree at `1` and at `K 1`, which span the plane.
  have hv : v = (v.re - v.im * (K 1).re / (K 1).im) • (1 : ℂ) + (v.im / (K 1).im) • K 1 := by
    apply Complex.ext
    · simp
      field_simp
      ring
    · simp
      field_simp
  have h1 : linearMap μ (K 1) = I * linearMap μ 1 := by
    simp only [linearMap_apply, map_one]
    linear_combination hμ
  have h2 : linearMap μ (K (K 1)) = I * linearMap μ (K 1) := by
    simp only [hK 1, linearMap_apply, map_neg, map_one]
    linear_combination (norm := (ring_nf; simp only [I_sq]; ring_nf)) (-I) * hμ
  rw [hv]
  simp only [map_add, map_smul]
  rw [h2, h1]
  simp only [Complex.real_smul]
  ring

/-- The coefficient `(i - b) / (conj b - i)` solves the equation of `linearMap_apply_eq_I_mul`
for `b = K 1`, when `K 1 ≠ -i`. -/
private theorem div_mul_conj_sub_I {b : ℂ} (hb : b ≠ -I) :
    (I - b) / (conj b - I) * (conj b - I) = I - b := by
  refine div_mul_cancel₀ _ fun h0 ↦ hb ?_
  have := congrArg conj (sub_eq_zero.mp h0)
  rwa [conj_conj, conj_I] at this

/-! ### Affine changes of coordinates -/

/-- An isothermal chart `e` for a field `K` on the plane, composed with a real-affine change of
coordinates `z ↦ A (z - c)` that carries a field `J` to `K`, is an isothermal chart for `J`. -/
private theorem exists_isothermal_chart_comp_affine {J K : ℂ → ℂ →L[ℝ] ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ} (he : ∀ w ∈ e.source, ContDiffAt ℝ 1 e w)
    (hes : ∀ w ∈ e.target, ContDiffAt ℝ 1 e.symm w)
    (hK : ∀ w ∈ e.source, ∀ v, fderiv ℝ e w (K w v) = I * fderiv ℝ e w v) (A : ℂ ≃L[ℝ] ℂ)
    (c : ℂ) (hJ : ∀ z, A (z - c) ∈ e.source → ∀ v, A (J z v) = K (A (z - c)) (A v)) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ, (∀ z, z ∈ F.source ↔ A (z - c) ∈ e.source) ∧
      (∀ z ∈ F.source, ContDiffAt ℝ 1 F z) ∧ (∀ z ∈ F.target, ContDiffAt ℝ 1 F.symm z) ∧
      ∀ z ∈ F.source, ∀ v, fderiv ℝ F z (J z v) = I * fderiv ℝ F z v := by
  let T : ℂ ≃ₜ ℂ := (Homeomorph.subRight c).trans A.toHomeomorph
  have hT : ∀ z, HasFDerivAt (fun z ↦ A (z - c)) (A : ℂ →L[ℝ] ℂ) z := fun z ↦
    (A : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  have hTc : ContDiff ℝ 1 fun z ↦ A (z - c) := A.contDiff.comp (contDiff_id.sub contDiff_const)
  have hTsc : ContDiff ℝ 1 fun w ↦ A.symm w + c := A.symm.contDiff.add contDiff_const
  let F := T.toOpenPartialHomeomorph.trans e
  have hFcoe : ⇑F = e ∘ fun z ↦ A (z - c) := rfl
  have hFsrc : ∀ z, z ∈ F.source ↔ A (z - c) ∈ e.source := fun z ↦ by simp [F, T]
  refine ⟨F, hFsrc, fun z hz ↦ ?_, fun a ha ↦ ?_, fun z hz v ↦ ?_⟩
  · rw [hFcoe]
    exact (he _ ((hFsrc z).1 hz)).comp z hTc.contDiffAt
  · rw [OpenPartialHomeomorph.trans_target] at ha
    rw [OpenPartialHomeomorph.coe_trans_symm]
    exact hTsc.contDiffAt.comp a (hes a ha.1)
  · have hw := (hFsrc z).1 hz
    have hFd : fderiv ℝ F z = (fderiv ℝ e (A (z - c))).comp (A : ℂ →L[ℝ] ℂ) := by
      rw [hFcoe]
      exact ((((he _ hw).differentiableAt one_ne_zero).hasFDerivAt).comp z (hT z)).fderiv
    rw [hFd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hJ z hw, hK _ hw]

/-! ### Fields equal to `i` at the origin -/

/-- The Beltrami coefficient `ν u = (i - K u 1) / (conj (K u 1) - i)` of a `C¹` field `K` of
complex structures with `K 0 = i` is `1/2`-Hölder near `0`, and conjugates `K u` to `i` there. -/
private theorem exists_holderOnWith_coefficient {K : ℂ → ℂ →L[ℝ] ℂ} (hK : ContDiffAt ℝ 1 K 0)
    (hsq : ∀ᶠ u in 𝓝 0, ∀ v, K u (K u v) = -v) (hK0 : K 0 1 = I) :
    ∃ ρ > 0, ∃ C : ℝ≥0,
      HolderOnWith C (1 / 2) (fun u ↦ (I - K u 1) / (conj (K u 1) - I)) (ball 0 ρ) ∧
      ∀ u ∈ ball (0 : ℂ) ρ, ∀ v, linearMap ((I - K u 1) / (conj (K u 1) - I)) (K u v) =
        I * linearMap ((I - K u 1) / (conj (K u 1) - I)) v := by
  set b : ℂ → ℂ := fun u ↦ K u 1
  set ν : ℂ → ℂ := fun u ↦ (I - b u) / (conj (b u) - I)
  have hbc : ContDiffAt ℝ 1 b 0 := hK.clm_apply contDiffAt_const
  have hν0 : ν 0 = 0 := by simp [ν, b, hK0]
  -- `ν` is `C¹` near `0`, hence Lipschitz there.
  have hνc : ContDiffAt ℝ 1 ν 0 := by
    have hden : ContDiffAt ℝ 1 (fun u ↦ conj (b u) - I) 0 :=
      (Complex.conjCLE.contDiff.contDiffAt.comp 0 hbc).sub contDiffAt_const
    have hden0 : conj (b 0) - I ≠ 0 := by
      rw [show b 0 = I from hK0, conj_I]
      norm_num [Complex.ext_iff]
    convert (contDiffAt_const (c := I)).sub hbc |>.mul (hden.inv hden0) using 1
    ext u
    simp [ν, div_eq_mul_inv]
  obtain ⟨L, t, ht, hL⟩ := hνc.exists_lipschitzOnWith
  have hgood : ∀ᶠ u in 𝓝 (0 : ℂ), u ∈ t ∧ (∀ v, K u (K u v) = -v) ∧ b u ≠ -I :=
    (show ∀ᶠ u in 𝓝 (0 : ℂ), u ∈ t from ht).and (hsq.and (hbc.continuousAt.eventually_ne
      (by rw [show b 0 = I from hK0]; norm_num [Complex.ext_iff])))
  obtain ⟨ρ, hρ, hρgood⟩ := Metric.eventually_nhds_iff_ball.1 hgood
  -- A Lipschitz function vanishing at `0` is bounded on a ball, hence Hölder there.
  have hνL : LipschitzOnWith L ν (ball 0 ρ) := hL.mono fun u hu ↦ (hρgood u hu).1
  have hνb : ∀ u ∈ ball (0 : ℂ) ρ, ‖ν u‖ ≤ ((L * ρ.toNNReal : ℝ≥0) : ℝ) := by
    intro u hu
    have h := hνL.dist_le_mul u hu 0 (mem_ball_self hρ)
    rw [hν0, dist_zero_right, dist_zero_right] at h
    refine h.trans ?_
    push_cast
    rw [Real.coe_toNNReal _ hρ.le]
    exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hu).le L.coe_nonneg
  refine ⟨ρ, hρ, _, hνL.holderOnWith_of_norm_le hνb (by norm_num), fun u hu v ↦ ?_⟩
  obtain ⟨-, hKsq, hbne⟩ := hρgood u hu
  exact linearMap_apply_eq_I_mul hKsq (div_mul_conj_sub_I hbne) v

/-- **Isothermal charts at a point where the field is `i`, after rescaling.** If `K` is a `C¹`
field of complex structures near `0` with `K 0 = i`, then for some `ε > 0` the rescaled field
`w ↦ K (ε w)` has a `C¹` isothermal chart at `0`, with `C¹` inverse. -/
private theorem exists_isothermal_chart_rescale {K : ℂ → ℂ →L[ℝ] ℂ} (hK : ContDiffAt ℝ 1 K 0)
    (hsq : ∀ᶠ u in 𝓝 0, ∀ v, K u (K u v) = -v) (hK0 : K 0 1 = I) :
    ∃ ε > (0 : ℝ), ∃ e : OpenPartialHomeomorph ℂ ℂ, 0 ∈ e.source ∧
      (∀ w ∈ e.source, ContDiffAt ℝ 1 e w) ∧ (∀ w ∈ e.target, ContDiffAt ℝ 1 e.symm w) ∧
      ∀ w ∈ e.source, ∀ v, fderiv ℝ e w (K (ε • w) v) = I * fderiv ℝ e w v := by
  obtain ⟨ρ, hρ, C', hνH, hνK⟩ := exists_holderOnWith_coefficient hK hsq hK0
  set ν : ℂ → ℂ := fun u ↦ (I - K u 1) / (conj (K u 1) - I)
  have hν0 : ν 0 = 0 := by simp [ν, hK0]
  have hα0 : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ≥0) < 1 := by
    rw [← NNReal.coe_lt_coe]
    norm_num
  -- The planar Beltrami chart on the disc of radius `2`, for the coefficient `χ w ν (ε w)`.
  obtain ⟨δ, hδ, C, hchart⟩ := exists_isComplexLinear_chart hα0 hα1 (0 : ℂ) (r := 2) two_pos
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨ε, ⟨⟨f, hf, hfχ, hfδ⟩, hερ⟩, hε⟩ :=
    ((((eventually_exists_holderSpace_cutoff_rescale hα0 hα1.le hρ hνH hν0 χ.contDiff
      χ.hasCompactSupport (lt_min hδ one_pos)).and (ball_mem_nhds (0 : ℝ) hρ)).filter_mono
        nhdsWithin_le_nhds).and self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).exists
  rw [χ.tsupport_eq] at hf
  have hf1 : ∀ w, ‖f w‖ < 1 := fun w ↦
    (HolderSpace.norm_apply_le f w).trans_lt (hfδ.trans_le (min_le_right _ _))
  set Jf : ℂ → AlmostComplexStructure ℂ := fun w ↦ (coefficientEquiv.symm ⟨f w, hf1 w⟩).val
  obtain ⟨h, -, -, -, -, -, -, -, -, hφC1, -, -, hφlin, e, he, he0, hesrc, hes⟩ :=
    hchart Jf (fun w _ ↦ (coefficientEquiv.symm ⟨f w, hf1 w⟩).property) f hf
      (fun w _ ↦ by simp [Jf]) (hfδ.trans_le (min_le_left _ _))
  rw [← he] at hφC1 hφlin
  -- On the unit disc, the structure with coefficient `f w = ν (ε w)` is `K (ε w)`.
  have hJfK : ∀ w ∈ ball (0 : ℂ) 1, ∀ v, (Jf w).toLinearMap v = K (ε • w) v := by
    intro w hw v
    have hu : ε • w ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff, norm_smul]
      calc ‖ε‖ * ‖w‖ ≤ ‖ε‖ * 1 := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hw).le
            (norm_nonneg _)
        _ < ρ := by simpa using hερ
    have hfw : (f w : ℂ) = ν (ε • w) := by
      rw [hfχ, χ.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp hw).le),
        one_smul]
    simp only [Jf, coefficientEquiv_symm_apply]
    rw [ContinuousLinearEquiv.symm_apply_eq, linearEquiv_apply, linearEquiv_apply]
    have hlin := hνK _ hu v
    simp only [linearMap_apply] at hlin
    simp only [hfw, ν]
    rw [hlin]
  -- Restrict the chart to the unit disc.
  refine ⟨ε, hε, e.restrOpen (ball 0 1) isOpen_ball, ⟨he0, mem_ball_self one_pos⟩,
    fun w hw ↦ ?_, fun w hw ↦ ?_, fun w hw v ↦ ?_⟩
  · exact hφC1.contDiffAt (isOpen_ball.mem_nhds (ball_subset_ball (by norm_num) (hesrc hw.1)))
  · exact hes w (by simpa using hw : w ∈ e.target ∧ _).1
  · have h := (hφlin w (ball_subset_closedBall (hesrc hw.1))).apply v
    rw [OpenPartialHomeomorph.coe_restrOpen, ← hJfK w hw.2 v]
    simpa [AlmostComplexStructure.ofComplexModule_apply] using h

/-! ### Isothermal charts -/

/-- **Isothermal coordinates on the plane.** Let `J` be a field of real-linear endomorphisms of the
plane which is `C¹` at `z₀` and squares to `-1` near `z₀`. Then there is an open partial
homeomorphism `e` of the plane, with `z₀` in its source, which is `C¹` on its source with `C¹`
inverse on its target and whose derivative carries `J` to multiplication by `i` at every point of
its source: `J = i` in the chart `e`. -/
theorem exists_isothermal_chart {J : ℂ → ℂ →L[ℝ] ℂ} {z₀ : ℂ} (hJ : ContDiffAt ℝ 1 J z₀)
    (hsq : ∀ᶠ z in 𝓝 z₀, ∀ v, J z (J z v) = -v) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ e.source ∧ (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  /- In the coordinates `u = B⁻¹ (z - z₀)`, where `B` carries `i` to `J z₀`, the field becomes
  `K u = B⁻¹ ∘ J (z₀ + B u) ∘ B`, with `K 0 = i`. -/
  obtain ⟨B, hB⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul
    (ContinuousLinearMap.ext hsq.self_of_nhds)
  set K : ℂ → ℂ →L[ℝ] ℂ :=
    fun u ↦ (B.symm : ℂ →L[ℝ] ℂ).comp ((J (z₀ + B u)).comp (B : ℂ →L[ℝ] ℂ))
  have hKc : ContDiffAt ℝ 1 K 0 := by
    have hJ₀ : ContDiffAt ℝ 1 J (z₀ + B 0) := by simpa using hJ
    exact contDiffAt_const.clm_comp
      ((hJ₀.comp 0 (contDiffAt_const.add B.contDiff.contDiffAt)).clm_comp contDiffAt_const)
  have hKsq : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ v, K u (K u v) = -v := by
    have hT : Tendsto (fun u : ℂ ↦ z₀ + B u) (𝓝 0) (𝓝 z₀) :=
      (show Continuous (fun u : ℂ ↦ z₀ + B u) by fun_prop).tendsto' 0 z₀ (by simp)
    filter_upwards [hT.eventually hsq] with u hu v
    simp [K, hu]
  /- After rescaling by `ε`, `K` has an isothermal chart `e` at `0`; composing it with
  `z ↦ ε⁻¹ B⁻¹ (z - z₀)` gives the chart of `J`. -/
  obtain ⟨ε, hε, e, he0, he, hes, heK⟩ := exists_isothermal_chart_rescale hKc hKsq
    (by simpa [K] using congr(B.symm ($hB 1)))
  obtain ⟨F, hFsrc, hF, hFs, hFJ⟩ := exists_isothermal_chart_comp_affine (J := J)
    (K := fun w ↦ K (ε • w)) he hes heK
    (B.symm.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 (ε⁻¹ : ℝ) (inv_ne_zero hε.ne'))))
    z₀ fun z _ v ↦ by
      simp only [K, ContinuousLinearEquiv.trans_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def,
        Units.val_mk0, map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
        mul_inv_cancel₀ hε.ne', one_smul, add_sub_cancel]
  exact ⟨F, (hFsrc z₀).2 (by simpa using he0), hF, hFs, hFJ⟩

end TauCeti.Beltrami
