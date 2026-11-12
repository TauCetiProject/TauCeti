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

Let `J` be a field of almost complex structures on the plane, tame at `c` and of class `C¹` near
`c`. There is a local chart `e` of the plane around `c`, of class `C¹` with `C¹` inverse, whose
differential carries `J` to multiplication by `i` at every point of its source
(`TauCeti.Beltrami.exists_isothermalChart_of_contDiffAt`).

The planar Beltrami chart `TauCeti.Beltrami.exists_isComplexLinear_chart` needs a coefficient
that is small in the Hölder norm. The coefficient `μ_J` of `J` is reduced to this case in three
steps, following McDuff–Salamon, Appendix E.

* *Normalization.* The real-linear map `A = linearEquiv μ_J(c)` carries `J c` to the standard
  structure (`TauCeti.Beltrami.exists_transport_eq_std_and_contDiffAt`), so the coefficient `μ₁`
  of the structure `J` read through `w ↦ A (w - c)` vanishes at `0`.
* *Rescaling and cutoff.* Rescaling by `ε` does not change the structures, and with a fixed cutoff
  `χ`, equal to `1` on the unit disc and vanishing off the disc of radius `2`, the coefficient
  `ν(z) = χ(z) μ₁(ε z)` is small in Hölder norm for `ε` small, because `μ₁` is Lipschitz near `0`
  and vanishes there (`TauCeti.eventually_exists_holderSpace_cutoff_rescale`).
* *Inversion.* For `ε` small the Beltrami solution has real derivative within `C ‖ν‖ < 1` of the
  identity on the disc, so the chart has an invertible derivative and a `C¹` inverse
  (`TauCeti.Beltrami.exists_isComplexLinear_chart_contDiffAt_symm`).

Restricting the chart of `ν` to the unit disc, where `ν` is the coefficient of the rescaled
structure, and composing it with `w ↦ ε⁻¹ A (w - c)` gives the chart of `J`
(`TauCeti.Beltrami.exists_isComplexLinear_chart_comp_affine`).

## Main results

* `TauCeti.Beltrami.exists_transport_eq_std_and_contDiffAt`: a `Cⁿ` structure tame at `c` is
  carried to the standard structure at `c` by a real-linear automorphism, and stays `Cⁿ` when read
  through it.
* `TauCeti.Beltrami.exists_isComplexLinear_chart_comp_affine`: precomposing a `Cⁿ` chart with
  `Cⁿ` inverse, in which `J'` is standard, with an affine equivalence carrying `J` to `J'` gives
  such a chart for `J`.
* `TauCeti.Beltrami.exists_isothermalChart_of_contDiffAt`: a `C¹` structure tame at `c` has a
  `C¹` chart at `c`, with `C¹` inverse, in which it is the standard structure.

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

/-- **Normalization at a point.** Let `J` be a field of almost complex structures on the plane,
tame at `c`, with `z ↦ J z` of class `Cⁿ` at `c` in the operator norm. There is a real-linear
automorphism `A` of the plane carrying `J c` to the standard structure, and the field
`w ↦ J (c + A⁻¹ w)` transported by `A` is of class `Cⁿ` at `0`. -/
theorem exists_transport_eq_std_and_contDiffAt {n : WithTop ℕ∞}
    {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ} (hJ : stdComplexSymplecticForm.Tames (J c))
    (hJs : ContDiffAt ℝ n (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) c) :
    ∃ A : ℂ ≃L[ℝ] ℂ,
      (J c).transport A.toLinearEquiv = AlmostComplexStructure.ofComplexModule ℂ ∧
      ContDiffAt ℝ n (fun w ↦ LinearMap.toContinuousLinearMap
        ((J (c + A.symm w)).transport A.toLinearEquiv).toLinearMap) 0 := by
  refine ⟨_, transport_linearEquiv_eq_std (J c) hJ, ?_⟩
  set A := linearEquiv (coefficientEquiv ⟨J c, hJ⟩).val _
  have hcl : (fun w ↦ LinearMap.toContinuousLinearMap
      ((J (c + A.symm w)).transport A.toLinearEquiv).toLinearMap) = fun w ↦
      (A : ℂ →L[ℝ] ℂ) ∘L LinearMap.toContinuousLinearMap (J (c + A.symm w)).toLinearMap ∘L
        (A.symm : ℂ →L[ℝ] ℂ) := by
    funext w
    ext v
    simp [AlmostComplexStructure.transport_toLinearMap, LinearEquiv.conj_apply]
  rw [hcl]
  have hin : ContDiffAt ℝ n (fun w : ℂ ↦ c + A.symm w) 0 :=
    contDiffAt_const.add A.symm.contDiff.contDiffAt
  have hJs' : ContDiffAt ℝ n (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap)
      (c + A.symm 0) := by
    simpa using hJs
  have hJc : ContDiffAt ℝ n
      (fun w ↦ LinearMap.toContinuousLinearMap (J (c + A.symm w)).toLinearMap) 0 :=
    ContDiffAt.comp (g := fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap)
      (f := fun w ↦ c + A.symm w) (0 : ℂ) hJs' hin
  exact contDiffAt_const.clm_comp (hJc.clm_comp contDiffAt_const)

/-- **Precomposing a chart with an affine equivalence.** Let `e` be an open partial homeomorphism
of the plane, of class `Cⁿ` on its source with `Cⁿ` inverse on its target, whose real differential
carries `J' z` to multiplication by `i` at every point `z` of its source. If the real-linear
automorphism `B` carries `J z` to `J' (B (z - c))` whenever `B (z - c)` lies in the source of `e`,
then `z ↦ e (B (z - c))` is an open partial homeomorphism with the same properties for `J`. -/
theorem exists_isComplexLinear_chart_comp_affine {n : WithTop ℕ∞}
    {J J' : ℂ → AlmostComplexStructure ℂ} (e : OpenPartialHomeomorph ℂ ℂ) (B : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (he : ∀ z ∈ e.source, ContDiffAt ℝ n e z) (hes : ∀ z ∈ e.target, ContDiffAt ℝ n e.symm z)
    (hJ' : ∀ z ∈ e.source, IsComplexLinear (J' z).toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ e z).toLinearMap)
    (hB : ∀ z, B (z - c) ∈ e.source → ∀ v, B (J z v) = J' (B (z - c)) (B v)) :
    ∃ e' : OpenPartialHomeomorph ℂ ℂ, (∀ z, z ∈ e'.source ↔ B (z - c) ∈ e.source) ∧
      (∀ z, e' z = e (B (z - c))) ∧
      (∀ z ∈ e'.source, ContDiffAt ℝ n e' z) ∧ (∀ z ∈ e'.target, ContDiffAt ℝ n e'.symm z) ∧
      ∀ z ∈ e'.source, IsComplexLinear (J z).toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ e' z).toLinearMap := by
  let S : OpenPartialHomeomorph ℂ ℂ :=
    ((Homeomorph.subRight c).trans B.toHomeomorph).toOpenPartialHomeomorph
  have hS : ⇑S = fun w ↦ B (w - c) := by
    funext w
    simp [S]
  have hSs : ⇑S.symm = fun z ↦ B.symm z + c := by
    funext z
    simp [S]
  have hSe : ∀ z, (S.trans e) z = e (B (z - c)) := fun z ↦ by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hS]
  have hsrc : ∀ z, z ∈ (S.trans e).source ↔ B (z - c) ∈ e.source := fun z ↦ by
    rw [OpenPartialHomeomorph.trans_source, hS]
    simp [S]
  refine ⟨S.trans e, hsrc, hSe, fun z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [OpenPartialHomeomorph.coe_trans, hS]
    exact (he _ ((hsrc z).1 hz)).comp z
      (B.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  · rw [OpenPartialHomeomorph.trans_target] at hz
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans, hSs]
    exact (B.symm.contDiff.add contDiff_const).contDiffAt.comp z (hes z hz.1)
  · have hd : fderiv ℝ (S.trans e) z = (fderiv ℝ e (B (z - c))).comp (B : ℂ →L[ℝ] ℂ) := by
      rw [show ⇑(S.trans e) = fun w ↦ (e ∘ B) (w - c) from funext hSe, fderiv_comp_sub,
        B.comp_right_fderiv]
    rw [hd]
    refine isComplexLinear_of_apply fun v ↦ ?_
    have := (hJ' _ ((hsrc z).1 hz)).apply (B v)
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at this ⊢
    rw [hB z ((hsrc z).1 hz)]
    exact this

/-- **Planar isothermal charts.** Let `J` be a field of almost complex structures on the plane,
tame at `c`, with `z ↦ J z` of class `C¹` at `c` in the operator norm. Then there is an open
partial homeomorphism `e` of the plane with `c` in its source and `e c = 0`, of class `C¹` on its
source with `C¹` inverse on its target, whose real differential carries `J z` to multiplication by
`i` at every point `z` of its source. No smallness of the Beltrami coefficient of `J` is
assumed. -/
theorem exists_isothermalChart_of_contDiffAt {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ}
    (hJ : stdComplexSymplecticForm.Tames (J c))
    (hJs : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) c) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e c = 0 ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧ (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, IsComplexLinear (J z).toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ e z).toLinearMap := by
  set J₀ := AlmostComplexStructure.ofComplexModule ℂ
  /- Step 1: normalize at `c`. Read `J` through `w ↦ A (w - c)`, where `A` carries `J c` to the
  standard structure; the coefficient `μ₁` of the new field `J₁` vanishes at `0`. -/
  obtain ⟨A, hA, hJ₁s⟩ := exists_transport_eq_std_and_contDiffAt hJ hJs
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
  obtain ⟨δ, hδ, hchart⟩ := exists_isComplexLinear_chart_contDiffAt_symm (α := 1 / 2)
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
  obtain ⟨e, hce, he0, -, heC, hesC, helin⟩ :=
    hchart J'' (fun z _ ↦ hJ''t z) ν hνmem (fun z _ ↦ hJ''μ z) (hνη.trans_le (min_le_left _ _))
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
  obtain ⟨e', he'src, he'app, he'C, he'sC, he'lin⟩ :=
    exists_isComplexLinear_chart_comp_affine e₁ B c (fun z hz ↦ heC z ((he₁s z).1 hz).1)
      (fun z hz ↦ hesC z hz.1) (fun z hz ↦ helin z ((he₁s z).1 hz).1) hBJ
  refine ⟨e', (he'src c).2 ?_, ?_, he'C, he'sC, he'lin⟩
  · rw [sub_self, map_zero, he₁s]
    exact ⟨hce, mem_ball_self one_pos⟩
  · rw [he'app, sub_self, map_zero]
    exact he0

end TauCeti.Beltrami
