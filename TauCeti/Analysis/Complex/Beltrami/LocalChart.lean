/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Beltrami.Chart
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
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
  identity on the disc, so the chart has an invertible derivative and a `C¹` inverse.

Composing the chart of `ν` with `w ↦ ε⁻¹ A (w - c)` and restricting it to the unit disc, where `ν`
is the coefficient of the rescaled structure, gives the chart of `J`.

## Main results

* `TauCeti.Beltrami.exists_transport_eq_std_and_contDiffAt`: a `C¹` structure tame at `c` is
  carried to the standard structure at `c` by a real-linear automorphism, and stays `C¹` when read
  through it.
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
tame at `c`, with `z ↦ J z` of class `C¹` at `c` in the operator norm. There is a real-linear
automorphism `A` of the plane carrying `J c` to the standard structure, and the field
`w ↦ J (c + A⁻¹ w)` transported by `A` is of class `C¹` at `0`. -/
theorem exists_transport_eq_std_and_contDiffAt {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ}
    (hJ : stdComplexSymplecticForm.Tames (J c))
    (hJs : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) c) :
    ∃ A : ℂ ≃L[ℝ] ℂ,
      (J c).transport A.toLinearEquiv = AlmostComplexStructure.ofComplexModule ℂ ∧
      ContDiffAt ℝ 1 (fun w ↦ LinearMap.toContinuousLinearMap
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
  have hin : ContDiffAt ℝ 1 (fun w : ℂ ↦ c + A.symm w) 0 :=
    contDiffAt_const.add A.symm.contDiff.contDiffAt
  have hJs' : ContDiffAt ℝ 1 (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap)
      (c + A.symm 0) := by
    simpa using hJs
  have hJc : ContDiffAt ℝ 1
      (fun w ↦ LinearMap.toContinuousLinearMap (J (c + A.symm w)).toLinearMap) 0 :=
    ContDiffAt.comp (g := fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap)
      (f := fun w ↦ c + A.symm w) (0 : ℂ) hJs' hin
  exact contDiffAt_const.clm_comp (hJc.clm_comp contDiffAt_const)

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
  /- Step 3: the planar Beltrami chart on the disc of radius `2`, applied to the rescaled cutoff
  coefficient `ν(z) = χ(z) μ₁(ε z)` for `ε` small. -/
  obtain ⟨δ, hδ, Cb, hchart⟩ := exists_isComplexLinear_chart (α := 1 / 2) (by norm_num)
    (by norm_num) 0 (r := 2) two_pos
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  set η : ℝ := min δ (min 1 ((Cb : ℝ) + 1)⁻¹)
  have hη : 0 < η := lt_min hδ (lt_min one_pos (by positivity))
  obtain ⟨ε, ⟨hε, hερ⟩, ν, hνmem, hνapp, hνη⟩ := ((eventually_mem_nhdsWithin.and
    ((eventually_lt_nhds hρ).filter_mono nhdsWithin_le_nhds)).and
    ((eventually_exists_holderSpace_cutoff_rescale (by norm_num) (by norm_num) hρ hμ₁H hμ₁0
      χ.contDiff χ.hasCompactSupport hη).filter_mono nhdsWithin_le_nhds) :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).exists
  rw [χ.tsupport_eq] at hνmem
  have hν1 : ∀ z, ‖ν z‖ < 1 := fun z ↦
    (HolderSpace.norm_apply_le _ z).trans_lt
      (hνη.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hCbν : Cb * ‖ν‖ < 1 := by
    have h1 : ‖ν‖ ≤ ((Cb : ℝ) + 1)⁻¹ := hνη.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc (Cb : ℝ) * ‖ν‖ ≤ Cb * ((Cb : ℝ) + 1)⁻¹ := by gcongr
      _ < 1 := by
        rw [← div_eq_mul_inv, div_lt_one (by positivity)]
        linarith
  let J'' : ℂ → AlmostComplexStructure ℂ := fun z ↦ (coefficientEquiv.symm ⟨ν z, hν1 z⟩).val
  have hJ''t : ∀ z, stdComplexSymplecticForm.Tames (J'' z) := fun z ↦
    (coefficientEquiv.symm _).property
  have hJ''μ : ∀ z, ν z = (coefficientEquiv ⟨J'' z, hJ''t z⟩).val := fun z ↦ by
    simp [J'']
  obtain ⟨h, -, -, hψC1, -, hnear, -, -, ha, hφC1, hφ0, -, hφlin, e, he, hce, hesub⟩ :=
    hchart J'' (fun z _ ↦ hJ''t z) ν hνmem (fun z _ ↦ hJ''μ z)
      (hνη.trans_le (min_le_left _ _))
  set ψ := cauchySolution h
  set φ := normalizedChart ψ 0
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
  /- Step 4: restrict the chart to the unit disc. On the disc `dψ` is within `Cb ‖ν‖ < 1` of the
  identity, so `dφ` is invertible and the restricted chart has a `C¹` inverse. -/
  have hsub2 : closedBall (0 : ℂ) 2 ⊆ ball 0 (2 + 1) := closedBall_subset_ball (by norm_num)
  have hφd : ∀ z ∈ closedBall (0 : ℂ) 2, ContDiffAt ℝ 1 φ z := fun z hz ↦
    hφC1.contDiffAt (isOpen_ball.mem_nhds (hsub2 hz))
  let e₁ := e.restrOpen (ball (0 : ℂ) 1) isOpen_ball
  have he₁ : ⇑e₁ = φ := by rw [OpenPartialHomeomorph.coe_restrOpen, he]
  have he₁s : e₁.source ⊆ ball (0 : ℂ) 1 ∩ closedBall 0 2 := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun z hz ↦ ⟨hz.2, ball_subset_closedBall (hesub hz.1)⟩
  have he₁C : ContDiffOn ℝ 1 e₁ e₁.source := fun z hz ↦ by
    rw [he₁]
    exact (hφd _ (he₁s hz).2).contDiffWithinAt
  have he₁symm : ContDiffOn ℝ 1 e₁.symm e₁.target :=
    e₁.contDiffOn_symm_of_isInvertible_fderiv he₁C fun z hz ↦ by
      rw [he₁]
      exact isInvertible_fderiv_normalizedChart ha ((hnear z (he₁s hz).2).trans_lt hCbν)
  /- Step 5: compose with `w ↦ ε⁻¹ A (w - c)`. -/
  let B : ℂ ≃L[ℝ] ℂ := A.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 ε⁻¹ (inv_ne_zero hε.ne')))
  have hB : ∀ v, B v = ε⁻¹ • A v := fun v ↦ by simp [B, Units.smul_def]
  let S : OpenPartialHomeomorph ℂ ℂ :=
    ((Homeomorph.subRight c).trans B.toHomeomorph).toOpenPartialHomeomorph
  have hSf : ⇑S = fun w ↦ B (w - c) := by
    funext w
    simp [S]
  have hSsf : ⇑S.symm = fun z ↦ B.symm z + c := by
    funext z
    simp [S]
  have hS : ∀ w, S w = B (w - c) := fun w ↦ by rw [hSf]
  have hSd : ∀ w, HasFDerivAt S (B : ℂ →L[ℝ] ℂ) w := fun w ↦ by
    rw [hSf]
    exact B.hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const c)
  have hSc : ContDiff ℝ 1 S := by
    rw [hSf]
    exact B.contDiff.comp (contDiff_id.sub contDiff_const)
  have hSsc : ContDiff ℝ 1 S.symm := by
    rw [hSsf]
    exact B.symm.contDiff.add contDiff_const
  refine ⟨S.trans e₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    refine ⟨mem_univ c, ?_⟩
    rw [mem_preimage, hS, sub_self, map_zero, OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hce, mem_ball_self one_pos⟩
  · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hS, sub_self, map_zero, he₁]
    exact normalizedChart_self ψ 0
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    rw [OpenPartialHomeomorph.coe_trans, he₁]
    exact (hφd _ (he₁s hz.2).2).comp z hSc.contDiffAt
  · intro z hz
    rw [OpenPartialHomeomorph.trans_target] at hz
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans]
    exact hSsc.contDiffAt.comp z ((he₁symm z hz.1).contDiffAt (e₁.open_target.mem_nhds hz.1))
  · intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hSz := he₁s hz.2
    have hd : HasFDerivAt (S.trans e₁) ((fderiv ℝ φ (S z)).comp (B : ℂ →L[ℝ] ℂ)) z := by
      rw [OpenPartialHomeomorph.coe_trans, he₁]
      exact ((hφd _ hSz.2).differentiableAt one_ne_zero).hasFDerivAt.comp z (hSd z)
    rw [hd.fderiv]
    -- `B` carries `J z` to `J'' (S z)`.
    have hBJ : ∀ v, B (J z v) = J'' (S z) (B v) := fun v ↦ by
      have hεS : ε • S z = A (z - c) := by
        rw [hS, hB, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
      have hzc : c + A.symm (A (z - c)) = z := by
        rw [ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel]
      rw [hJ''J₁ _ hSz.1, hεS, hB, hB, map_smul, hJ₁, hzc]
    refine isComplexLinear_of_apply fun v ↦ ?_
    have := (hφlin (S z) hSz.2).apply (B v)
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    rw [hBJ]
    exact this

end TauCeti.Beltrami
