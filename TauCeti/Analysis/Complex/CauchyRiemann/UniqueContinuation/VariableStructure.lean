/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
public import TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy

/-!
# Unique continuation for classical solutions with a variable complex structure

Let `ξ` be a map of class `C¹` on an open set `Ω ⊆ ℂ` solving the linear Cauchy–Riemann equation

`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`

for a field `J` of real-linear complex structures, `J(z)² = -1`, of class `C¹`, and a measurable,
locally bounded field `C` of real-linear maps. Linearized Floer and Cauchy–Riemann operators along
a map `u` have this form, with `J(z) = J(z, u(z))`, and so does the difference of two solutions of
a nonlinear Floer equation.

The classical similarity principle `TauCeti.hasSimilarityFactorizationAt_of_contDiffOn` treats
the standard structure `J = i`. The standard frame `Φ(z) = ½(1 - J(z) J(z₀)) Φ₁` of
`TauCeti.Analysis.Complex.CauchyRiemann.StandardFrame` satisfies `J(z) Φ(z) = Φ(z) i` and is
invertible near `z₀`; since it is an affine function of `J`, it is of class `C¹`, and so is the
map `η = Φ⁻¹ ξ`. Expanding `ξ = Φ η` by the product rule gives

`∂ₛξ + J ∂ₜξ + C ξ = Φ (∂ₛη + i ∂ₜη + C' η)`,  `C' = Φ⁻¹(∂ₛΦ + J ∂ₜΦ + C Φ)`

(`TauCeti.frameCoeff`), a classical equation for `η` with the standard structure and a measurable,
locally bounded coefficient. Hence `η`, and with it `ξ = Φ η`, has a similarity factorization at
every point of `Ω` (`TauCeti.hasSimilarityFactorizationAt_of_contDiffOn_of_comp_eq_neg_id`), for
`ξ` with values in a finite-dimensional complex normed space.

For values in a finite-dimensional *real* normed space `E`, as for maps into a symplectic vector
space, a real-linear frame `ℂⁿ → E` in which `J(z₀)` is multiplication by `i`
(`ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`) transports
the equation to `ℂⁿ`. Unique continuation follows: on a connected open set, a solution vanishing on
a nonempty open subset vanishes identically
(`TauCeti.eqOn_zero_of_contDiffOn_of_comp_eq_neg_id_of_eqOn_zero`).

## Main results

* `TauCeti.hasSimilarityFactorizationAt_of_contDiffOn_of_comp_eq_neg_id`: the similarity
  factorization of classical solutions for a `C¹` complex structure.
* `TauCeti.eqOn_zero_of_contDiffOn_of_comp_eq_neg_id_of_eqOn_zero`: unique continuation for
  classical solutions with values in a finite-dimensional real normed space.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 and its proof, and Section 2.3 on unique continuation.
-/

public noncomputable section

open Complex ContinuousLinearMap MeasureTheory Metric Set Filter Topology

namespace TauCeti

section Complex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {Ω : Set ℂ} {ξ : ℂ → V} {J C : ℂ → V →L[ℝ] V}

/-- The coefficient `C' = Φ⁻¹(∂ₛΦ + J ∂ₜΦ + C Φ)` of the reduced equation is measurable and
locally bounded on a disc where the frame `Φ` is `C¹` and invertible, `J` is continuous, and `C`
is measurable and locally bounded. -/
private theorem aestronglyMeasurable_frameCoeff_and_bounded {B : Set ℂ} (hB : IsOpen B)
    {Φ : ℂ → V →L[ℝ] V} (hBΩ : B ⊆ Ω) (hΦ : ContDiffOn ℝ 1 Φ B) (hJ : ContinuousOn J B)
    (hu : ∀ z ∈ B, IsUnit (Φ z)) (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M) :
    AEStronglyMeasurable (frameCoeff J C Φ (fderiv ℝ Φ)) (volume.restrict B) ∧
      ∀ z ∈ B, ∃ M, ∀ᶠ w in 𝓝 z, ‖frameCoeff J C Φ (fderiv ℝ Φ) w‖ ≤ M := by
  have hΨ : ContinuousOn (fun z ↦ Ring.inverse (Φ z)) B := fun z hz ↦ by
    have h := NormedRing.inverse_continuousAt (hu z hz).unit
    rw [IsUnit.unit_spec] at h
    exact h.comp_continuousWithinAt (hΦ.continuousOn z hz)
  have hD : ContinuousOn (fderiv ℝ Φ) B := hΦ.continuousOn_fderiv_of_isOpen hB le_rfl
  -- the part `A = ∂ₛΦ + J ∂ₜΦ` of the coefficient that does not involve `C` is continuous
  set A : ℂ → V →L[ℝ] V := fun z ↦ fderiv ℝ Φ z 1 + J z ∘L fderiv ℝ Φ z I
  have hA : ContinuousOn A B :=
    (hD.clm_apply continuousOn_const).add (hJ.clm_comp (hD.clm_apply continuousOn_const))
  have hfc (z : ℂ) : frameCoeff J C Φ (fderiv ℝ Φ) z =
      Ring.inverse (Φ z) ∘L (A z + C z ∘L Φ z) := frameCoeff_def
  have hBm : MeasurableSet B := hB.measurableSet
  refine ⟨?_, fun z hz ↦ ?_⟩
  · have hC : AEStronglyMeasurable C (volume.restrict B) :=
      hCm.mono_measure (Measure.restrict_mono hBΩ le_rfl)
    have hCΦ : AEStronglyMeasurable (fun z ↦ C z ∘L Φ z) (volume.restrict B) := by
      simpa using (compL ℝ V V V).continuous₂.comp_aestronglyMeasurable₂ hC
        (hΦ.continuousOn.aestronglyMeasurable hBm)
    have h := (compL ℝ V V V).continuous₂.comp_aestronglyMeasurable₂
      (hΨ.aestronglyMeasurable hBm) ((hA.aestronglyMeasurable hBm).add hCΦ)
    rw [show frameCoeff J C Φ (fderiv ℝ Φ) = _ from funext hfc]
    simpa only [compL_apply, Pi.add_apply] using h
  · obtain ⟨M, hM⟩ := hCb z (hBΩ hz)
    have hzB : B ∈ 𝓝 z := hB.mem_nhds hz
    refine ⟨(‖Ring.inverse (Φ z)‖ + 1) * ((‖A z‖ + 1) + M * (‖Φ z‖ + 1)), ?_⟩
    have hle {f : ℂ → V →L[ℝ] V} (hf : ContinuousAt f z) : ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ ‖f z‖ + 1 :=
      hf.norm.eventually (Iic_mem_nhds (lt_add_one _))
    filter_upwards [hM, hle (hΨ.continuousAt hzB), hle (hA.continuousAt hzB),
      hle (hΦ.continuousOn.continuousAt hzB)] with w hwC hwΨ hwA hwΦ
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hwC
    rw [hfc]
    refine (opNorm_comp_le _ _).trans (mul_le_mul hwΨ ?_ (norm_nonneg _) (by positivity))
    refine (norm_add_le _ _).trans (add_le_add hwA ?_)
    exact (opNorm_comp_le _ _).trans (mul_le_mul hwC hwΦ (norm_nonneg _) hM0)

/-- **The classical frame reduction.** On an open set `B` where `Φ` is a `C¹` family of
invertible real-linear maps with `J Φ = Φ i`, a `C¹` solution `ξ` of `∂ₛξ + J ∂ₜξ + C ξ = 0` gives
the `C¹` map `η = Φ⁻¹ ξ`, which solves `∂ₛη + i ∂ₜη + C' η = 0` for
`C' = Φ⁻¹(∂ₛΦ + J ∂ₜΦ + C Φ)`. -/
private theorem contDiffOn_and_eq_zero_frameCoeff {B : Set ℂ} (hB : IsOpen B)
    {Φ : ℂ → V →L[ℝ] V} (hΦ : ContDiffOn ℝ 1 Φ B) (hu : ∀ z ∈ B, IsUnit (Φ z))
    (hJΦ : ∀ z ∈ B, J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V))
    (hξ : ContDiffOn ℝ 1 ξ B)
    (heq : ∀ z ∈ B, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0) :
    ContDiffOn ℝ 1 (fun z ↦ Ring.inverse (Φ z) (ξ z)) B ∧ ∀ z ∈ B,
      fderiv ℝ (fun z ↦ Ring.inverse (Φ z) (ξ z)) z 1 +
        I • fderiv ℝ (fun z ↦ Ring.inverse (Φ z) (ξ z)) z I +
        frameCoeff J C Φ (fderiv ℝ Φ) z (Ring.inverse (Φ z) (ξ z)) = 0 := by
  have := FiniteDimensional.completeSpace ℂ V
  have hΨd : ContDiffOn ℝ 1 (fun z ↦ Ring.inverse (Φ z)) B := fun z hz ↦ by
    have h := contDiffAt_ringInverse ℝ (n := 1) (hu z hz).unit
    rw [IsUnit.unit_spec] at h
    exact h.comp_contDiffWithinAt z (hΦ z hz)
  set η : ℂ → V := fun z ↦ Ring.inverse (Φ z) (ξ z)
  have hηd : ContDiffOn ℝ 1 η B := hΨd.clm_apply hξ
  refine ⟨hηd, fun z hz ↦ ?_⟩
  have hzB : B ∈ 𝓝 z := hB.mem_nhds hz
  -- `ξ = Φ η` near `z`, so the product rule computes `dξ` from `dΦ` and `dη`
  have hξη : ξ =ᶠ[𝓝 z] fun w ↦ Φ w (η w) := eventuallyEq_of_mem hzB fun w hw ↦ by
    simpa [η] using (congr($(Ring.mul_inverse_cancel _ (hu w hw)) (ξ w))).symm
  have h := heq z hz
  rw [hξη.fderiv_eq, fderiv_clm_apply ((hΦ.contDiffAt hzB).differentiableAt one_ne_zero)
    ((hηd.contDiffAt hzB).differentiableAt one_ne_zero), hξη.eq_of_nhds] at h
  simp only [add_apply, comp_apply, flip_apply] at h
  refine (ContinuousLinearMap.isUnit_iff_bijective.1 (hu z hz)).1 ?_
  rw [← add_frame_eq (hu z hz) (hJΦ z hz), map_zero]
  simp only [map_add, η] at h ⊢
  convert h using 1
  abel

/-- **The similarity principle for a variable complex structure**, for classical solutions. Let
`ξ` be of class `C¹` on an open set `Ω ⊆ ℂ` and solve `∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`, for a `C¹`
field `J` of real-linear maps with `J(z)² = -1` and a measurable, locally bounded field `C` of
real-linear maps of a finite-dimensional complex normed space `V`. Then `ξ` has a similarity
factorization at every point of `Ω`: near `z₀` it is `Φ σ`, with `Φ` continuous and invertible at
`z₀` and `σ` holomorphic. -/
theorem hasSimilarityFactorizationAt_of_contDiffOn_of_comp_eq_neg_id (hΩ : IsOpen Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨Φ₁, hΦ₁⟩ := (J z₀).exists_continuousLinearEquiv_comp_eq_comp_I_smul (hJsq z₀ hz₀)
  set Φ := standardFrame J z₀ Φ₁
  obtain ⟨r, hr, hrΩ, hu⟩ :=
    exists_ball_isUnit_standardFrame (Φ₁ := Φ₁) hΩ hz₀ hJ.continuousOn (hJsq z₀ hz₀)
  set B := ball z₀ r
  have hΦB : ContDiffOn ℝ 1 Φ B := (contDiffOn_standardFrame hJ).mono hrΩ
  obtain ⟨hηd, heqη⟩ := contDiffOn_and_eq_zero_frameCoeff isOpen_ball hΦB hu
    (fun z hz ↦ comp_standardFrame (hJsq z (hrΩ hz)) (hJsq z₀ hz₀) hΦ₁) (hξ.mono hrΩ)
    fun z hz ↦ heq z (hrΩ hz)
  have hξη : EqOn ξ (fun z ↦ Φ z (Ring.inverse (Φ z) (ξ z))) B := fun z hz ↦ by
    simpa using (congr($(Ring.mul_inverse_cancel _ (hu z hz)) (ξ z))).symm
  obtain ⟨hC'm, hC'b⟩ := aestronglyMeasurable_frameCoeff_and_bounded isOpen_ball hrΩ hΦB
    (hJ.continuousOn.mono hrΩ) hu hCm hCb
  have hfac := (hasSimilarityFactorizationAt_of_contDiffOn isOpen_ball hηd hC'm hC'b heqη
    (mem_ball_self hr)).clm_apply ((hΦB.continuousOn).continuousAt (ball_mem_nhds z₀ hr))
      (isUnit_standardFrame_self (hJsq z₀ hz₀))
  obtain ⟨Φ', σ, hΦ', hΦ'₀, hσ, hΦσ⟩ := hasSimilarityFactorizationAt_iff.1 hfac
  refine hasSimilarityFactorizationAt_iff.2 ⟨Φ', σ, hΦ', hΦ'₀, hσ, ?_⟩
  filter_upwards [ball_mem_nhds z₀ hr, hΦσ] with z hz hzσ
  exact (hξη hz).trans hzσ

end Complex

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Set ℂ} {ξ : ℂ → E} {J C : ℂ → E →L[ℝ] E}

/-- **Unique continuation for a variable complex structure.** Let `ξ` be of class `C¹` on a
connected open set `Ω ⊆ ℂ`, with values in a finite-dimensional real normed space `E`, and solve
`∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`, for a `C¹` field `J` of real-linear maps with `J(z)² = -1` and a
measurable, locally bounded field `C` of real-linear maps. If `ξ` vanishes on a nonempty open
subset of `Ω`, it vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_comp_eq_neg_id_of_eqOn_zero (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hξ : ContDiffOn ℝ 1 ξ Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ E)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0) {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  obtain ⟨z₀, hz₀⟩ := hUne
  -- a real-linear frame `ℂⁿ → E` transports the equation to a complex coordinate space
  obtain ⟨n, Φ₁, -⟩ :=
    ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul (J z₀)
      (hJsq z₀ (hUΩ hz₀))
  set W := EuclideanSpace ℂ (Fin n)
  set T : (E →L[ℝ] E) ≃L[ℝ] (W →L[ℝ] W) := Φ₁.symm.arrowCongr Φ₁.symm
  have hT (A : E →L[ℝ] E) (w : W) : T A w = Φ₁.symm (A (Φ₁ w)) := by simp [T]
  set ξ' : ℂ → W := fun z ↦ Φ₁.symm (ξ z)
  have hfd (z : ℂ) : fderiv ℝ ξ' z = (Φ₁.symm : E →L[ℝ] W) ∘L fderiv ℝ ξ z :=
    Φ₁.symm.comp_fderiv
  have hξ' : ContDiffOn ℝ 1 ξ' Ω := Φ₁.symm.contDiff.comp_contDiffOn hξ
  have hJ' : ContDiffOn ℝ 1 (fun z ↦ T (J z)) Ω := T.contDiff.comp_contDiffOn hJ
  have hJsq' : ∀ z ∈ Ω, T (J z) ∘L T (J z) = -ContinuousLinearMap.id ℝ W := fun z hz ↦ by
    have h (v : E) : J z (J z v) = -v := congr($(hJsq z hz) v)
    exact ContinuousLinearMap.ext fun w ↦ by simp [hT, h]
  have hCm' : AEStronglyMeasurable (fun z ↦ T (C z)) (volume.restrict Ω) :=
    T.continuous.comp_aestronglyMeasurable hCm
  have hCb' : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖T (C w)‖ ≤ M := fun z hz ↦ by
    obtain ⟨M, hM⟩ := hCb z hz
    refine ⟨‖(T : (E →L[ℝ] E) →L[ℝ] (W →L[ℝ] W))‖ * M, hM.mono fun w hw ↦ ?_⟩
    exact ((T : (E →L[ℝ] E) →L[ℝ] (W →L[ℝ] W)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
  have heq' : ∀ z ∈ Ω, fderiv ℝ ξ' z 1 + T (J z) (fderiv ℝ ξ' z I) + T (C z) (ξ' z) = 0 :=
    fun z hz ↦ by
      simp only [hfd, comp_apply, ContinuousLinearEquiv.coe_coe, hT]
      simp only [ξ', ContinuousLinearEquiv.apply_symm_apply, ← map_add, heq z hz, map_zero]
  have hzero : EqOn ξ' 0 Ω := eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero hΩ hΩc
    hξ'.continuousOn (fun z hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn_of_comp_eq_neg_id
      hΩ hξ' hJ' hJsq' hCm' hCb' heq' hz) hU ⟨z₀, hz₀⟩ hUΩ
      (fun z hz ↦ by simp [ξ', h₀ hz])
  intro z hz
  simpa [ξ'] using hzero hz

end Real

end TauCeti
