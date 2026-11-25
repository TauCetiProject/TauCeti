/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
import TauCeti.MeasureTheory.Function.RankOne

/-!
# Unique continuation for Cauchy–Riemann differential inequalities

Let `V` be a finite-dimensional real normed space, `Ω ⊆ ℂ` open, `J : ℂ → V →L[ℝ] V` a `C¹`
field of complex structures on `V`, `J(z)² = -1`, and `ξ : ℂ → V` a map of class `C¹` on `Ω`
satisfying the differential inequality

`‖∂ₛξ + J(z) ∂ₜξ‖ ≤ M ‖ξ‖`

near every zero of `ξ` in `Ω`, in the coordinate `z = s + i t`, with a constant `M` that may
depend on the zero. Away from the zeros of `ξ` the inequality holds automatically, because `‖ξ‖`
is bounded below there, so it is not assumed. This is the shape of the equation satisfied by the
difference of two solutions of a nonlinear Cauchy–Riemann equation, such as two pseudoholomorphic
curves or two Floer solutions: the nonlinear terms are only locally Lipschitz, so the difference
solves no linear equation with a prescribed coefficient, but it obeys such an inequality near its
zeros. This file proves that `ξ` has the zero structure of a holomorphic map:

* it vanishes on a connected open `Ω` if it vanishes on a nonempty open subset of `Ω`
  (`TauCeti.eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_le`);
* it vanishes on `Ω` if it vanishes to infinite order at one point of `Ω`
  (`TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO_of_norm_le`);
* otherwise its zeros are isolated
  (`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_le`).

The inequality is turned into a linear equation `∂ₛξ + J ∂ₜξ + C ξ = 0` for the solution-dependent
coefficient `C = -(∂ₛξ + J ∂ₜξ) ξ* / ‖ξ‖²`, the normalized rank-one operator
`TauCeti.rankOneDivNormSq` for an auxiliary Euclidean structure on `V`
(`MeasureTheory.AEStronglyMeasurable.exists_clm_apply_eq`). This coefficient is measurable, sends
`ξ` to `-(∂ₛξ + J ∂ₜξ)`, and is bounded by `M` up to the distortion of the Euclidean norm. The
zero structure then follows from the variable-structure theorems of
`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3: Theorem 2.3.5 and its proof (Step 2, the replacement of a real-linear coefficient
  along the solution) and the unique continuation for pseudoholomorphic curves derived from it.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292 (unique continuation for Floer trajectories).
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Set Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Set ℂ} {J : ℂ → V →L[ℝ] V} {ξ : ℂ → V}

/-- A `C¹` map obeying the differential inequality near its zeros solves a linear Cauchy–Riemann
equation with a measurable, locally bounded coefficient: the regularity the variable-structure
theorems ask for. -/
private theorem exists_coeff_of_norm_le (hΩ : IsOpen Ω) (hJ : ContinuousOn J Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hb : ∀ z ∈ Ω, ξ z = 0 →
      ∃ M, ∀ᶠ w in 𝓝 z, ‖fderiv ℝ ξ w 1 + J w (fderiv ℝ ξ w I)‖ ≤ M * ‖ξ w‖) :
    ∃ C : ℂ → V →L[ℝ] V, AEStronglyMeasurable C (volume.restrict Ω) ∧
      (∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M) ∧
      ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0 := by
  -- The Cauchy–Riemann operator of `ξ`, continuous on `Ω`.
  set D : ℂ → V := fun w ↦ fderiv ℝ ξ w 1 + J w (fderiv ℝ ξ w I)
  have hDc : ContinuousOn D Ω := by
    have hdξ := hξ.continuousOn_fderiv_of_isOpen hΩ le_rfl
    exact (hdξ.clm_apply continuousOn_const).add (hJ.clm_apply (hdξ.clm_apply continuousOn_const))
  -- Away from the zeros of `ξ` the inequality holds automatically, since `‖ξ‖` is bounded below.
  replace hb (z) (hz : z ∈ Ω) : ∃ M, ∀ᶠ w in 𝓝 z, ‖D w‖ ≤ M * ‖ξ w‖ := by
    rcases eq_or_ne (ξ z) 0 with h0 | h0
    · exact hb z hz h0
    have hz' := hΩ.mem_nhds hz
    exact isBigO_iff.1 <| (hDc.continuousAt hz').isBigO (F := ℝ) |>.trans
      ((hξ.continuousOn.continuousAt hz').isTheta (F := ℝ) h0).symm.isBigO
  -- At a zero of `ξ` in `Ω` the inequality forces `D = 0`.
  have hD0 (z) (hz : z ∈ Ω) (h0 : ξ z = 0) : D z = 0 := by
    obtain ⟨M, hM⟩ := hb z hz
    simpa [h0] using hM.self_of_nhds
  -- The rank-one coefficient carrying `ξ` to `-D` on `Ω`.
  obtain ⟨c, hc0, C, hCm, hCx, hCn⟩ := AEStronglyMeasurable.exists_clm_apply_eq (𝕜 := ℝ)
    (y := Ω.indicator (-D)) (x := ξ) (μ := volume.restrict Ω)
    ((hDc.neg.aestronglyMeasurable hΩ.measurableSet).congr
      (indicator_ae_eq_restrict hΩ.measurableSet.nullMeasurableSet).symm)
    (hξ.continuousOn.aestronglyMeasurable hΩ.measurableSet) fun t h0 ↦ by
      by_cases ht : t ∈ Ω
      · simp [indicator_of_mem ht, hD0 t ht h0]
      · exact indicator_of_notMem ht _
  refine ⟨C, hCm, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨M, hM⟩ := hb z hz
    refine ⟨c * |M|, (hM.and (hΩ.mem_nhds hz)).mono fun w ⟨hw, hwΩ⟩ ↦ (hCn w).trans ?_⟩
    gcongr
    rw [indicator_of_mem hwΩ, Pi.neg_apply, norm_neg]
    exact div_le_of_le_mul₀ (norm_nonneg _) (abs_nonneg _)
      (hw.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)))
  · rw [hCx z, indicator_of_mem hz, Pi.neg_apply, add_neg_cancel]

/-- **Unique continuation for a Cauchy–Riemann differential inequality.** On a connected open set
`Ω`, a `C¹` map `ξ` into a finite-dimensional real normed space with
`‖∂ₛξ + J ∂ₜξ‖ ≤ M ‖ξ‖` near every zero of `ξ` in `Ω`, for a `C¹` field `J` of complex
structures, `J(z)² = -1`, that vanishes on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_le (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hb : ∀ z ∈ Ω, ξ z = 0 →
      ∃ M, ∀ᶠ w in 𝓝 z, ‖fderiv ℝ ξ w 1 + J w (fderiv ℝ ξ w I)‖ ≤ M * ‖ξ w‖)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) :
    EqOn ξ 0 Ω := by
  obtain ⟨C, hCm, hCb, heq⟩ := exists_coeff_of_norm_le hΩ hJ.continuousOn hξ hb
  exact eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure hΩ hΩc hJ hJJ hξ hCm hCb heq hU
    hUne hUΩ h₀

/-- **Unique continuation from a zero of infinite order for a Cauchy–Riemann differential
inequality.** On a connected open set `Ω`, a `C¹` map `ξ` into a finite-dimensional real normed
space with `‖∂ₛξ + J ∂ₜξ‖ ≤ M ‖ξ‖` near every zero of `ξ` in `Ω`, for a `C¹` field `J` of
complex structures, `J(z)² = -1`, that vanishes to infinite order at one point of `Ω` vanishes
on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_forall_isBigO_of_norm_le (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hb : ∀ z ∈ Ω, ξ z = 0 →
      ∃ M, ∀ᶠ w in 𝓝 z, ‖fderiv ℝ ξ w 1 + J w (fderiv ℝ ξ w I)‖ ≤ M * ‖ξ w‖)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 Ω := by
  obtain ⟨C, hCm, hCb, heq⟩ := exists_coeff_of_norm_le hΩ hJ.continuousOn hξ hb
  exact eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure hΩ hΩc hJ hJJ hξ hCm hCb heq
    hz₀ h₀

/-- **Isolated zeros for a Cauchy–Riemann differential inequality.** On a connected open set `Ω`,
the zeros of a `C¹` map `ξ` into a finite-dimensional real normed space with
`‖∂ₛξ + J ∂ₜξ‖ ≤ M ‖ξ‖` near every zero of `ξ` in `Ω`, for a `C¹` field `J` of complex
structures, `J(z)² = -1`, that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_le (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hb : ∀ z ∈ Ω, ξ z = 0 →
      ∃ M, ∀ᶠ w in 𝓝 z, ‖fderiv ℝ ξ w 1 + J w (fderiv ℝ ξ w I)‖ ≤ M * ‖ξ w‖)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨C, hCm, hCb, heq⟩ := exists_coeff_of_norm_le hΩ hJ.continuousOn hξ hb
  exact setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure hΩ hΩc hJ hJJ hξ
    hCm hCb heq hne

end TauCeti
