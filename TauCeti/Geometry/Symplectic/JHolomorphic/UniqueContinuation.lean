/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line

/-!
# Unique continuation for linear Cauchy–Riemann equations on the standard line

Let `ξ` be a map of class `C¹` on an open set `Ω` of the standard complex line `ℝ × ℝ`, with
values in a finite-dimensional real normed space `V`, solving the linear Cauchy–Riemann equation

`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`

in the coordinates `(s, t)`, for a `C¹` field `J` of real-linear complex structures,
`J(z)² = -1`, and a measurable, locally bounded field `C` of real-linear maps. Linearized
Cauchy–Riemann and Floer operators along a map, and their formal adjoints, have this form.

In the complex coordinate `Complex.equivRealProdCLM` this is the equation of
`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure`, so on a connected
`Ω` the unique continuation theorems proved there apply: a solution vanishing to infinite order
at one point of `Ω`, or on a nonempty open subset of `Ω`, vanishes on `Ω`, and the zeros of a
solution that is not identically zero form a discrete subset of `Ω`.

## Main results

* `TauCeti.eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_forall_isBigO`: unique continuation
  from a zero of infinite order.
* `TauCeti.eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_eqOn_zero`: unique continuation from
  a nonempty open subset.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_prod_of_comp_eq_neg_id`: isolated
  zeros.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (unique continuation).
-/

public section

open Complex ContinuousLinearMap MeasureTheory Set Filter Topology Asymptotics

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Set (ℝ × ℝ)} {ξ : ℝ × ℝ → V} {J C : ℝ × ℝ → V →L[ℝ] V}

/-- **Unique continuation from a zero of infinite order in the coordinates `(s, t)`.** Let `ξ` be
of class `C¹` on a connected open set `Ω ⊆ ℝ × ℝ`, with values in a finite-dimensional real normed
space `V`, and solve `∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`, for a `C¹` field `J` of real-linear maps with
`J² = -1` and a measurable, locally bounded field `C` of real-linear maps. If
`ξ = O(‖z - z₀‖ⁿ)` near a point `z₀ ∈ Ω` for every `n`, then `ξ` vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_forall_isBigO (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hξ : ContDiffOn ℝ 1 ξ Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
      C z (ξ z) = 0)
    {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) :
    EqOn ξ 0 Ω := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  have hmaps : MapsTo e (e ⁻¹' Ω) Ω := mapsTo_preimage _ _
  have hΩc' : IsPreconnected (e ⁻¹' Ω) := by
    rw [← e.image_symm_eq_preimage]
    exact hΩc.image _ e.symm.continuous.continuousOn
  have he' : MeasurePreserving e (volume.restrict (e ⁻¹' Ω)) (volume.restrict Ω) :=
    volume_preserving_equiv_real_prod.restrict_preimage hΩ.measurableSet
  -- `‖e y - z₀‖ = O(y - e⁻¹ z₀)`, so `ξ ∘ e` vanishes to infinite order at `e⁻¹ z₀`
  have hlin : (fun y : ℂ ↦ ‖e y - z₀‖) =O[𝓝 (e.symm z₀)] fun y ↦ y - e.symm z₀ := by
    simpa [map_sub] using
      ((e : ℂ →L[ℝ] ℝ × ℝ).isBigO_comp (fun y ↦ y - e.symm z₀) (𝓝 (e.symm z₀))).norm_left
  have hT : Tendsto e (𝓝 (e.symm z₀)) (𝓝 z₀) := by
    simpa using e.continuous.tendsto (e.symm z₀)
  have h := eqOn_zero_of_contDiffOn_of_comp_eq_neg_id_of_forall_isBigO (ξ := ξ ∘ e)
    (J := J ∘ e) (C := C ∘ e) (hΩ.preimage e.continuous) hΩc'
    (hξ.comp e.contDiff.contDiffOn hmaps) (hJ.comp e.contDiff.contDiffOn hmaps)
    (fun y hy ↦ hJsq (e y) hy) (hCm.comp_measurePreserving he')
    (fun y hy ↦ (hCb (e y) hy).imp fun _ hM ↦ e.continuous.continuousAt.eventually hM)
    (fun y hy ↦ by
      simpa only [he, fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I,
        Function.comp_apply] using heq (e y) hy)
    (z₀ := e.symm z₀) (by simpa using hz₀)
    fun n ↦ ((h₀ n).comp_tendsto hT).trans (hlin.pow n)
  intro z hz
  simpa using h (x := e.symm z) (by simpa using hz)

/-- **Unique continuation in the coordinates `(s, t)`.** Let `ξ` be of class `C¹` on a connected
open set `Ω ⊆ ℝ × ℝ`, with values in a finite-dimensional real normed space `V`, and solve
`∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`, for a `C¹` field `J` of real-linear maps with `J² = -1` and a
measurable, locally bounded field `C` of real-linear maps. If `ξ` vanishes on a nonempty open
subset of `Ω`, it vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_eqOn_zero {U : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hJ : ContDiffOn ℝ 1 J Ω) (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
      C z (ξ z) = 0)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  obtain ⟨z₀, hz₀⟩ := hUne
  refine eqOn_zero_of_contDiffOn_prod_of_comp_eq_neg_id_of_forall_isBigO hΩ hΩc hξ hJ hJsq hCm
    hCb heq (hUΩ hz₀) fun n ↦ ?_
  exact (isBigO_zero _ _).congr' (eventuallyEq_of_mem (hU.mem_nhds hz₀) fun z hz ↦ (h₀ hz).symm)
    EventuallyEq.rfl

/-- **Isolated zeros in the coordinates `(s, t)`.** Let `ξ` be of class `C¹` on a connected open
set `Ω ⊆ ℝ × ℝ`, with values in a finite-dimensional real normed space `V`, and solve
`∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`, for a `C¹` field `J` of real-linear maps with `J² = -1` and a
measurable, locally bounded field `C` of real-linear maps. If `ξ` is not identically zero on `Ω`,
its zeros form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_prod_of_comp_eq_neg_id (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hξ : ContDiffOn ℝ 1 ξ Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJsq : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
      C z (ξ z) = 0)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  have hmaps : MapsTo e (e ⁻¹' Ω) Ω := mapsTo_preimage _ _
  have hΩc' : IsPreconnected (e ⁻¹' Ω) := by
    rw [← e.image_symm_eq_preimage]
    exact hΩc.image _ e.symm.continuous.continuousOn
  have he' : MeasurePreserving e (volume.restrict (e ⁻¹' Ω)) (volume.restrict Ω) :=
    volume_preserving_equiv_real_prod.restrict_preimage hΩ.measurableSet
  obtain ⟨z, hz, hξz⟩ := hne
  have h := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_comp_eq_neg_id (ξ := ξ ∘ e)
    (J := J ∘ e) (C := C ∘ e) (hΩ.preimage e.continuous) hΩc'
    (hξ.comp e.contDiff.contDiffOn hmaps) (hJ.comp e.contDiff.contDiffOn hmaps)
    (fun y hy ↦ hJsq (e y) hy) (hCm.comp_measurePreserving he')
    (fun y hy ↦ (hCb (e y) hy).imp fun _ hM ↦ e.continuous.continuousAt.eventually hM)
    (fun y hy ↦ by
      simpa only [he, fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I,
        Function.comp_apply] using heq (e y) hy)
    ⟨e.symm z, by simpa using hz, by simpa using hξz⟩
  -- the zeros of `ξ` are the image under `e` of the zeros of `ξ ∘ e`
  have hemb : Topology.IsEmbedding e := e.toHomeomorph.isEmbedding
  rw [← image_preimage_eq Ω e.surjective, ← image_preimage_eq {z | ξ z ≠ 0} e.surjective,
    hemb.image_mem_codiscreteWithin]
  exact h

end TauCeti
