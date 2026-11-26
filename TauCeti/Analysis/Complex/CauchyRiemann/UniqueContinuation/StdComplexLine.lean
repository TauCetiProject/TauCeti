/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.DifferentialInequality
import TauCeti.Topology.Codiscrete

/-!
# Cauchy–Riemann differential inequalities on the standard complex line `ℝ × ℝ`

The unique continuation theorems for Cauchy–Riemann differential inequalities in
`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.DifferentialInequality` are stated for
maps on open subsets of `ℂ`. Floer and pseudoholomorphic-curve theory works on the standard
complex line `ℝ × ℝ`, with the coordinate directions `TauCeti.stdComplexLineReal = (1, 0)` and
`TauCeti.stdComplexLineImag = (0, 1)`. This file transports those theorems along
`Complex.equivRealProdCLM`, for a `C¹` map `ξ : ℝ × ℝ → V` with

`‖∂ₛξ + J(z) ∂ₜξ‖ ≤ M ‖ξ‖`

near every zero of `ξ` in a connected open set `Ω ⊆ ℝ × ℝ`, `J(z)² = -1`:

* `ξ` vanishes on `Ω` if it vanishes on a nonempty open subset of `Ω`
  (`TauCeti.eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_fderiv_le`);
* otherwise its zeros are isolated
  (`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_fderiv_le`).
-/

public section

open Complex Filter Set Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Set (ℝ × ℝ)} {J : ℝ × ℝ → V →L[ℝ] V} {ξ : ℝ × ℝ → V}

/-- In the complex coordinate `Complex.equivRealProdCLM`, the Cauchy–Riemann inequality on `ℝ × ℝ`
near the zeros of `ξ` becomes the inequality near the zeros of `ξ ∘ Complex.equivRealProdCLM`
that the unique continuation theorems on `ℂ` ask for. -/
private theorem exists_eventually_norm_le_comp_equivRealProdCLM
    (hb : ∀ z ∈ Ω, ξ z = 0 → ∃ M, ∀ᶠ w in 𝓝 z,
      ‖fderiv ℝ ξ w stdComplexLineReal + J w (fderiv ℝ ξ w stdComplexLineImag)‖ ≤ M * ‖ξ w‖) :
    ∀ z ∈ equivRealProdCLM ⁻¹' Ω, (ξ ∘ equivRealProdCLM) z = 0 → ∃ M, ∀ᶠ w in 𝓝 z,
      ‖fderiv ℝ (ξ ∘ equivRealProdCLM) w 1 +
        (J ∘ equivRealProdCLM) w (fderiv ℝ (ξ ∘ equivRealProdCLM) w I)‖ ≤
        M * ‖(ξ ∘ equivRealProdCLM) w‖ := fun z hz h ↦
  (hb _ hz h).imp fun _ hM ↦ (equivRealProdCLM.continuous.tendsto z).eventually hM |>.mono
    fun w hw ↦ by rwa [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I]

variable [FiniteDimensional ℝ V]

/-- **Unique continuation for a Cauchy–Riemann differential inequality on `ℝ × ℝ`.** On a
connected open set `Ω ⊆ ℝ × ℝ`, a `C¹` map `ξ` into a finite-dimensional real normed space with
`‖∂ₛξ + J ∂ₜξ‖ ≤ M ‖ξ‖` near every zero of `ξ` in `Ω`, for a `C¹` field `J` of complex
structures, `J(z)² = -1`, that vanishes on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_fderiv_le
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hb : ∀ z ∈ Ω, ξ z = 0 → ∃ M, ∀ᶠ w in 𝓝 z,
      ‖fderiv ℝ ξ w stdComplexLineReal + J w (fderiv ℝ ξ w stdComplexLineImag)‖ ≤ M * ‖ξ w‖)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) :
    EqOn ξ 0 Ω := by
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁⟩ := hUne
  exact (eqOn_zero_of_contDiffOn_of_eqOn_zero_of_norm_le (hΩ.preimage e.continuous)
    ((e.toHomeomorph.isPreconnected_preimage).2 hΩc)
    (hJ.comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ)) (fun w hw ↦ hJJ (e w) hw)
    (hξ.comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ))
    (exists_eventually_norm_le_comp_equivRealProdCLM hb) (hU.preimage e.continuous)
    ⟨e.symm z₁, by simpa using hz₁⟩ (preimage_mono hUΩ) fun w hw ↦ h₀ hw).cancel_right
    e.surjective.surjOn_preimage

/-- **Isolated zeros for a Cauchy–Riemann differential inequality on `ℝ × ℝ`.** On a connected
open set `Ω ⊆ ℝ × ℝ`, the zeros of a `C¹` map `ξ` into a finite-dimensional real normed space with
`‖∂ₛξ + J ∂ₜξ‖ ≤ M ‖ξ‖` near every zero of `ξ` in `Ω`, for a `C¹` field `J` of complex
structures, `J(z)² = -1`, that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_fderiv_le
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hb : ∀ z ∈ Ω, ξ z = 0 → ∃ M, ∀ᶠ w in 𝓝 z,
      ‖fderiv ℝ ξ w stdComplexLineReal + J w (fderiv ℝ ξ w stdComplexLineImag)‖ ≤ M * ‖ξ w‖)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  set e := Complex.equivRealProdCLM
  obtain ⟨z₁, hz₁, hne₁⟩ := hne
  exact (e.toHomeomorph.preimage_mem_codiscreteWithin (s := {z | ξ z ≠ 0})).1
    (setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_norm_le (hΩ.preimage e.continuous)
      ((e.toHomeomorph.isPreconnected_preimage).2 hΩc)
      (hJ.comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ)) (fun w hw ↦ hJJ (e w) hw)
      (hξ.comp_continuousLinearMap (e : ℂ →L[ℝ] ℝ × ℝ))
      (exists_eventually_norm_le_comp_equivRealProdCLM hb)
      ⟨e.symm z₁, by simpa using hz₁, by simpa using hne₁⟩)

end TauCeti
