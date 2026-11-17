/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.DiscreteSubset

/-!
# Transferring local statements along the real coordinates of `ℂ`

A statement about maps on `ℝ × ℝ` is often proved by reading the domain as `ℂ` through
`Complex.equivRealProdCLM`, writing `e` for it below. This file moves the conclusions back and the
hypotheses forward:

* a field `J(z, x)` that is `Cⁿ` near the graph of a `Cⁿ` map `u` over an open set `Ω` gives a
  `Cⁿ` map `w ↦ J(e w, u (e w))` on `e ⁻¹' Ω` (`TauCeti.contDiffOn_comp_equivRealProdCLM`);
* vanishing on `e ⁻¹' Ω` in the complex coordinate is vanishing on `Ω`
  (`TauCeti.eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM`);
* vanishing to infinite order at `z₀`, measured by `‖z - z₀‖ⁿ`, is vanishing to infinite order at
  `e⁻¹ z₀` in the complex coordinate (`TauCeti.isBigO_comp_equivRealProdCLM`);
* a set whose preimage is codiscrete in `e ⁻¹' Ω` is codiscrete in `Ω`
  (`TauCeti.mem_codiscreteWithin_of_preimage_equivRealProdCLM`).
-/

public section

open Asymptotics Filter Function Set Topology

namespace TauCeti

/-- In the complex coordinate `e = Complex.equivRealProdCLM`, a field `J(z, x)` that is `Cⁿ` near
the graph of a `Cⁿ` map `u` over an open set `Ω` gives a `Cⁿ` map `w ↦ J(e w, u (e w))` on
`e ⁻¹' Ω`. -/
theorem contDiffOn_comp_equivRealProdCLM {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {Ω : Set (ℝ × ℝ)}
    {J : ℝ × ℝ → E → F} {u : ℝ × ℝ → E} (hΩ : IsOpen Ω)
    (hJ : ∀ z ∈ Ω, ContDiffAt ℝ n (fun p : (ℝ × ℝ) × E ↦ J p.1 p.2) (z, u z))
    (hu : ContDiffOn ℝ n u Ω) :
    ContDiffOn ℝ n (fun w ↦ J (Complex.equivRealProdCLM w) (u (Complex.equivRealProdCLM w)))
      (Complex.equivRealProdCLM ⁻¹' Ω) := fun w hw ↦ by
  set e := Complex.equivRealProdCLM
  have hgraph : ContDiffAt ℝ n (fun w ↦ (e w, u (e w))) w :=
    e.contDiff.contDiffAt.prodMk ((hu.contDiffAt (hΩ.mem_nhds hw)).comp w e.contDiff.contDiffAt)
  exact ((hJ (e w) hw).comp w hgraph).contDiffWithinAt

/-- A map vanishing on `e ⁻¹' Ω` in the complex coordinate `e = Complex.equivRealProdCLM` vanishes
on `Ω`. -/
theorem eqOn_zero_of_eqOn_zero_comp_equivRealProdCLM {E : Type*} [Zero E] {ξ : ℝ × ℝ → E}
    {Ω : Set (ℝ × ℝ)}
    (h : EqOn (ξ ∘ Complex.equivRealProdCLM) 0 (Complex.equivRealProdCLM ⁻¹' Ω)) :
    EqOn ξ 0 Ω := fun z hz ↦ by
  simpa using h (show Complex.equivRealProdCLM.symm z ∈ _ by simpa using hz)

/-- Vanishing to infinite order at `z₀` is vanishing to infinite order in the complex coordinate
`Complex.equivRealProdCLM`. -/
theorem isBigO_comp_equivRealProdCLM {E : Type*} [Norm E] {ξ : ℝ × ℝ → E} {z₀ : ℝ × ℝ}
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ n) (n : ℕ) :
    (ξ ∘ Complex.equivRealProdCLM) =O[𝓝 (Complex.equivRealProdCLM.symm z₀)]
      fun w ↦ (w - Complex.equivRealProdCLM.symm z₀) ^ n := by
  set e := Complex.equivRealProdCLM
  -- In the complex coordinate the vanishing order is measured by `‖e w - e w₀‖ ≤ ‖e‖ ‖w - w₀‖`.
  have h := (h₀ n).comp_tendsto
    ((e.continuous.tendsto (e.symm z₀)).trans_eq (by rw [e.apply_symm_apply]))
  refine h.trans (IsBigO.of_bound (‖(e : ℂ →L[ℝ] ℝ × ℝ)‖ ^ n) (Eventually.of_forall fun w ↦ ?_))
  have hw : e w - z₀ = e (w - e.symm z₀) := by simp
  simp only [comp_apply, hw, norm_pow, norm_norm, ← mul_pow]
  gcongr
  exact (e : ℂ →L[ℝ] ℝ × ℝ).le_opNorm _

/-- A set whose preimage under `e = Complex.equivRealProdCLM` is codiscrete in `e ⁻¹' Ω` is
codiscrete in `Ω`. -/
theorem mem_codiscreteWithin_of_preimage_equivRealProdCLM {s Ω : Set (ℝ × ℝ)}
    (h : Complex.equivRealProdCLM ⁻¹' s ∈ codiscreteWithin (Complex.equivRealProdCLM ⁻¹' Ω)) :
    s ∈ codiscreteWithin Ω := by
  set e := Complex.equivRealProdCLM
  -- Transport the codiscrete set back along the homeomorphism `e`.
  have := (e.toHomeomorph.isEmbedding.image_mem_codiscreteWithin (s := e ⁻¹' s)
    (t := e ⁻¹' Ω)).2 h
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph, image_preimage_eq _ e.surjective] using this

end TauCeti
