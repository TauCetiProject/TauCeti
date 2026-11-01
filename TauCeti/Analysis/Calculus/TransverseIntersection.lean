/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
public import TauCeti.Analysis.Calculus.TangentCone.Chart
public import TauCeti.Analysis.Calculus.TangentCone.LevelSet
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Transverse intersections of flattened sets

Let `S₁` and `S₂` be subsets of a real or complex Banach space which are flattened, near a common
point `y`, by forward `C^n` charts (`n ≥ 1`) whose inverses are differentiable at the images of
`y`. They meet **transversally** at `y` when their tangent spaces at `y` span the whole space. The
tangent spaces are taken intrinsically, as the spans of Mathlib's tangent cones `tangentConeAt`;
by `TauCeti.IsSliceChart.span_tangentConeAt_eq_comap` this agrees with the tangent space read off
either chart. The model subspaces and the intersection of the tangent spaces are assumed to be
complemented. This last condition is the complemented-kernel hypothesis for the combined normal
equation. All these complementation hypotheses are automatic in finite dimensions.

This file proves that a transverse intersection is again an embedded `C^n` submanifold near `y`,
whose tangent space is the intersection of the two tangent spaces: there is a `C^n` chart with
`C^n` inverse flattening `S₁ ∩ S₂` onto that intersection of subspaces, and the tangent cone of
`S₁ ∩ S₂` at `y` already equals that intersection. In finite dimensions, its dimension is
therefore `dim T₁ + dim T₂ - dim E`.

The most common second set is a regular level set `g⁻¹ {0}`, whose tangent space is `ker g'`;
cutting by it is transverse when the tangent space of the first set and `ker g'` span the whole
space. The underlying regular-level tangent-cone calculation is
`HasStrictFDerivAt.tangentConeAt_preimage_singleton`. The charts come from the complemented-kernel
implicit function theorem, `HasStrictFDerivAt.exists_isSliceChart_preimage_zero`, applied to the
pair of normal equations.

## Main results

* `TauCeti.exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top`: a transverse
  intersection of two flattened sets is flattened onto the intersection of their tangent spaces.
* `TauCeti.tangentConeAt_inter_of_span_tangentConeAt_sup_eq_top` and its span form
  `TauCeti.span_tangentConeAt_inter_of_span_tangentConeAt_sup_eq_top`: the tangent cone of a
  transverse intersection is the intersection of the two tangent spaces.
* `TauCeti.exists_isSliceChart_inter_preimage_zero` and
  `TauCeti.tangentConeAt_inter_preimage_zero`, with span form
  `TauCeti.span_tangentConeAt_inter_preimage_zero`: the same statements for the cut of a flattened
  set by a transverse regular level set with complemented derivative kernel.

## References

* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §5.
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

-- One normal equation supplies both the slice chart and the intrinsic tangent-cone formula.
private theorem exists_isSliceChart_inter_and_tangentConeAt {n : ℕ∞ω} (hn : n ≠ 0)
    {S₁ S₂ : Set E} {L₁ L₂ : Submodule 𝕜 E} {e₁ e₂ : OpenPartialHomeomorph E E} {y : E}
    (h₁ : IsSliceChart e₁ (L₁ : Set E) S₁) (h₂ : IsSliceChart e₂ (L₂ : Set E) S₂)
    (hy₁ : y ∈ e₁.source) (hy₂ : y ∈ e₂.source) (hyS₁ : y ∈ S₁) (hyS₂ : y ∈ S₂)
    (hc₁ : ∀ z ∈ e₁.source, ContDiffAt 𝕜 n e₁ z) (hc₂ : ∀ z ∈ e₂.source, ContDiffAt 𝕜 n e₂ z)
    (hs₁ : DifferentiableAt 𝕜 e₁.symm (e₁ y)) (hs₂ : DifferentiableAt 𝕜 e₂.symm (e₂ y))
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊔
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) = ⊤)
    (hL₁ : L₁.ClosedComplemented) (hL₂ : L₂.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y)).ClosedComplemented) :
    (∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt 𝕜 n e z) ∧
      (∀ z ∈ e.target, ContDiffAt 𝕜 n e.symm z) ∧
      IsSliceChart e ((Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
        Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) : Submodule 𝕜 E) : Set E) (S₁ ∩ S₂)) ∧
    tangentConeAt 𝕜 (S₁ ∩ S₂) y =
      ((Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
        Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) : Submodule 𝕜 E) : Set E) := by
  obtain ⟨A₁, hA₁⟩ := e₁.exists_hasFDerivAt_of_chart hy₁
    ((hc₁ y hy₁).differentiableAt hn) hs₁
  obtain ⟨A₂, hA₂⟩ := e₂.exists_hasFDerivAt_of_chart hy₂
    ((hc₂ y hy₂).differentiableAt hn) hs₂
  rw [h₁.span_tangentConeAt_eq_comap hL₁.isClosed hy₁ hyS₁ hA₁,
    h₂.span_tangentConeAt_eq_comap hL₂.isClosed hy₂ hyS₂ hA₂] at htr hI ⊢
  -- Near `y`, `S₁ ∩ S₂` is the zero set of `g`, which projects each chart onto a complement of
  -- its model subspace.
  obtain ⟨C₁, hC₁⟩ := hL₁.exists_isTopCompl
  obtain ⟨C₂, hC₂⟩ := hL₂.exists_isTopCompl
  have : CompleteSpace C₁ := hC₁.isClosed'.completeSpace_coe
  have : CompleteSpace C₂ := hC₂.isClosed'.completeSpace_coe
  let P₁ : E →L[𝕜] C₁ := C₁.projectionOntoL L₁ hC₁.symm
  let P₂ : E →L[𝕜] C₂ := C₂.projectionOntoL L₂ hC₂.symm
  have hP₁ (v : E) : P₁ v = 0 ↔ v ∈ L₁ := Submodule.projectionOntoL_apply_eq_zero_iff _
  have hP₂ (v : E) : P₂ v = 0 ↔ v ∈ L₂ := Submodule.projectionOntoL_apply_eq_zero_iff _
  let g : E → C₁ × C₂ := fun z ↦ (P₁ (e₁ z), P₂ (e₂ z))
  let g' : E →L[𝕜] C₁ × C₂ :=
    (P₁.comp (A₁ : E →L[𝕜] E)).prod (P₂.comp (A₂ : E →L[𝕜] E))
  have hgC : ∀ z ∈ e₁.source ∩ e₂.source, ContDiffAt 𝕜 n g z := fun z hz ↦
    (P₁.contDiff.contDiffAt.comp z (hc₁ z hz.1)).prodMk
      (P₂.contDiff.contDiffAt.comp z (hc₂ z hz.2))
  have hg : HasStrictFDerivAt g g' y :=
    (hgC y ⟨hy₁, hy₂⟩).hasStrictFDerivAt'
      ((P₁.hasFDerivAt.comp y hA₁).prodMk (P₂.hasFDerivAt.comp y hA₂)) hn
  have hker₁ : (P₁.comp (A₁ : E →L[𝕜] E)).ker = L₁.comap (A₁ : E →ₗ[𝕜] E) := by
    ext v; simp [hP₁]
  have hker₂ : (P₂.comp (A₂ : E →L[𝕜] E)).ker = L₂.comap (A₂ : E →ₗ[𝕜] E) := by
    ext v; simp [hP₂]
  -- Transversality is the surjectivity of the derivative of `g`.
  have hrange : g'.range = ⊤ := by
    have hsurj₁ : (P₁.comp (A₁ : E →L[𝕜] E)).range = ⊤ :=
      LinearMap.range_eq_top.2 <| (Submodule.projectionOntoL_surjective hC₁.symm).comp A₁.surjective
    have hsurj₂ : (P₂.comp (A₂ : E →L[𝕜] E)).range = ⊤ :=
      LinearMap.range_eq_top.2 <| (Submodule.projectionOntoL_surjective hC₂.symm).comp A₂.surjective
    rw [ContinuousLinearMap.range_prod_eq (by rw [hker₁, hker₂]; exact htr), hsurj₁, hsurj₂,
      Submodule.prod_top]
  have hker : g'.ker = L₁.comap (A₁ : E →ₗ[𝕜] E) ⊓ L₂.comap (A₂ : E →ₗ[𝕜] E) := by
    rw [← hker₁, ← hker₂]
    exact ContinuousLinearMap.ker_prod _ _
  have hkerC : g'.ker.ClosedComplemented := by rwa [hker]
  have hmem (z : E) (hz : z ∈ e₁.source ∩ e₂.source) : z ∈ S₁ ∩ S₂ ↔ g z = 0 := by
    simp [g, hP₁, hP₂, h₁.mem_iff hz.1, h₂.mem_iff hz.2]
  have hgy : g y = 0 := (hmem y ⟨hy₁, hy₂⟩).1 ⟨hyS₁, hyS₂⟩
  obtain ⟨e, hye, hes, hC, hCs, he⟩ := hg.exists_isSliceChart_preimage_zero hn hrange hkerC
    (e₁.open_source.inter e₂.open_source) ⟨hy₁, hy₂⟩ hgC
  refine ⟨⟨e, hye, hC, hCs, isSliceChart_iff.2 fun z hz ↦ ?_⟩, ?_⟩
  · rw [← hker, ← he.mem_iff hz]
    exact hmem z (hes hz)
  -- The intersection is locally the regular zero set of `g`, whose cone is exactly `ker g'`.
  · have hU := (e₁.open_source.inter e₂.open_source).mem_nhds ⟨hy₁, hy₂⟩
    have hsets : (S₁ ∩ S₂) ∩ (e₁.source ∩ e₂.source) =
        (g ⁻¹' {0}) ∩ (e₁.source ∩ e₂.source) := by
      ext z
      by_cases hz : z ∈ e₁.source ∩ e₂.source
      · simp only [mem_inter_iff, hz, and_true, mem_preimage, mem_singleton_iff]
        exact hmem z hz
      · simp only [mem_inter_iff, hz, and_false]
    rw [← tangentConeAt_inter_nhds hU, hsets, tangentConeAt_inter_nhds hU]
    simpa only [hgy, hker] using hg.tangentConeAt_preimage_singleton hrange hkerC

/-- **A transverse intersection of embedded submanifolds is an embedded submanifold.** Let
`C^n` charts `e₁` and `e₂` (`n ≠ 0`), with inverses differentiable at the images of `y`, flatten
`S₁` and `S₂` onto linear subspaces near a common point `y`. If the tangent spaces of `S₁` and `S₂`
at `y` span the whole space, then a `C^n` chart with `C^n` inverse flattens `S₁ ∩ S₂` near `y`
onto the intersection of those tangent spaces. The model subspaces and the intersection of the
tangent spaces must be complemented. -/
theorem exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top {n : ℕ∞ω} (hn : n ≠ 0)
    {S₁ S₂ : Set E} {L₁ L₂ : Submodule 𝕜 E} {e₁ e₂ : OpenPartialHomeomorph E E} {y : E}
    (h₁ : IsSliceChart e₁ (L₁ : Set E) S₁) (h₂ : IsSliceChart e₂ (L₂ : Set E) S₂)
    (hy₁ : y ∈ e₁.source) (hy₂ : y ∈ e₂.source) (hyS₁ : y ∈ S₁) (hyS₂ : y ∈ S₂)
    (hc₁ : ∀ z ∈ e₁.source, ContDiffAt 𝕜 n e₁ z) (hc₂ : ∀ z ∈ e₂.source, ContDiffAt 𝕜 n e₂ z)
    (hs₁ : DifferentiableAt 𝕜 e₁.symm (e₁ y)) (hs₂ : DifferentiableAt 𝕜 e₂.symm (e₂ y))
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊔
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) = ⊤)
    (hL₁ : L₁.ClosedComplemented) (hL₂ : L₂.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y)).ClosedComplemented) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt 𝕜 n e z) ∧
      (∀ z ∈ e.target, ContDiffAt 𝕜 n e.symm z) ∧
      IsSliceChart e ((Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
        Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) : Submodule 𝕜 E) : Set E) (S₁ ∩ S₂) :=
  (exists_isSliceChart_inter_and_tangentConeAt hn h₁ h₂ hy₁ hy₂ hyS₁ hyS₂ hc₁ hc₂ hs₁ hs₂
    htr hL₁ hL₂ hI).1

/-- The tangent cone of a transverse intersection of split submanifolds in a Banach space is
exactly the intersection of their tangent spaces, provided that this intersection is
complemented. -/
theorem tangentConeAt_inter_of_span_tangentConeAt_sup_eq_top {n : ℕ∞ω} (hn : n ≠ 0)
    {S₁ S₂ : Set E} {L₁ L₂ : Submodule 𝕜 E} {e₁ e₂ : OpenPartialHomeomorph E E} {y : E}
    (h₁ : IsSliceChart e₁ (L₁ : Set E) S₁) (h₂ : IsSliceChart e₂ (L₂ : Set E) S₂)
    (hy₁ : y ∈ e₁.source) (hy₂ : y ∈ e₂.source) (hyS₁ : y ∈ S₁) (hyS₂ : y ∈ S₂)
    (hc₁ : ∀ z ∈ e₁.source, ContDiffAt 𝕜 n e₁ z) (hc₂ : ∀ z ∈ e₂.source, ContDiffAt 𝕜 n e₂ z)
    (hs₁ : DifferentiableAt 𝕜 e₁.symm (e₁ y)) (hs₂ : DifferentiableAt 𝕜 e₂.symm (e₂ y))
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊔
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) = ⊤)
    (hL₁ : L₁.ClosedComplemented) (hL₂ : L₂.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y)).ClosedComplemented) :
    tangentConeAt 𝕜 (S₁ ∩ S₂) y =
      ((Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
        Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) : Submodule 𝕜 E) : Set E) :=
  (exists_isSliceChart_inter_and_tangentConeAt hn h₁ h₂ hy₁ hy₂ hyS₁ hyS₂ hc₁ hc₂ hs₁ hs₂
    htr hL₁ hL₂ hI).2

/-- **The tangent space of a transverse intersection.** Under the hypotheses of
`TauCeti.exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top`, the tangent space of
`S₁ ∩ S₂` at `y`, taken intrinsically as the span of its tangent cone, is the intersection of the
tangent spaces of `S₁` and `S₂` at `y`. -/
theorem span_tangentConeAt_inter_of_span_tangentConeAt_sup_eq_top {n : ℕ∞ω} (hn : n ≠ 0)
    {S₁ S₂ : Set E} {L₁ L₂ : Submodule 𝕜 E} {e₁ e₂ : OpenPartialHomeomorph E E} {y : E}
    (h₁ : IsSliceChart e₁ (L₁ : Set E) S₁) (h₂ : IsSliceChart e₂ (L₂ : Set E) S₂)
    (hy₁ : y ∈ e₁.source) (hy₂ : y ∈ e₂.source) (hyS₁ : y ∈ S₁) (hyS₂ : y ∈ S₂)
    (hc₁ : ∀ z ∈ e₁.source, ContDiffAt 𝕜 n e₁ z) (hc₂ : ∀ z ∈ e₂.source, ContDiffAt 𝕜 n e₂ z)
    (hs₁ : DifferentiableAt 𝕜 e₁.symm (e₁ y)) (hs₂ : DifferentiableAt 𝕜 e₂.symm (e₂ y))
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊔
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) = ⊤)
    (hL₁ : L₁.ClosedComplemented) (hL₂ : L₂.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y)).ClosedComplemented) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 (S₁ ∩ S₂) y) =
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓ Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) := by
  rw [tangentConeAt_inter_of_span_tangentConeAt_sup_eq_top hn h₁ h₂ hy₁ hy₂ hyS₁ hyS₂ hc₁ hc₂
    hs₁ hs₂ htr hL₁ hL₂ hI,
    Submodule.span_eq]

/-- **Cutting by a transverse regular level set.** Let a `C^n` chart `e₁` (`n ≠ 0`), whose inverse
is differentiable at `e₁ y`, flatten `S` onto a linear subspace near `y ∈ S`, and let `g` be `C^n`
on an open set around `y`, with `g y = 0` and surjective strict derivative `g'` at `y`. If the
tangent space of `S` at `y` and `ker g'` span the whole space, then a `C^n` chart with `C^n` inverse
flattens `S ∩ g⁻¹ {0}` near `y` onto the intersection of the tangent space of `S` with `ker g'`.
The model subspace, the derivative kernel, and that intersection must be complemented. -/
theorem exists_isSliceChart_inter_preimage_zero {n : ℕ∞ω} (hn : n ≠ 0) {S : Set E}
    {L : Submodule 𝕜 E} {e₁ : OpenPartialHomeomorph E E} {y : E}
    (h₁ : IsSliceChart e₁ (L : Set E) S) (hy₁ : y ∈ e₁.source) (hyS : y ∈ S)
    (hc₁ : ∀ z ∈ e₁.source, ContDiffAt 𝕜 n e₁ z) (hs₁ : DifferentiableAt 𝕜 e₁.symm (e₁ y))
    {g : E → F} {g' : E →L[𝕜] F} (hg : HasStrictFDerivAt g g' y) (hg' : g'.range = ⊤)
    (hgy : g y = 0) {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hC : ∀ z ∈ U, ContDiffAt 𝕜 n g z)
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊔ g'.ker = ⊤)
    (hL : L.ClosedComplemented) (hker : g'.ker.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊓ g'.ker).ClosedComplemented) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt 𝕜 n e z) ∧
      (∀ z ∈ e.target, ContDiffAt 𝕜 n e.symm z) ∧
      IsSliceChart e ((Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊓ g'.ker : Submodule 𝕜 E) : Set E)
        (S ∩ g ⁻¹' {0}) := by
  obtain ⟨e₂, hy₂, -, hc₂, hs₂, h₂⟩ :=
    hg.exists_isSliceChart_preimage_zero hn hg' hker hU hyU hC
  have hlevel := hg.span_tangentConeAt_preimage_singleton hg' hker
  rw [hgy] at hlevel
  rw [← hlevel] at htr hI ⊢
  exact exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top hn h₁ h₂ hy₁ hy₂ hyS hgy hc₁
    hc₂ hs₁ ((hs₂ _ (e₂.map_source hy₂)).differentiableAt hn) htr hL hker hI

/-- The tangent cone of a transverse regular-level cut of a split submanifold in a Banach space
is exactly the intersection of its tangent space with the derivative's kernel, provided that the
kernel and the intersection are complemented. -/
theorem tangentConeAt_inter_preimage_zero {n : ℕ∞ω} (hn : n ≠ 0) {S : Set E}
    {L : Submodule 𝕜 E} {e₁ : OpenPartialHomeomorph E E} {y : E}
    (h₁ : IsSliceChart e₁ (L : Set E) S) (hy₁ : y ∈ e₁.source) (hyS : y ∈ S)
    (hc₁ : ∀ z ∈ e₁.source, ContDiffAt 𝕜 n e₁ z) (hs₁ : DifferentiableAt 𝕜 e₁.symm (e₁ y))
    {g : E → F} {g' : E →L[𝕜] F} (hg : HasStrictFDerivAt g g' y) (hg' : g'.range = ⊤)
    (hgy : g y = 0) {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hC : ∀ z ∈ U, ContDiffAt 𝕜 n g z)
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊔ g'.ker = ⊤)
    (hL : L.ClosedComplemented) (hker : g'.ker.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊓ g'.ker).ClosedComplemented) :
    tangentConeAt 𝕜 (S ∩ g ⁻¹' {0}) y =
      ((Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊓ g'.ker : Submodule 𝕜 E) : Set E) := by
  obtain ⟨e₂, hy₂, -, hc₂, hs₂, h₂⟩ :=
    hg.exists_isSliceChart_preimage_zero hn hg' hker hU hyU hC
  have hlevel := hg.span_tangentConeAt_preimage_singleton hg' hker
  rw [hgy] at hlevel
  rw [← hlevel] at htr hI ⊢
  exact tangentConeAt_inter_of_span_tangentConeAt_sup_eq_top hn h₁ h₂ hy₁ hy₂ hyS hgy hc₁
    hc₂ hs₁ ((hs₂ _ (e₂.map_source hy₂)).differentiableAt hn) htr hL hker hI

/-- The tangent space of a transverse regular-level cut, expressed as the span of its tangent
cone, is the intersection of the original tangent space with the derivative's kernel. -/
theorem span_tangentConeAt_inter_preimage_zero {n : ℕ∞ω} (hn : n ≠ 0) {S : Set E}
    {L : Submodule 𝕜 E} {e₁ : OpenPartialHomeomorph E E} {y : E}
    (h₁ : IsSliceChart e₁ (L : Set E) S) (hy₁ : y ∈ e₁.source) (hyS : y ∈ S)
    (hc₁ : ∀ z ∈ e₁.source, ContDiffAt 𝕜 n e₁ z) (hs₁ : DifferentiableAt 𝕜 e₁.symm (e₁ y))
    {g : E → F} {g' : E →L[𝕜] F} (hg : HasStrictFDerivAt g g' y) (hg' : g'.range = ⊤)
    (hgy : g y = 0) {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hC : ∀ z ∈ U, ContDiffAt 𝕜 n g z)
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊔ g'.ker = ⊤)
    (hL : L.ClosedComplemented) (hker : g'.ker.ClosedComplemented)
    (hI : (Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊓ g'.ker).ClosedComplemented) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 (S ∩ g ⁻¹' {0}) y) =
      Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊓ g'.ker := by
  rw [tangentConeAt_inter_preimage_zero hn h₁ hy₁ hyS hc₁ hs₁ hg hg' hgy hU hyU hC htr hL hker hI,
    Submodule.span_eq]

end TauCeti
