/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
public import TauCeti.Analysis.Calculus.TangentCone.Chart
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Transverse intersections of flattened sets

Let `S₁` and `S₂` be subsets of a finite-dimensional space which are flattened, near a common
point `y`, by forward `C^n` charts (`n ≥ 1`) whose inverses are differentiable at the images of
`y`. They meet **transversally** at `y` when their tangent spaces at `y` span the whole space. The
tangent spaces are taken intrinsically, as the spans of Mathlib's tangent cones `tangentConeAt`;
by `TauCeti.IsSliceChart.span_tangentConeAt_eq_comap` this agrees with the tangent space read off
either chart.

This file proves that a transverse intersection is again an embedded `C^n` submanifold near `y`,
whose tangent space is the intersection of the two tangent spaces: there is a `C^n` chart with
`C^n` inverse flattening `S₁ ∩ S₂` onto that intersection of subspaces, and the span of the tangent
cone of `S₁ ∩ S₂` at `y` is that intersection. Its dimension is therefore
`dim T₁ + dim T₂ - dim E`.

## Main results

* `TauCeti.exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top`: a transverse
  intersection of two flattened sets is flattened onto the intersection of their tangent spaces.
* `TauCeti.span_tangentConeAt_inter_of_span_tangentConeAt_sup_eq_top`: the tangent space of a
  transverse intersection is the intersection of the two tangent spaces.

## References

* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §5.
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **A transverse intersection of embedded submanifolds is an embedded submanifold.** Let
`C^n` charts `e₁` and `e₂` (`n ≠ 0`), with inverses differentiable at the images of `y`, flatten
`S₁` and `S₂` onto linear subspaces near a common point `y`. If the tangent spaces of `S₁` and `S₂`
at `y` span the whole space, then a `C^n` chart with `C^n` inverse flattens `S₁ ∩ S₂` near `y`
onto the intersection of those tangent spaces. -/
theorem exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top {n : ℕ∞ω} (hn : n ≠ 0)
    {S₁ S₂ : Set E} {L₁ L₂ : Submodule 𝕜 E} {e₁ e₂ : OpenPartialHomeomorph E E} {y : E}
    (h₁ : IsSliceChart e₁ (L₁ : Set E) S₁) (h₂ : IsSliceChart e₂ (L₂ : Set E) S₂)
    (hy₁ : y ∈ e₁.source) (hy₂ : y ∈ e₂.source) (hyS₁ : y ∈ S₁) (hyS₂ : y ∈ S₂)
    (hc₁ : ∀ z ∈ e₁.source, ContDiffAt 𝕜 n e₁ z) (hc₂ : ∀ z ∈ e₂.source, ContDiffAt 𝕜 n e₂ z)
    (hs₁ : DifferentiableAt 𝕜 e₁.symm (e₁ y)) (hs₂ : DifferentiableAt 𝕜 e₂.symm (e₂ y))
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊔
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) = ⊤) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt 𝕜 n e z) ∧
      (∀ z ∈ e.target, ContDiffAt 𝕜 n e.symm z) ∧
      IsSliceChart e ((Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓
        Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) : Submodule 𝕜 E) : Set E) (S₁ ∩ S₂) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hd₁ := (hc₁ y hy₁).differentiableAt hn
  have hd₂ := (hc₂ y hy₂).differentiableAt hn
  obtain ⟨A₁, hA₁⟩ := e₁.isInvertible_fderiv hy₁ hd₁ hs₁
  obtain ⟨A₂, hA₂⟩ := e₂.isInvertible_fderiv hy₂ hd₂ hs₂
  replace hA₁ : HasFDerivAt e₁ (A₁ : E →L[𝕜] E) y := hA₁ ▸ hd₁.hasFDerivAt
  replace hA₂ : HasFDerivAt e₂ (A₂ : E →L[𝕜] E) y := hA₂ ▸ hd₂.hasFDerivAt
  rw [h₁.span_tangentConeAt_eq_comap L₁.closed_of_finiteDimensional hy₁ hyS₁ hA₁,
    h₂.span_tangentConeAt_eq_comap L₂.closed_of_finiteDimensional hy₂ hyS₂ hA₂] at htr ⊢
  -- Near `y`, `S₁ ∩ S₂` is the zero set of `g`, which projects each chart onto a complement of
  -- its model subspace.
  obtain ⟨C₁, hC₁⟩ := L₁.exists_isCompl
  obtain ⟨C₂, hC₂⟩ := L₂.exists_isCompl
  have : CompleteSpace (C₁ × C₂) := FiniteDimensional.complete 𝕜 _
  let P₁ : E →L[𝕜] C₁ := (C₁.projectionOnto L₁ hC₁.symm).toContinuousLinearMap
  let P₂ : E →L[𝕜] C₂ := (C₂.projectionOnto L₂ hC₂.symm).toContinuousLinearMap
  have hP₁ (v : E) : P₁ v = 0 ↔ v ∈ L₁ := Submodule.projectionOnto_apply_eq_zero_iff _
  have hP₂ (v : E) : P₂ v = 0 ↔ v ∈ L₂ := Submodule.projectionOnto_apply_eq_zero_iff _
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
      LinearMap.range_eq_top.2 <| (Submodule.projectionOnto_surjective _).comp A₁.surjective
    have hsurj₂ : (P₂.comp (A₂ : E →L[𝕜] E)).range = ⊤ :=
      LinearMap.range_eq_top.2 <| (Submodule.projectionOnto_surjective _).comp A₂.surjective
    rw [ContinuousLinearMap.range_prod_eq (by rw [hker₁, hker₂]; exact htr), hsurj₁, hsurj₂,
      Submodule.prod_top]
  obtain ⟨e, hye, hes, hC, hCs, he⟩ := hg.exists_isSliceChart_preimage_zero hn hrange
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.closed_of_finiteDimensional _))
    (e₁.open_source.inter e₂.open_source) ⟨hy₁, hy₂⟩ hgC
  refine ⟨e, hye, hC, hCs, isSliceChart_iff.2 fun z hz ↦ ?_⟩
  have hker : g'.ker = L₁.comap (A₁ : E →ₗ[𝕜] E) ⊓ L₂.comap (A₂ : E →ₗ[𝕜] E) := by
    rw [← hker₁, ← hker₂]
    exact ContinuousLinearMap.ker_prod _ _
  rw [← hker, ← he.mem_iff hz]
  simp [g, hP₁, hP₂, h₁.mem_iff (hes hz).1, h₂.mem_iff (hes hz).2]

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
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) = ⊤) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 (S₁ ∩ S₂) y) =
      Submodule.span 𝕜 (tangentConeAt 𝕜 S₁ y) ⊓ Submodule.span 𝕜 (tangentConeAt 𝕜 S₂ y) := by
  obtain ⟨e, hye, hC, hCs, he⟩ := exists_isSliceChart_inter_of_span_tangentConeAt_sup_eq_top hn
    h₁ h₂ hy₁ hy₂ hyS₁ hyS₂ hc₁ hc₂ hs₁ hs₂ htr
  have hd := (hC y hye).differentiableAt hn
  obtain ⟨A, hA⟩ := e.isInvertible_fderiv hye hd
    ((hCs _ (e.map_source hye)).differentiableAt hn)
  -- The tangent cone of `S₁ ∩ S₂` lies in both tangent spaces, and has the same dimension as
  -- their intersection, read off the chart `e`.
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 fun v hv ↦
    ⟨Submodule.subset_span (tangentConeAt_mono inter_subset_left hv),
      Submodule.subset_span (tangentConeAt_mono inter_subset_right hv)⟩) ?_
  exact he.finrank_span_tangentConeAt (Submodule.closed_of_finiteDimensional _) hye
    ⟨hyS₁, hyS₂⟩ (hA ▸ hd.hasFDerivAt)

end TauCeti
