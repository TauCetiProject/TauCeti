/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Analysis.Distribution.Monotone
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Sets with a constant normal are half-spaces

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `ν ∈ E`. This file shows that a set `s ⊆ E` whose distributional normal is the constant
`ν` is, up to a null set, a half-space `{x | ⟪x, ν⟫ < c}`, the empty set or the whole space.
The hypothesis is phrased through test vector fields: `∫_s div φ dμ ≥ 0` whenever `⟪φ, ν⟫ ≥ 0`
pointwise. It holds when `Dχ_s = -ν m` for a positive measure `m`. In particular it holds when
`s` has locally finite perimeter and its outer normal `ν_s` equals `ν` almost everywhere for the
perimeter measure
(`TauCeti.ae_eq_empty_or_univ_or_setOf_inner_lt_of_outerNormal_ae_eq`). This is the step of
De Giorgi's blow-up theorem that identifies the limits of the blow-ups at a point of the reduced
boundary.

The proof has two steps.

* Testing with `φ = ψ w` for a nonnegative test function `ψ` and `⟪w, ν⟫ ≥ 0` shows that the
  directional derivative `∂_w χ_s` is nonpositive, so `χ_s (x + w) ≤ χ_s x` almost everywhere
  (`TauCeti.ae_apply_add_le_of_forall_integral_lineDeriv_mul_nonneg`).
* A null-measurable set `s` with `(· + w) ⁻¹' s ⊆ s` almost everywhere, for every `w` with
  `⟪w, ν⟫ ≥ 0`, is almost a half-space
  (`TauCeti.ae_eq_empty_or_univ_or_setOf_inner_lt_of_preimage_add_ae_le`). Its essential interior
  is a representative of `s` for which these inclusions hold exactly, so it is a lower set for the
  preorder `x ≤ y ↔ ⟪x, ν⟫ ≤ ⟪y, ν⟫`; such a set lies between `{⟪x, ν⟫ < c}` and
  `{⟪x, ν⟫ ≤ c}`, which differ by a null hyperplane.

When `ν = 0` the half-space case does not occur: the set is then null or conull.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2 (Theorem 1, the blow-up of a set of finite perimeter at a point of the reduced boundary).
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §15.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter TestFunction
open scoped ENNReal RealInnerProductSpace Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E} {ν : E}

/-- **Sets that are almost monotone along a half-space of directions are half-spaces.** If a
null-measurable set `s` satisfies `x + w ∈ s → x ∈ s` for almost every `x`, for each `w` with
`⟪w, ν⟫ ≥ 0`, then `s` is almost everywhere equal to the empty set, the whole space, or a
half-space `{x | ⟪x, ν⟫ < c}`. -/
theorem ae_eq_empty_or_univ_or_setOf_inner_lt_of_preimage_add_ae_le
    (hs : NullMeasurableSet s μ) (h : ∀ w, 0 ≤ ⟪w, ν⟫ → (· + w) ⁻¹' s ≤ᵐ[μ] s) :
    s =ᵐ[μ] (∅ : Set E) ∨ s =ᵐ[μ] (univ : Set E) ∨ ∃ c : ℝ, s =ᵐ[μ] {x | ⟪x, ν⟫ < c} := by
  set I := essentialInterior μ s
  have hI : s =ᵐ[μ] I := (essentialInterior_ae_eq hs).symm
  -- The essential interior is a lower set for `x ↦ ⟪x, ν⟫`.
  have hdown (y : E) (hy : y ∈ I) (z : E) (hz : ⟪z, ν⟫ ≤ ⟪y, ν⟫) : z ∈ I := by
    have hw : 0 ≤ ⟪y - z, ν⟫ := by rw [inner_sub_left]; linarith
    refine essentialInterior_mono_ae (h _ hw) ?_
    rw [essentialInterior_preimage_add_right, mem_preimage, add_sub_cancel]
    exact hy
  rcases I.eq_empty_or_nonempty with hIe | ⟨y₀, hy₀⟩
  · exact Or.inl (hIe ▸ hI)
  by_cases hIu : ∀ z, z ∈ I
  · exact Or.inr (Or.inl ((eq_univ_of_forall hIu) ▸ hI))
  obtain ⟨z₀, hz₀⟩ := not_forall.1 hIu
  -- Some point lies outside `I`, so `⟪·, ν⟫` is bounded above on `I` and `ν ≠ 0`.
  have hlt (y : E) (hy : y ∈ I) : ⟪y, ν⟫ < ⟪z₀, ν⟫ :=
    lt_of_not_ge fun hle => hz₀ (hdown y hy z₀ hle)
  have hν : ν ≠ 0 := by
    rintro rfl
    simpa using hlt y₀ hy₀
  have hbdd : BddAbove ((⟪·, ν⟫) '' I) := ⟨⟪z₀, ν⟫, by
    rintro _ ⟨y, hy, rfl⟩
    exact (hlt y hy).le⟩
  set c := sSup ((⟪·, ν⟫) '' I)
  refine Or.inr (Or.inr ⟨c, hI.trans (ae_eq_set.2 ⟨?_, ?_⟩)⟩)
  · -- `I` lies in `{⟪x, ν⟫ ≤ c}`, which exceeds `{⟪x, ν⟫ < c}` by a null hyperplane.
    refine measure_mono_null (fun y hy => ?_) (Measure.addHaar_setOf_inner_eq μ hν c)
    exact le_antisymm (le_csSup hbdd ⟨y, hy.1, rfl⟩) (not_lt.1 hy.2)
  · -- `{⟪x, ν⟫ < c}` lies in `I`.
    refine measure_mono_null (fun x hx => ?_) measure_empty
    rw [Set.mem_sdiff, mem_ofPred_eq] at hx
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := exists_lt_of_lt_csSup (Set.Nonempty.image _ ⟨y₀, hy₀⟩) hx.1
    exact hx.2 (hdown y hy x hxy.le)

/-- **Sets with a constant normal are half-spaces.** Let `s` be null-measurable with
`0 ≤ ∫_s div φ dμ` for every test vector field `φ` with `⟪φ, ν⟫ ≥ 0` pointwise, as holds when the
distributional derivative of `χ_s` is `-ν` times a positive measure. Then `s` is almost everywhere
equal to the empty set, the whole space, or a half-space `{x | ⟪x, ν⟫ < c}`. -/
theorem ae_eq_empty_or_univ_or_setOf_inner_lt_of_integral_divergenceCLM_mul_indicator_nonneg
    (hs : NullMeasurableSet s μ)
    (h : ∀ φ : 𝓓((⊤ : Opens E), E), (∀ x, 0 ≤ ⟪φ x, ν⟫) →
      0 ≤ ∫ x, divergenceCLM φ x * s.indicator 1 x ∂μ) :
    s =ᵐ[μ] (∅ : Set E) ∨ s =ᵐ[μ] (univ : Set E) ∨ ∃ c : ℝ, s =ᵐ[μ] {x | ⟪x, ν⟫ < c} := by
  have hu : LocallyIntegrable (s.indicator (1 : E → ℝ)) μ :=
    LocallyIntegrable.indicator₀ (locallyIntegrable_const (1 : ℝ)) hs
  refine ae_eq_empty_or_univ_or_setOf_inner_lt_of_preimage_add_ae_le hs fun w hw => ?_
  -- Testing with `ψ w` shows that `∂_w χ_s` is nonpositive.
  have hmono := ae_apply_add_le_of_forall_integral_lineDeriv_mul_nonneg (v := w) hu fun ψ hψ => by
    rw [← divergenceCLM_postcompCLM_toSpanSingleton]
    exact h _ fun x => by simpa [real_inner_smul_left] using mul_nonneg (hψ x) hw
  filter_upwards [hmono] with x hx hxs
  by_contra hx'
  have h10 : (1 : ℝ) ≤ 0 := by
    simpa [indicator_of_mem (mem_preimage.1 hxs), indicator_of_notMem hx'] using hx
  linarith

/-- **Sets of locally finite perimeter with a constant outer normal are half-spaces.** If `s` has
locally finite perimeter in `E` and its measure-theoretic outer normal equals `ν` almost
everywhere for the perimeter measure `|Dχ_s|`, then `s` is almost everywhere equal to the empty
set, the whole space, or a half-space `{x | ⟪x, ν⟫ < c}`. -/
theorem ae_eq_empty_or_univ_or_setOf_inner_lt_of_outerNormal_ae_eq
    (hu : LocallyIntegrable (s.indicator (1 : E → ℝ)) μ)
    (hfin : ∀ K, IsCompact K →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hν : ∀ᵐ y : (⊤ : Opens E) ∂variationMeasure μ ⊤ (s.indicator 1),
      outerNormal μ ⊤ s y = ν) :
    s =ᵐ[μ] (∅ : Set E) ∨ s =ᵐ[μ] (univ : Set E) ∨ ∃ c : ℝ, s =ᵐ[μ] {x | ⟪x, ν⟫ < c} := by
  have hs : NullMeasurableSet s μ :=
    (aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable
  refine ae_eq_empty_or_univ_or_setOf_inner_lt_of_integral_divergenceCLM_mul_indicator_nonneg hs
    fun φ hφ => ?_
  rw [integral_divergenceCLM_mul_indicator_eq_integral_inner_outerNormal (hu.locallyIntegrableOn _)
    (fun K hK _ => hfin K hK)]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hν] with y hy
  rw [hy]
  exact hφ y

end TauCeti
