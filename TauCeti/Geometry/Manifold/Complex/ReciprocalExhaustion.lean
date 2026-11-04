/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.Morse.ScalarComposition
import TauCeti.Geometry.Manifold.Complex.SquaredDistance

/-!
# Morse indices of reciprocal plurisubharmonic exhaustions

At a nondegenerate critical point of a strictly plurisubharmonic function ρ on a complex
n-manifold, the Morse index of `(1 + ρ)⁻¹` is at least n, provided `ρ ≠ -1` at that point.
Indeed, its index is `2n` minus the index of ρ, which is at most n.

Combining this with Haar genericity of low-index squared-distance Morse functions along smooth
holomorphic immersions (`TauCeti.ae_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le`) and strict
plurisubharmonicity of squared distance
(`TauCeti.isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff`), for a smooth holomorphic
immersion `i : M → F` of a second-countable complex manifold into a finite-dimensional complex
inner product space and almost every center `a ∈ F`, `y ↦ (1 + ‖i y - a‖ ^ 2)⁻¹` is a real Morse
function whose critical points all have index at least `finrank ℂ E`
(`TauCeti.ae_isMorse_and_finrank_le_manifoldMorseIndex_inv_one_add_norm_sq_sub_comp`), and in
particular such a center `a : F` exists without any measurable-space hypothesis on `F`
(`TauCeti.exists_isMorse_and_finrank_le_manifoldMorseIndex_inv_one_add_norm_sq_sub_comp`).

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

open Function MeasureTheory Module
open scoped ContDiff Manifold

namespace TauCeti

section Pointwise

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) 2 M] {f : M → ℝ} {x : M}

/-- The reciprocal of one plus a strictly plurisubharmonic function has index at least the
complex dimension at every nondegenerate critical point of the original function where the
denominator is nonzero.
The complementary-index formula is
`manifoldMorseIndex_inv_one_add_add_manifoldMorseIndex_eq_finrank` in the
`IsManifoldNondegenerateCriticalPoint` namespace. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.le_manifoldMorseIndex_inv_one_add
    (h : IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hc : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) (hf : 1 + f x ≠ 0) :
    Module.finrank ℂ E ≤ manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ (1 + f y)⁻¹) x := by
  have hbound := h.manifoldMorseIndex_le hc.contMDiffAt
    (mvfderiv_eq_zero_iff.mp hc.mvfderiv_eq_zero)
  have hsum := hc.manifoldMorseIndex_inv_one_add_add_manifoldMorseIndex_eq_finrank hf
  have hdim : Module.finrank ℝ E = 2 * Module.finrank ℂ E :=
    finrank_real_eq_two_mul_finrank_complex
  omega

end Pointwise

section Immersion

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [SecondCountableTopology M]
  {i : M → F}

/-- **Generic high-index reciprocal squared-distance Morse functions on a holomorphically immersed
manifold.** For a smooth holomorphic immersion `i : M → F` of a second-countable complex manifold
into a finite-dimensional complex inner product space and almost every `a ∈ F` (with respect to any
Haar measure `μ`), `y ↦ (1 + ‖i y - a‖ ^ 2)⁻¹` is a real Morse function on `M` whose critical points
all have Morse index at least `finrank ℂ E`. -/
theorem ae_isMorse_and_finrank_le_manifoldMorseIndex_inv_one_add_norm_sq_sub_comp
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) i x)) :
    ∀ᵐ a ∂μ, IsMorse 𝓘(ℝ, E) (fun y ↦ (1 + ‖i y - a‖ ^ 2)⁻¹) ∧
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ (1 + ‖i y - a‖ ^ 2)⁻¹),
        finrank ℂ E ≤ manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ (1 + ‖i y - a‖ ^ 2)⁻¹) x := by
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  have : IsManifold 𝓘(ℂ, E) 2 M := .of_le (n := ∞) (by norm_cast)
  filter_upwards [ae_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le μ hi hinj] with a ⟨ha, _⟩
  have hpos : ∀ y, 1 + ‖i y - a‖ ^ 2 ≠ 0 := fun y ↦ by positivity
  refine ⟨ha.inv_one_add hpos, fun x hx ↦ ?_⟩
  have hderiv : deriv (fun t : ℝ ↦ (1 + t)⁻¹) (‖i x - a‖ ^ 2) ≠ 0 := by
    rw [deriv_fun_inv'' (differentiableAt_id.const_add 1) (hpos x)]
    simp [hpos x]
  have hx' : x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) :=
    (mem_criticalPoints_scalar_comp_iff (φ := fun t ↦ (1 + t)⁻¹)
      ((ha.contMDiff x).mdifferentiableAt (by simp)) hderiv).1 hx
  have hpsh : IsManifoldStrictlyPlurisubharmonicAt E (fun y ↦ ‖i y - a‖ ^ 2) x :=
    (isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff ((hi x).of_le (by norm_cast))).2
      (injective_mvfderiv_iff.2 (hinj x))
  exact hpsh.le_manifoldMorseIndex_inv_one_add
    (ha.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx') (hpos x)

/-- **Existence of a high-index reciprocal squared-distance Morse function on a holomorphically
immersed manifold.** -/
theorem exists_isMorse_and_finrank_le_manifoldMorseIndex_inv_one_add_norm_sq_sub_comp
    (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) i x)) :
    ∃ a : F, IsMorse 𝓘(ℝ, E) (fun y ↦ (1 + ‖i y - a‖ ^ 2)⁻¹) ∧
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ (1 + ‖i y - a‖ ^ 2)⁻¹),
        finrank ℂ E ≤ manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ (1 + ‖i y - a‖ ^ 2)⁻¹) x := by
  let _ : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact
    (ae_isMorse_and_finrank_le_manifoldMorseIndex_inv_one_add_norm_sq_sub_comp Measure.addHaar hi
      hinj).exists

end Immersion

end TauCeti
