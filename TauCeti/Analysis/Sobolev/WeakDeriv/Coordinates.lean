/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Finite-coordinate characterization of weak derivatives

Weak differentiation of a function with finite-dimensional real normed codomain is equivalent
to weak differentiation of its scalar coordinates in any finite basis. Each direction includes
local integrability and the distributional identity for every scalar coordinate, for any measure
and open set, including a zero-dimensional codomain. For an arbitrary complete codomain, a locally
integrable candidate is a weak derivative as soon as its images under all continuous linear
functionals are, since these separate points (Hahn–Banach).

## Main declarations

* `hasWeakLineDerivOn_iff_coordinates`: directional weak derivatives in scalar coordinates.
* `hasWeakFDerivOn_iff_coordinates`: the corresponding Fréchet weak derivative criterion.
* `hasWeakLineDerivOn_of_forall_strongDual`, `hasWeakFDerivOn_of_forall_strongDual`: the
  criteria by continuous linear functionals, for any complete codomain.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Finite ι] {μ : Measure E} {Ω : Opens E}

/-- Weak directional differentiation with finite-dimensional codomain is equivalent to
weak differentiation of all scalar coordinates. -/
theorem hasWeakLineDerivOn_iff_coordinates (b : Module.Basis ι ℝ F)
    {u u' : E → F} {v : E} :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ i, HasWeakLineDerivOn μ Ω (fun x ↦ b.coord i (u x))
        (fun x ↦ b.coord i (u' x)) v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro h i
    exact h.clm_comp (b.coord i).toContinuousLinearMap
  · intro h
    have hs := HasWeakLineDerivOn.sum Finset.univ (fun i _ ↦
      (h i).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)))
    have hu : (fun x ↦ ∑ i, b.coord i (u x) • b i) = u := by
      funext x
      exact b.sum_repr (u x)
    have hu' : (fun x ↦ ∑ i, b.coord i (u' x) • b i) = u' := by
      funext x
      exact b.sum_repr (u' x)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, hu, hu'] using hs

/-- A finite-dimensional weak Fréchet derivative is detected by scalar coordinates in any
finite basis of the codomain. -/
theorem hasWeakFDerivOn_iff_coordinates (b : Module.Basis ι ℝ F)
    {u : E → F} {D : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ Ω u D ↔
      ∀ i, HasWeakFDerivOn μ Ω (fun x ↦ b.coord i (u x))
        (fun x ↦ (b.coord i).toContinuousLinearMap.comp (D x)) := by
  simp only [hasWeakFDerivOn_iff, hasWeakLineDerivOn_iff_coordinates b,
    ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
  exact forall_comm

section StrongDual

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Continuous linear functionals detect weak directional derivatives: for locally integrable
`u` and `u'` with complete codomain, it suffices that `ℓ ∘ u'` be a weak derivative of `ℓ ∘ u`
for every `ℓ`. No finite-dimensionality is needed. -/
theorem hasWeakLineDerivOn_of_forall_strongDual {u u' : E → G} {v : E}
    (hu : LocallyIntegrableOn u Ω μ) (hu' : LocallyIntegrableOn u' Ω μ)
    (h : ∀ ℓ : StrongDual ℝ G,
      HasWeakLineDerivOn μ Ω (fun x ↦ ℓ (u x)) (fun x ↦ ℓ (u' x)) v) :
    HasWeakLineDerivOn μ Ω u u' v := by
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance, hu, hu', fun φ ↦ ?_⟩
  have h₁ := integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v
  have h₂ : Integrable (fun x ↦ (φ : E → ℝ) x • u' x) μ := TestFunction.integrable_smul φ hu'
  rw [← sub_eq_zero, sub_neg_eq_add]
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  have hℓ := (h ℓ).integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [map_add, ← ℓ.integral_comp_comm h₁, ← ℓ.integral_comp_comm h₂]
  simp only [map_smul]
  rw [hℓ, neg_add_cancel]

/-- Continuous linear functionals detect weak Fréchet derivatives with complete codomain, given
local integrability of the function and of each directional component of the candidate. -/
theorem hasWeakFDerivOn_of_forall_strongDual {u : E → G} {D : E → E →L[ℝ] G}
    (hu : LocallyIntegrableOn u Ω μ) (hD : ∀ v, LocallyIntegrableOn (fun x ↦ D x v) Ω μ)
    (h : ∀ ℓ : StrongDual ℝ G,
      HasWeakFDerivOn μ Ω (fun x ↦ ℓ (u x)) (fun x ↦ ℓ.comp (D x))) :
    HasWeakFDerivOn μ Ω u D :=
  hasWeakFDerivOn_iff.2 fun v ↦
    hasWeakLineDerivOn_of_forall_strongDual hu (hD v) fun ℓ ↦ (h ℓ).hasWeakLineDerivOn v

end StrongDual

end TauCeti
