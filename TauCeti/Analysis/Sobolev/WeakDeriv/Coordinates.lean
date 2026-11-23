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
integrable candidate is a weak derivative as soon as its images under a point-separating family of
continuous linear maps are (`hasWeakLineDerivOn_of_forall_clm_comp`), and in particular when its
images under all continuous linear functionals are, since these separate points (Hahn–Banach).

## Main declarations

* `hasWeakLineDerivOn_iff_coordinates`: directional weak derivatives in scalar coordinates.
* `hasWeakFDerivOn_iff_coordinates`: the corresponding Fréchet weak derivative criterion.
* `hasWeakLineDerivOn_of_forall_clm_comp`: the criterion by any point-separating family of
  continuous linear maps, for any complete codomain.
* `hasWeakLineDerivOn_of_forall_strongDual`, `hasWeakFDerivOn_of_forall_strongDual`: the
  criteria by continuous linear functionals, for any complete codomain.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public noncomputable section

namespace TauCeti

open LineDeriv MeasureTheory TopologicalSpace

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

/-- A point-separating family of continuous linear maps detects weak directional derivatives: for
locally integrable `u` and `u'` with complete codomain `G`, it suffices that `L a ∘ u'` be a weak
derivative of `L a ∘ u` for every `a`. No finite-dimensionality is needed. -/
theorem hasWeakLineDerivOn_of_forall_clm_comp {α H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {u u' : E → G} {v : E} (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn u' Ω μ) (L : α → G →L[ℝ] H)
    (hsep : ∀ y z : G, (∀ a, L a y = L a z) → y = z)
    (hL : ∀ a, HasWeakLineDerivOn μ Ω (fun x ↦ L a (u x)) (fun x ↦ L a (u' x)) v) :
    HasWeakLineDerivOn μ Ω u u' v := by
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨‹CompleteSpace G›, hu, hu', fun φ ↦ ?_⟩
  apply hsep
  intro a
  have := (hL a).completeSpace
  have h1 := ContinuousLinearMap.integral_comp_comm (L a)
    (integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v)
  have h2 := ContinuousLinearMap.integral_comp_comm (L a) (TestFunction.integrable_smul φ hu')
  calc L a (∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ)
      = ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • L a (u x) ∂μ := by
          simpa only [Function.comp_def, map_smul] using h1.symm
    _ = -∫ x, (φ : E → ℝ) x • L a (u' x) ∂μ :=
          (hL a).integral_lineDeriv_smul_eq_neg_integral_smul φ
    _ = L a (-∫ x, (φ : E → ℝ) x • u' x ∂μ) := by
          rw [map_neg]
          congr 1
          simpa only [Function.comp_def, map_smul] using h2

/-- Continuous linear functionals detect weak directional derivatives: for locally integrable
`u` and `u'` with complete codomain, it suffices that `ℓ ∘ u'` be a weak derivative of `ℓ ∘ u`
for every `ℓ`. No finite-dimensionality is needed. -/
theorem hasWeakLineDerivOn_of_forall_strongDual {u u' : E → G} {v : E}
    (hu : LocallyIntegrableOn u Ω μ) (hu' : LocallyIntegrableOn u' Ω μ)
    (h : ∀ ℓ : StrongDual ℝ G,
      HasWeakLineDerivOn μ Ω (fun x ↦ ℓ (u x)) (fun x ↦ ℓ (u' x)) v) :
    HasWeakLineDerivOn μ Ω u u' v :=
  hasWeakLineDerivOn_of_forall_clm_comp hu hu' id
    (fun y z hyz ↦ sub_eq_zero.1 <|
      SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ by
        rw [map_sub, sub_eq_zero]
        exact hyz ℓ)
    h

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
