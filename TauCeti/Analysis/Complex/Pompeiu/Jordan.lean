/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Cycle
public import TauCeti.Analysis.Contour.Cycle.Jordan

/-!
# The Cauchy–Pompeiu formula on finitely connected Jordan regions

Specializing the frontier-based contour-cycle Cauchy–Pompeiu formula
(`TauCeti.cauchyPompeiu_smul_of_trace_subset_frontier` and
`TauCeti.cauchyPompeiu_of_trace_subset_frontier`) to `Contour.jordanRegion γ₀ s γ` and its
positively oriented boundary cycle `Contour.jordanBoundaryCycle γ₀ s γ` gives the
Cauchy–Pompeiu formula on finitely connected Jordan regions.

## Main results

* `TauCeti.cauchyPompeiu_jordanBoundaryCycle_smul`
* `TauCeti.cauchyPompeiu_jordanBoundaryCycle`

## References

* A. Rainer, *Advanced Complex Analysis*, Proposition 10.1, p. 23.
* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Section 1.2.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace TauCeti

section JordanRegion

variable {ι : Type*}

/-- **Cauchy–Pompeiu formula on a finitely connected Jordan region (Banach-valued).** Given an
outer simple closed absolutely continuous curve `γ₀` and simple closed absolutely continuous hole
curves `(γ i)_{i ∈ s}` whose filled hulls are pairwise disjoint and contained in the inside of `γ₀`,
let `Δ := Contour.jordanRegion γ₀ s γ` be the resulting finitely connected Jordan region. For any
real `C¹` map `f : ℂ → E` on an open neighborhood `Ω` of `closure Δ` into a complex Banach space `E`
and any `ξ ∈ Δ`, `f ξ` is represented by integrating over `Contour.jordanBoundaryCycle γ₀ s γ` and
over `Δ`. -/
theorem cauchyPompeiu_jordanBoundaryCycle_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {γ₀ : Contour.AbsolutelyContinuousClosedCurve}
    {s : Finset ι} {γ : ι → Contour.AbsolutelyContinuousClosedCurve} {Ω : Set ℂ}
    (hab₀ : γ₀.a ≠ γ₀.b) (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : IsOpen Ω) (hclosure : closure (Contour.jordanRegion γ₀ s γ) ⊆ Ω)
    (f : ℂ → E) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Contour.jordanRegion γ₀ s γ) :
    f ξ = (2 * (Real.pi : ℂ) * I)⁻¹ •
        (Contour.jordanBoundaryCycle γ₀ s γ).integral (fun z ↦ (z - ξ)⁻¹ • f z) -
      (Real.pi : ℂ)⁻¹ • ∫ z in Contour.jordanRegion γ₀ s γ,
        (z - ξ)⁻¹ • conjWirtingerDeriv f z 1 :=
  cauchyPompeiu_smul_of_trace_subset_frontier hΩ Contour.isOpen_jordanRegion hclosure
    (Contour.jordanBoundaryCycle γ₀ s γ)
    (Contour.Cycle.trace_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj).subset
    (fun _ hz ↦ Contour.Cycle.windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hz)
    f hf hξ

/-- **Cauchy–Pompeiu formula on a finitely connected Jordan region.** Given an outer simple closed
absolutely continuous curve `γ₀` and simple closed absolutely continuous hole curves
`(γ i)_{i ∈ s}` whose filled hulls are pairwise disjoint and contained in the inside of `γ₀`, let
`Δ := Contour.jordanRegion γ₀ s γ` be the resulting finitely connected Jordan region. For any real
`C¹` function `f : ℂ → ℂ` on an open neighborhood `Ω` of `closure Δ` and any `ξ ∈ Δ`, `f ξ` is
represented by integrating over `Contour.jordanBoundaryCycle γ₀ s γ` and over `Δ`, written with the
real directional derivatives `f_x + i f_y = 2 \bar∂ f`. -/
theorem cauchyPompeiu_jordanBoundaryCycle {γ₀ : Contour.AbsolutelyContinuousClosedCurve}
    {s : Finset ι} {γ : ι → Contour.AbsolutelyContinuousClosedCurve} {Ω : Set ℂ}
    (hab₀ : γ₀.a ≠ γ₀.b) (hinj₀ : InjOn γ₀ (Ico (min γ₀.a γ₀.b) (max γ₀.a γ₀.b)))
    (hab : ∀ i ∈ s, (γ i).a ≠ (γ i).b)
    (hinj : ∀ i ∈ s, InjOn (γ i) (Ico (min (γ i).a (γ i).b) (max (γ i).a (γ i).b)))
    (hsub : ∀ i ∈ s, filledHull (γ i '' uIcc (γ i).a (γ i).b) ⊆
      filledHull (γ₀ '' uIcc γ₀.a γ₀.b) \ (γ₀ '' uIcc γ₀.a γ₀.b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i ↦ filledHull (γ i '' uIcc (γ i).a (γ i).b))
    (hΩ : IsOpen Ω) (hclosure : closure (Contour.jordanRegion γ₀ s γ) ⊆ Ω)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f Ω) {ξ : ℂ} (hξ : ξ ∈ Contour.jordanRegion γ₀ s γ) :
    f ξ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Contour.jordanBoundaryCycle γ₀ s γ).integral (fun z ↦ f z / (z - ξ)) -
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ z in Contour.jordanRegion γ₀ s γ,
          (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / (z - ξ) :=
  cauchyPompeiu_of_trace_subset_frontier hΩ Contour.isOpen_jordanRegion hclosure
    (Contour.jordanBoundaryCycle γ₀ s γ)
    (Contour.Cycle.trace_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj).subset
    (fun _ hz ↦ Contour.Cycle.windingNumber_jordanBoundaryCycle hab₀ hinj₀ hab hinj hsub hdisj hz)
    f hf hξ

end JordanRegion

end TauCeti

end
