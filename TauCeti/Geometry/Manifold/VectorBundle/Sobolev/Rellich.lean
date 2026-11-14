/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Pi
public import TauCeti.Analysis.Sobolev.Wkp.FiniteCover
public import TauCeti.Analysis.Sobolev.Wkp.Local.Compactness
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer

/-!
# Rellich compactness for Sobolev sections of a vector bundle

Let `M` be a smooth Hausdorff manifold without boundary modelled on a finite-dimensional real inner
product space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F`, and let `A` be a finite bundle atlas, so that `M` is compact. For `1 ≤ p < ∞` and every order
`k`, the inclusion `W^{k+1,p}(V) → W^{k,p}(V)` of `TauCeti.SectionChartData.lowerOrderL` is a
compact operator (`TauCeti.SobolevSection.isCompactOperator_lowerOrderL`).

The local input is Rellich compactness on relatively compact subdomains,
`TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`. It does not apply directly to the chart
images `A.image j`, whose closures need not lie inside an open set on which the chart data are
controlled. Instead the chart data in chart `j` are transferred from the other charts with
`TauCeti.FiniteBundleAtlas.transferL` (`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`).

Shrink the chart domains to open sets `D i` with `closure (D i) ⊆ A.dom i` that still cover `M`.
The chart image `A.image j` is covered by the finitely many pieces `A.chart j '' (A.dom j ∩ D i)`
(`TauCeti.FiniteBundleAtlas.exists_transfer_cover`). On each piece the chart-`j` data are
transferred from the chart-`i` data restricted to `A.chart i '' D i`, which has compact closure
inside `A.image i`, so the piece data depend compactly on the section from order `k + 1` to order
`k`. Compactness on the pieces gives compactness on `A.image j`
(`TauCeti.Wkp.isCompactOperator_of_restrictL`), and compactness of every chart component gives
compactness into the Sobolev sections, which are closed in the product of the chartwise Sobolev
spaces (`TauCeti.SectionChartData.isCompactOperator_of_forall_apply`).

## Main results

* `TauCeti.SectionChartData.isCompactOperator_of_forall_apply`: a map into the Sobolev sections is
  a compact operator as soon as all its chart components are.
* `TauCeti.SobolevSection.isCompactOperator_lowerOrderL`: **Rellich's theorem** for Sobolev
  sections, `W^{k+1,p}(V) → W^{k,p}(V)` is compact.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter III, Theorem 2.6.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

section Components

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] {C : SectionChartData E F S}
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Compactness into Sobolev sections is componentwise.** If the chart transitions carry null
sets to null sets, a map into the Sobolev sections is a compact operator as soon as all its chart
components are. -/
theorem SectionChartData.isCompactOperator_of_forall_apply (hC : C.AETransition μ) {X : Type*}
    [TopologicalSpace X] [AddCommMonoid X] {f : X → C.sobolevSections μ p k}
    (hf : ∀ i m, IsCompactOperator fun x ↦ (f x : C.SobolevData μ p k) i m) :
    IsCompactOperator f :=
  (IsCompactOperator.pi fun i ↦ IsCompactOperator.pi fun m ↦ hf i m).codRestrict
    (fun x ↦ (f x).2) (isClosed_sobolevSections hC)

end Components

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

variable (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-! ### Rellich compactness -/

namespace SobolevSection

/-- **Rellich's theorem for Sobolev sections.** On a compact manifold without boundary, given by a
finite bundle atlas of a Hausdorff manifold, the inclusion `W^{k+1,p}(V) → W^{k,p}(V)` is a compact
operator for every order `k` and every `1 ≤ p < ∞`. -/
theorem isCompactOperator_lowerOrderL [T2Space M] (hp : p ≠ ⊤) :
    IsCompactOperator (A.sectionChartData.lowerOrderL μ p k) := by
  obtain ⟨P, Q, hP, hPc, hPD, hQc, hQ, hPQ, hcov⟩ := A.exists_transfer_cover
  have hPj (i j : Fin A.n) : P i j ≤ A.image j :=
    SetLike.coe_subset_coe.1 ((hP i j).trans (A.overlap_subset_image i j))
  have hQi (i : Fin A.n) : Q i ≤ A.image i :=
    SetLike.coe_subset_coe.1 (subset_closure.trans (hQ i))
  -- By local Rellich compactness, the chart-`i` data on `Q i` depend compactly on the section.
  have hrel (i : Fin A.n) : IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦ fun l ↦
      Wkp.restrictL (hQi i) k
        ((A.sectionChartData.lowerOrderL μ p k w : A.sectionChartData.SobolevData μ p k) i l) :=
    IsCompactOperator.pi fun l ↦ by
      convert (Wkp.isCompactOperator_restrictL_lowerOrderL (hQc i) (hQ i) k).comp_clm
        ((ContinuousLinearMap.proj l).comp
          ((ContinuousLinearMap.proj i).comp
            (A.sectionChartData.sobolevSections μ p (k + 1)).subtypeL))
        using 1
      funext w
      simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
      -- The inclusion followed by the two projections evaluates `w` at `i` and `l`. This holds
      -- by definition only, as the index type `Fin A.sectionChartData.n` unfolds to `Fin A.n`.
      exact congrArg _ ((SectionChartData.lowerOrderL_apply _ _ _ _ w i l).trans
        (Wkp.lowerOrderL_apply k _).symm)
  refine SectionChartData.isCompactOperator_of_forall_apply (A.aeTransition_sectionChartData μ)
    fun j m ↦ ?_
  -- The pieces `P i j` cover the image of chart `j`, and on `P i j` the chart-`j` data are
  -- transferred from the chart-`i` data on `Q i`.
  refine Wkp.isCompactOperator_of_restrictL (fun i ↦ hPj i j) (hcov j) fun i ↦ ?_
  convert (hrel i).clm_comp ((ContinuousLinearMap.proj m).comp
    (A.transferL μ p k hp i j (hPc i j) (hPD i j) (hPQ i j))) using 1
  funext w
  exact A.restrictL_eq_transferL μ p k hp (A.sectionChartData.lowerOrderL μ p k w).2 (hP i j)
    (hPc i j) (hPD i j) (hQi i) (hPQ i j) m

end SobolevSection

end Sobolev

end TauCeti
