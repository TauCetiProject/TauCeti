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
images `A.image i`, whose closures need not lie inside an open set on which the chart data are
controlled. Instead the chart data in chart `i` are transferred from the other charts with
`TauCeti.FiniteBundleAtlas.transferL` (`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`).

Shrink the chart domains to open sets `D j` with `closure (D j) ⊆ A.dom j` that still cover `M`.
The chart image `A.image i` is covered by the finitely many pieces `A.chart i '' (A.dom i ∩ D j)`
(`TauCeti.FiniteBundleAtlas.exists_transfer_cover`). On each piece the chart-`i` data are
transferred from the chart-`j` data restricted to `A.chart j '' D j`, which has compact closure
inside `A.image j`, so the piece data depend compactly on the section from order `k + 1` to order
`k`. Gluing the pieces with `TauCeti.Wkp.restrictCompatibleEquiv` gives compactness on `A.image i`,
and the space of Sobolev sections is closed in the product of the chartwise Sobolev spaces.

## Main results

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
  have hPi (i j : Fin A.n) : P i j ≤ A.image i :=
    SetLike.coe_subset_coe.1 ((hP i j).trans (A.overlap_subset_image j i))
  have hQi (j : Fin A.n) : Q j ≤ A.image j :=
    SetLike.coe_subset_coe.1 (subset_closure.trans (hQ j))
  -- On each piece, the chart-`i` data are transferred from the chart-`j` data on `Q j`, which
  -- depend compactly on the section by local Rellich compactness.
  have hpiece (i j : Fin A.n) (m : Fin (finrank ℝ F)) :
      IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦
        Wkp.restrictL (hPi i j) k
          (Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m)) := by
    have hrel : IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦ fun l ↦
        Wkp.restrictL (hQi j) k
          (Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) j l)) :=
      IsCompactOperator.pi fun l ↦ by
        convert (Wkp.isCompactOperator_restrictL_lowerOrderL (hQc j) (hQ j) k).comp_clm
          ((ContinuousLinearMap.proj l).comp
            ((ContinuousLinearMap.proj j).comp
              (A.sectionChartData.sobolevSections μ p (k + 1)).subtypeL))
          using 1
        funext w
        simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
        rw [Wkp.lowerOrderL_apply]
        rfl
    convert hrel.clm_comp ((ContinuousLinearMap.proj m).comp
      (A.transferL μ p k hp i j (hPc i j) (hPD i j) (hPQ i j))) using 1
    funext w
    have e (i' : Fin A.n) (m' : Fin (finrank ℝ F)) :
        (A.sectionChartData.lowerOrderL μ p k w : A.sectionChartData.SobolevData μ p k) i' m' =
          Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i' m') :=
      SectionChartData.lowerOrderL_apply _ _ _ _ w i' m'
    exact (congrArg (Wkp.restrictL (hPi i j) k) (e i m).symm).trans
      ((congrFun (A.restrictL_eq_transferL μ p k hp (A.sectionChartData.lowerOrderL μ p k w).2
        (hP i j) (hPc i j) (hPD i j) (hQi j) (hPQ i j)) m).trans
        (congrArg (fun u ↦ A.transferL μ p k hp i j (hPc i j) (hPD i j) (hPQ i j) u m)
          (funext fun l ↦ congrArg (Wkp.restrictL (hQi j) k) (e j l))))
  -- Gluing the pieces gives compactness of the chart-`i` components.
  have hchart (i : Fin A.n) (m : Fin (finrank ℝ F)) :
      IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦
        Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m) := by
    let R := Wkp.restrictCompatibleEquiv (mu := μ) (p := p) (Omega := A.sectionChartData.image i)
      (hPi i) (hcov i) k
    have hfam : IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦
        R (Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m)) := by
      convert (IsCompactOperator.pi fun j ↦ hpiece i j m).codRestrict
        (fun w ↦ Wkp.restrictL_mem_compatibleFamilies (hPi i) k
          (Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m)))
        (Wkp.isClosed_compatibleFamilies _ k) using 1
      funext w
      exact Subtype.ext (funext fun j ↦ by
        rw [Set.val_codRestrict_apply]
        exact Wkp.restrictCompatibleEquiv_apply_coe _ _ _ _ j)
    convert hfam.clm_comp R.symm.toContinuousLinearMap using 1
    funext w
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  have hmem (w : SobolevSection A μ p (k + 1)) :
      (fun i m ↦ Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m)) ∈
        A.sectionChartData.sobolevSections μ p k := by
    convert (A.sectionChartData.lowerOrderL μ p k w).2 using 1
    funext i m
    rw [SectionChartData.lowerOrderL_apply]
  have key : ⇑(A.sectionChartData.lowerOrderL μ p k) = fun w : SobolevSection A μ p (k + 1) ↦
      (⟨fun i m ↦ Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m),
        hmem w⟩ : A.sectionChartData.sobolevSections μ p k) :=
    funext fun w ↦ Subtype.ext <| funext fun i ↦ funext fun m ↦
      SectionChartData.lowerOrderL_apply A.sectionChartData μ p k w i m
  rw [key]
  exact (IsCompactOperator.pi fun (i : Fin A.sectionChartData.n) ↦
    IsCompactOperator.pi fun m ↦ hchart i m).codRestrict hmem
    (SectionChartData.isClosed_sobolevSections (A.aeTransition_sectionChartData μ))

end SobolevSection

end Sobolev

end TauCeti
