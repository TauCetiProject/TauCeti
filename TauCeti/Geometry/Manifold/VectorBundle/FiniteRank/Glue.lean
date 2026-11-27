/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Glue
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousLinearEquiv

/-!
# Real `C^n` regularity of glued finite-rank cores

Let `D : GluingData Φ` glue `P` near `K` to `Q` along `Φ : P ⟶ Q`, over a real manifold `M`, with
scalars in a normed `ℝ`-algebra `𝕜` such as `ℂ`. If the transitions of `Q` and the chart operators
of `Φ` are real `C^n` on their chart overlaps, and those of `P` inside `V`, then so are the
transitions of the glued core (`GluingData.contMDiffOn_coordChange_glue`) and the chart operators
of the isomorphism `D.glueIso` with `Q` in both directions
(`GluingData.contMDiffOn_inChartCoordinates_glueIso_hom`,
`GluingData.contMDiffOn_inChartCoordinates_glueIso_inv`). Every transition and chart operator is
built from these by composing with the fixed reindexing equivalence and by inverting operators,
and inversion is `C^n` where it is applied (`ContMDiffOn.clm_inverse`).

The transitions of `Q` are assumed real `C^n` on chart overlaps, as in
`SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore`, and those of `P` only on the parts of
chart overlaps inside `V`, since charts of `P` are used only there; this covers a pullback of `Q`
along a map which is smooth only near `K`. The morphism `Φ` is assumed real `C^n`
in charts: for all labels `i` and `j`, its fibre maps read in the chart `i` of `P` and the chart `j`
of `Q`, `x ↦ P.core.inChartCoordinates Q.core i j x (Φ.fiberMap x)`, are real `C^n` on the overlap
of the two charts.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore.GluingData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {P Q : FiniteRankBundleCore 𝕜 M} {Φ : P ⟶ Q} (D : GluingData Φ)

/-- Precomposing operators with the reindexing back to the coordinates of `P` is real `C^n`. -/
theorem contDiff_comp_rankEquiv_symm {m : ℕ} :
    ContDiff ℝ n fun f : (Fin P.rank → 𝕜) →L[𝕜] (Fin m → 𝕜) ↦
      f.comp D.rankEquiv.symm.toContinuousLinearMap :=
  (contDiff_id.clm_comp contDiff_const).restrict_scalars ℝ

/-- Postcomposing operators with the reindexing to the coordinates of `Q` is real `C^n`. -/
theorem contDiff_rankEquiv_comp {m : ℕ} :
    ContDiff ℝ n fun f : (Fin m → 𝕜) →L[𝕜] (Fin P.rank → 𝕜) ↦
      D.rankEquiv.toContinuousLinearMap.comp f :=
  (contDiff_const.clm_comp contDiff_id).restrict_scalars ℝ

section

variable
  (hQ : ∀ i j, ContMDiffOn I 𝓘(ℝ, (Fin Q.rank → 𝕜) →L[𝕜] (Fin Q.rank → 𝕜)) n
    (Q.core.coordChange i j) (Q.core.baseSet i ∩ Q.core.baseSet j))
  (hΦ : ∀ i j, ContMDiffOn I 𝓘(ℝ, (Fin P.rank → 𝕜) →L[𝕜] (Fin Q.rank → 𝕜)) n
    (fun x ↦ P.core.inChartCoordinates Q.core i j x (Φ.fiberMap x))
    (P.core.baseSet i ∩ Q.core.baseSet j))

include hQ hΦ

/-- Reading a chart of the glued core in a chart of `Q` is real `C^n` when the transitions of `Q`
and the chart operators of `Φ` are. -/
theorem contMDiffOn_chartToQ (i k : M) :
    ContMDiffOn I 𝓘(ℝ, (Fin Q.rank → 𝕜) →L[𝕜] (Fin Q.rank → 𝕜)) n (D.chartToQ i k)
      (D.baseSet i ∩ Q.core.baseSet k) := by
  by_cases hi : i ∈ D.V
  · exact ((ContDiff.contMDiff D.contDiff_comp_rankEquiv_symm).comp_contMDiffOn
      ((hΦ i k).mono (inter_subset_inter_left _ (D.baseSet_subset_of_mem hi)))).congr
        fun x _ ↦ D.chartToQ_of_mem hi
  · exact ((hQ i k).mono (inter_subset_inter_left _ (D.baseSet_subset_of_notMem hi))).congr
      fun x _ ↦ D.chartToQ_of_notMem hi

/-- In charts, the comparison of the glued core with `Q` is real `C^n` when the transitions of `Q`
and the chart operators of `Φ` are. -/
theorem contMDiffOn_inChartCoordinates_glueIso_hom (i k : M) :
    ContMDiffOn I 𝓘(ℝ, (Fin D.glue.rank → 𝕜) →L[𝕜] (Fin Q.rank → 𝕜)) n
      (fun x ↦ D.glue.core.inChartCoordinates Q.core i k x (D.glueIso.hom.fiberMap x))
      (D.glue.core.baseSet i ∩ Q.core.baseSet k) :=
  (D.contMDiffOn_chartToQ hQ hΦ i k).congr fun _ hx ↦ by
    rw [glueIso_hom]
    exact D.inChartCoordinates_glueHom hx.1 hx.2

variable [CompleteSpace 𝕜]

/-- In charts, the inverse comparison of `Q` with the glued core is real `C^n` when the transitions
of `Q` and the chart operators of `Φ` are. -/
theorem contMDiffOn_inChartCoordinates_glueIso_inv (k i : M) :
    ContMDiffOn I 𝓘(ℝ, (Fin Q.rank → 𝕜) →L[𝕜] (Fin D.glue.rank → 𝕜)) n
      (fun x ↦ Q.core.inChartCoordinates D.glue.core k i x (D.glueIso.inv.fiberMap x))
      (Q.core.baseSet k ∩ D.glue.core.baseSet i) := by
  have hs : Q.core.baseSet k ∩ D.glue.core.baseSet i ⊆ D.baseSet i ∩ Q.core.baseSet k :=
    fun _ hx ↦ ⟨hx.2, hx.1⟩
  exact (((D.contMDiffOn_chartToQ hQ hΦ i k).mono hs).clm_inverse fun x hx ↦
    D.isInvertible_chartToQ (hs hx).1 (hs hx).2).congr fun _ hx ↦
      D.inChartCoordinates_glueIso_inv hx.1 hx.2

/-- The transitions of the glued core are real `C^n` when those of `Q` and the chart operators of
`Φ` are, and those of `P` are inside `V`, the only place where charts of `P` are used. -/
theorem contMDiffOn_coordChange_glue
    (hP : ∀ i j, ContMDiffOn I 𝓘(ℝ, (Fin P.rank → 𝕜) →L[𝕜] (Fin P.rank → 𝕜)) n
      (P.core.coordChange i j) (P.core.baseSet i ∩ P.core.baseSet j ∩ D.V)) (i j : M) :
    ContMDiffOn I 𝓘(ℝ, (Fin D.glue.rank → 𝕜) →L[𝕜] (Fin D.glue.rank → 𝕜)) n
      (D.glue.core.coordChange i j) (D.glue.core.baseSet i ∩ D.glue.core.baseSet j) := by
  have hpost := ContDiff.contMDiff (D.contDiff_rankEquiv_comp (n := n) (m := Q.rank))
  simp only [baseSet_glue]
  by_cases hjV : j ∈ D.V
  · by_cases hiV : i ∈ D.V
    · have hpre := ContDiff.contMDiff (D.contDiff_comp_rankEquiv_symm (n := n) (m := P.rank))
      exact (hpost.comp_contMDiffOn (hpre.comp_contMDiffOn ((hP i j).mono fun x hx ↦
        ⟨D.baseSet_inter_subset_of_mem_of_mem hiV hjV hx, (D.baseSet_of_mem hiV ▸ hx.1).2⟩))).congr
          fun x _ ↦ D.coordChange_of_mem_of_mem hiV hjV
    · have hs := D.baseSet_inter_subset_of_notMem_of_mem hiV hjV
      exact (hpost.comp_contMDiffOn (((hΦ j i).mono hs).clm_inverse fun x hx ↦
        D.isInvertible_inChartCoordinates hjV hx.2 (hs hx).2)).congr
          fun x _ ↦ D.coordChange_of_notMem_of_mem hiV hjV
  · exact ((D.contMDiffOn_chartToQ hQ hΦ i j).mono (D.baseSet_inter_subset_of_notMem hjV)).congr
      fun x _ ↦ D.coordChange_of_notMem hjV

end

end TauCeti.FiniteRankBundleCore.GluingData
