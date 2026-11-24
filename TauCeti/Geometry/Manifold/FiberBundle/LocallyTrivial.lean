/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological
public import TauCeti.Geometry.Manifold.Instances.EuclideanProd
public import TauCeti.Topology.Homotopy.SerreFibration.TotalSpace

/-!
# Charts on the total space of a locally trivial map

Let `proj : Z → B` be a locally trivial map with fibre `F`: every point of `B` lies in the base
set of a trivialization `e : Z ⊇ proj⁻¹(U) ≃ₜ U × F` (`Bundle.Trivialization F proj`). The
trivializations are open partial homeomorphisms from `Z` to `B × F` covering `Z`, so they chart `Z`
on the product `B × F` (`TauCeti.chartedSpaceOfExistsTrivialization`). The atlas consists of all
trivializations, and the chart at `z` is one whose base set contains `proj z`; each chart keeps the
base coordinate (`TauCeti.chartedSpaceOfExistsTrivialization_chartAt_fst`).

Mathlib charts the total space `Bundle.TotalSpace F E` of a fibre bundle in the same way
(`FiberBundle.chartedSpace'`). Here the total space is an arbitrary topological space and the
trivializations are not part of a `FiberBundle` structure; this covers locally trivial maps that
arise as subspaces, such as sphere bundles cut out of a product by orthogonality conditions.

When the base and the fibre are themselves charted on Euclidean spaces `𝕜ⁿ` and `𝕜ᵐ`, composing
with their product charts charts `Z` on `𝕜ⁿ⁺ᵐ`
(`TauCeti.euclideanChartedSpaceOfExistsTrivialization`). For `𝕜 = ℝ` and `Z` Hausdorff, this makes
`Z` a topological manifold of dimension `n + m` without boundary, the setting of homological
orientations and fundamental classes (`TauCeti.HomologicalOrientation`). If the base and the fibre
are simply connected, so is `Z`, and it is orientable
(`TauCeti.nonempty_homologicalOrientation_of_exists_trivialization`).

## Main definitions

* `TauCeti.chartedSpaceOfExistsTrivialization`: a locally trivial map with fibre `F` charts its
  total space on `B × F`.
* `TauCeti.euclideanChartedSpaceOfExistsTrivialization`: when `B` and `F` are charted on `𝕜ⁿ` and
  `𝕜ᵐ`, the total space is charted on `𝕜ⁿ⁺ᵐ`.

## Main results

* `TauCeti.mem_atlas_chartedSpaceOfExistsTrivialization_iff`: the charts are the
  trivializations.
* `TauCeti.exists_chartedSpaceOfExistsTrivialization_chartAt_eq`: the chart at `z` is a
  trivialization whose base set contains `proj z`.
* `TauCeti.euclideanChartedSpaceOfExistsTrivialization_chartAt`: the Euclidean chart at `z` is the
  chart at `z` followed by the product of the charts of `B` at `proj z` and of `F` at the fibre
  coordinate of `z`.
* `TauCeti.nonempty_homologicalOrientation_of_exists_trivialization`: with simply connected base
  and fibre, the total space has a homological orientation.
-/

public section

open Bundle

namespace TauCeti

section Charts

variable {Z B F : Type*} [TopologicalSpace Z] [TopologicalSpace B] [TopologicalSpace F]
  {proj : Z → B}

/-- **The total space of a locally trivial map is charted on the product of the base and the
fibre.** If every point of `B` lies in the base set of a trivialization of `proj : Z → B` with
fibre `F`, the trivializations chart `Z` on `B × F`. The atlas consists of all trivializations, and
the chart at `z` is a trivialization, chosen once and for all, whose base set contains `proj z`. -/
@[instance_reducible]
noncomputable def chartedSpaceOfExistsTrivialization
    (h : ∀ b, ∃ e : Trivialization F proj, b ∈ e.baseSet) : ChartedSpace (B × F) Z where
  atlas := Set.range fun e : Trivialization F proj ↦ e.toOpenPartialHomeomorph
  chartAt z := (h (proj z)).choose.toOpenPartialHomeomorph
  mem_chart_source z := (h (proj z)).choose.mem_source.2 (h (proj z)).choose_spec
  chart_mem_atlas _ := ⟨_, rfl⟩

variable (h : ∀ b, ∃ e : Trivialization F proj, b ∈ e.baseSet)

/-- The charts of `TauCeti.chartedSpaceOfExistsTrivialization` are the trivializations. -/
theorem mem_atlas_chartedSpaceOfExistsTrivialization_iff {c : OpenPartialHomeomorph Z (B × F)} :
    c ∈ (letI := chartedSpaceOfExistsTrivialization h; atlas (B × F) Z) ↔
      ∃ e : Trivialization F proj, e.toOpenPartialHomeomorph = c :=
  Iff.rfl

/-- The chart at `z` of `TauCeti.chartedSpaceOfExistsTrivialization` is a trivialization whose base
set contains `proj z`. -/
theorem exists_chartedSpaceOfExistsTrivialization_chartAt_eq (z : Z) :
    ∃ e : Trivialization F proj, proj z ∈ e.baseSet ∧
      (letI := chartedSpaceOfExistsTrivialization h; chartAt (B × F) z) =
        e.toOpenPartialHomeomorph :=
  ⟨_, (h (proj z)).choose_spec, rfl⟩

/-- The charts of `TauCeti.chartedSpaceOfExistsTrivialization` keep the base coordinate: on its
source, the first coordinate of a chart is the projection. -/
@[simp]
theorem chartedSpaceOfExistsTrivialization_chartAt_fst (z : Z) {y : Z}
    (hy : y ∈ (letI := chartedSpaceOfExistsTrivialization h; chartAt (B × F) z).source) :
    ((letI := chartedSpaceOfExistsTrivialization h; chartAt (B × F) z) y).1 = proj y := by
  obtain ⟨e, -, he⟩ := exists_chartedSpaceOfExistsTrivialization_chartAt_eq h z
  rw [he] at hy ⊢
  exact e.coe_fst hy

/-- The base coordinate of `z` in its own chart is `proj z`. -/
theorem chartedSpaceOfExistsTrivialization_chartAt_self_fst (z : Z) :
    ((letI := chartedSpaceOfExistsTrivialization h; chartAt (B × F) z) z).1 = proj z :=
  chartedSpaceOfExistsTrivialization_chartAt_fst h z
    (letI := chartedSpaceOfExistsTrivialization h; mem_chart_source (B × F) z)

section Euclidean

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) B]
  [ChartedSpace (EuclideanSpace 𝕜 (Fin m)) F]

/-- **The total space of a locally trivial map with Euclidean base and fibre is charted on the
Euclidean space of the sum of the dimensions.** If `B` and `F` are charted on `𝕜ⁿ` and `𝕜ᵐ`, the
charts of `TauCeti.chartedSpaceOfExistsTrivialization` followed by the product charts of `B × F`
(`TauCeti.prodEuclideanChartedSpace`) chart `Z` on `𝕜ⁿ⁺ᵐ`. -/
@[instance_reducible]
noncomputable def euclideanChartedSpaceOfExistsTrivialization :
    ChartedSpace (EuclideanSpace 𝕜 (Fin (n + m))) Z :=
  letI := chartedSpaceOfExistsTrivialization h
  letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := B) (N := F)
  ChartedSpace.comp _ (B × F) Z

/-- The chart at `z` of `TauCeti.euclideanChartedSpaceOfExistsTrivialization` is the chart at `z`
of `TauCeti.chartedSpaceOfExistsTrivialization`, followed by the product of the chart of `B` at
`proj z` and the chart of `F` at the fibre coordinate of `z`, followed by the identification of
`𝕜ⁿ × 𝕜ᵐ` with `𝕜ⁿ⁺ᵐ`. -/
theorem euclideanChartedSpaceOfExistsTrivialization_chartAt (z : Z) :
    (letI := euclideanChartedSpaceOfExistsTrivialization (𝕜 := 𝕜) (n := n) (m := m) h;
      chartAt (EuclideanSpace 𝕜 (Fin (n + m))) z) =
      (letI := chartedSpaceOfExistsTrivialization h;
        (chartAt (B × F) z).trans
          (((chartAt (EuclideanSpace 𝕜 (Fin n)) (proj z)).prod
            (chartAt (EuclideanSpace 𝕜 (Fin m)) (chartAt (B × F) z z).2)).trans
            EuclideanSpace.finAddEquivProd.symm.toHomeomorph.toOpenPartialHomeomorph)) := by
  let := chartedSpaceOfExistsTrivialization h
  let := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := B) (N := F)
  -- Up to the base point `proj z` of the chart of `B`, which is the base coordinate of `z` in its
  -- own chart, both sides are the composite chart of `ChartedSpace.comp`.
  rw [← chartedSpaceOfExistsTrivialization_chartAt_self_fst h z,
    ← prodEuclideanChartedSpace_chartAt]
  exact chartAt_comp _ (B × F) z

end Euclidean

end Charts

section Orientation

variable {Z : Type} {B F : Type*} [TopologicalSpace Z] [T2Space Z] [TopologicalSpace B]
  [TopologicalSpace F] {proj : Z → B} {n m : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) F] [SimplyConnectedSpace B] [SimplyConnectedSpace F]

/-- **The total space of a locally trivial map with simply connected base and fibre is
orientable.** If `B` and `F` are simply connected and charted on `ℝⁿ` and `ℝᵐ`, and the total space
`Z` of a locally trivial map `proj : Z → B` with fibre `F` is Hausdorff, then `Z`, charted on
`ℝⁿ⁺ᵐ` by `TauCeti.euclideanChartedSpaceOfExistsTrivialization`, has a homological orientation in
its dimension `n + m`: `Z` is simply connected, so a local orientation at one point extends. -/
theorem nonempty_homologicalOrientation_of_exists_trivialization
    (h : ∀ b, ∃ e : Trivialization F proj, b ∈ e.baseSet) :
    Nonempty (letI := euclideanChartedSpaceOfExistsTrivialization (𝕜 := ℝ) (n := n) (m := m) h;
      HomologicalOrientation Z (EuclideanSpace ℝ (Fin (n + m))) (n + m)) := by
  have := simplyConnectedSpace_of_exists_trivialization h
  let := euclideanChartedSpaceOfExistsTrivialization (𝕜 := ℝ) (n := n) (m := m) h
  exact HomologicalOrientation.nonempty_of_simplyConnectedSpace (by simp)

end Orientation

end TauCeti
