/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Joining two charts with disjoint sources

Let `M` be a manifold modelled on a nontrivial normed space `E`, with the model `𝓘(𝕜, E)`. Two
charts `e₁` and `e₂` of the maximal `C^n` atlas with disjoint sources need not have disjoint
targets, so they cannot be glued directly. If both targets are bounded, translating the second
chart by a long enough vector `v` separates the targets, and the two charts then glue to a single
chart of the maximal atlas, equal to `e₁` on the source of `e₁` and to `e₂ + v` on the source of
`e₂` (`OpenPartialHomeomorph.exists_mem_maximalAtlas_of_disjoint_source`). Restricting a chart `e`
over an open set `W` with compact closure in its target, and a chart `c` to a neighbourhood of a
compact set `S` away from `e⁻¹(closure W)`, gives a chart that contains `S` in its source and has
the same inverse as `e` on `W` (`OpenPartialHomeomorph.exists_mem_maximalAtlas_eqOn_symm`). On a
manifold modelled on a nontrivial finite-dimensional real space, a compact set `K` then carries a
finite smooth partition of unity each of whose pieces lies in the source of a chart agreeing with a
given chart `e` over a compact subset of its target
(`IsCompact.exists_smoothPartition_mem_maximalAtlas_eqOn_symm`).

Any open neighbourhood `U` of a point `x` contains the source of a chart of the maximal atlas at
`x`, the preferred chart at `x` restricted to `U`
(`OpenPartialHomeomorph.exists_mem_maximalAtlas_source_subset`).

Such charts see two distant regions of `M` at once. Since chart compressions of operators are
taken in every chart of the maximal atlas, this lets a statement made in all charts control how an
operator connects two distant points: this is how the composition of pseudodifferential operators
on a manifold is reduced to the composition in `ℝⁿ`.
-/

public section

open Set Bornology
open scoped Manifold ContDiff

universe u

namespace OpenPartialHomeomorph

/-- A chart of the maximal atlas at `x` whose source lies in a given open neighbourhood `U` of `x`:
the preferred chart at `x`, restricted to `U`. -/
theorem exists_mem_maximalAtlas_source_subset {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : WithTop ℕ∞} [IsManifold I n M] {x : M} {U : Set M} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ c : OpenPartialHomeomorph M H,
      c ∈ IsManifold.maximalAtlas I n M ∧ x ∈ c.source ∧ c.source ⊆ U := by
  refine ⟨_, restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas x) hU, ?_⟩
  rw [restr_source' _ _ hU]
  exact ⟨⟨mem_chart_source H x, hx⟩, fun _ hy ↦ hy.2⟩

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : WithTop ℕ∞}
  [IsManifold 𝓘(𝕜, E) n M]

/-- **Joining two charts with disjoint sources.** Two charts of the maximal atlas with disjoint
sources and bounded targets are the restrictions of a single chart `e` of the maximal atlas, with
source the union of their sources, after translating the second chart by a vector `v`. -/
theorem exists_mem_maximalAtlas_of_disjoint_source [Nontrivial E]
    {e₁ e₂ : OpenPartialHomeomorph M E} (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) (hs : Disjoint e₁.source e₂.source)
    (h₁ : IsBounded e₁.target) (h₂ : IsBounded e₂.target) :
    ∃ e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M, ∃ v : E,
      e.source = e₁.source ∪ e₂.source ∧ EqOn e e₁ e₁.source ∧
        EqOn e (fun x ↦ e₂ x + v) e₂.source := by
  classical
  obtain ⟨R₁, hR₁⟩ := h₁.subset_ball 0
  obtain ⟨R₂, hR₂⟩ := h₂.subset_ball 0
  obtain ⟨v, hv⟩ := NormedSpace.exists_lt_norm 𝕜 E (R₁ + R₂)
  -- Translating the second chart by `v` moves its target away from the first target.
  let e₂' := e₂.transHomeomorph (Homeomorph.addRight v)
  have ht : Disjoint e₁.target e₂'.target := by
    refine disjoint_left.2 fun y hy₁ hy₂ ↦ ?_
    have h₁ : ‖y‖ < R₁ := by simpa using hR₁ hy₁
    have h₂ : ‖y - v‖ < R₂ := by
      simpa [e₂', Homeomorph.addRight_symm, sub_eq_add_neg] using hR₂ hy₂
    linarith [norm_sub_norm_le v y, norm_sub_rev v y]
  let e := e₁.disjointUnion e₂' hs ht
  -- `disjointUnion` overrides only the source and target of `piecewise`, so `e` and `e.symm` are
  -- definitionally `Set.piecewise e₁.source e₁ e₂'` and `Set.piecewise e₁.target e₁.symm e₂'.symm`,
  -- and are evaluated below by `piecewise_eq_of_mem` and `piecewise_eq_of_notMem`.
  have hesrc : e.source = e₁.source ∪ e₂.source := rfl
  have he₁eq : EqOn e e₁ e₁.source := fun x hx ↦ piecewise_eq_of_mem _ _ _ hx
  have he₂eq : EqOn e (fun x ↦ e₂ x + v) e₂.source := fun x hx ↦
    piecewise_eq_of_notMem _ _ _ (disjoint_right.1 hs hx)
  refine ⟨e, e.mem_maximalAtlas_of_contMDiffOn ?_ ?_, v, hesrc, he₁eq, he₂eq⟩
  · rw [hesrc, contMDiffOn_union_iff_of_isOpen e₁.open_source e₂.open_source]
    exact ⟨(contMDiffOn_of_mem_maximalAtlas he₁).congr he₁eq,
      ((contDiff_id.add contDiff_const).contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas he₂)).congr he₂eq⟩
  · have htgt : e.target = e₁.target ∪ e₂'.target := rfl
    rw [htgt, contMDiffOn_union_iff_of_isOpen e₁.open_target e₂'.open_target]
    refine ⟨(contMDiffOn_symm_of_mem_maximalAtlas he₁).congr
      fun y hy ↦ piecewise_eq_of_mem _ _ _ hy, ?_⟩
    refine ((contMDiffOn_symm_of_mem_maximalAtlas he₂).comp
      (contDiff_id.sub (contDiff_const (c := v))).contMDiff.contMDiffOn fun y hy ↦ ?_).congr
      fun y hy ↦ ?_
    · simpa [e₂', Homeomorph.addRight_symm, sub_eq_add_neg] using hy
    · rw [show e.symm y = e₂'.symm y from piecewise_eq_of_notMem _ _ _ (disjoint_right.1 ht hy)]
      simp [e₂', Homeomorph.addRight_symm, sub_eq_add_neg]

/-- **A chart joining a compact set to an open set read through another chart.** Let `W` be an
open set with compact closure in the target of the chart `e`, and let `S` be a compact subset of
the source of a chart `c` that does not meet `e⁻¹(closure W)`. Then there is a chart `e'` of the
maximal atlas with `S` in its source and `W` in its target, with the same inverse as `e` on `W`:
it is `e` over `W`, joined to `c` near `S` with its image moved away from `W`. -/
theorem exists_mem_maximalAtlas_eqOn_symm [Nontrivial E] [T2Space M]
    {e c : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) {W : Set E} (hWo : IsOpen W)
    (hWe : closure W ⊆ e.target) (hWc : IsCompact (closure W)) {S : Set M} (hS : IsCompact S)
    (hSc : S ⊆ c.source) (hSL : Disjoint S (e.symm '' closure W)) :
    ∃ e' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M,
      S ⊆ e'.source ∧ W ⊆ e'.target ∧ EqOn e'.symm e.symm W := by
  set L := e.symm '' closure W
  have hLc : IsCompact L := hWc.image_of_continuousOn (e.continuousOn_symm.mono hWe)
  -- The chart `e` restricted over `W`.
  set e₁ := e.restr (e.source ∩ e ⁻¹' W) with he₁def
  have he₁src : e₁.source = e.source ∩ (e.source ∩ e ⁻¹' W) :=
    e.restr_source' _ (e.isOpen_inter_preimage hWo)
  have he₁t : e₁.target ⊆ W := fun y hy ↦ by
    have h₁ := he₁src ▸ e₁.map_target hy
    have h₂ := e₁.right_inv hy
    simp only [he₁def, restr_apply, restr_symm_apply] at h₁ h₂
    exact h₂ ▸ h₁.2.2
  have hWe₁ : ∀ y ∈ W, e.symm y ∈ e₁.source ∧ e₁ (e.symm y) = y := fun y hy ↦ by
    have hy' := subset_closure.trans hWe hy
    refine ⟨he₁src ▸ ⟨e.map_target hy', e.map_target hy', ?_⟩, by simp [he₁def, e.right_inv hy']⟩
    simpa [e.right_inv hy'] using hy
  -- The chart `c` restricted away from `L` and to a bounded target containing `c(S)`.
  obtain ⟨R, hR⟩ := (hS.image_of_continuousOn (c.continuousOn.mono hSc)).isBounded.subset_ball 0
  have hopen : IsOpen (Lᶜ ∩ (c.source ∩ c ⁻¹' Metric.ball 0 R)) :=
    hLc.isClosed.isOpen_compl.inter (c.isOpen_inter_preimage Metric.isOpen_ball)
  set e₂ := c.restr (Lᶜ ∩ (c.source ∩ c ⁻¹' Metric.ball 0 R)) with he₂def
  have he₂s : e₂.source = c.source ∩ (Lᶜ ∩ (c.source ∩ c ⁻¹' Metric.ball 0 R)) :=
    c.restr_source' _ hopen
  obtain ⟨e', he', -, he's, he'₁, -⟩ := exists_mem_maximalAtlas_of_disjoint_source
    (restr_mem_maximalAtlas _ he (e.isOpen_inter_preimage hWo)) (restr_mem_maximalAtlas _ hc hopen)
    (disjoint_left.2 fun x hx₁ hx₂ ↦ (he₂s ▸ hx₂).2.1
      ⟨e x, subset_closure (he₁src ▸ hx₁).2.2, e.left_inv (he₁src ▸ hx₁).1⟩)
    (hWc.isBounded.subset (he₁t.trans subset_closure))
    ((Metric.isBounded_ball (x := (0 : E)) (r := R)).subset fun y hy ↦ by
      have h₁ := he₂s ▸ e₂.map_target hy
      have h₂ := e₂.right_inv hy
      simp only [he₂def, restr_apply, restr_symm_apply] at h₁ h₂
      exact h₂ ▸ h₁.2.2.2)
  refine ⟨e', he', fun x hx ↦ he's ▸ Or.inr (he₂s ▸ ⟨hSc hx, disjoint_left.1 hSL hx, hSc hx,
    hR (mem_image_of_mem _ hx)⟩), fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨hy₁, hy₂⟩ := hWe₁ y hy
    rw [← hy₂, ← he'₁ hy₁]
    exact e'.map_source (he's ▸ Or.inl hy₁)
  · obtain ⟨hy₁, hy₂⟩ := hWe₁ y hy
    rw [← hy₂, ← he'₁ hy₁, e'.left_inv (he's ▸ Or.inl hy₁), he'₁ hy₁, hy₂]

end OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **Charts for a partition of unity.** Let `e` be a chart, `C` a compact subset of its target and
`K` a compact subset of `M`. There are finitely many smooth functions `ρᵢ` adding up to `1` on `K`,
with compact supports, and charts `eᵢ` containing the support of `ρᵢ` in their sources and `C` in
their targets, with the same inverse as `e` on `C`. Where the support of `ρᵢ` leaves the source of
`e`, the chart `eᵢ` is made of a neighbourhood of `e⁻¹(C)` read through `e` and a neighbourhood of
the support of `ρᵢ`, with disjoint images. -/
theorem IsCompact.exists_smoothPartition_mem_maximalAtlas_eqOn_symm {K : Set M} (hK : IsCompact K)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {C : Set E}
    (hC : IsCompact C) (hCe : C ⊆ e.target) :
    ∃ (ι : Type u) (_ : Fintype ι) (ρ : ι → C^∞⟮𝓘(ℝ, E), M; ℝ⟯)
      (e' : ι → OpenPartialHomeomorph M E), (∀ x ∈ K, ∑ i, ρ i x = 1) ∧
      ∀ i, e' i ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
        IsCompact (tsupport (ρ i)) ∧ tsupport (ρ i) ⊆ (e' i).source ∧ C ⊆ (e' i).target ∧
          EqOn (e' i).symm e.symm C := by
  classical
  -- A bounded open neighbourhood `W` of `C` and the compact set `L = e⁻¹(closure W)`.
  obtain ⟨W, hWo, hCW, hWe, hWc⟩ := exists_open_between_and_isCompact_closure hC e.open_target hCe
  set L := e.symm '' closure W
  have hLc : IsCompact L := hWc.image_of_continuousOn (e.continuousOn_symm.mono hWe)
  have hLe : L ⊆ e.source := image_subset_iff.2 fun y hy ↦ e.map_target (hWe hy)
  -- A finite smooth bump covering of `K` whose bumps lie in `e.source`, or away from `L`.
  obtain ⟨ι, _, f, hf⟩ := hK.exists_smoothBumpCovering_isSubordinate 𝓘(ℝ, E)
    (U := fun x ↦ if x ∈ e.source then e.source else Lᶜ) fun x _ ↦ by
      split_ifs with hx
      · exact e.open_source.mem_nhds hx
      · exact hLc.isClosed.isOpen_compl.mem_nhds fun hxL ↦ hx (hLe hxL)
  have hchart : ∀ i, ∃ e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M,
      tsupport (f i) ⊆ e'.source ∧ C ⊆ e'.target ∧ EqOn e'.symm e.symm C := by
    intro i
    by_cases hc : f.c i ∈ e.source
    · exact ⟨e, he, by simpa [hc] using hf i, hCe, eqOn_refl _ _⟩
    obtain ⟨e', he', hfE, hWE, hEe⟩ := OpenPartialHomeomorph.exists_mem_maximalAtlas_eqOn_symm he
      (IsManifold.chart_mem_maximalAtlas (f.c i)) hWo hWe hWc (f i).hasCompactSupport.isCompact
      (f i).tsupport_subset_chartAt_source
      (subset_compl_iff_disjoint_right.1 (by simpa [hc] using hf i))
    exact ⟨e', he', hfE, hCW.trans hWE, hEe.mono hCW⟩
  choose e' he' hfE hCE hEe using hchart
  have hρ (i) : tsupport (f.toSmoothPartitionOfUnity i) ⊆ tsupport (f i) :=
    closure_mono (f.support_toSmoothPartitionOfUnity_subset i)
  refine ⟨ι, inferInstance, fun i ↦ f.toSmoothPartitionOfUnity i, e', fun x hx ↦ ?_, fun i ↦
    ⟨he' i, (f i).hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _) (hρ i),
      (hρ i).trans (hfE i), hCE i, hEe i⟩⟩
  rw [← finsum_eq_sum_of_fintype]
  exact f.toSmoothPartitionOfUnity.sum_eq_one hx
