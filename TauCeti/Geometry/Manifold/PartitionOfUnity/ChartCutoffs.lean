/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Sets.Compacts
public import TauCeti.Geometry.Manifold.ContMDiffMap.Prod
import TauCeti.Geometry.Manifold.ContMDiff.Atlas

/-!
# Charts with subordinate cutoffs

To transport a construction from model spaces to a manifold `P` one covers `P` by charts into the
model space `E` and cuts functions off with a partition of unity subordinate to the charts. A
`TauCeti.ChartCutoffs I P n ι` packages this data: charts `cᵢ : P → E`, `C^n` with `C^n` inverses,
and `C^n` cutoffs `ρᵢ` summing to `1` with `tsupport ρᵢ` in the source of `cᵢ`, each mapped by `cᵢ`
into a compact subset of the target, finitely many of which meet any compact set.

On a Hausdorff `σ`-compact manifold with finite-dimensional model, every family of such charts
indexed by the points of `P`, each containing its point, carries cutoffs
(`TauCeti.ChartCutoffs.exists_chart_eq`); for a boundaryless model, chart cutoffs exist
(`TauCeti.ChartCutoffs.nonempty`). Chart cutoffs on `M` and on `N` multiply to chart cutoffs on
`M × N` with the product charts (`TauCeti.ChartCutoffs.prod`).

## Main declarations

* `TauCeti.ChartCutoffs`: charts with subordinate cutoffs.
* `TauCeti.ChartCutoffs.meeting`: the finitely many indices whose cutoffs meet a compact set; the
  corresponding cutoffs sum to `1` on it (`TauCeti.ChartCutoffs.sum_meeting_eq_one`).
* `TauCeti.ChartCutoffs.exists_chart_eq`, `TauCeti.ChartCutoffs.nonempty`: existence.
* `TauCeti.ChartCutoffs.prod`: product chart cutoffs.
-/

public noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {P : Type*} [TopologicalSpace P] [ChartedSpace H P] {n : ℕ∞}

variable (ι : Type*) (I P n) in
/-- **Charts with subordinate cutoffs** on `P`, indexed by `ι`: `C^n` charts into the model space
with `C^n` inverses, and `C^n` cutoffs summing to `1`, each supported in the source of its chart
and mapped by it into a compact subset of the target, finitely many of which meet any compact
set. -/
structure ChartCutoffs where
  /-- The charts. -/
  chart : ι → OpenPartialHomeomorph P E
  /-- The charts are `C^n` on their sources. -/
  contMDiffOn_chart : ∀ i, ContMDiffOn I 𝓘(ℝ, E) n (chart i) (chart i).source
  /-- The inverses of the charts are `C^n` on their targets. -/
  contMDiffOn_chart_symm : ∀ i, ContMDiffOn 𝓘(ℝ, E) I n (chart i).symm (chart i).target
  /-- The cutoffs. -/
  cutoff : ι → C^n⟮I, P; ℝ⟯
  /-- Each cutoff is supported in the source of its chart. -/
  tsupport_subset : ∀ i, tsupport (cutoff i) ⊆ (chart i).source
  /-- Compact subsets of the chart targets containing the images of the supports of the cutoffs. -/
  box : ι → Compacts E
  /-- Each compact set lies in the target of its chart. -/
  box_subset : ∀ i, (box i : Set E) ⊆ (chart i).target
  /-- Each chart maps the support of its cutoff into its compact set. -/
  mapsTo : ∀ i, MapsTo (chart i) (tsupport (cutoff i)) (box i)
  /-- Finitely many cutoffs meet a compact set. -/
  finite : ∀ K : Set P, IsCompact K → {i | (tsupport (cutoff i) ∩ K).Nonempty}.Finite
  /-- The cutoffs sum to `1`. -/
  sum_eq_one : ∀ z, ∑ᶠ i, cutoff i z = 1

namespace ChartCutoffs

variable {ι : Type*}

/-- The indices of the cutoffs meeting a compact set. -/
def meeting (A : ChartCutoffs I P n ι) (K : Set P) (hK : IsCompact K) : Finset ι :=
  (A.finite K hK).toFinset

theorem mem_meeting (A : ChartCutoffs I P n ι) {K : Set P} {hK : IsCompact K} {i : ι} :
    i ∈ A.meeting K hK ↔ (tsupport (A.cutoff i) ∩ K).Nonempty := by
  simp [meeting]

/-- A cutoff not meeting a compact set `K` vanishes on `K`. -/
theorem cutoff_eq_zero (A : ChartCutoffs I P n ι) {K : Set P} {hK : IsCompact K} {i : ι}
    (hi : i ∉ A.meeting K hK) {z : P} (hz : z ∈ K) : A.cutoff i z = 0 := by
  by_contra h
  exact hi (A.mem_meeting.2 ⟨z, subset_tsupport _ h, hz⟩)

/-- On a compact set `K` the cutoffs meeting `K` sum to `1`. -/
theorem sum_meeting_eq_one (A : ChartCutoffs I P n ι) {K : Set P} (hK : IsCompact K) {z : P}
    (hz : z ∈ K) : ∑ i ∈ A.meeting K hK, A.cutoff i z = 1 := by
  rw [← A.sum_eq_one z, finsum_eq_sum_of_support_subset]
  intro i hi
  by_contra h
  exact hi (A.cutoff_eq_zero h hz)

/-- A function of pairs of indices which vanishes unless its first index meets the compact set `K`
and its second index meets the compact set `L` has its sum over the pairs of meeting indices. -/
theorem finsum_prod_eq_sum_meeting {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N]
    [ChartedSpace H' N] {κ : Type*} {α : Type*} [AddCommMonoid α] (A : ChartCutoffs I P n ι)
    (B : ChartCutoffs J N n κ) {K : Set P} (hK : IsCompact K) {L : Set N} (hL : IsCompact L)
    {f : ι → κ → α} (hf₁ : ∀ i j, i ∉ A.meeting K hK → f i j = 0)
    (hf₂ : ∀ i j, j ∉ B.meeting L hL → f i j = 0) :
    ∑ᶠ p : ι × κ, f p.1 p.2 = ∑ i ∈ A.meeting K hK, ∑ j ∈ B.meeting L hL, f i j := by
  rw [finsum_eq_sum_of_support_subset (s := A.meeting K hK ×ˢ B.meeting L hL) _ fun p hp ↦ ?_,
    Finset.sum_product]
  rw [Finset.coe_product, mem_prod, Finset.mem_coe, Finset.mem_coe]
  by_contra h
  rcases not_and_or.1 h with h | h
  exacts [hp (hf₁ _ _ h), hp (hf₂ _ _ h)]

variable [IsManifold I ∞ P] [FiniteDimensional ℝ E] [T2Space P] [SigmaCompactSpace P]

/-- On a Hausdorff `σ`-compact manifold with finite-dimensional model, a family of `C^n` charts
with `C^n` inverses, indexed by the points of `P` and each containing its point, carries cutoffs. -/
theorem exists_chart_eq (c : P → OpenPartialHomeomorph P E)
    (hc : ∀ x, ContMDiffOn I 𝓘(ℝ, E) n (c x) (c x).source)
    (hcs : ∀ x, ContMDiffOn 𝓘(ℝ, E) I n (c x).symm (c x).target) (hxc : ∀ x, x ∈ (c x).source) :
    ∃ A : ChartCutoffs I P n P, A.chart = c := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace P := ChartedSpace.locallyCompactSpace H P
  -- Shrink each chart source to an open neighbourhood with compact closure inside it.
  choose W hWo hxW hWs hWc using fun x : P ↦ exists_open_between_and_isCompact_closure
    isCompact_singleton (c x).open_source (singleton_subset_iff.2 (hxc x))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ W hWo
    fun y _ ↦ mem_iUnion.2 ⟨y, hxW y rfl⟩
  exact ⟨{
    chart := c
    contMDiffOn_chart := hc
    contMDiffOn_chart_symm := hcs
    cutoff := fun x ↦ ⟨ρ x, (ρ x).contMDiff.of_le (WithTop.coe_le_coe.2 le_top)⟩
    tsupport_subset := fun x ↦ (hρ x).trans (subset_closure.trans (hWs x))
    box := fun x ↦ ⟨c x '' closure (W x),
      (hWc x).image_of_continuousOn ((c x).continuousOn.mono (hWs x))⟩
    box_subset := fun x ↦ image_subset_iff.2 fun y hy ↦ (c x).map_source (hWs x hy)
    mapsTo := fun x y hy ↦ mem_image_of_mem _ (subset_closure (hρ x hy))
    finite := fun K hK ↦ ρ.locallyFinite.closure.finite_nonempty_inter_compact hK
    sum_eq_one := fun z ↦ ρ.sum_eq_one (mem_univ z) }, rfl⟩

variable (ι I P n) in
/-- On a boundaryless Hausdorff `σ`-compact manifold with finite-dimensional model, chart cutoffs
exist. -/
theorem nonempty [I.Boundaryless] : Nonempty (ChartCutoffs I P n P) :=
  let ⟨A, _⟩ := exists_chart_eq (fun x : P ↦ (chartAt H x).extendTrans I (Homeomorph.refl E))
    (fun x ↦ (OpenPartialHomeomorph.contMDiffOn_extendTrans _
      (IsManifold.chart_mem_maximalAtlas x) contDiff_id).of_le (WithTop.coe_le_coe.2 le_top))
    (fun x ↦ (OpenPartialHomeomorph.contMDiffOn_extendTrans_symm _
      (IsManifold.chart_mem_maximalAtlas x) contDiff_id).of_le (WithTop.coe_le_coe.2 le_top))
    fun x ↦ by rw [OpenPartialHomeomorph.extendTrans_source]; exact mem_chart_source H x
  ⟨A⟩

end ChartCutoffs

/-! ### Products -/

namespace ChartCutoffs

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {ι κ : Type*}

/-- The product of chart cutoffs on `P` and on `N`: the product charts `cᵢ × dⱼ` with the product
cutoffs `(x, y) ↦ ρᵢ x * σⱼ y`. -/
@[expose, simps chart cutoff box]
def prod (A : ChartCutoffs I P n ι) (B : ChartCutoffs J N n κ) :
    ChartCutoffs (I.prod J) (P × N) n (ι × κ) where
  chart p := (A.chart p.1).prod (B.chart p.2)
  contMDiffOn_chart p :=
    ((A.contMDiffOn_chart p.1).comp contMDiffOn_fst mapsTo_fst_prod).prodMk_space
      ((B.contMDiffOn_chart p.2).comp contMDiffOn_snd mapsTo_snd_prod)
  contMDiffOn_chart_symm p :=
    ((A.contMDiffOn_chart_symm p.1).comp contDiff_fst.contMDiff.contMDiffOn
      mapsTo_fst_prod).prodMk
    ((B.contMDiffOn_chart_symm p.2).comp contDiff_snd.contMDiff.contMDiffOn mapsTo_snd_prod)
  cutoff p := (A.cutoff p.1).mulProd (B.cutoff p.2)
  tsupport_subset p := (ContMDiffMap.tsupport_mulProd_subset _ _).trans
    (prod_mono (A.tsupport_subset p.1) (B.tsupport_subset p.2))
  box p := A.box p.1 ×ˢ B.box p.2
  box_subset p := prod_mono (A.box_subset p.1) (B.box_subset p.2)
  mapsTo p := ((A.mapsTo p.1).prodMap (B.mapsTo p.2)).mono_left
    (ContMDiffMap.tsupport_mulProd_subset _ _)
  finite K hK := ((A.finite _ (hK.image continuous_fst)).prod
    (B.finite _ (hK.image continuous_snd))).subset fun p ⟨z, hz, hzK⟩ ↦
      ⟨⟨z.1, (ContMDiffMap.tsupport_mulProd_subset _ _ hz).1, mem_image_of_mem _ hzK⟩,
        ⟨z.2, (ContMDiffMap.tsupport_mulProd_subset _ _ hz).2, mem_image_of_mem _ hzK⟩⟩
  sum_eq_one z := by
    refine (A.finsum_prod_eq_sum_meeting B isCompact_singleton isCompact_singleton
      (f := fun i j ↦ A.cutoff i z.1 * B.cutoff j z.2)
      (fun i j hi ↦ by rw [A.cutoff_eq_zero hi rfl, zero_mul])
      (fun i j hj ↦ by rw [B.cutoff_eq_zero hj rfl, mul_zero])).trans ?_
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [A.sum_meeting_eq_one _ rfl, B.sum_meeting_eq_one _ rfl, one_mul]

end ChartCutoffs

end TauCeti
