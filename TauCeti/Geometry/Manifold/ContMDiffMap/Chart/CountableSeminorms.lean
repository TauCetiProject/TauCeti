/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CoordinateChange
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Separation.Basic

/-!
# Cofinal compact chart seminorms

A chart cover controls every compact chart C^k seminorm by finitely many chart seminorms from
the cover. Compact pieces subordinate to a finite subcover reduce the estimate to the native
quantitative coordinate-change bounds. Compact exhaustions then give a countable cofinal family
when the chosen chart index is countable. The coefficient space may be any normed space.

These are the compact-cover estimates for the weak Whitney topology, as in Hirsch,
*Differential Topology*, Chapter 2, §1.
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold TauCeti.ManifoldWeakWhitney
namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]
  {ι : Type*} (c : ι → M)
  (hcover : ∀ x : M, ∃ i, x ∈ (extChartAt I (c i)).source)

/-- If compact pieces `P i`, `i ∈ t`, of a chart target cover a compact set `L`, and the chart
seminorm on each piece is bounded by `C i ≥ 0` times a seminorm `q`, then the chart seminorm on
`L` is bounded by `1 + ∑ i ∈ t, C i` times `q`. -/
theorem chartCkSeminorm_le_of_subset_biUnion {κ : Type*} (x : M)
    (L : TopologicalSpace.Compacts (extChartAt I x).target) (t : Finset κ)
    (P : κ → TopologicalSpace.Compacts (extChartAt I x).target)
    (hLP : (L : Set (extChartAt I x).target) ⊆ ⋃ i ∈ t, (P i : Set (extChartAt I x).target))
    (k : ℕ) (hk : k ≤ n) (q : Seminorm 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯) {C : κ → ℝ}
    (hC : ∀ i ∈ t, 0 ≤ C i) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯)
    (hb : ∀ i ∈ t, chartCkSeminorm x (P i) k hk f ≤ C i * q f) :
    chartCkSeminorm x L k hk f ≤ (1 + ∑ i ∈ t, C i) * q f := by
  have hsum : 0 ≤ ∑ i ∈ t, C i := Finset.sum_nonneg hC
  refine (chartCkSeminorm_le_iff x L k hk f
    (mul_nonneg (add_nonneg zero_le_one hsum) (apply_nonneg q f))).mpr fun m hm z hz ↦ ?_
  obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.mp (hLP hz)
  have hderiv := (chartCkSeminorm_le_iff x (P i) k hk f
    (apply_nonneg _ _)).mp le_rfl m hm z hzi
  have hCi : C i ≤ 1 + ∑ j ∈ t, C j :=
    (Finset.single_le_sum hC hit).trans (le_add_of_nonneg_left zero_le_one)
  exact hderiv.trans ((hb i hit).trans (mul_le_mul_of_nonneg_right hCi (apply_nonneg q f)))

include hcover in
/-- Every compact chart seminorm is bounded by a positive multiple of a finite supremum of
seminorms from any covering chart system. -/
theorem exists_chartCkSeminorm_le_finset_sup (x : M)
    (K : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    ∃ (t : Finset ι) (L : ∀ i, TopologicalSpace.Compacts (extChartAt I (c i)).target)
      (C : ℝ), 0 < C ∧ ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
      chartCkSeminorm x K k hk f ≤
        C * (t.sup fun i ↦ chartCkSeminorm (F := F) (c i) (L i) k hk) f := by
  classical
  let U (i : ι) : Set (extChartAt I x).target :=
    {z | (extChartAt I x).symm z ∈ (extChartAt I (c i)).source}
  have hs : Continuous (fun z : (extChartAt I x).target ↦ (extChartAt I x).symm z) :=
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm x)
  have hU (i : ι) : IsOpen (U i) := (isOpen_extChartAt_source (c i)).preimage hs
  have hc : (K : Set (extChartAt I x).target) ⊆ ⋃ i, U i := by
    intro z _
    obtain ⟨i, hi⟩ := hcover ((extChartAt I x).symm z)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨t, ht⟩ := K.isCompact.elim_finite_subcover U hU hc
  obtain ⟨P, hP, hPU, hKP⟩ := K.isCompact.finite_compact_cover t U (fun i _ ↦ hU i) ht
  let A (i : ι) : TopologicalSpace.Compacts (extChartAt I x).target := ⟨P i, hP i⟩
  have hb (i : ι) : ∃ (L : TopologicalSpace.Compacts (extChartAt I (c i)).target) (C : ℝ),
      0 < C ∧ ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
        chartCkSeminorm x (A i) k hk f ≤ C * chartCkSeminorm (F := F) (c i) L k hk f := by
    obtain ⟨L, -, C, D, hC, -, h⟩ := exists_chartCkSeminorm_coordChange
      (F := F) x (c i) (A i) (fun z hz ↦ hPU i hz) k hk
    exact ⟨L, C, hC, fun f ↦ (h f).1⟩
  choose L C hC hbound using hb
  let q : Seminorm 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
    t.sup fun i ↦ chartCkSeminorm (F := F) (c i) (L i) k hk
  have hsum : 0 ≤ ∑ i ∈ t, C i := Finset.sum_nonneg fun i _ ↦ (hC i).le
  refine ⟨t, L, 1 + ∑ i ∈ t, C i, add_pos_of_pos_of_nonneg zero_lt_one hsum, fun f ↦ ?_⟩
  refine chartCkSeminorm_le_of_subset_biUnion x K t A hKP.subset k hk q
    (fun i _ ↦ (hC i).le) f fun i hit ↦ (hbound i f).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup (f := fun i ↦ chartCkSeminorm (F := F) (c i) (L i) k hk) hit f) (hC i).le

/-- Compact chart seminorms on a chosen chart cover and chosen compact exhaustions.
The index is countable whenever the chart cover index is countable. -/
noncomputable def chartExhaustionSeminormFamily
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    SeminormFamily 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯ (ι × ℕ × {k : ℕ // k ≤ n}) :=
  fun j ↦ chartCkSeminorm (c j.1) ⟨A j.1 j.2.1, (A j.1).isCompact j.2.1⟩
    j.2.2.1 j.2.2.2

/-- The exhaustion family uses exactly the native compact chart seminorms. -/
@[simp]
theorem chartExhaustionSeminormFamily_apply
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target)
    (i : ι) (j k : ℕ) (hk : k ≤ n) :
    chartExhaustionSeminormFamily (F := F) c A (i, j, ⟨k, hk⟩) =
      chartCkSeminorm (c i) ⟨A i j, (A i).isCompact j⟩ k hk := by
  rfl

include hcover in
/-- Exhaustion seminorms from a covering chart system control every compact chart seminorm
by a positive multiple of a finite supremum. -/
theorem exists_chartCkSeminorm_le_exhaustion_finset_sup
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target)
    (x : M) (K : TopologicalSpace.Compacts (extChartAt I x).target)
    (k : ℕ) (hk : k ≤ n) :
    ∃ (s : Finset (ι × ℕ × {k : ℕ // k ≤ n})) (C : ℝ), 0 < C ∧
      ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
        chartCkSeminorm x K k hk f ≤ C *
          (s.sup (chartExhaustionSeminormFamily (F := F) c A)) f := by
  classical
  obtain ⟨t, L, C, hC, hbound⟩ :=
    exists_chartCkSeminorm_le_finset_sup (F := F) c hcover x K k hk
  choose j hj using fun i ↦ (A i).exists_superset_of_isCompact (L i).isCompact
  let b (i : ι) : ι × ℕ × {k : ℕ // k ≤ n} := (i, j i, ⟨k, hk⟩)
  let s := t.image b
  refine ⟨s, C, hC, fun f ↦ (hbound f).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro i hi
  have hmono : chartCkSeminorm (F := F) (c i) (L i) k hk ≤
      chartExhaustionSeminormFamily c A (b i) := by
    intro g
    refine (chartCkSeminorm_le_iff (c i) (L i) k hk g (apply_nonneg _ _)).mpr ?_
    intro m hm z hz
    exact (chartCkSeminorm_le_iff (c i)
      ⟨A i (j i), (A i).isCompact (j i)⟩ k hk g (apply_nonneg _ _)).mp
        le_rfl m hm z (hj i hz)
  exact (hmono f).trans (Seminorm.le_finset_sup_apply (Finset.mem_image_of_mem b hi))


include hcover in
/-- The exhaustion seminorms generate exactly the existing weak Whitney topology.
No new topology on smooth maps is introduced. -/
theorem withSeminorms_chartExhaustion
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    WithSeminorms (chartExhaustionSeminormFamily (F := F) (n := n) c A) := by
  classical
  have hp := withSeminorms_manifoldWeakWhitney (I := I) (M := M) (F := F) (n := n)
  let _ := hp.isTopologicalAddGroup
  refine hp.congr ?_ (Seminorm.IsBounded.of_real ?_)
  · intro j
    rcases j with ⟨i, l, k, hk⟩
    have hcont : Continuous (chartExhaustionSeminormFamily (F := F) c A (i, l, ⟨k, hk⟩)) := by
      rw [chartExhaustionSeminormFamily_apply]
      exact Seminorm.continuous_of_forall fun r hr ↦
        ball_chartCkSeminorm_mem_nhds _ _ _ _ _ hr
    obtain ⟨s, C, -, hbound⟩ := Seminorm.bound_of_continuous hp _ hcont
    exact ⟨s, C, by simpa only [Seminorm.comp_id] using hbound⟩
  · rintro ⟨x, ⟨k, hk⟩, K⟩
    obtain ⟨s, C, -, hbound⟩ :=
      exists_chartCkSeminorm_le_exhaustion_finset_sup (F := F) c hcover A x K k hk
    refine ⟨s, C, fun f ↦ ?_⟩
    have hderiv : chartDerivativeSeminorm (F := F) x K k hk f ≤
        chartCkSeminorm x K k hk f :=
      (chartDerivativeSeminorm_le_iff x K k hk f (apply_nonneg _ _)).mpr
        fun z hz ↦ (chartCkSeminorm_le_iff x K k hk f (apply_nonneg _ _)).mp
          le_rfl k le_rfl z hz
    simpa only [LinearMap.id_apply, chartSeminormFamily_apply] using
      hderiv.trans (hbound f)


include hcover in
/-- A countable covering chart system with compact exhaustions makes the native weak Whitney
map topology first countable, also for finite regularity and empty source manifolds. -/
theorem firstCountableTopology_chartExhaustion [Countable ι]
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    FirstCountableTopology C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
  (withSeminorms_chartExhaustion (F := F) c hcover A).firstCountableTopology

include hcover in
/-- The native weak Whitney map topology is metrizable when a countable covering chart system
and compact exhaustions are supplied. The metric is the native uniform-space certificate. -/
theorem metrizableSpace_chartExhaustion [Countable ι]
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    TopologicalSpace.MetrizableSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯ := by
  let _ := firstCountableTopology_chartExhaustion (F := F) (n := n) c hcover A
  let _ : UniformSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
    IsTopologicalAddGroup.rightUniformSpace _
  let _ : IsUniformAddGroup C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
    isUniformAddGroup_of_addCommGroup
  let _ : (uniformity C^n⟮I, M; 𝓘(𝕜, F), F⟯).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.metrizableSpace


/-- On a sigma-compact manifold with locally compact, second-countable model,
the existing vector-valued weak Whitney topology is metrizable. Arbitrary normed targets are
allowed; no finite-dimensionality of the coefficient space or completeness is required. -/
theorem metrizableSpace_manifoldWeakWhitney_of_sigmaCompact
    [LocallyCompactSpace E] [SecondCountableTopology E]
    [SigmaCompactSpace M] :
    TopologicalSpace.MetrizableSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯ := by
  obtain ⟨s, hs, hcover⟩ := countable_cover_nhds_of_sigmaCompact
    (fun x : M ↦ extChartAt_source_mem_nhds (I := I) x)
  let _ := hs.to_subtype
  have hc : ∀ x : M, ∃ i : s, x ∈ (extChartAt I (i : M)).source := by
    intro x
    have hx : x ∈ ⋃ y ∈ s, (extChartAt I y).source := by rw [hcover]; trivial
    obtain ⟨y, hy, hx⟩ := mem_iUnion₂.mp hx
    exact ⟨⟨y, hy⟩, hx⟩
  let _ (i : s) : LocallyCompactSpace (extChartAt I (i : M)).target := by
    rw [extChartAt_target]
    exact ((chartAt H (i : M)).open_target.preimage I.continuous_symm).isLocallyClosed.inter
      I.isClosed_range.isLocallyClosed |>.locallyCompactSpace
  exact metrizableSpace_chartExhaustion (F := F) (n := n) (fun i : s ↦ (i : M)) hc
    (fun i ↦ CompactExhaustion.choice (extChartAt I (i : M)).target)

end ContMDiffMap
