/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms

/-!
# Continuous linear maps on smooth sections have compact support

All compact frame-coordinate derivative seminorms generate
`ContMDiffSection.frameTopology`, with no countability or local compactness assumption.
Consequently Mathlib's `WithSeminorms` continuity criteria bound every continuous linear map
from sections to a normed space by finitely many of these seminorms. Since each seminorm only
sees a section near a compact subset of the base, such a map vanishes on every section which is
zero near one fixed compact subset of the base. This is the support part of the
identification of the continuous dual of smooth sections with compactly supported
distributions.

## References

* L. Schwartz, *Théorie des distributions*, Chapter III, §7, Theorem XXV.
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- All compact chart derivative seminorms of the frame coefficients, indexed by a frame, a chart
centre in its domain, an admissible derivative order, and a compact coordinate set. -/
def frameSeminormFamily :
    SeminormFamily 𝕜 Cₛ^n⟮I; F, V⟯
      (Σ i, Σ x : U i, {m : ℕ // m ≤ n} × Compacts (extChartAt I x).target) :=
  SeminormFamily.sigma fun i ↦
    (ContMDiffMap.chartSeminormFamily (I := I) (M := U i) (F := F) (n := n)).comp
      ((e i).frameCoordinates (hU i))

/-- Every entry is one of the existing compact frame derivative seminorms. -/
@[simp]
theorem frameSeminormFamily_apply (i : ι) (x : U i) (m : ℕ) (hm : m ≤ n)
    (K : Compacts (extChartAt I x).target) :
    frameSeminormFamily (I := I) (n := n) e U hU ⟨i, x, ⟨m, hm⟩, K⟩ =
      (e i).chartDerivativeSeminorm (hU i) x K m hm := by
  ext s
  simp only [frameSeminormFamily, SeminormFamily.sigma, SeminormFamily.comp_apply,
    Seminorm.comp_apply, ContMDiffMap.chartSeminormFamily_apply,
    ContMDiffMap.chartDerivativeSeminorm_apply, Trivialization.chartDerivativeSeminorm_apply]

/-- All compact frame derivative seminorms generate exactly the frame topology. Neither
countability of the frames nor local compactness of the model is needed. -/
theorem withSeminorms_frameSeminormFamily :
    let _ := frameTopology (I := I) (n := n) e U hU
    WithSeminorms (frameSeminormFamily (I := I) (n := n) e U hU) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have hp := withSeminorms_pi fun i ↦
    ContMDiffMap.withSeminorms_manifoldWeakWhitney (I := I) (M := U i) (F := F) (n := n)
  have h := (isInducing_sectionFrameCoordinates (I := I) (n := n) e U hU).withSeminorms hp
  convert h using 1
  ext j s
  simp only [frameSeminormFamily, SeminormFamily.sigma, SeminormFamily.comp_apply,
    Seminorm.comp_apply]
  congr 1
  ext x
  simp only [LinearMap.proj_apply, TauCeti.Manifold.sectionFrameCoordinates_apply,
    Bundle.Trivialization.frameCoordinates_apply]

/-- The points of the base represented by the compact coordinate set of a frame seminorm. -/
private def frameSeminormSupport
    (j : Σ i, Σ x : U i, {m : ℕ // m ≤ n} × Compacts (extChartAt I x).target) : Set M :=
  Subtype.val '' ((extChartAt I j.2.1).symm ''
    (Subtype.val '' (j.2.2.2 : Set (extChartAt I j.2.1).target)))

omit [IsManifold I n M] in
private theorem isCompact_frameSeminormSupport
    (j : Σ i, Σ x : U i, {m : ℕ // m ≤ n} × Compacts (extChartAt I x).target) :
    IsCompact (frameSeminormSupport (I := I) (n := n) U j) := by
  unfold frameSeminormSupport
  exact ((j.2.2.2.isCompact.image continuous_subtype_val).image_of_continuousOn
    ((continuousOn_extChartAt_symm j.2.1).mono (by rintro _ ⟨z, -, rfl⟩; exact z.2))).image
    continuous_subtype_val

/-- A frame seminorm vanishes on a section which is zero near the points it represents. -/
private theorem frameSeminormFamily_eq_zero
    (j : Σ i, Σ x : U i, {m : ℕ // m ≤ n} × Compacts (extChartAt I x).target)
    {s : Cₛ^n⟮I; F, V⟯}
    (hs : ∀ᶠ y in 𝓝ˢ (frameSeminormSupport (I := I) (n := n) U j), s y = 0) :
    frameSeminormFamily (I := I) (n := n) e U hU j s = 0 := by
  obtain ⟨i, x, ⟨m, hm⟩, K⟩ := j
  rw [frameSeminormFamily_apply]
  have hCk : ContMDiffMap.chartCkSeminorm x K m hm ((e i).frameCoordinates (hU i) s) = 0 := by
    refine ContMDiffMap.chartCkSeminorm_eq_zero_of_eventuallyEq_zero x K m hm fun z hz ↦ ?_
    have hz' : (((extChartAt I x).symm z : U i) : M) ∈
        frameSeminormSupport (I := I) (n := n) U ⟨i, x, ⟨m, hm⟩, K⟩ := by
      unfold frameSeminormSupport
      exact ⟨_, ⟨z, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    have hnhds := (continuous_subtype_val.continuousAt
      (x := (extChartAt I x).symm z)).eventually (hs.filter_mono (nhds_le_nhdsSet hz'))
    filter_upwards [hnhds] with y hy
    exact ((e i).frameCoordinates_eq_iff (hU i) s 0 y).mpr (by simpa using hy) |>.trans
      (by simp)
  refine le_antisymm ?_ (apply_nonneg _ _)
  refine ((e i).chartDerivativeSeminorm_le_iff (hU i) x K m hm s le_rfl).mpr fun z hz ↦ ?_
  exact (ContMDiffMap.chartCkSeminorm_le_iff x K m hm _ le_rfl).mp hCk.le m le_rfl z hz

/-- **Continuous linear maps on smooth sections have compact support.** A linear map from
sections to a normed space which is continuous for the compact derivative frame topology
vanishes on every section which is zero near one fixed compact subset of the base. Neither a
covering nor countability of the frame system is needed. -/
theorem exists_isCompact_forall_eventually_eq_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] G)
    (hf : let _ := frameTopology (I := I) (n := n) e U hU; Continuous f) :
    ∃ K : Set M, IsCompact K ∧ ∀ s : Cₛ^n⟮I; F, V⟯, (∀ᶠ y in 𝓝ˢ K, s y = 0) → f s = 0 := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have hp := withSeminorms_frameSeminormFamily (I := I) (n := n) e U hU
  have h0 : f ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : Cₛ^n⟮I; F, V⟯) :=
    hf.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds (0 : G) one_pos)
  obtain ⟨⟨t, r⟩, hr, hball⟩ := hp.hasBasis_zero_ball.mem_iff.mp h0
  refine ⟨⋃ j ∈ t, frameSeminormSupport (I := I) (n := n) U j,
    t.isCompact_biUnion fun j _ ↦ isCompact_frameSeminormSupport (I := I) (n := n) U j,
    fun s hs ↦ ?_⟩
  have hsup : (t.sup (frameSeminormFamily (I := I) (n := n) e U hU)) s = 0 :=
    le_antisymm (Seminorm.finset_sup_apply_le le_rfl fun j hj ↦
      (frameSeminormFamily_eq_zero e U hU j (hs.filter_mono (nhdsSet_mono
        (subset_biUnion_of_mem hj)))).le) (apply_nonneg _ _)
  by_contra hne
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 (‖f s‖⁻¹)
  have hmem : c • s ∈ (t.sup (frameSeminormFamily (I := I) (n := n) e U hU)).ball 0 r := by
    rw [Seminorm.mem_ball_zero, map_smul_eq_mul, hsup, mul_zero]
    exact hr
  have hlt : ‖c‖ * ‖f s‖ < 1 := by
    simpa [norm_smul] using hball hmem
  have hpos : 0 < ‖f s‖ := norm_pos_iff.mpr hne
  have := (inv_lt_iff_one_lt_mul₀ hpos).mp hc
  linarith

end ContMDiffSection
