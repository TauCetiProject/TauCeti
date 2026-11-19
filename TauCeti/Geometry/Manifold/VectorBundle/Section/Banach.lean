/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Complete
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WithSeminorms
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CoordinateChange

/-!
# The Banach space of `C^k` sections of a vector bundle over a compact manifold

Let `V` be a smooth vector bundle with model fibre `F` over a manifold `M`, and `k` a natural
number. A *finite frame atlas* is a finite family of smooth frames `e i` with frame domains
`U i`, together with, for each `i`, a point `c i` of `U i` and a compact subset `K i` of the
extended chart target of the open submanifold `U i` at `c i`, such that every point of `M` has
coordinates in the relative interior of some `K i` (`TauCeti.IsCompactChartCover`). Its `C^k`
seminorm (`ContMDiffSection.frameAtlasSeminorm`) is the largest coordinate derivative of order at
most `k` of the frame coefficients of a section on the pieces `K i`.

On `C^k` sections this seminorm generates the compact derivative topology
`ContMDiffSection.frameTopology` of the frames
(`ContMDiffSection.withSeminorms_frameAtlasSeminorm`). To see this, the frame domains are refined
to the open sets of points with coordinates in the relative interior of a piece
(`TopologicalSpace.Opens.chartPieceInterior`). The refined frames
give the same topology (`ContMDiffSection.frameTopology_eq_of_covers`), and on them every compact
chart derivative of the coefficients is bounded, through a change of charts, by the derivatives on
the piece (`ContMDiffSection.exists_chartDerivativeSeminorm_le_frameAtlasSeminorm`). Two finite
frame atlases, possibly for different covering frame systems, therefore give equivalent norms
(`ContMDiffSection.exists_frameAtlasSeminorm_le`).

Every covering frame system over a compact manifold modelled on a locally compact space refines to
a finite frame atlas (`TauCeti.exists_finite_compact_chart_cover_subordinate`), so the `C^k`
sections form a normable space (`ContMDiffSection.isNormableSpace_frameTopology`). With the norm
of a finite frame atlas (`ContMDiffSection.frameAtlasNormedAddCommGroup`) they form a Banach space
when the manifold is boundaryless and the model fibre is complete
(`ContMDiffSection.completeSpace_frameAtlas`). For the bundle of symmetric bilinear forms on the
tangent bundle this is the Banach space of `C^k` symmetric tensor fields, and over a compact
manifold its positive-definite elements, the `C^k` Riemannian metrics, form an open cone in it
(`TauCeti.Manifold.isOpen_positiveDefiniteSymmetricSections_frameTopology`). These are the spaces
of metrics to which Banach-space genericity arguments, such as the Sard–Smale
theorem, are applied.

The structures are definitions rather than instances, since they depend on the chosen atlas.

## Main definitions

* `ContMDiffSection.frameAtlasSeminorm`: the `C^k` seminorm of a finite frame atlas.
* `ContMDiffSection.frameAtlasNormedAddCommGroup`, `ContMDiffSection.frameAtlasNormedSpace`: the
  normed space of `C^k` sections with this norm and the compact derivative topology.

## Main results

* `ContMDiffSection.withSeminorms_frameAtlasSeminorm`: the seminorm of a finite frame atlas
  generates the frame topology on `C^k` sections.
* `ContMDiffSection.exists_frameAtlasSeminorm_le`: the norms of two finite frame atlases are
  equivalent.
* `ContMDiffSection.isNormableSpace_frameTopology`: over a compact manifold modelled on a locally
  compact space, the `C^k` sections form a normable space for any covering frame system.
* `ContMDiffSection.completeSpace_frameAtlas`: over a boundaryless manifold, with complete model
  fibre and `𝕜 = ℝ` or `ℂ`, the normed space of `C^k` sections is complete.

## References

* R. Hamilton, *The inverse function theorem of Nash and Moser*, Bull. Amer. Math. Soc. 7 (1982),
  Part I, Example 1.1.5, for the spaces of sections of vector bundles.
* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for the `C^k` topologies.
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold NNReal TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {ι : Type*} [Fintype ι] (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (c : ∀ i, U i) (K : ∀ i, Compacts (extChartAt I (c i)).target)

section Seminorm

variable {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]

/-- The `C^k` seminorm of a finite frame atlas: the largest coordinate derivative of order at most
`k` of the coefficients of a section in the frame `e i`, read in the chart of the frame domain
`U i` at `c i`, on the compact coordinate piece `K i`. -/
def frameAtlasSeminorm (k : ℕ) (hk : k ≤ n) : Seminorm 𝕜 Cₛ^n⟮I; F, V⟯ :=
  Finset.univ.sup fun i ↦ (e i).chartCkSeminorm (hU i) (c i) (K i) k hk

/-- Each compact frame `C^k` seminorm of a finite frame atlas is bounded by the seminorm of the
atlas. -/
theorem chartCkSeminorm_le_frameAtlasSeminorm (k : ℕ) (hk : k ≤ n) (i : ι)
    (s : Cₛ^n⟮I; F, V⟯) :
    (e i).chartCkSeminorm (hU i) (c i) (K i) k hk s ≤ frameAtlasSeminorm e U hU c K k hk s :=
  Seminorm.le_finset_sup_apply (p := fun j ↦ (e j).chartCkSeminorm (hU j) (c j) (K j) k hk)
    (Finset.mem_univ i)

/-- A nonnegative bound on the seminorm of a finite frame atlas is exactly a bound on every
coordinate derivative of order at most `k` of the frame coefficients on every piece. -/
theorem frameAtlasSeminorm_le_iff (k : ℕ) (hk : k ≤ n) (s : Cₛ^n⟮I; F, V⟯) {r : ℝ}
    (hr : 0 ≤ r) :
    frameAtlasSeminorm e U hU c K k hk s ≤ r ↔
      ∀ i (m : ℕ) (hm : m ≤ k), ∀ z ∈ K i,
        ‖ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) (c i) m
          ((Nat.cast_le.mpr hm).trans hk) z‖ ≤ r := by
  constructor
  · intro h i
    exact ((e i).chartCkSeminorm_le_iff (hU i) (c i) (K i) k hk s hr).mp
      ((chartCkSeminorm_le_frameAtlasSeminorm e U hU c K k hk i s).trans h)
  · intro h
    exact Seminorm.finset_sup_apply_le hr fun i _ ↦
      ((e i).chartCkSeminorm_le_iff (hU i) (c i) (K i) k hk s hr).mpr (h i)

/-- The seminorm of a finite frame atlas is continuous for the frame topology. -/
theorem continuous_frameAtlasSeminorm (k : ℕ) (hk : k ≤ n) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous (frameAtlasSeminorm e U hU c K k hk) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  exact Seminorm.continuous_finsetSup fun i _ ↦
    continuous_chartCkSeminorm e U hU i (c i) (K i) k hk

end Seminorm

variable {k : ℕ} [ContMDiffVectorBundle k F V I] [IsManifold I k M]

/-- On an open subset `W` of a frame domain `U i` all of whose points have coordinates in the
piece `K i`, every compact chart derivative seminorm of the coefficients in the frame `e i` is
bounded by a positive multiple of the seminorm of the atlas. -/
theorem exists_chartDerivativeSeminorm_le_frameAtlasSeminorm (i : ι) {W : Opens M}
    (hWU : W ≤ U i)
    (hWK : ∀ y : W, ∃ hs : Opens.inclusion hWU y ∈ (extChartAt I (c i)).source,
      (⟨extChartAt I (c i) (Opens.inclusion hWU y), (extChartAt I (c i)).map_source hs⟩ :
        (extChartAt I (c i)).target) ∈ K i)
    (x : W) (L : Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ (k : ℕ∞ω)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Cₛ^k⟮I; F, V⟯,
      (e i).chartDerivativeSeminorm (fun _ hy ↦ hU i (hWU hy)) x L m hm s ≤
        C * frameAtlasSeminorm e U hU c K k le_rfl s := by
  let inc : C^k⟮I, W; I, U i⟯ := ⟨Opens.inclusion hWU, contMDiff_inclusion hWU⟩
  let L' : Compacts (extChartAt I (Opens.inclusion hWU x)).target :=
    L.map (inclusion ((U i).extChartAt_target_subset_of_le hWU x)) (continuous_inclusion _)
  -- Each point of `L'` represents a point of `W`, which has coordinates in `K i`.
  have hL' : ∀ z ∈ L', (extChartAt I (Opens.inclusion hWU x)).symm z =
      Opens.inclusion hWU ((extChartAt I x).symm z) := by
    rintro _ ⟨z, -, rfl⟩
    apply Subtype.ext
    rw [(U i).coe_extChartAt_symm_apply _ ((U i).extChartAt_target_subset_of_le hWU x z.2)]
    exact ((W.coe_extChartAt_symm_apply x z.2)).symm
  obtain ⟨C, hCpos, hC⟩ := ContMDiffMap.exists_chartCkSeminorm_le_coordChange (F := F)
    (Opens.inclusion hWU x) (c i) L' (K i)
    (fun z hz ↦ hL' z hz ▸ (hWK ((extChartAt I x).symm z)).1)
    (fun z hz ↦ by
      obtain ⟨hs, hK⟩ := hWK ((extChartAt I x).symm z)
      convert hK using 3
      exact hL' z hz) k le_rfl
  refine ⟨C, hCpos, fun s ↦ ?_⟩
  have hcoe : (e i).frameCoordinates (fun _ hy ↦ hU i (hWU hy)) s =
      ((e i).frameCoordinates (hU i) s).comp inc := by
    ext y
    rw [ContMDiffMap.comp_apply]
    exact ((e i).frameCoordinates_apply _ s y).trans
      ((e i).frameCoordinates_apply (hU i) s (Opens.inclusion hWU y)).symm
  have hderiv : (e i).chartDerivativeSeminorm (fun _ hy ↦ hU i (hWU hy)) x L m hm s ≤
      ContMDiffMap.chartCkSeminorm x L k le_rfl
        ((e i).frameCoordinates (fun _ hy ↦ hU i (hWU hy)) s) :=
    ((e i).chartDerivativeSeminorm_apply _ x L m hm s).trans_le
      ((ContMDiffMap.chartDerivativeSeminorm_apply x L m hm _).symm.trans_le
        (ContMDiffMap.chartDerivativeSeminorm_le_chartCkSeminorm x L (by exact_mod_cast hm)
          le_rfl _))
  rw [hcoe, ContMDiffMap.chartCkSeminorm_comp_inclusion] at hderiv
  exact hderiv.trans ((hC _).trans (mul_le_mul_of_nonneg_left
    (((e i).chartCkSeminorm_apply (hU i) (c i) (K i) k le_rfl s).symm.trans_le
      (chartCkSeminorm_le_frameAtlasSeminorm e U hU c K k le_rfl i s)) hCpos.le))

/-- **The seminorm of a finite frame atlas generates the frame topology** on `C^k` sections. -/
theorem withSeminorms_frameAtlasSeminorm [LocallyCompactSpace E]
    (hK : TauCeti.IsCompactChartCover U c K) :
    let _ := frameTopology (I := I) (n := k) e U hU
    WithSeminorms fun _ : Unit ↦ frameAtlasSeminorm e U hU c K k le_rfl := by
  -- The frame domains refined to the points with coordinates in the interior of a piece. They
  -- give the same topology, and their frame seminorms are bounded by the atlas seminorm.
  let W (i : ι) : Opens M := (U i).chartPieceInterior (c i) (K i)
  have hWU (i : ι) : W i ≤ U i := (U i).chartPieceInterior_le (c i) (K i)
  have hW (i : ι) : (W i : Set M) ⊆ (e i).baseSet := fun _ hy ↦ hU i (hWU i hy)
  have htop := frameTopology_eq_of_covers (I := I) (n := k) e U hU hK.exists_mem e W hW hK.covers
  rw [htop]
  let _ := frameTopology (I := I) (n := k) e W hW
  have hp := withSeminorms_frameSeminormFamily (I := I) (n := k) e W hW
  have hcont : Continuous (frameAtlasSeminorm e U hU c K k le_rfl) := by
    have h := continuous_frameAtlasSeminorm (I := I) e U hU c K k le_rfl
    rwa [htop] at h
  refine hp.congr ?_ (Seminorm.IsBounded.of_real ?_)
  · intro _
    obtain ⟨s, C, -, hbound⟩ := Seminorm.bound_of_continuous hp _ hcont
    exact ⟨s, C, by simpa only [Seminorm.comp_id] using hbound⟩
  · rintro ⟨i, x, ⟨m, hm⟩, L⟩
    obtain ⟨C, -, hC⟩ := exists_chartDerivativeSeminorm_le_frameAtlasSeminorm e U hU c K i
      (hWU i) (fun ⟨_, hy⟩ ↦
        let ⟨_, hs, hint⟩ := Opens.mem_chartPieceInterior.mp hy
        ⟨hs, interior_subset hint⟩) x L m hm
    refine ⟨{()}, C, fun s ↦ ?_⟩
    simpa only [LinearMap.id_apply, frameSeminormFamily_apply, Finset.sup_singleton] using hC s

/-- **The seminorm of a finite frame atlas is a norm** on `C^k` sections. -/
theorem frameAtlasSeminorm_eq_zero_iff [LocallyCompactSpace E]
    (hK : TauCeti.IsCompactChartCover U c K) (s : Cₛ^k⟮I; F, V⟯) :
    frameAtlasSeminorm e U hU c K k le_rfl s = 0 ↔ s = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  let _ := frameTopology (I := I) (n := k) e U hU
  have := t2Space_frameTopology (I := I) (n := k) e U hU hK.exists_mem
  by_contra hs
  obtain ⟨-, hne⟩ := (withSeminorms_frameAtlasSeminorm e U hU c K hK).separating_of_T1 s hs
  exact hne h

/-- **Equivalence of the norms of finite frame atlases.** The seminorm of a finite frame atlas is
bounded by a positive multiple of that of any other, possibly for another frame system. -/
theorem exists_frameAtlasSeminorm_le [LocallyCompactSpace E]
    (hK : TauCeti.IsCompactChartCover U c K)
    {ι' : Type*} [Fintype ι'] (e' : ι' → Trivialization F (π F V))
    [∀ i, MemTrivializationAtlas (e' i)]
    {U' : ι' → Opens M} (hU' : ∀ i, (U' i : Set M) ⊆ (e' i).baseSet)
    {c' : ∀ i, U' i} {K' : ∀ i, Compacts (extChartAt I (c' i)).target}
    (hK' : TauCeti.IsCompactChartCover U' c' K') :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Cₛ^k⟮I; F, V⟯,
      frameAtlasSeminorm e' U' hU' c' K' k le_rfl s ≤
        C * frameAtlasSeminorm e U hU c K k le_rfl s := by
  let _ := frameTopology (I := I) (n := k) e U hU
  have hcont : Continuous (frameAtlasSeminorm e' U' hU' c' K' k le_rfl) := by
    have h := continuous_frameAtlasSeminorm (I := I) e' U' hU' c' K' k le_rfl
    rwa [← frameTopology_eq_of_covers e U hU hK.exists_mem e' U' hU' hK'.exists_mem] at h
  obtain ⟨t, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (withSeminorms_frameAtlasSeminorm e U hU c K hK) _ hcont
  refine ⟨C, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC), fun s ↦ (hbound s).trans ?_⟩
  rw [_root_.smul_apply, NNReal.smul_def, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun _ _ ↦ le_rfl) C.2

/-- **Normability of `C^k` sections over a compact manifold.** Over a compact manifold modelled on
a locally compact space, the compact derivative topology of any covering frame system on the
`C^k` sections is generated by a single seminorm, that of a finite frame atlas. -/
theorem isNormableSpace_frameTopology [CompactSpace M] [LocallyCompactSpace E]
    {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet) (hcover : ∀ y : M, ∃ i, y ∈ U i) :
    let _ := frameTopology (I := I) (n := k) e U hU
    IsNormableSpace 𝕜 Cₛ^k⟮I; F, V⟯ := by
  obtain ⟨t, r, c, K, hK⟩ := TauCeti.exists_finite_compact_chart_cover_subordinate (I := I) U hcover
  rw [frameTopology_eq_of_covers e U hU hcover (fun j ↦ e (r j)) (fun j ↦ U (r j))
    (fun j ↦ hU (r j)) hK.exists_mem]
  intro _
  exact ⟨⟨_, withSeminorms_frameAtlasSeminorm (fun j ↦ e (r j)) (fun j ↦ U (r j))
    (fun j ↦ hU (r j)) c K hK⟩⟩

section Normed

variable [LocallyCompactSpace E] (k) (hK : TauCeti.IsCompactChartCover U c K)

include hK in
/-- The normed group of `C^k` sections with the norm of a finite frame atlas. Its topology is the
compact derivative topology of the frames. -/
noncomputable abbrev frameAtlasNormedAddCommGroup : NormedAddCommGroup Cₛ^k⟮I; F, V⟯ := by
  let _ : Norm Cₛ^k⟮I; F, V⟯ := ⟨frameAtlasSeminorm e U hU c K k le_rfl⟩
  let core : NormedSpace.Core 𝕜 Cₛ^k⟮I; F, V⟯ :=
    { norm_nonneg s := apply_nonneg _ s
      norm_smul a s := map_smul_eq_mul _ a s
      norm_triangle s t := map_add_le_add _ s t
      norm_eq_zero_iff s := frameAtlasSeminorm_eq_zero_iff e U hU c K hK s }
  let _ := frameTopology (I := I) (n := k) e U hU
  have hp : WithSeminorms fun _ : Unit ↦ frameAtlasSeminorm e U hU c K k le_rfl :=
    withSeminorms_frameAtlasSeminorm e U hU c K hK
  refine NormedAddCommGroup.ofCoreReplaceTopology core ?_
  rw [hp.topologicalSpace_eq_iInf, ciInf_unique]

/-- The normed space of `C^k` sections with the norm of a finite frame atlas. -/
noncomputable abbrev frameAtlasNormedSpace :
    letI := frameAtlasNormedAddCommGroup e U hU c K k hK
    NormedSpace 𝕜 Cₛ^k⟮I; F, V⟯ :=
  letI := frameAtlasNormedAddCommGroup e U hU c K k hK
  { norm_smul_le a s := (map_smul_eq_mul (frameAtlasSeminorm e U hU c K k le_rfl) a s).le }

/-- The norm of the normed group of sections is the seminorm of the finite frame atlas. -/
theorem norm_frameAtlas (s : Cₛ^k⟮I; F, V⟯) :
    letI := frameAtlasNormedAddCommGroup e U hU c K k hK
    ‖s‖ = frameAtlasSeminorm e U hU c K k le_rfl s :=
  rfl

/-- **The Banach space of `C^k` sections.** Over a boundaryless manifold modelled on a locally
compact space over `ℝ` or `ℂ`, the `C^k` sections of a bundle with complete model fibre form a
complete normed space for the norm of a finite frame atlas. -/
theorem completeSpace_frameAtlas [IsRCLikeNormedField 𝕜] [I.Boundaryless]
    [CompleteSpace F] :
    letI := frameAtlasNormedAddCommGroup e U hU c K k hK
    CompleteSpace Cₛ^k⟮I; F, V⟯ := by
  let _ := frameAtlasNormedAddCommGroup e U hU c K k hK
  have := isUniformAddGroup_frameUniformSpace (I := I) (n := k) e U hU
  -- The norm uniformity and the frame uniformity are uniform additive group structures with the
  -- same topology, hence equal.
  have h : (PseudoMetricSpace.toUniformSpace : UniformSpace Cₛ^k⟮I; F, V⟯) =
      frameUniformSpace (I := I) (n := k) e U hU :=
    IsUniformAddGroup.ext inferInstance this (congrArg (fun t ↦ @nhds _ t 0)
      (frameUniformSpace_toTopologicalSpace (I := I) (n := k) e U hU).symm)
  rw [h]
  exact completeSpace_frameTopology e U hU hK.exists_mem

end Normed

end ContMDiffSection
