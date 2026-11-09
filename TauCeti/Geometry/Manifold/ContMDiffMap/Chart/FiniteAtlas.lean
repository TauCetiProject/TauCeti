/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CountableSeminorms
public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Finite-atlas `C^k` norms

Let `M` be a manifold and `k` a natural number. A *finite chart atlas with compact coordinate
pieces* is a finite family of points `c i` together with compact subsets `K i` of the extended
chart targets at `c i`, such that every point of `M` has coordinates in the relative interior of
some `K i`. Its `C^k` seminorm on vector-valued maps is the maximum over `i` of the compact chart
seminorms `ContMDiffMap.chartCkSeminorm (c i) (K i) k`, that is, the largest coordinate
derivative of order at most `k` on the pieces `K i`.

This seminorm is a norm (`ContMDiffMap.finiteAtlasSeminorm_eq_zero_iff`). On `C^k` maps it
generates the weak Whitney topology (`ContMDiffMap.withSeminorms_finiteAtlasSeminorm`), and
two finite atlases give equivalent norms (`ContMDiffMap.exists_finiteAtlasSeminorm_le`). A compact
manifold modelled on a locally compact space has such an atlas, so its space of vector-valued `C^k`
maps is a normable space (`ContMDiffMap.isNormableSpace_of_compactSpace`). These are the finite-jet
norms on which Banach-space methods such as the Sard–Smale theorem are applied to spaces of `C^k`
functions on compact manifolds.

The atlas may include boundary and corner charts: derivatives are taken within the extended chart
targets and interiors are relative to them. The coefficient space is an arbitrary normed space.

## Main definitions

* `ContMDiffMap.finiteAtlasSeminorm`: the `C^k` seminorm of a finite chart atlas with compact
  coordinate pieces.

## Main results

* `ContMDiffMap.exists_chartCkSeminorm_le_finiteAtlasSeminorm`: every compact chart `C^k`
  seminorm is bounded by a multiple of the finite-atlas seminorm.
* `ContMDiffMap.exists_finiteAtlasSeminorm_le`: the seminorms of two finite atlases are
  equivalent.
* `ContMDiffMap.finiteAtlasSeminorm_eq_zero_iff`: the finite-atlas seminorm is a norm.
* `ContMDiffMap.withSeminorms_finiteAtlasSeminorm`: it generates the weak Whitney topology on
  `C^k` maps.
* `ContMDiffMap.exists_finiteAtlas`: compact manifolds modelled on locally compact spaces have
  finite atlases with compact coordinate pieces.
* `ContMDiffMap.isNormableSpace_of_compactSpace`: on such manifolds the weak Whitney topology on
  vector-valued `C^k` maps is normable.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for the `C^k` topology on maps of
  a compact manifold defined by finitely many charts.
-/

public section

open Set Filter Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The points of a chart source whose coordinates lie in a relatively open subset of the chart
target form an open subset of the manifold. -/
theorem isOpen_setOf_extChartAt_mem (x : M) {O : Set (extChartAt I x).target} (hO : IsOpen O) :
    IsOpen {y : M | ∃ hy : y ∈ (extChartAt I x).source,
      (⟨extChartAt I x y, (extChartAt I x).map_source hy⟩ : (extChartAt I x).target) ∈ O} := by
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hO
  have hset : {y : M | ∃ hy : y ∈ (extChartAt I x).source,
      (⟨extChartAt I x y, (extChartAt I x).map_source hy⟩ : (extChartAt I x).target) ∈
        Subtype.val ⁻¹' V} = (extChartAt I x).source ∩ extChartAt I x ⁻¹' V := by
    ext y
    exact ⟨fun ⟨hy, hyV⟩ ↦ ⟨hy, hyV⟩, fun ⟨hy, hyV⟩ ↦ ⟨hy, hyV⟩⟩
  rw [hset]
  exact isOpen_extChartAt_preimage' x hV

end TauCeti

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]
  {ι : Type*} [Fintype ι] (c : ι → M)
  (K : ∀ i, TopologicalSpace.Compacts (extChartAt I (c i)).target)

/-- The `C^k` seminorm of a finite chart atlas with compact coordinate pieces `K i` in the
extended chart targets at the points `c i`: the largest coordinate derivative of order at most
`k` on the pieces. -/
noncomputable def finiteAtlasSeminorm (k : ℕ) (hk : k ≤ n) :
    Seminorm 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
  Finset.univ.sup fun i ↦ chartCkSeminorm (c i) (K i) k hk

/-- Each chart seminorm of a finite atlas is bounded by the finite-atlas seminorm. -/
theorem chartCkSeminorm_le_finiteAtlasSeminorm (k : ℕ) (hk : k ≤ n) (i : ι) :
    chartCkSeminorm (F := F) (c i) (K i) k hk ≤ finiteAtlasSeminorm c K k hk :=
  Finset.le_sup (f := fun i ↦ chartCkSeminorm (F := F) (c i) (K i) k hk) (Finset.mem_univ i)

/-- A nonnegative bound on the finite-atlas seminorm is a bound on every coordinate derivative
of order at most `k` on every compact piece. -/
theorem finiteAtlasSeminorm_le_iff (k : ℕ) (hk : k ≤ n) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) {r : ℝ}
    (hr : 0 ≤ r) :
    finiteAtlasSeminorm c K k hk f ≤ r ↔
      ∀ i (m : ℕ) (hm : m ≤ k), ∀ z ∈ K i,
        ‖chartIteratedFDeriv f (c i) m ((Nat.cast_le.mpr hm).trans hk) z‖ ≤ r := by
  constructor
  · intro h i
    exact (chartCkSeminorm_le_iff (c i) (K i) k hk f hr).mp
      ((chartCkSeminorm_le_finiteAtlasSeminorm c K k hk i f).trans h)
  · intro h
    exact Seminorm.finset_sup_apply_le hr fun i _ ↦
      (chartCkSeminorm_le_iff (c i) (K i) k hk f hr).mpr (h i)

/-- The finite-atlas seminorm is continuous for the weak Whitney topology. -/
theorem continuous_finiteAtlasSeminorm (k : ℕ) (hk : k ≤ n) :
    Continuous (finiteAtlasSeminorm (F := F) c K k hk) := by
  have := isTopologicalAddGroup_manifoldWeakWhitney (I := I) (M := M) (F := F) (n := n)
  refine Seminorm.continuous_of_forall fun r hr ↦ ?_
  rw [finiteAtlasSeminorm, Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
  exact (biInter_finset_mem _).mpr fun i _ ↦ ball_chartCkSeminorm_mem_nhds _ _ _ _ _ hr

variable {c K}

section Cover

variable (hK : ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt I (c i)).source,
  (⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ : (extChartAt I (c i)).target) ∈
    interior (K i : Set (extChartAt I (c i)).target))

include hK in
/-- If the relative interiors of the compact pieces cover the manifold, every compact chart `C^k`
seminorm is bounded by a positive multiple of the finite-atlas seminorm. -/
theorem exists_chartCkSeminorm_le_finiteAtlasSeminorm (x : M)
    (L : TopologicalSpace.Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
      chartCkSeminorm x L k hk f ≤ C * finiteAtlasSeminorm c K k hk f := by
  classical
  -- The coordinate points of the chart at `x` represented in the interior of the piece `K i`.
  let U (i : ι) : Set (extChartAt I x).target :=
    {z | ∃ hz : (extChartAt I x).symm z ∈ (extChartAt I (c i)).source,
      (⟨extChartAt I (c i) ((extChartAt I x).symm z), (extChartAt I (c i)).map_source hz⟩ :
        (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target)}
  have hs : Continuous (fun z : (extChartAt I x).target ↦ (extChartAt I x).symm z) :=
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm x)
  have hU (i : ι) : IsOpen (U i) :=
    (TauCeti.isOpen_setOf_extChartAt_mem (c i) isOpen_interior).preimage hs
  have hc : (L : Set (extChartAt I x).target) ⊆ ⋃ i ∈ Finset.univ, U i := by
    intro z _
    obtain ⟨i, hi⟩ := hK ((extChartAt I x).symm z)
    exact mem_biUnion (Finset.mem_univ i) hi
  obtain ⟨P, hP, hPU, hLP⟩ := L.isCompact.finite_compact_cover Finset.univ U
    (fun i _ ↦ hU i) hc
  have hb (i : ι) : ∃ C : ℝ, 0 < C ∧ ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
      chartCkSeminorm x ⟨P i, hP i⟩ k hk f ≤ C * chartCkSeminorm (c i) (K i) k hk f :=
    exists_chartCkSeminorm_le_coordChange x (c i) ⟨P i, hP i⟩ (K i)
      (fun z hz ↦ (hPU i hz).1) (fun z hz ↦ interior_subset (hPU i hz).2) k hk
  choose C hC hbound using hb
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ (hC i).le
  refine ⟨1 + ∑ i, C i, add_pos_of_pos_of_nonneg zero_lt_one hsum, fun f ↦ ?_⟩
  have hq := apply_nonneg (finiteAtlasSeminorm (F := F) c K k hk) f
  refine (chartCkSeminorm_le_iff x L k hk f
    (mul_nonneg (add_pos_of_pos_of_nonneg zero_lt_one hsum).le hq)).mpr fun m hm z hz ↦ ?_
  have hz' : z ∈ (L : Set (extChartAt I x).target) := hz
  rw [hLP] at hz'
  obtain ⟨i, -, hzi⟩ := mem_iUnion₂.mp hz'
  have hderiv := (chartCkSeminorm_le_iff x ⟨P i, hP i⟩ k hk f
    (apply_nonneg _ _)).mp le_rfl m hm z hzi
  have hCi : C i ≤ 1 + ∑ j, C j :=
    (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  exact hderiv.trans ((hbound i f).trans
    ((mul_le_mul_of_nonneg_left (chartCkSeminorm_le_finiteAtlasSeminorm c K k hk i f)
      (hC i).le).trans (mul_le_mul_of_nonneg_right hCi hq)))

include hK in
/-- **Equivalence of finite-atlas norms.** The `C^k` seminorm of any finite atlas is bounded by
a positive multiple of that of a finite atlas whose interiors cover the manifold. -/
theorem exists_finiteAtlasSeminorm_le {ι' : Type*} [Fintype ι'] (c' : ι' → M)
    (K' : ∀ i, TopologicalSpace.Compacts (extChartAt I (c' i)).target) (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
      finiteAtlasSeminorm c' K' k hk f ≤ C * finiteAtlasSeminorm c K k hk f := by
  classical
  choose C hC hbound using fun i ↦
    exists_chartCkSeminorm_le_finiteAtlasSeminorm (F := F) hK (c' i) (K' i) k hk
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ (hC i).le
  refine ⟨1 + ∑ i, C i, add_pos_of_pos_of_nonneg zero_lt_one hsum, fun f ↦ ?_⟩
  have hq := apply_nonneg (finiteAtlasSeminorm (F := F) c K k hk) f
  refine Seminorm.finset_sup_apply_le
    (mul_nonneg (add_pos_of_pos_of_nonneg zero_lt_one hsum).le hq) fun i _ ↦ ?_
  have hCi : C i ≤ 1 + ∑ j, C j :=
    (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  exact (hbound i f).trans (mul_le_mul_of_nonneg_right hCi hq)

include hK in
/-- **The finite-atlas seminorm is a norm**: it vanishes only on the zero map, since every point
has coordinates in some compact piece, where the derivative of order zero is the value of the
map. -/
theorem finiteAtlasSeminorm_eq_zero_iff (k : ℕ) (hk : k ≤ n) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    finiteAtlasSeminorm c K k hk f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  ext y
  obtain ⟨i, hy, hyK⟩ := hK y
  have hle := (finiteAtlasSeminorm_le_iff c K k hk f le_rfl).mp h.le i 0 (Nat.zero_le k) _
    (interior_subset hyK)
  have h0 : chartIteratedFDeriv f (c i) 0 ((Nat.cast_le.mpr (Nat.zero_le k)).trans hk)
      ⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ = 0 :=
    norm_le_zero_iff.mp hle
  have hval := chartIteratedFDeriv_zero_apply f (c i)
    ⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ (fun j ↦ Fin.elim0 j)
  rw [(extChartAt I (c i)).left_inv hy] at hval
  rw [← hval]
  exact congrArg (fun A : E [×0]→L[𝕜] F ↦ A (fun j ↦ Fin.elim0 j)) h0

end Cover

section Topology

variable (k : ℕ) [IsManifold I k M]

/-- **The finite-atlas norm generates the weak Whitney topology** on `C^k` maps, when the
relative interiors of its compact pieces cover the manifold. -/
theorem withSeminorms_finiteAtlasSeminorm
    (hK : ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt I (c i)).source,
      (⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ :
        (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target)) :
    WithSeminorms fun _ : Unit ↦ finiteAtlasSeminorm (F := F) (n := k) c K k le_rfl := by
  have hp := withSeminorms_manifoldWeakWhitney (I := I) (M := M) (F := F) (n := k)
  let _ := hp.isTopologicalAddGroup
  refine hp.congr ?_ (Seminorm.IsBounded.of_real ?_)
  · intro _
    obtain ⟨s, C, -, hbound⟩ := Seminorm.bound_of_continuous hp _
      (continuous_finiteAtlasSeminorm (F := F) c K k le_rfl)
    exact ⟨s, C, by simpa only [Seminorm.comp_id] using hbound⟩
  · rintro ⟨x, ⟨m, hm⟩, L⟩
    have hmk : m ≤ k := by exact_mod_cast hm
    obtain ⟨C, -, hbound⟩ :=
      exists_chartCkSeminorm_le_finiteAtlasSeminorm (F := F) hK x L k le_rfl
    refine ⟨{()}, C, fun f ↦ ?_⟩
    have hderiv : chartDerivativeSeminorm (F := F) x L m hm f ≤
        chartCkSeminorm x L k le_rfl f :=
      (chartDerivativeSeminorm_le_iff x L m hm f (apply_nonneg _ _)).mpr
        fun z hz ↦ (chartCkSeminorm_le_iff x L k le_rfl f (apply_nonneg _ _)).mp
          le_rfl m hmk z hz
    simpa only [LinearMap.id_apply, chartSeminormFamily_apply, Finset.sup_singleton] using
      hderiv.trans (hbound f)

omit [IsManifold I k M] in
/-- A compact manifold modelled on a locally compact space has a finite atlas with compact
coordinate pieces whose relative interiors cover it. -/
theorem exists_finiteAtlas [CompactSpace M] [LocallyCompactSpace H] :
    ∃ (N : ℕ) (c : Fin N → M) (K : ∀ i, TopologicalSpace.Compacts (extChartAt I (c i)).target),
      ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target) := by
  obtain ⟨N, α, u, b, hu, hs⟩ := TauCeti.exists_finite_precompact_chart_cover (I := I)
    (isCompact_univ : IsCompact (univ : Set M))
  have hK (i : Fin N) :
      IsCompact (Subtype.val ⁻¹' b i : Set (extChartAt I (α i)).target) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr (hu i).2.2.2.1]
    exact (hu i).2.2.1
  refine ⟨N, α, fun i ↦ ⟨_, hK i⟩, fun y ↦ ?_⟩
  obtain ⟨i, hyi⟩ := mem_iUnion.mp (hs (mem_univ y))
  have hy : y ∈ (extChartAt I (α i)).source := (hu i).2.1 hyi
  refine ⟨i, hy, ?_⟩
  -- The coordinate points whose inverse chart lies in `u i` form a relatively open set
  -- inside the compact piece.
  have hO : IsOpen {z : (extChartAt I (α i)).target | (extChartAt I (α i)).symm z ∈ u i} :=
    (hu i).1.preimage (continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_extChartAt_symm (α i)))
  refine interior_maximal (fun z hz ↦ ?_) hO ?_
  · have hmem := (hu i).2.2.2.2 (mem_image_of_mem _ hz)
    rwa [(extChartAt I (α i)).right_inv z.2] at hmem
  · change (extChartAt I (α i)).symm (extChartAt I (α i) y) ∈ u i
    rwa [(extChartAt I (α i)).left_inv hy]

/-- **Normability of `C^k` maps on a compact manifold.** On a compact manifold modelled on a
locally compact space, the weak Whitney topology on vector-valued `C^k` maps is generated by
a single seminorm, the `C^k` seminorm of a finite atlas. -/
theorem isNormableSpace_of_compactSpace [CompactSpace M] [LocallyCompactSpace H] :
    IsNormableSpace 𝕜 C^k⟮I, M; 𝓘(𝕜, F), F⟯ := by
  obtain ⟨N, c, K, hK⟩ := exists_finiteAtlas (I := I) (M := M)
  exact ⟨⟨_, withSeminorms_finiteAtlasSeminorm (F := F) k hK⟩⟩

end Topology

end ContMDiffMap
