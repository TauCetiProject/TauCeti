/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.WithSeminorms
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.ExtChartAt.LocallyCompact
import TauCeti.Geometry.Manifold.VectorBundle.Section.Complete
import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover

/-!
# Finite-atlas `C^k` norms on bundle sections

Let `V` be a smooth vector bundle over a manifold `M` and `k` a natural number. Lifting the
vector-valued map norms of `TauCeti.Geometry.Manifold.ContMDiffMap.Chart.FiniteAtlas` and
`TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Banach` (`ContMDiffMap.finiteAtlasSeminorm`,
`ContMDiffMap.finiteAtlasNormedAddCommGroup`) to bundle trivializations, a *finite chart-frame
atlas with compact coordinate pieces* consists of finitely many smooth bundle trivializations `e i`
on open subsets `U i ⊆ (e i).baseSet`, chart centres `c i : U i`, and compact subsets `K i` of the
extended chart targets `(extChartAt I (c i)).target` whose relative interiors cover `M`. Its `C^k`
seminorm `ContMDiffSection.finiteAtlasSeminorm` on `C^n` sections (`k ≤ n`) is the maximum over `i`
of `Bundle.Trivialization.chartCkSeminorm (e i) (hU i) (c i) (K i) k hk`.

Partitioning any compact coordinate piece across a covering finite chart-frame atlas and applying
the compact overlap estimate (`Bundle.Trivialization.exists_chartCkSeminorm_le_coordChange`) shows
that every compact chart-frame `C^k` seminorm, in any smooth trivialization, is bounded by a
multiple of the finite-atlas seminorm
(`ContMDiffSection.exists_chartCkSeminorm_le_finiteAtlasSeminorm`), so any two covering finite
chart-frame atlases define equivalent norms (`ContMDiffSection.exists_finiteAtlasSeminorm_le`).

When the compact pieces cover `M`, the finite-atlas seminorm bounds every frame-coordinate value on
the pieces (`ContMDiffSection.norm_frameCoordinates_apply_le_finiteAtlasSeminorm`) and vanishes only
on the zero section (`ContMDiffSection.finiteAtlasSeminorm_eq_zero_iff`). On `C^k` sections, a
finite chart-frame atlas with covering relative interiors generates
`ContMDiffSection.frameTopology` (`ContMDiffSection.withSeminorms_finiteAtlasSeminorm`) and equips
`Cₛ^k⟮I; F, V⟯` with a normed space structure (`ContMDiffSection.finiteAtlasNormedAddCommGroup`,
`ContMDiffSection.finiteAtlasNormedSpace`) that is complete over `RCLike` normed fields when the
model fibre is complete (`ContMDiffSection.completeSpace_finiteAtlas`). Every open cover on a
compact manifold modelled on a locally compact space admits a subordinate finite compact chart cover
(`TauCeti.exists_finite_compact_chart_cover_of_opens_cover`), so `ContMDiffSection.frameTopology` on
`C^k` sections is normable (`ContMDiffSection.isNormableSpace_frameTopology_of_compactSpace`).

Derivatives are taken within extended chart targets and interiors are relative to them, so
boundary and corner charts are included throughout. Whenever a compact coordinate piece has nonempty
relative interior in an extended chart target, the model vector space is automatically locally
compact (`ModelWithCorners.locallyCompactSpace_of_nonempty_interior_extChartAt_target`), so covering
finite-atlas comparisons and Banach completeness need no separate local compactness assumption on
the model space. Neither finite rank of the fibres nor Hausdorffness of the base is required.

## Main definitions

* `ContMDiffSection.finiteAtlasSeminorm`: the `C^k` seminorm of a finite chart-frame atlas with
  compact coordinate pieces.
* `ContMDiffSection.finiteAtlasNormedAddCommGroup` and
  `ContMDiffSection.finiteAtlasNormedSpace`: the normed space of `C^k` sections for a covering
  finite chart-frame atlas, carrying `ContMDiffSection.frameTopology`.

## Main results

* `ContMDiffSection.exists_chartCkSeminorm_le_finiteAtlasSeminorm` and
  `ContMDiffSection.exists_finiteAtlasSeminorm_le`: dominance of compact chart-frame `C^k`
  seminorms and equivalence of finite chart-frame `C^k` norms.
* `ContMDiffSection.norm_frameCoordinates_apply_le_finiteAtlasSeminorm`,
  `ContMDiffSection.finiteAtlasSeminorm_eq_zero_iff`, and
  `ContMDiffSection.exists_pos_forall_mem_of_isOpen_totalSpace`: pointwise frame-coordinate
  control, separation of points, and uniform stability of open conditions in the total space.
* `ContMDiffSection.withSeminorms_finiteAtlasSeminorm_subtype`,
  `ContMDiffSection.withSeminorms_finiteAtlasSeminorm_subtype_of_cover`,
  `ContMDiffSection.withSeminorms_finiteAtlasSeminorm`,
  `ContMDiffSection.withSeminorms_finiteAtlasSeminorm_of_cover`,
  `ContMDiffSection.withSeminorms_finiteAtlasSeminorm_infty`, and
  `ContMDiffSection.withSeminorms_finiteAtlasSeminorm_infty_of_cover`: generation of
  `ContMDiffSection.frameTopology` on `C^n`, `C^k`, and `C^∞` sections.
* `ContMDiffSection.completeSpace_finiteAtlas` and
  `ContMDiffSection.isNormableSpace_frameTopology_of_compactSpace`: Banach completeness and
  normability on compact manifolds.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for finite-atlas `C^k` norms on
  compact manifolds.
* R. Hamilton, *The inverse function theorem of Nash and Moser*, Bull. Amer. Math. Soc. 7 (1982),
  Part I, Example 1.1.5, for section spaces over compact manifolds.
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*}
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V]

/-- On an empty base manifold, `C^n` sections form a subsingleton. -/
instance subsingleton_of_isEmpty {n : ℕ∞ω} [IsEmpty M] : Subsingleton Cₛ^n⟮I; F, V⟯ :=
  coe_injective.subsingleton

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

section FiniteAtlasSeminorm

variable {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} [Fintype ι]
  (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  (c : ∀ i, U i) (K : ∀ i, Compacts (extChartAt I (c i)).target)

/-- The `C^k` seminorm of a finite chart-frame atlas with compact coordinate pieces `K i` in the
inherited extended chart targets at `c i : U i`: the maximum over `i` of the compact chart-frame
`C^k` seminorms. -/
def finiteAtlasSeminorm (k : ℕ) (hk : k ≤ n) : Seminorm 𝕜 Cₛ^n⟮I; F, V⟯ :=
  Finset.univ.sup fun i ↦ (e i).chartCkSeminorm (hU i) (c i) (K i) k hk

/-- Defining formula for `ContMDiffSection.finiteAtlasSeminorm`. -/
theorem finiteAtlasSeminorm_def (k : ℕ) (hk : k ≤ n) :
    finiteAtlasSeminorm e U hU c K k hk =
      Finset.univ.sup fun i ↦ (e i).chartCkSeminorm (hU i) (c i) (K i) k hk :=
  (rfl)

/-- On an empty index type, the finite-atlas `C^k` seminorm is zero. -/
@[simp]
theorem finiteAtlasSeminorm_of_isEmpty [IsEmpty ι] (k : ℕ) (hk : k ≤ n) :
    finiteAtlasSeminorm e U hU c K k hk = 0 := by
  rw [finiteAtlasSeminorm_def, Finset.univ_eq_empty, Finset.sup_empty, Seminorm.bot_eq_zero]

/-- Each piece's compact chart-frame `C^k` seminorm is bounded by the finite-atlas seminorm. -/
theorem chartCkSeminorm_le_finiteAtlasSeminorm (k : ℕ) (hk : k ≤ n) (i : ι) :
    (e i).chartCkSeminorm (hU i) (c i) (K i) k hk ≤ finiteAtlasSeminorm e U hU c K k hk :=
  Finset.le_sup (f := fun i ↦ (e i).chartCkSeminorm (hU i) (c i) (K i) k hk) (Finset.mem_univ i)

/-- Each piece's compact chart-frame derivative seminorm of order `m ≤ k` is bounded by the
finite-atlas `C^k` seminorm. -/
theorem chartDerivativeSeminorm_le_finiteAtlasSeminorm (k : ℕ) (hk : k ≤ n) (i : ι)
    {m : ℕ} (hm : m ≤ k) (s : Cₛ^n⟮I; F, V⟯) :
    (e i).chartDerivativeSeminorm (hU i) (c i) (K i) m ((Nat.cast_le.mpr hm).trans hk) s ≤
      finiteAtlasSeminorm e U hU c K k hk s :=
  ((e i).chartDerivativeSeminorm_le_chartCkSeminorm (hU i) (c i) (K i) hm hk s).trans
    (chartCkSeminorm_le_finiteAtlasSeminorm e U hU c K k hk i s)

/-- On each compact piece `K i`, the finite-atlas `C^k` seminorm bounds the norm of the frame
coordinates. -/
theorem norm_frameCoordinates_apply_le_finiteAtlasSeminorm (k : ℕ) (hk : k ≤ n) (i : ι)
    (s : Cₛ^n⟮I; F, V⟯) {z : (extChartAt I (c i)).target} (hz : z ∈ K i) :
    ‖(e i).frameCoordinates (hU i) s ((extChartAt I (c i)).symm z)‖ ≤
      finiteAtlasSeminorm e U hU c K k hk s := by
  have hle := ((e i).chartDerivativeSeminorm_le_iff (hU i) (c i) (K i) 0 (by simp) s
    (apply_nonneg _ _)).mp
      (chartDerivativeSeminorm_le_finiteAtlasSeminorm e U hU c K k hk i (Nat.zero_le k) s) z hz
  rwa [ContMDiffMap.chartIteratedFDeriv_self_target_apply, norm_iteratedFDerivWithin_zero,
    Function.comp_apply] at hle

/-- A nonnegative bound on the finite-atlas `C^k` seminorm is simultaneous control of every
frame-coordinate derivative through order `k` on every compact piece. -/
theorem finiteAtlasSeminorm_le_iff (k : ℕ) (hk : k ≤ n) (s : Cₛ^n⟮I; F, V⟯) {r : ℝ} (hr : 0 ≤ r) :
    finiteAtlasSeminorm e U hU c K k hk s ≤ r ↔
      ∀ i (m : ℕ) (hm : m ≤ k), ∀ z ∈ K i,
        ‖ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) (c i) m
          ((Nat.cast_le.mpr hm).trans hk) z‖ ≤ r := by
  constructor
  · intro h i
    exact ((e i).chartCkSeminorm_le_iff (hU i) (c i) (K i) k hk s hr).mp
      ((chartCkSeminorm_le_finiteAtlasSeminorm e U hU c K k hk i s).trans h)
  · intro h
    exact Seminorm.finset_sup_apply_le hr fun i _ ↦
      ((e i).chartCkSeminorm_le_iff (hU i) (c i) (K i) k hk s hr).mpr (h i)

/-- A positive strict bound on the finite-atlas `C^k` seminorm is simultaneous strict control of
every frame-coordinate derivative through order `k` on every compact piece. -/
theorem finiteAtlasSeminorm_lt_iff (k : ℕ) (hk : k ≤ n) (s : Cₛ^n⟮I; F, V⟯) {r : ℝ} (hr : 0 < r) :
    finiteAtlasSeminorm e U hU c K k hk s < r ↔
      ∀ i (m : ℕ) (hm : m ≤ k), ∀ z ∈ K i,
        ‖ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) (c i) m
          ((Nat.cast_le.mpr hm).trans hk) z‖ < r := by
  constructor
  · intro h i
    exact ((e i).chartCkSeminorm_lt_iff (hU i) (c i) (K i) k hk s hr).mp
      ((chartCkSeminorm_le_finiteAtlasSeminorm e U hU c K k hk i s).trans_lt h)
  · intro h
    exact Seminorm.finset_sup_apply_lt hr fun i _ ↦
      ((e i).chartCkSeminorm_lt_iff (hU i) (c i) (K i) k hk s hr).mpr (h i)

/-- A nonnegative bound on the finite-atlas `C^k` seminorm of `t - s` is uniform control of the
differences of all frame-coordinate derivatives through order `k` on every compact piece. -/
theorem finiteAtlasSeminorm_sub_le_iff (k : ℕ) (hk : k ≤ n) (s t : Cₛ^n⟮I; F, V⟯)
    {r : ℝ} (hr : 0 ≤ r) :
    finiteAtlasSeminorm e U hU c K k hk (t - s) ≤ r ↔
      ∀ i (m : ℕ) (hm : m ≤ k), ∀ z ∈ K i,
        ‖ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) t) (c i) m
            ((Nat.cast_le.mpr hm).trans hk) z -
          ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) (c i) m
            ((Nat.cast_le.mpr hm).trans hk) z‖ ≤ r := by
  rw [finiteAtlasSeminorm_le_iff e U hU c K k hk (t - s) hr]
  refine forall_congr' fun i ↦ forall_congr' fun m ↦ forall_congr' fun hm ↦
    forall₂_congr fun z _ ↦ ?_
  rw [map_sub, ContMDiffMap.chartIteratedFDeriv_sub, ContinuousMap.sub_apply]

/-- Membership in a finite-atlas `C^k` seminorm ball is uniform proximity of all frame-coordinate
derivatives through order `k` on every compact piece. -/
theorem mem_ball_finiteAtlasSeminorm_iff (k : ℕ) (hk : k ≤ n) (s t : Cₛ^n⟮I; F, V⟯)
    {r : ℝ} (hr : 0 < r) :
    t ∈ (finiteAtlasSeminorm e U hU c K k hk).ball s r ↔
      ∀ i (m : ℕ) (hm : m ≤ k), ∀ z ∈ K i,
        ‖ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) t) (c i) m
            ((Nat.cast_le.mpr hm).trans hk) z -
          ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) (c i) m
            ((Nat.cast_le.mpr hm).trans hk) z‖ < r := by
  rw [Seminorm.mem_ball, finiteAtlasSeminorm_lt_iff e U hU c K k hk (t - s) hr]
  refine forall_congr' fun i ↦ forall_congr' fun m ↦ forall_congr' fun hm ↦
    forall₂_congr fun z _ ↦ ?_
  rw [map_sub, ContMDiffMap.chartIteratedFDeriv_sub, ContinuousMap.sub_apply]

/-- Raising the derivative order increases the finite-atlas `C^k` seminorm. -/
theorem finiteAtlasSeminorm_le_of_le {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ n) :
    finiteAtlasSeminorm e U hU c K k ((Nat.cast_le.mpr hkl).trans hl) ≤
      finiteAtlasSeminorm e U hU c K l hl :=
  Finset.sup_mono_fun fun i _ ↦ (e i).chartCkSeminorm_le_of_le (hU i) (c i) (K i) hkl hl

/-- The finite-atlas `C^k` seminorm is continuous for `ContMDiffSection.frameTopology` in the same
frame family. -/
theorem continuous_finiteAtlasSeminorm (k : ℕ) (hk : k ≤ n) :
    letI := frameTopology (I := I) (n := n) e U hU
    Continuous (finiteAtlasSeminorm e U hU c K k hk) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  refine Seminorm.continuous_finsetSup fun i _ ↦ ?_
  exact ((ContMDiffMap.continuous_chartCkSeminorm (c i) (K i) k hk).comp
    (continuous_frameCoordinates (I := I) (n := n) e U hU i)).congr fun s ↦
      ((e i).chartCkSeminorm_apply (hU i) (c i) (K i) k hk s).symm

section

variable {e U hU c K}

/-- Convergence in the finite-atlas `C^k` seminorm implies pointwise convergence of every
frame-coordinate derivative through order `k` on the compact pieces. -/
theorem tendsto_chartIteratedFDeriv_of_tendsto_finiteAtlasSeminorm {k : ℕ} {hk : k ≤ n}
    {P : Type*} {l : Filter P} {u : P → Cₛ^n⟮I; F, V⟯} {s : Cₛ^n⟮I; F, V⟯}
    (h : Tendsto (fun p ↦ finiteAtlasSeminorm e U hU c K k hk (u p - s)) l (𝓝 0))
    (i : ι) {m : ℕ} (hm : m ≤ k) {z : (extChartAt I (c i)).target} (hz : z ∈ K i) :
    Tendsto (fun p ↦ ContMDiffMap.chartIteratedFDeriv
        ((e i).frameCoordinates (hU i) (u p)) (c i) m ((Nat.cast_le.mpr hm).trans hk) z) l
      (𝓝 (ContMDiffMap.chartIteratedFDeriv
        ((e i).frameCoordinates (hU i) s) (c i) m ((Nat.cast_le.mpr hm).trans hk) z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) h
  have hb := (finiteAtlasSeminorm_le_iff e U hU c K k hk (u p - s) (apply_nonneg _ _)).mp
    le_rfl i m hm z hz
  rwa [map_sub, ContMDiffMap.chartIteratedFDeriv_sub, ContinuousMap.sub_apply] at hb

end

variable {c K}

section Cover

variable (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
  ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
    (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
      (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

include hK

/-- If the relative interiors of the compact pieces cover `M`, every compact chart-frame `C^k`
seminorm in any smooth trivialization is bounded by a positive multiple of the finite-atlas `C^k`
seminorm. -/
theorem exists_chartCkSeminorm_le_finiteAtlasSeminorm
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    {U' : Opens M} (hU' : (U' : Set M) ⊆ e'.baseSet)
    (x : U') (L : Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Cₛ^n⟮I; F, V⟯,
      e'.chartCkSeminorm hU' x L k hk s ≤ C * finiteAtlasSeminorm e U hU c K k hk s := by
  classical
  let O (i : ι) : Set (extChartAt I x).target :=
    {z | ∃ hyU : ((extChartAt I x).symm z : M) ∈ U i,
      ∃ hy : (⟨((extChartAt I x).symm z : M), hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨((extChartAt I x).symm z : M), hyU⟩,
          (extChartAt I (c i)).map_source hy⟩ : (extChartAt I (c i)).target) ∈
          interior (K i : Set (extChartAt I (c i)).target)}
  have hc : (L : Set (extChartAt I x).target) ⊆ ⋃ i ∈ Finset.univ, O i := fun z _ ↦ by
    obtain ⟨i, hi⟩ := hK ((extChartAt I x).symm z : M)
    exact mem_biUnion (Finset.mem_univ i) hi
  obtain ⟨P, hP, hPO, hLP⟩ := L.isCompact.finite_compact_cover Finset.univ O
    (fun i _ ↦ TauCeti.isOpen_setOf_extChartAt_symm_mem x (c i) isOpen_interior) hc
  choose C hC hbound using fun i : ι ↦
    e'.exists_chartCkSeminorm_le_coordChange (e i) hU' (hU i) x (c i) ⟨P i, hP i⟩ (K i)
      (fun z hz ↦ let ⟨hyU, hy, hint⟩ := hPO i hz; ⟨hyU, hy, interior_subset hint⟩) k hk
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ (hC i).le
  refine ⟨1 + ∑ i, C i, add_pos_of_pos_of_nonneg zero_lt_one hsum, fun s ↦ ?_⟩
  have hq := apply_nonneg (finiteAtlasSeminorm e U hU c K k hk) s
  refine (e'.chartCkSeminorm_le_iff hU' x L k hk s (by positivity)).mpr fun m hm z hz ↦ ?_
  obtain ⟨i, -, hzi⟩ := mem_iUnion₂.mp (hLP.subset hz)
  have hderiv := ((e'.chartCkSeminorm_le_iff hU' x ⟨P i, hP i⟩ k hk s (apply_nonneg _ _)).mp
    le_rfl m hm z hzi).trans (hbound i s)
  have hCi : C i ≤ 1 + ∑ j, C j :=
    (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  exact hderiv.trans ((mul_le_mul_of_nonneg_left
    (chartCkSeminorm_le_finiteAtlasSeminorm e U hU c K k hk i s) (hC i).le).trans
      (mul_le_mul_of_nonneg_right hCi hq))

/-- **Equivalence of finite chart-frame `C^k` norms.** The `C^k` seminorm of any finite chart-frame
atlas is bounded by a positive multiple of that of a finite chart-frame atlas whose compact pieces
have relative interiors covering `M`. -/
theorem exists_finiteAtlasSeminorm_le {ι' : Type*} [Fintype ι']
    (e' : ι' → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (e' j)]
    (U' : ι' → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (c' : ∀ j, U' j) (K' : ∀ j, Compacts (extChartAt I (c' j)).target)
    (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Cₛ^n⟮I; F, V⟯,
      finiteAtlasSeminorm e' U' hU' c' K' k hk s ≤
        C * finiteAtlasSeminorm e U hU c K k hk s := by
  classical
  choose C hC hbound using fun j ↦
    exists_chartCkSeminorm_le_finiteAtlasSeminorm e U hU hK (e' j) (hU' j) (c' j) (K' j) k hk
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ ↦ (hC j).le
  refine ⟨1 + ∑ j, C j, add_pos_of_pos_of_nonneg zero_lt_one hsum, fun s ↦ ?_⟩
  calc finiteAtlasSeminorm e' U' hU' c' K' k hk s
      ≤ ∑ j, (e' j).chartCkSeminorm (hU' j) (c' j) (K' j) k hk s := by
        refine (Seminorm.finset_sup_le_sum
          (fun j ↦ (e' j).chartCkSeminorm (hU' j) (c' j) (K' j) k hk) Finset.univ s).trans_eq ?_
        simp only [sum_apply]
    _ ≤ ∑ j, C j * finiteAtlasSeminorm e U hU c K k hk s := Finset.sum_le_sum fun j _ ↦ hbound j s
    _ = (∑ j, C j) * finiteAtlasSeminorm e U hU c K k hk s := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 + ∑ j, C j) * finiteAtlasSeminorm e U hU c K k hk s :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (apply_nonneg _ _)

end Cover

/-- **The finite-atlas `C^k` seminorm is a norm** when the compact pieces cover `M`: it vanishes
only on the zero section. -/
theorem finiteAtlasSeminorm_eq_zero_iff
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ K i)
    (k : ℕ) (hk : k ≤ n) (s : Cₛ^n⟮I; F, V⟯) :
    finiteAtlasSeminorm e U hU c K k hk s = 0 ↔ s = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  ext y
  obtain ⟨i, hyU, hy, hyK⟩ := hK y
  let z : (extChartAt I (c i)).target :=
    ⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩
  have hval : (e i).frameCoordinates (hU i) s ((extChartAt I (c i)).symm z) = 0 :=
    norm_le_zero_iff.mp ((norm_frameCoordinates_apply_le_finiteAtlasSeminorm e U hU c K k hk i s
      hyK).trans h.le)
  rw [(extChartAt I (c i)).left_inv hy] at hval
  exact ((e i).frameCoordinates_eq_iff (hU i) s 0 ⟨y, hyU⟩).mp (by simpa using hval)

omit [IsManifold I n M] [Fintype ι] in
private theorem eventually_forall_mem_of_isOpen_totalSpace_piece
    {Ω : Set (TotalSpace F V)} (hΩ : IsOpen Ω)
    {s₀ : Cₛ^n⟮I; F, V⟯} (hs₀ : ∀ y : M, ⟨y, s₀ y⟩ ∈ Ω) (i : ι) :
    ∀ᶠ w : F in 𝓝 0, ∀ z ∈ K i,
      (⟨((extChartAt I (c i)).symm z : M),
        (e i).symm ((extChartAt I (c i)).symm z : M)
          ((e i).frameCoordinates (hU i) s₀ ((extChartAt I (c i)).symm z) + w)⟩ :
        TotalSpace F V) ∈ Ω := by
  have hq : Continuous (fun z : (extChartAt I (c i)).target ↦ (extChartAt I (c i)).symm z) :=
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm (c i))
  have hf₀ : Continuous ((e i).frameCoordinates (hU i) s₀) :=
    ((e i).frameCoordinates (hU i) s₀).contMDiff.continuous
  have hcoord : Continuous (fun p : F × (extChartAt I (c i)).target ↦
      (((extChartAt I (c i)).symm p.2 : M),
        (e i).frameCoordinates (hU i) s₀ ((extChartAt I (c i)).symm p.2) + p.1)) :=
    (continuous_subtypeVal.comp (hq.comp continuous_snd)).prodMk
      ((hf₀.comp (hq.comp continuous_snd)).add continuous_fst)
  have htot : Continuous (fun p : F × (extChartAt I (c i)).target ↦
      (⟨((extChartAt I (c i)).symm p.2 : M),
        (e i).symm ((extChartAt I (c i)).symm p.2 : M)
          ((e i).frameCoordinates (hU i) s₀ ((extChartAt I (c i)).symm p.2) + p.1)⟩ :
        TotalSpace F V)) :=
    (e i).continuousOn_symm.comp_continuous hcoord
      fun p ↦ ⟨hU i ((extChartAt I (c i)).symm p.2).property, mem_univ _⟩
  refine (K i).isCompact.eventually_forall_of_forall_eventually fun z _ ↦
    (hΩ.preimage htot).mem_nhds ?_
  rw [mem_preimage]
  have h0 : (e i).symm ((extChartAt I (c i)).symm z : M)
      ((e i).frameCoordinates (hU i) s₀ ((extChartAt I (c i)).symm z) + 0) =
      s₀ ((extChartAt I (c i)).symm z : M) := by
    rw [add_zero, Trivialization.frameCoordinates_apply,
      (e i).symm_apply_apply_mk (hU i ((extChartAt I (c i)).symm z).property)]
  rw [h0]
  exact hs₀ _

/-- **Uniform finite-atlas stability of open conditions in the total space.** If `Ω` is an open
subset of `TotalSpace F V` containing the graph of a `C^n` section `s₀`, and the compact pieces
`K i` of a finite chart-frame atlas cover `M` (including boundary and corner charts), there is a
positive radius `δ > 0` in the finite-atlas `C^k` seminorm (`k ≤ n`) within which the graph of
every `C^n` section remains in `Ω`. -/
theorem exists_pos_forall_mem_of_isOpen_totalSpace
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ K i)
    (k : ℕ) (hk : k ≤ n) {Ω : Set (TotalSpace F V)} (hΩ : IsOpen Ω)
    {s₀ : Cₛ^n⟮I; F, V⟯} (hs₀ : ∀ y : M, ⟨y, s₀ y⟩ ∈ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Cₛ^n⟮I; F, V⟯,
      finiteAtlasSeminorm e U hU c K k hk (s - s₀) < δ → ∀ y : M, ⟨y, s y⟩ ∈ Ω := by
  have hev : ∀ᶠ w : F in 𝓝 0, ∀ i, ∀ z ∈ K i,
      (⟨((extChartAt I (c i)).symm z : M),
        (e i).symm ((extChartAt I (c i)).symm z : M)
          ((e i).frameCoordinates (hU i) s₀ ((extChartAt I (c i)).symm z) + w)⟩ :
        TotalSpace F V) ∈ Ω :=
    eventually_all.mpr fun i ↦ eventually_forall_mem_of_isOpen_totalSpace_piece e U hU hΩ hs₀ i
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun s hlt y ↦ ?_⟩
  obtain ⟨i, hyU, hy, hzK⟩ := hK y
  let z : (extChartAt I (c i)).target :=
    ⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩
  have hnorm : ‖(e i).frameCoordinates (hU i) (s - s₀) ((extChartAt I (c i)).symm z)‖ < δ :=
    (norm_frameCoordinates_apply_le_finiteAtlasSeminorm e U hU c K k hk i (s - s₀) hzK).trans_lt
      hlt
  have hmem := hball ((dist_zero_right _).trans_lt hnorm) i z hzK
  have hsum : (e i).symm ((extChartAt I (c i)).symm z : M)
      ((e i).frameCoordinates (hU i) s₀ ((extChartAt I (c i)).symm z) +
        (e i).frameCoordinates (hU i) (s - s₀) ((extChartAt I (c i)).symm z)) =
      s ((extChartAt I (c i)).symm z : M) := by
    rw [map_sub, ContMDiffMap.coe_sub, Pi.sub_apply, add_sub_cancel,
      Trivialization.frameCoordinates_apply,
      (e i).symm_apply_apply_mk (hU i ((extChartAt I (c i)).symm z).property)]
  rw [hsum] at hmem
  have hpt : ((extChartAt I (c i)).symm z : M) = y :=
    congrArg Subtype.val ((extChartAt I (c i)).left_inv hy)
  rwa [hpt] at hmem

end FiniteAtlasSeminorm

section GeneralWithSeminorms

variable {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} [Fintype ι]
  (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt I (c i)).target}
  (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
    ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
      (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
        (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

include hK

/-- **The finite-atlas `C^k` seminorms (`k ≤ n`) generate `ContMDiffSection.frameTopology`** on
`C^n` sections when the relative interiors of the compact pieces cover `M`, for any regularity
`n : ℕ∞ω` (neither local compactness of the model nor absence of boundary is required). -/
theorem withSeminorms_finiteAtlasSeminorm_subtype :
    letI := frameTopology (I := I) (n := n) e U hU
    WithSeminorms
      (fun k : {k : ℕ // (k : ℕ∞ω) ≤ n} ↦ finiteAtlasSeminorm (n := n) e U hU c K k.val k.property)
          := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have hp := withSeminorms_frameSeminormFamily (I := I) (n := n) e U hU
  let _ := hp.isTopologicalAddGroup
  refine hp.congr ?_ (Seminorm.IsBounded.of_real ?_)
  · intro k
    obtain ⟨s, C, -, hbound⟩ := Seminorm.bound_of_continuous hp _
      (continuous_finiteAtlasSeminorm (n := n) e U hU c K k.val k.property)
    exact ⟨s, C, by simpa only [Seminorm.comp_id] using hbound⟩
  · rintro ⟨i, x, ⟨m, hm⟩, L⟩
    obtain ⟨C, -, hbound⟩ := exists_chartCkSeminorm_le_finiteAtlasSeminorm (n := n) e U hU hK
      (e i) (hU i) x L m hm
    refine ⟨{⟨m, hm⟩}, C, fun s ↦ ?_⟩
    simpa only [LinearMap.id_apply, frameSeminormFamily_apply, Finset.sup_singleton] using
      ((e i).chartDerivativeSeminorm_le_chartCkSeminorm (hU i) x L le_rfl hm s).trans (hbound s)

/-- The finite-atlas `C^k` seminorms (`k ≤ n`) of any finite chart-frame atlas whose compact pieces
have relative interiors covering `M` generate `ContMDiffSection.frameTopology` on `C^n` sections
for *any* covering smooth frame system. -/
theorem withSeminorms_finiteAtlasSeminorm_subtype_of_cover
    {κ : Type*} (e' : κ → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (hcover' : ∀ y : M, ∃ j, y ∈ U' j) :
    letI := frameTopology (I := I) (n := n) e' U' hU'
    WithSeminorms
      (fun k : {k : ℕ // (k : ℕ∞ω) ≤ n} ↦ finiteAtlasSeminorm (n := n) e U hU c K k.val k.property)
          := by
  have heq : frameTopology (I := I) (n := n) e' U' hU' =
      frameTopology (I := I) (n := n) e U hU := by
    rcases isEmpty_or_nonempty M with _ | _
    · exact Subsingleton.elim _ _
    · have : LocallyCompactSpace E := I.locallyCompactSpace_of_extChartAt_interior_cover hK
      exact frameTopology_eq_of_covers e' U' hU' hcover' e U hU
        (TauCeti.cover_of_extChartAt_cover hK)
  rw [heq]
  exact withSeminorms_finiteAtlasSeminorm_subtype e U hU hK

end GeneralWithSeminorms

section Topology

variable (k : ℕ) [ContMDiffVectorBundle k F V I] [IsManifold I k M]
  {ι : Type*} [Fintype ι]
  (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt I (c i)).target}

private theorem withSeminorms_unit_of_subtype [TopologicalSpace Cₛ^k⟮I; F, V⟯]
    (hp : WithSeminorms
      (fun m : {m : ℕ // (m : ℕ∞ω) ≤ k} ↦ finiteAtlasSeminorm (n := k) e U hU c K m.val m.property))
          :
    WithSeminorms (fun _ : Unit ↦ finiteAtlasSeminorm (n := k) e U hU c K k le_rfl) := by
  refine hp.congr ?_ ?_
  · exact fun _ ↦ ⟨{⟨k, le_rfl⟩}, 1, by
      simpa only [Finset.sup_singleton, one_smul, Seminorm.comp_id] using le_rfl⟩
  · exact fun m ↦ ⟨{()}, 1, by
      simpa only [Finset.sup_singleton, one_smul, Seminorm.comp_id] using
        finiteAtlasSeminorm_le_of_le (n := k) e U hU c K (Nat.cast_le.mp m.property) le_rfl⟩

variable (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
  ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
    (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
      (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

include hK

/-- **The finite-atlas `C^k` norm generates `ContMDiffSection.frameTopology`** on `C^k` sections
when the relative interiors of its compact pieces cover `M`. Neither local compactness of the model
nor absence of boundary is required. -/
theorem withSeminorms_finiteAtlasSeminorm :
    letI := frameTopology (I := I) (n := k) e U hU
    WithSeminorms (fun _ : Unit ↦ finiteAtlasSeminorm (n := k) e U hU c K k le_rfl) := by
  let _ := frameTopology (I := I) (n := k) e U hU
  exact withSeminorms_unit_of_subtype k e U hU
    (withSeminorms_finiteAtlasSeminorm_subtype (n := k) e U hU hK)

/-- A finite chart-frame `C^k` norm whose compact pieces have relative interiors covering `M`
generates `ContMDiffSection.frameTopology` for *any* covering smooth frame system. -/
theorem withSeminorms_finiteAtlasSeminorm_of_cover
    {κ : Type*} (e' : κ → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (hcover' : ∀ y : M, ∃ j, y ∈ U' j) :
    letI := frameTopology (I := I) (n := k) e' U' hU'
    WithSeminorms (fun _ : Unit ↦ finiteAtlasSeminorm (n := k) e U hU c K k le_rfl) := by
  let _ := frameTopology (I := I) (n := k) e' U' hU'
  exact withSeminorms_unit_of_subtype k e U hU
    (withSeminorms_finiteAtlasSeminorm_subtype_of_cover (n := k) e U hU hK e' U' hU' hcover')

/-- The normed group of `C^k` bundle sections equipped with the `C^k` norm of a finite chart-frame
atlas whose compact pieces have relative interiors covering `M`. Its topology is definitionally
`ContMDiffSection.frameTopology e U hU`. -/
@[instance_reducible]
def finiteAtlasNormedAddCommGroup : NormedAddCommGroup Cₛ^k⟮I; F, V⟯ :=
  letI := frameTopology (I := I) (n := k) e U hU
  letI : Norm Cₛ^k⟮I; F, V⟯ := ⟨finiteAtlasSeminorm e U hU c K k le_rfl⟩
  NormedAddCommGroup.ofCoreReplaceTopology
    (𝕜 := 𝕜)
    { norm_nonneg s := apply_nonneg _ s
      norm_smul a s := map_smul_eq_mul _ a s
      norm_triangle s t := map_add_le_add _ s t
      norm_eq_zero_iff s := finiteAtlasSeminorm_eq_zero_iff e U hU
        (TauCeti.extChartAt_cover_of_interior_cover hK) k le_rfl s }
    ((withSeminorms_finiteAtlasSeminorm k e U hU hK).topologicalSpace_eq_iInf.trans ciInf_unique)

/-- The normed space structure on `C^k` bundle sections for a covering finite chart-frame atlas. -/
@[instance_reducible]
def finiteAtlasNormedSpace :
    letI := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
    NormedSpace 𝕜 Cₛ^k⟮I; F, V⟯ :=
  letI := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
  { norm_smul_le a s := (map_smul_eq_mul (finiteAtlasSeminorm e U hU c K k le_rfl) a s).le }

/-- The norm in `ContMDiffSection.finiteAtlasNormedAddCommGroup` is the finite-atlas `C^k`
seminorm. -/
theorem norm_finiteAtlas (s : Cₛ^k⟮I; F, V⟯) :
    letI := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
    ‖s‖ = finiteAtlasSeminorm e U hU c K k le_rfl s :=
  (rfl)

/-- The distance in `ContMDiffSection.finiteAtlasNormedAddCommGroup` is the finite-atlas `C^k`
seminorm of the difference. -/
theorem dist_finiteAtlas (s t : Cₛ^k⟮I; F, V⟯) :
    letI := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
    dist s t = finiteAtlasSeminorm e U hU c K k le_rfl (s - t) := by
  let _ := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
  exact dist_eq_norm s t

/-- The topology underlying `ContMDiffSection.finiteAtlasNormedAddCommGroup` is
`ContMDiffSection.frameTopology e U hU`. -/
@[simp]
theorem topologicalSpace_finiteAtlasNormedAddCommGroup :
    (finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK).toUniformSpace.toTopologicalSpace =
      frameTopology (I := I) (n := k) e U hU :=
  (rfl)

/-- **Completeness of `C^k` sections in the finite-atlas norm.** On a manifold over `ℝ` or `ℂ`
(including manifolds with boundary or corners), `C^k` sections of a bundle with complete model fibre
form a Banach space for any covering finite chart-frame norm. -/
theorem completeSpace_finiteAtlas [IsRCLikeNormedField 𝕜] [CompleteSpace F] :
    letI := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
    CompleteSpace Cₛ^k⟮I; F, V⟯ := by
  let _ := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
  rcases isEmpty_or_nonempty M with _ | _
  · infer_instance
  · have : LocallyCompactSpace E := I.locallyCompactSpace_of_extChartAt_interior_cover hK
    have htop : (PseudoMetricSpace.toUniformSpace : UniformSpace Cₛ^k⟮I; F, V⟯).toTopologicalSpace =
        (frameUniformSpace (I := I) (n := k) e U hU).toTopologicalSpace :=
      (topologicalSpace_finiteAtlasNormedAddCommGroup k e U hU hK).trans
        (frameUniformSpace_toTopologicalSpace (I := I) (n := k) e U hU).symm
    have e_unif : (PseudoMetricSpace.toUniformSpace : UniformSpace Cₛ^k⟮I; F, V⟯) =
        frameUniformSpace (I := I) (n := k) e U hU :=
      IsUniformAddGroup.ext inferInstance
        (isUniformAddGroup_frameUniformSpace (I := I) (n := k) e U hU) (by rw [htop])
    rw [e_unif]
    exact completeSpace_frameTopology (I := I) (n := k) e U hU
      (TauCeti.cover_of_extChartAt_cover hK)

end Topology

section SmoothTopology

variable [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]
  (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt I (c i)).target}
  (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
    ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
      (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
        (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

include hK

/-- **The finite-atlas `C^k` norms generate the `C^∞` section topology.** When the relative
interiors of the compact pieces cover `M`, the countable sequence of finite-atlas `C^k` seminorms
(`k : ℕ`) generates `ContMDiffSection.frameTopology` on smooth sections, including on manifolds with
boundary and corners. -/
theorem withSeminorms_finiteAtlasSeminorm_infty :
    letI := frameTopology (I := I) (n := ∞) e U hU
    WithSeminorms (fun k : ℕ ↦ finiteAtlasSeminorm (n := ∞) e U hU c K k (by simp)) := by
  let _ := frameTopology (I := I) (n := ∞) e U hU
  exact (withSeminorms_finiteAtlasSeminorm_subtype (n := ∞) e U hU hK).congr_equiv
    (Equiv.subtypeUnivEquiv fun k : ℕ ↦ (by simp : (k : ℕ∞ω) ≤ ∞)).symm

/-- The countable sequence of `C^k` norms of any finite chart-frame atlas with covering relative
interiors generates `ContMDiffSection.frameTopology` on smooth sections for *any* covering smooth
frame system. -/
theorem withSeminorms_finiteAtlasSeminorm_infty_of_cover
    {κ : Type*} (e' : κ → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (hcover' : ∀ y : M, ∃ j, y ∈ U' j) :
    letI := frameTopology (I := I) (n := ∞) e' U' hU'
    WithSeminorms (fun k : ℕ ↦ finiteAtlasSeminorm (n := ∞) e U hU c K k (by simp)) := by
  let _ := frameTopology (I := I) (n := ∞) e' U' hU'
  exact (withSeminorms_finiteAtlasSeminorm_subtype_of_cover (n := ∞) e U hU hK e' U' hU'
    hcover').congr_equiv (Equiv.subtypeUnivEquiv fun k : ℕ ↦ (by simp : (k : ℕ∞ω) ≤ ∞)).symm

end SmoothTopology

section CompactBase

variable (k : ℕ) [ContMDiffVectorBundle k F V I] [IsManifold I k M]
  {κ : Type*} (e : κ → Trivialization F (π F V)) [∀ j, MemTrivializationAtlas (e j)]
  (U : κ → Opens M) (hU : ∀ j, (U j : Set M) ⊆ (e j).baseSet)

/-- **Normability of `C^k` bundle sections on a compact manifold.** On a compact manifold modelled
on a locally compact space, `ContMDiffSection.frameTopology` on `C^k` sections is generated by a
single seminorm for every covering smooth frame system, including on manifolds with boundary and
corners. -/
theorem isNormableSpace_frameTopology_of_compactSpace [CompactSpace M] [LocallyCompactSpace H]
    (hcover : ∀ y : M, ∃ j, y ∈ U j) :
    letI := frameTopology (I := I) (n := k) e U hU
    IsNormableSpace 𝕜 Cₛ^k⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := k) e U hU
  obtain ⟨N, r, c, K, hK⟩ :=
    TauCeti.exists_finite_compact_chart_cover_of_opens_cover (I := I) U hcover
  exact ⟨⟨_, withSeminorms_finiteAtlasSeminorm_of_cover k
    (fun i ↦ e (r i)) (fun i ↦ U (r i)) (fun i ↦ hU (r i)) hK e U hU hcover⟩⟩

end CompactBase

end ContMDiffSection
