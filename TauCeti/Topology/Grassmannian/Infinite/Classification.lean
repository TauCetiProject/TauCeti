/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Infinite.Tautological
public import TauCeti.Topology.VectorBundle.Core.Hom
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance
public import TauCeti.Topology.VectorBundle.WeightedCoordinates
public import Mathlib.CategoryTheory.IsomorphismClasses
import TauCeti.Topology.FiberBundle.Pullback
import Mathlib.Data.Nat.Pairing

/-!
# Universal vector bundle classification over paracompact bases

Over `ℝ` or `ℂ` (more generally any `RCLike 𝕜`), homotopy classes of continuous maps from a
paracompact `R₁` space `X` (in particular any paracompact Hausdorff space) to the infinite
Grassmannian `TauCeti.infiniteGrassmannian 𝕜 k` classify rank-`k` `𝕜`-vector bundles over `X` up to
isomorphism, via pullback of the universal tautological bundle
`TauCeti.infiniteGrassmannian.Tautological 𝕜 k`.

The argument factors cleanly into four stages, each stated at its natural generality:

* **Classifying coordinates (`TauCeti.IsClassifyingCoordinates`).** Over any nontrivially normed
  field `𝕜` and any topological space `X`, a family of fibrewise linear injections
  `j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)` whose coordinates are continuous on `TotalSpace F E` and locally
  supported in a fixed initial segment `Finset.range N` determines a continuous classifying map
  `IsClassifyingCoordinates.classifyContinuousMap : C(X, infiniteGrassmannian 𝕜 k)` sending `x` to
  `LinearMap.range (j x)`. Over a complete scalar field, `classifyTautologicalHomeomorph` identifies
  `E` with `(classifyContinuousMap : _ → _) *ᵖ (Tautological 𝕜 k)`.
* **Existence over paracompact normal bases (`TauCeti.exists_isClassifyingCoordinates`).** Over any
  complete nontrivially normed `ℝ`-algebra field `𝕜`, a countable locally finite trivializing family
  (`TauCeti.exists_countable_locallyFinite_trivialization`) and a subordinate partition of unity
  produce classifying coordinates after flattening `ℕ →₀ (Fin k → 𝕜)` into `ℕ →₀ 𝕜` along
  `Nat.pair` (`TauCeti.flattenFinsupp`). We also bridge `PartitionOfUnity.weightedFrameCoordinates`
  for Riemannian and Hermitian bundles (`IsClassifyingCoordinates.of_weightedFrameCoordinates`).
* **Even/odd coordinate shifts and homotopy uniqueness.** For any strictly monotone `s : ℕ → ℕ`,
  linear interpolation `t ↦ (1 - t) • id + t • lmapDomain s` is fibrewise injective at every time,
  and stagewise descent from `Σ n, finiteGrassmannian 𝕜 k n` along `isQuotientMap_sigmaToInfinite`
  shows `id` is homotopic to `mapContinuousMap (lmapDomain s) _`
  (`homotopic_id_mapContinuousMap_lmapDomain`). Interleaving any two classifying coordinate families
  into even and odd coordinates (`2 * m` and `2 * m + 1`) shows their classifying maps are
  homotopic (`IsClassifyingCoordinates.homotopic_classifyContinuousMap`), and comparing stagewise
  with `Tautological.subtype` proves that any classifying map of `Tautological 𝕜 k` itself is
  homotopic to the identity (`homotopic_id_classifyContinuousMap_tautological`). Over `RCLike 𝕜`
  (where `infiniteGrassmannian 𝕜 k` is paracompact normal), any two maps over an arbitrary base `X`
  with isomorphic tautological pullbacks are therefore homotopic (`homotopic_of_pullback_equiv`).
* **Small isomorphism-class bijection (`TauCeti.infiniteGrassmannian.classificationEquiv`).**
  Combining homotopy uniqueness with `ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`
  and the small coordinate category `TauCeti.FiniteRankBundleCore 𝕜 X` yields a natural bijection
  between `[X, infiniteGrassmannian 𝕜 k]` and isomorphism classes of rank-`k` vector bundles over
  `X`, handling degenerate cases (`X = Empty`, `k = 0`) without side conditions.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, §5, Theorem 5.6 and Lemma 5.9.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.16.
-/

public noncomputable section

open Bundle Set Function Filter CategoryTheory
open _root_.Finsupp
open scoped Topology unitInterval

namespace TauCeti

section FlattenFinsupp

/-- Flatten finitely supported sequences of `k`-tuples `ℕ →₀ (Fin k → 𝕜)` into `ℕ →₀ 𝕜` via
Cantor pairing `Nat.pair` / `Nat.unpair`. -/
def flattenFinsupp (𝕜 : Type*) [Semiring 𝕜] (k : ℕ) :
    (ℕ →₀ (Fin k → 𝕜)) →ₗ[𝕜] (ℕ →₀ 𝕜) where
  toFun f := Finsupp.ofSupportFinite
    (fun m ↦ if h : m.unpair.2 < k then f m.unpair.1 ⟨m.unpair.2, h⟩ else 0) <| by
      refine ((f.support ×ˢ Finset.range k).finite_toSet.image
        (fun p : ℕ × ℕ ↦ Nat.pair p.1 p.2)).subset fun m hm ↦ ?_
      simp only [mem_support, ne_eq] at hm
      split_ifs at hm with hk
      · refine ⟨(m.unpair.1, m.unpair.2), ?_, Nat.pair_unpair m⟩
        simp only [Finset.coe_product, Finset.coe_range, mem_prod, Finset.mem_coe,
          Finsupp.mem_support_iff, mem_Iio]
        exact ⟨fun h0 ↦ hm (by simp [h0]), hk⟩
      · exact (hm rfl).elim
  map_add' f g := by
    ext m
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.coe_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    ext m
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    split_ifs <;> simp

@[simp]
theorem flattenFinsupp_apply {𝕜 : Type*} [Semiring 𝕜] (k : ℕ)
    (f : ℕ →₀ (Fin k → 𝕜)) (m : ℕ) :
    flattenFinsupp 𝕜 k f m = if h : m.unpair.2 < k then f m.unpair.1 ⟨m.unpair.2, h⟩ else 0 :=
  (rfl)

theorem flattenFinsupp_apply_pair {𝕜 : Type*} [Semiring 𝕜] (k : ℕ)
    (f : ℕ →₀ (Fin k → 𝕜)) (n : ℕ) (i : Fin k) :
    flattenFinsupp 𝕜 k f (Nat.pair n i.1) = f n i := by
  simp [flattenFinsupp_apply, Nat.unpair_pair, i.2]

/-- Flattening `ℕ →₀ (Fin k → 𝕜)` into `ℕ →₀ 𝕜` is injective for every `k : ℕ`, including
`k = 0`. -/
theorem flattenFinsupp_injective (𝕜 : Type*) [Semiring 𝕜] (k : ℕ) :
    Injective (flattenFinsupp 𝕜 k) := by
  intro f g hfg
  ext n i
  simpa only [flattenFinsupp_apply_pair] using
    congrArg (fun w : ℕ →₀ 𝕜 ↦ w (Nat.pair n i.1)) hfg

/-- If `f` is supported in the first `N` blocks, `flattenFinsupp 𝕜 k f` is supported below
`(max N k) ^ 2`. -/
theorem support_flattenFinsupp_subset_range {𝕜 : Type*} [Semiring 𝕜] {k N : ℕ}
    {f : ℕ →₀ (Fin k → 𝕜)} (hf : f.support ⊆ Finset.range N) :
    (flattenFinsupp 𝕜 k f).support ⊆ Finset.range (max N k ^ 2) := by
  intro m hm
  rw [Finsupp.mem_support_iff, flattenFinsupp_apply] at hm
  split_ifs at hm with hk
  · have hn : m.unpair.1 < N := Finset.mem_range.1 <| hf <|
      Finsupp.mem_support_iff.2 fun h0 ↦ hm (by simp [h0])
    have hmax : max m.unpair.1 m.unpair.2 + 1 ≤ max N k :=
      Nat.succ_le_of_lt (max_lt (hn.trans_le (le_max_left N k)) (hk.trans_le (le_max_right N k)))
    rw [Finset.mem_range, ← Nat.pair_unpair m]
    exact (Nat.pair_lt_max_add_one_sq _ _).trans_le (Nat.pow_le_pow_left hmax 2)
  · exact (hm rfl).elim

end FlattenFinsupp

section CoordinateInclusionSupport

/-- A finitely supported sequence whose support lies in `Finset.range N` is recovered by restricting
to `Fin N` and applying `coordinateInclusion N`. -/
theorem coordinateInclusion_of_support_subset_range {𝕜 : Type*} [Semiring 𝕜] {N : ℕ}
    {v : ℕ →₀ 𝕜} (hv : v.support ⊆ Finset.range N) :
    coordinateInclusion (R := 𝕜) N (fun i : Fin N ↦ v i.1) = v := by
  ext m
  by_cases hm : m < N
  · exact coordinateInclusion_apply_val (fun i : Fin N ↦ v i.1) ⟨m, hm⟩
  · rw [coordinateInclusion_apply_of_le _ (Nat.le_of_not_gt hm)]
    symm
    exact Finsupp.notMem_support_iff.1 fun hmem ↦ hm (Finset.mem_range.1 (hv hmem))

end CoordinateInclusionSupport

section ClassifyingCoordinates

/-- A family of fibrewise linear maps `j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)` forms **classifying
coordinates** for a bundle `E` with model `F` when each ambient coordinate is continuous on the
total space, the supports are locally contained in a fixed finite initial segment of `ℕ`, and each
`j x` is injective. -/
structure IsClassifyingCoordinates (𝕜 : Type*) [Field 𝕜] [TopologicalSpace 𝕜]
    {X : Type*} [TopologicalSpace X] (F : Type*) [TopologicalSpace F]
    (E : X → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    (j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)) : Prop where
  /-- Every ambient coordinate is continuous on the total space. -/
  continuous_coord : ∀ m : ℕ, Continuous fun p : TotalSpace F E ↦ j p.proj p.2 m
  /-- Locally on the base, all fibre vectors have coordinates supported in a fixed `range N`. -/
  locally_supported : ∀ x : X, ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ v : E y,
    (j y v).support ⊆ Finset.range N
  /-- On every fibre, the coordinate map is injective. -/
  injective : ∀ x : X, Injective (j x)

namespace IsClassifyingCoordinates

section Operations

variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  {E' : X → Type*} [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜 (E' x)]
  [TopologicalSpace (TotalSpace G E')]
  {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)}

omit [IsTopologicalSemiring 𝕜] in
/-- Pulling back classifying coordinates along `f : C(Y, X)` yields classifying coordinates on
`(f : Y → X) *ᵖ E`. -/
theorem pullback (hj : IsClassifyingCoordinates 𝕜 F E j) (f : C(Y, X)) :
    IsClassifyingCoordinates 𝕜 F ((f : Y → X) *ᵖ E) (fun y ↦ j (f y)) where
  continuous_coord m :=
    (hj.continuous_coord m).comp (Pullback.continuous_lift F E (f : Y → X))
  locally_supported y := by
    obtain ⟨N, hN⟩ := hj.locally_supported (f y)
    exact ⟨N, f.continuous.continuousAt.preimage_mem_nhds hN⟩
  injective y := hj.injective (f y)

omit [IsTopologicalSemiring 𝕜] in
/-- Precomposing classifying coordinates with a continuous family of fibrewise linear injections
preserves `IsClassifyingCoordinates`. -/
theorem compLinearMap (hj : IsClassifyingCoordinates 𝕜 F E j)
    (Φ : ∀ x, E' x →ₗ[𝕜] E x) (hΦ_inj : ∀ x, Injective (Φ x))
    (hΦ_cont : Continuous fun p : TotalSpace G E' ↦
      TotalSpace.mk' F (E := E) p.proj (Φ p.proj p.2)) :
    IsClassifyingCoordinates 𝕜 G E' (fun x ↦ (j x).comp (Φ x)) where
  continuous_coord m := (hj.continuous_coord m).comp hΦ_cont
  locally_supported x := by
    obtain ⟨N, hN⟩ := hj.locally_supported x
    exact ⟨N, hN.mono fun y hy v ↦ hy (Φ y v)⟩
  injective x := (hj.injective x).comp (hΦ_inj x)

/-- Postcomposing classifying coordinates with *any* injective `𝕜`-linear map
`φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)` yields classifying coordinates, with no continuity assumption on
`φ`: locally `j` lands in a finite coordinate stage where `φ` is automatically continuous. -/
theorem postcomp (hj : IsClassifyingCoordinates 𝕜 F E j) (hπ : Continuous (π F E))
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) :
    IsClassifyingCoordinates 𝕜 F E (fun x ↦ φ.comp (j x)) where
  continuous_coord m := by
    refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
    obtain ⟨N, hN⟩ := hj.locally_supported p₀.proj
    have hlin : Continuous ((Finsupp.lapply (R := 𝕜) (M := 𝕜) m).comp
        (φ.comp (coordinateInclusion N))) :=
      LinearMap.continuous_on_pi _
    have hcoord : Continuous (fun q : TotalSpace F E ↦ fun r : Fin N ↦ j q.proj q.2 r.1) :=
      continuous_pi fun r ↦ hj.continuous_coord r.1
    refine (hlin.comp hcoord).continuousAt.congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt.preimage_mem_nhds hN] with q hq
    dsimp only [Function.comp_def, LinearMap.comp_apply, Finsupp.lapply_apply]
    rw [coordinateInclusion_of_support_subset_range (hq q.2)]
  locally_supported x := by
    obtain ⟨N, hN⟩ := hj.locally_supported x
    have hfg : ((⊤ : Submodule 𝕜 (Fin N → 𝕜)).map (φ.comp (coordinateInclusion N))).FG :=
      (Module.Finite.iff_fg.1 inferInstance).map _
    obtain ⟨M, hM⟩ := hfg.exists_le_supported_Iio
    refine ⟨M, hN.mono fun y hy v r hr ↦ Finset.mem_range.2 ?_⟩
    rw [LinearMap.comp_apply, ← coordinateInclusion_of_support_subset_range (hy v)] at hr
    exact hM ⟨fun i : Fin N ↦ j y v i.1, trivial, rfl⟩ hr
  injective x := hφ.comp (hj.injective x)

end Operations

section Classify

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}

/-- The image `LinearMap.range (j x)` of classifying coordinates has cardinal rank `k`. -/
theorem rank_range_eq (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) :
    Module.rank 𝕜 (LinearMap.range (j x)) = k := by
  let e : F ≃ₗ[𝕜] LinearMap.range (j x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F E x).symm.toLinearEquiv.trans
      (LinearEquiv.ofInjective (j x) (hj.injective x))
  have : Module.Finite 𝕜 (LinearMap.range (j x)) := Module.Finite.equiv e
  exact (Module.finrank_eq_rank 𝕜 (LinearMap.range (j x))).symm.trans
    (congrArg Nat.cast (e.symm.finrank_eq.trans hk))

/-- Classifying coordinates send each base point `x` to the `k`-dimensional subspace
`LinearMap.range (j x)` in `infiniteGrassmannian 𝕜 k`. -/
@[expose] def classify (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) : infiniteGrassmannian 𝕜 k :=
  ⟨LinearMap.range (j x), hj.rank_range_eq hk x⟩

@[simp]
theorem coe_classify (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) :
    (hj.classify hk x).1 = LinearMap.range (j x) := (rfl)

/-- Helper: on a chart domain where `j` is supported below `N`, the coordinates of a transformed
basis form a full-rank frame in `Fin N → 𝕜` spanning `hj.classify hk y`. -/
private theorem frameSpan_localFrame_eq (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (b : Module.Basis (Fin k) 𝕜 F) {N : ℕ} {y : X} (hy : y ∈ e.baseSet)
    (hsupp : ∀ v : E y, (j y v).support ⊆ Finset.range N) :
    ∃ hlin : LinearIndependent 𝕜 (fun (i : Fin k) (r : Fin N) ↦ j y (e.symm y (b i)) r.1),
      finiteGrassmannian.toInfinite
        (finiteGrassmannian.frameSpan ⟨_, hlin⟩) = hj.classify hk y := by
  let f : Fin k → Fin N → 𝕜 := fun i r ↦ j y (e.symm y (b i)) r.1
  let L : F →ₗ[𝕜] (ℕ →₀ 𝕜) := (j y).comp (e.linearEquivAt 𝕜 y hy).symm.toLinearMap
  have hL : Injective L := (hj.injective y).comp (e.linearEquivAt 𝕜 y hy).symm.injective
  have hinc (i : Fin k) : coordinateInclusion (R := 𝕜) N (f i) = L (b i) :=
    coordinateInclusion_of_support_subset_range (hsupp _)
  have hlin : LinearIndependent 𝕜 f := by
    refine Fintype.linearIndependent_iff.2 fun g hg ↦ ?_
    have h0 : L (∑ i, g i • b i) = L 0 := by
      rw [map_sum, map_zero]
      ext m
      rw [Finsupp.zero_apply]
      change Finsupp.applyAddHom m (∑ i, L (g i • b i)) = 0
      rw [map_sum]
      by_cases hm : m < N
      · have hfm (i : Fin k) : f i ⟨m, hm⟩ = L (b i) m :=
          (coordinateInclusion_apply_val (f i) ⟨m, hm⟩).symm.trans
            (congrArg (fun v : ℕ →₀ 𝕜 ↦ v m) (hinc i))
        have eval_m := congrArg (fun u : Fin N → 𝕜 ↦ u ⟨m, hm⟩) hg
        simp only [Finsupp.applyAddHom_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, ← hfm]
        simpa using eval_m
      · refine Finset.sum_eq_zero fun i _ ↦ ?_
        rw [Finsupp.applyAddHom_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact mul_eq_zero_of_right _
          (Finsupp.notMem_support_iff.1 fun hmem ↦ hm (Finset.mem_range.1 (hsupp _ hmem)))
    exact Fintype.linearIndependent_iff.1 b.linearIndependent g (hL h0)
  have hcomp : coordinateInclusion (R := 𝕜) N ∘ f = L ∘ b := funext hinc
  refine ⟨hlin, Subtype.ext ?_⟩
  rw [finiteGrassmannian.coe_toInfinite, finiteGrassmannian.coe_frameSpan, coe_classify,
    Submodule.map_span, ← range_comp]
  change Submodule.span 𝕜 (range (coordinateInclusion (R := 𝕜) N ∘ f)) = _
  rw [hcomp, range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The classifying map of `IsClassifyingCoordinates` is continuous into the direct-limit topology
of `infiniteGrassmannian 𝕜 k`. -/
@[fun_prop]
theorem continuous_classify (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) :
    Continuous (hj.classify hk) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  let e := trivializationAt F E x₀
  let b := Module.finBasisOfFinrankEq 𝕜 F hk
  obtain ⟨N, hN⟩ := hj.locally_supported x₀
  obtain ⟨U, hU_sub, hU_open, hx₀U⟩ := mem_nhds_iff.1
    (Filter.inter_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E x₀)) hN)
  let raw : U → Fin k → Fin N → 𝕜 := fun z i r ↦ j z.1 (e.symm z.1 (b i)) r.1
  have hraw : Continuous raw := by
    refine continuous_pi fun i ↦ continuous_pi fun r ↦ continuous_iff_continuousAt.2 fun z ↦ ?_
    have hz : (z.1, b i) ∈ e.baseSet ×ˢ (univ : Set F) := ⟨(hU_sub z.2).1, mem_univ _⟩
    have hpair : Continuous (fun u : U ↦ (u.1, b i)) :=
      continuous_subtype_val.prodMk continuous_const
    have hsec : ContinuousAt (fun u : U ↦ TotalSpace.mk' F u.1 (e.symm u.1 (b i))) z :=
      ContinuousAt.comp (f := fun u : U ↦ (u.1, b i))
        (e.continuousOn_symm.continuousAt
          ((e.open_baseSet.prod isOpen_univ).mem_nhds hz)) hpair.continuousAt
    exact (hj.continuous_coord r.1).continuousAt.comp hsec
  have hspec (z : U) :=
    hj.frameSpan_localFrame_eq hk e b (hU_sub z.2).1 (hU_sub z.2).2
  let frameMap : U → finiteFullRankFrame 𝕜 k N := fun z ↦ ⟨raw z, (hspec z).1⟩
  have hframe : Continuous (finiteGrassmannian.toInfinite ∘
      finiteGrassmannian.frameSpan ∘ frameMap) :=
    finiteGrassmannian.continuous_toInfinite.comp
      (finiteGrassmannian.continuous_frameSpan.comp (hraw.subtype_mk _))
  have hon : ContinuousOn (hj.classify hk) U :=
    continuousOn_iff_continuous_domRestrict.2 <| hframe.congr fun z ↦ (hspec z).2
  exact hon.continuousAt (hU_open.mem_nhds hx₀U)

/-- The classifying map bundled as `C(X, infiniteGrassmannian 𝕜 k)`. -/
@[expose] def classifyContinuousMap (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) : C(X, infiniteGrassmannian 𝕜 k) :=
  ⟨hj.classify hk, hj.continuous_classify hk⟩

@[simp]
theorem classifyContinuousMap_apply (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) :
    hj.classifyContinuousMap hk x = hj.classify hk x := (rfl)

@[simp]
theorem classifyContinuousMap_pullback {Y : Type*} [TopologicalSpace Y]
    (hj : IsClassifyingCoordinates 𝕜 F E j) (f : C(Y, X)) (hk : Module.finrank 𝕜 F = k) :
    (hj.pullback f).classifyContinuousMap hk = (hj.classifyContinuousMap hk).comp f :=
  ContinuousMap.ext fun _ ↦ rfl

/-- Precomposing classifying coordinates with a continuous family of fibrewise linear *equivalences*
leaves the classifying map strictly unchanged. -/
theorem classifyContinuousMap_compLinearEquiv
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {E' : X → Type*} [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜 (E' x)]
    [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G E')]
    [FiberBundle G E'] [VectorBundle 𝕜 G E']
    (hj : IsClassifyingCoordinates 𝕜 F E j)
    (Φ : ∀ x, E' x ≃ₗ[𝕜] E x)
    (hΦ_cont : Continuous fun p : TotalSpace G E' ↦
      TotalSpace.mk' F (E := E) p.proj (Φ p.proj p.2))
    (hk : Module.finrank 𝕜 F = k) (hk' : Module.finrank 𝕜 G = k) :
    (hj.compLinearMap (E' := E') (fun x ↦ (Φ x).toLinearMap) (fun x ↦ (Φ x).injective)
      hΦ_cont).classifyContinuousMap hk' = hj.classifyContinuousMap hk := by
  ext1 x
  apply Subtype.ext
  rw [classifyContinuousMap_apply, classifyContinuousMap_apply, coe_classify, coe_classify,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range (Φ x))]

@[simp]
theorem classifyContinuousMap_postcomp (hj : IsClassifyingCoordinates 𝕜 F E j)
    (φ : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜)) (hφ : Injective φ) (hk : Module.finrank 𝕜 F = k) :
    (hj.postcomp (FiberBundle.continuous_proj F E) φ hφ).classifyContinuousMap hk =
      (infiniteGrassmannian.mapContinuousMap φ hφ).comp (hj.classifyContinuousMap hk) := by
  ext1 x
  apply Subtype.ext
  simp [LinearMap.range_comp]

/-- Over a complete scalar field, `j x` identifies each fibre `E x` continuously and linearly with
the tautological fibre over `hj.classify hk x`, without requiring `T2Space` or topological-group
assumptions on `E x`. -/
def classifyTautologicalEquiv [CompleteSpace 𝕜] (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) :
    E x ≃L[𝕜] infiniteGrassmannian.Tautological 𝕜 k (hj.classify hk x) :=
  let e₁ := VectorBundle.continuousLinearEquivAt 𝕜 F E x
  let e₂ : F ≃ₗ[𝕜] infiniteGrassmannian.Tautological 𝕜 k (hj.classify hk x) :=
    e₁.symm.toLinearEquiv.trans
      ((LinearEquiv.ofInjective (j x) (hj.injective x)).trans
        (infiniteGrassmannian.tautologicalEquiv 𝕜 k (hj.classify hk x)).symm)
  e₁.trans e₂.toContinuousLinearEquiv

@[simp]
theorem val_classifyTautologicalEquiv [CompleteSpace 𝕜] (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) (x : X) (v : E x) :
    (hj.classifyTautologicalEquiv hk x v).val = j x v := by
  let e₁ := VectorBundle.continuousLinearEquivAt 𝕜 F E x
  let w : (hj.classify hk x).1 := LinearEquiv.ofInjective (j x) (hj.injective x) (e₁.symm (e₁ v))
  have hw : (hj.classifyTautologicalEquiv hk x v).val = w.1 :=
    infiniteGrassmannian.val_tautologicalEquiv_symm (hj.classify hk x) w
  exact hw.trans <|
    (LinearEquiv.ofInjective_apply (f := j x) (h := hj.injective x) (e₁.symm (e₁ v))).trans
      (congrArg (j x) (e₁.symm_apply_apply v))

end Classify

section ClassifyHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [TopologicalSpace X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}

/-- Over a complete scalar field, `hj.classifyTautologicalEquiv` glues to a bundle homeomorphism
from `TotalSpace F E` to the pullback of `infiniteGrassmannian.Tautological 𝕜 k` along
`hj.classifyContinuousMap hk`. -/
def classifyTautologicalHomeomorph (hj : IsClassifyingCoordinates 𝕜 F E j)
    (hk : Module.finrank 𝕜 F = k) :
    TotalSpace F E ≃ₜ
      TotalSpace (Fin k → 𝕜)
        ((hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k)) :=
  bundleHomeomorph (𝕜 := 𝕜) (F₁ := F) (F₂ := Fin k → 𝕜) (E₁ := E)
    (E₂ := (hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k))
    (hj.classifyTautologicalEquiv hk) <|
      Bundle.Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj F E, by
        refine infiniteGrassmannian.continuous_totalSpace_iff.2
          ⟨(hj.classifyContinuousMap hk).continuous.comp (FiberBundle.continuous_proj F E),
            fun m ↦ ?_⟩
        refine (hj.continuous_coord m).congr fun p ↦ ?_
        rw [← hj.val_classifyTautologicalEquiv hk p.proj p.2]
        rfl⟩

@[simp]
theorem classifyTautologicalHomeomorph_apply
    (hj : IsClassifyingCoordinates 𝕜 F E j) (hk : Module.finrank 𝕜 F = k)
    (p : TotalSpace F E) :
    hj.classifyTautologicalHomeomorph hk p =
      TotalSpace.mk' (Fin k → 𝕜) p.proj (hj.classifyTautologicalEquiv hk p.proj p.2) :=
  bundleHomeomorph_apply (𝕜 := 𝕜) (F₁ := F) (F₂ := Fin k → 𝕜) (E₁ := E)
    (E₂ := (hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k))
    (hj.classifyTautologicalEquiv hk) _ p

@[simp]
theorem classifyTautologicalHomeomorph_symm_apply
    (hj : IsClassifyingCoordinates 𝕜 F E j) (hk : Module.finrank 𝕜 F = k)
    (p : TotalSpace (Fin k → 𝕜)
      ((hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k))) :
    (hj.classifyTautologicalHomeomorph hk).symm p =
      TotalSpace.mk' F p.proj ((hj.classifyTautologicalEquiv hk p.proj).symm p.2) :=
  bundleHomeomorph_symm_apply (𝕜 := 𝕜) (F₁ := F) (F₂ := Fin k → 𝕜) (E₁ := E)
    (E₂ := (hj.classifyContinuousMap hk : _ → _) *ᵖ (infiniteGrassmannian.Tautological 𝕜 k))
    (hj.classifyTautologicalEquiv hk) _ p

end ClassifyHomeomorph

end IsClassifyingCoordinates

end ClassifyingCoordinates

section Existence

/-- Block coordinates associated to a countable family of linear trivializations, a subordinate
partition of unity, and a finite basis of the model fibre `F`. -/
private def partitionBlockCoordinates {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : X → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    (ρ : PartitionOfUnity ℕ X univ) (e : ℕ → Trivialization F (π F E)) [∀ n, (e n).IsLinear 𝕜]
    {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (x : X) :
    E x →ₗ[𝕜] (ℕ →₀ (Fin r → 𝕜)) where
  toFun v := Finsupp.ofSupportFinite
    (fun n ↦ (algebraMap ℝ 𝕜 (ρ n x)) • b.equivFun ((e n).linearMapAt 𝕜 x v))
    ((ρ.locallyFinite.point_finite x).subset fun n hn ↦ by
      contrapose hn
      have hz : ρ n x = 0 := by simpa only [mem_ofPred_eq, mem_support, not_not] using hn
      simp [hz])
  map_add' v w := by
    ext n i
    simp [smul_add]
  map_smul' c v := by
    ext n i
    simp only [Finsupp.ofSupportFinite_coe, LinearMap.map_smul, LinearEquiv.map_smul,
      Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

@[simp]
private theorem partitionBlockCoordinates_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : X → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    (ρ : PartitionOfUnity ℕ X univ) (e : ℕ → Trivialization F (π F E)) [∀ n, (e n).IsLinear 𝕜]
    {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (x : X) (v : E x) (n : ℕ) :
    partitionBlockCoordinates ρ e b x v n =
      (algebraMap ℝ 𝕜 (ρ n x)) • b.equivFun ((e n).linearMapAt 𝕜 x v) := (rfl)

private theorem continuous_partitionBlockCoordinates_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAlgebra ℝ 𝕜]
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    (ρ : PartitionOfUnity ℕ X univ) (e : ℕ → Trivialization F (π F E)) [∀ n, (e n).IsLinear 𝕜]
    (hρ : ρ.IsSubordinate fun n ↦ (e n).baseSet)
    {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (n : ℕ) (i : Fin r) :
    Continuous fun p : TotalSpace F E ↦
      partitionBlockCoordinates ρ e b p.proj p.2 n i := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  by_cases hp : p.proj ∈ tsupport (ρ n)
  · have hb_mem : p.proj ∈ (e n).baseSet := hρ n hp
    have hsrc : p ∈ (e n).source := (e n).mem_source.2 hb_mem
    have hw : Continuous (fun q : TotalSpace F E ↦ algebraMap ℝ 𝕜 (ρ n q.proj)) :=
      (continuous_algebraMap ℝ 𝕜).comp ((ρ n).continuous.comp (FiberBundle.continuous_proj F E))
    have hlin : Continuous (fun w : F ↦ b.equivFun w i) :=
      (continuous_apply i).comp b.equivFun.toLinearMap.continuous_of_finiteDimensional
    have htriv : ContinuousAt (fun q : TotalSpace F E ↦ b.equivFun ((e n) q).2 i) p :=
      hlin.continuousAt.comp
        (((e n).continuousOn.continuousAt ((e n).open_source.mem_nhds hsrc)).snd)
    refine (hw.continuousAt.mul htriv).congr_of_eventuallyEq ?_
    filter_upwards [(e n).open_source.mem_nhds hsrc] with q hq
    have hq_base : q.proj ∈ (e n).baseSet := (e n).mem_source.1 hq
    simp only [partitionBlockCoordinates_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
      (e n).coe_linearMapAt_of_mem hq_base]
  · refine (continuousAt_const (y := (0 : 𝕜))).congr_of_eventuallyEq ?_
    have hzero : ρ n =ᶠ[𝓝 p.proj] 0 := notMem_tsupport_iff_eventuallyEq.1 hp
    filter_upwards [(FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds hzero]
      with q hq
    have hq0 : ρ n q.proj = 0 := hq
    simp [hq0]

/-- Every finite-rank vector bundle over a paracompact normal base (in particular any paracompact
Hausdorff base) over a complete nontrivially normed `ℝ`-algebra field admits
`IsClassifyingCoordinates`. -/
theorem exists_isClassifyingCoordinates
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAlgebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X] [ParacompactSpace X] [NormalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] :
    ∃ j : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜), IsClassifyingCoordinates 𝕜 F E j := by
  obtain ⟨e, he_lin, he_cov, -⟩ :=
    exists_countable_locallyFinite_trivialization 𝕜 (B := X) (F := F) (E := E)
  have := he_lin
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun n ↦ (e n).baseSet) (fun n ↦ (e n).open_baseSet)
    (fun x _ ↦ he_cov.ge (mem_univ x))
  let b := Module.finBasis 𝕜 F
  let j₀ := partitionBlockCoordinates ρ e b
  refine ⟨fun x ↦ (flattenFinsupp 𝕜 (Module.finrank 𝕜 F)).comp (j₀ x), ⟨?_, ?_, ?_⟩⟩
  · intro m
    by_cases hk : m.unpair.2 < Module.finrank 𝕜 F
    · refine (continuous_partitionBlockCoordinates_apply ρ e hρ b
        m.unpair.1 ⟨m.unpair.2, hk⟩).congr fun p ↦ ?_
      simp [j₀, flattenFinsupp_apply, hk]
    · refine (continuous_const (y := (0 : 𝕜))).congr fun p ↦ ?_
      simp [flattenFinsupp_apply, hk]
  · intro x
    classical
    let N := (ρ.fintsupport x).sup id + 1
    refine ⟨max N (Module.finrank 𝕜 F) ^ 2,
      (ρ.eventually_finsupport_subset x).mono fun y hy v ↦
        support_flattenFinsupp_subset_range fun n hn ↦ Finset.mem_range.2 ?_⟩
    have hn_supp : n ∈ ρ.finsupport y := by
      rw [ρ.mem_finsupport, mem_support]
      intro h0
      exact Finsupp.mem_support_iff.1 hn (by simp [j₀, h0])
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (hy hn_supp))
  · intro x
    have hj₀_inj : Injective (j₀ x) := by
      intro v w hvw
      have hne : ∃ n, ρ n x ≠ 0 := by
        by_contra! hall
        have hsum := ρ.sum_eq_one (mem_univ x)
        simp [hall] at hsum
      obtain ⟨n, hn⟩ := hne
      have hx_base : x ∈ (e n).baseSet := hρ n (subset_tsupport (ρ n) hn)
      have hvn : j₀ x v n = j₀ x w n := congrArg (fun f ↦ f n) hvw
      simp only [j₀, partitionBlockCoordinates_apply] at hvn
      have hscalar : algebraMap ℝ 𝕜 (ρ n x) ≠ 0 := by
        rw [← map_zero (algebraMap ℝ 𝕜)]
        exact (RingHom.injective (algebraMap ℝ 𝕜)).ne hn
      have hlin : (e n).linearMapAt 𝕜 x v = (e n).linearMapAt 𝕜 x w :=
        b.equivFun.injective ((smul_right_inj hscalar).1 hvn)
      rw [← (e n).symm_linearMapAt (R := 𝕜) hx_base v,
        ← (e n).symm_linearMapAt (R := 𝕜) hx_base w, hlin]
    exact (flattenFinsupp_injective 𝕜 _).comp hj₀_inj

/-- Square-root-weighted orthonormal block coordinates (`PartitionOfUnity.weightedFrameCoordinates`)
for a Riemannian or Hermitian vector bundle flatten directly to `IsClassifyingCoordinates`. -/
theorem IsClassifyingCoordinates.of_weightedFrameCoordinates
    {𝕜 X F V : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    {E : X → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
    {r : ℕ} (ρ : PartitionOfUnity ℕ X univ)
    (e : ℕ → Trivialization F (π F E)) [∀ n, (e n).IsLinear 𝕜]
    (he : ∀ n, {x | 0 < ρ n x} ⊆ (e n).baseSet)
    (c : Module.Basis (Fin r) 𝕜 F) (b : OrthonormalBasis (Fin r) 𝕜 V) :
    let coords : V ≃ₗ[𝕜] (Fin r → 𝕜) :=
      b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (Fin r → 𝕜))
    IsClassifyingCoordinates 𝕜 F E fun x ↦
      (flattenFinsupp 𝕜 r).comp
        ((Finsupp.mapRange.linearEquiv coords).toLinearMap.comp
          (ρ.weightedFrameCoordinates e c b x)) := by
  intro coords
  have hcoords_cont : Continuous coords :=
    (PiLp.continuous_ofLp 2 _).comp b.repr.continuous
  refine ⟨fun m ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · by_cases hr : m.unpair.2 < r
    · refine ((continuous_apply ⟨m.unpair.2, hr⟩).comp
        (hcoords_cont.comp (ρ.continuous_weightedFrameCoordinates_apply e c b he m.unpair.1))).congr
          fun p ↦ ?_
      simp [flattenFinsupp_apply, hr]
    · refine (continuous_const (y := (0 : 𝕜))).congr fun p ↦ ?_
      simp [flattenFinsupp_apply, hr]
  · obtain ⟨N, hN⟩ := ρ.locally_support_weightedFrameCoordinates_range c b e x
    exact ⟨max N r ^ 2, hN.mono fun y hy v ↦
      support_flattenFinsupp_subset_range
        ((Finsupp.support_mapRange (f := coords) (hf := map_zero coords)).trans (hy v))⟩
  · exact (flattenFinsupp_injective 𝕜 r).comp <|
      (Finsupp.mapRange.linearEquiv coords).injective.comp
        (ρ.weightedFrameCoordinates_injective e c b (mem_univ x))

end Existence

section HomotopyUniqueness

namespace infiniteGrassmannian

/-- The image of `Tautological.subtype W` is the underlying submodule `W.1`. -/
@[simp]
theorem Tautological.range_subtype {𝕜 : Type*} [Field 𝕜] {k : ℕ}
    (W : infiniteGrassmannian 𝕜 k) :
    LinearMap.range (Tautological.subtype W) = W.1 :=
  le_antisymm (by rintro _ ⟨v, rfl⟩; rw [Tautological.subtype_apply]; exact v.property)
    fun w hw ↦ ⟨⟨w, hw⟩, Tautological.subtype_apply _ _⟩

/-- A map out of `Y × infiniteGrassmannian 𝕜 k` for a locally compact space `Y` (such as
`unitInterval`) is continuous if and only if its restriction to `Y × finiteGrassmannian 𝕜 k n` is
continuous for every stage `n : ℕ`. -/
theorem continuous_prod_left_iff {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] {k : ℕ}
    {Y Z : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [TopologicalSpace Z]
    {g : Y × infiniteGrassmannian 𝕜 k → Z} :
    Continuous g ↔
      ∀ n, Continuous fun q : Y × finiteGrassmannian 𝕜 k n ↦
        g (q.1, finiteGrassmannian.toInfinite q.2) := by
  refine ⟨fun hg n ↦ hg.comp (continuous_id.prodMap finiteGrassmannian.continuous_toInfinite),
    fun hg ↦ isQuotientMap_sigmaToInfinite.continuous_lift_prod_right ?_⟩
  let G : C(Σ n, finiteGrassmannian 𝕜 k n, C(Y, Z)) :=
    ⟨fun s ↦ ContinuousMap.curry
      ⟨fun r : finiteGrassmannian 𝕜 k s.1 × Y ↦ g (r.2, finiteGrassmannian.toInfinite r.1),
        (hg s.1).comp continuous_swap⟩ s.2,
      continuous_sigma fun n ↦ (ContinuousMap.curry
        ⟨_, (hg n).comp continuous_swap⟩).continuous⟩
  refine ((ContinuousMap.continuous_uncurry_of_continuous G).comp continuous_swap).congr fun p ↦ ?_
  rcases p with ⟨y, ⟨n, V⟩⟩
  simp [G, Function.uncurry]

section Shifts

/-- Linear interpolation `(1 - c) • id + c • lmapDomain s` along a strictly monotone coordinate
shift `s : ℕ → ℕ`. -/
private def shiftInterp (𝕜 : Type*) [CommRing 𝕜] (s : ℕ → ℕ) (c : 𝕜) :
    (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  (1 - c) • LinearMap.id + c • Finsupp.lmapDomain 𝕜 𝕜 s

@[simp]
private theorem shiftInterp_zero (𝕜 : Type*) [CommRing 𝕜] (s : ℕ → ℕ) :
    shiftInterp 𝕜 s 0 = LinearMap.id := by
  ext v m
  simp [shiftInterp]

@[simp]
private theorem shiftInterp_one (𝕜 : Type*) [CommRing 𝕜] (s : ℕ → ℕ) :
    shiftInterp 𝕜 s 1 = Finsupp.lmapDomain 𝕜 𝕜 s := by
  ext v m
  simp [shiftInterp]

/-- For any strictly monotone `s : ℕ → ℕ` and any scalar `c` in an integral domain `𝕜`,
`shiftInterp 𝕜 s c` is injective: on the top index `m` of the support of a nonzero vector, either
`s m = m` (giving `v m ≠ 0`) or `m < s m` (giving `c * v m` at index `s m` when `c ≠ 0`). -/
private theorem shiftInterp_injective {𝕜 : Type*} [CommRing 𝕜] [IsDomain 𝕜]
    {s : ℕ → ℕ} (hs : StrictMono s) (c : 𝕜) :
    Injective (shiftInterp 𝕜 s c) := by
  refine LinearMap.ker_eq_bot.1 <| LinearMap.ker_eq_bot'.2 fun v hv ↦ ?_
  by_contra hv0
  let m := v.support.max' (Finsupp.support_nonempty_iff.2 hv0)
  have hm_mem : m ∈ v.support := Finset.max'_mem _ _
  have hvm : v m ≠ 0 := Finsupp.mem_support_iff.1 hm_mem
  have hle : m ≤ s m := hs.id_le m
  rcases hle.eq_or_lt with h_eq | h_lt
  · have heval := congrArg (fun w : ℕ →₀ 𝕜 ↦ w m) hv
    simp only [shiftInterp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finsupp.zero_apply, Finsupp.lmapDomain_apply] at heval
    have hmap : Finsupp.mapDomain s v m = v m := by
      conv_lhs => rw [h_eq]
      exact Finsupp.mapDomain_apply_of_injective hs.injective v m
    rw [hmap, ← add_mul, sub_add_cancel, one_mul] at heval
    exact hvm heval
  · by_cases hc : c = 0
    · have hv' : v = 0 := by simpa [hc] using hv
      exact hv0 hv'
    · have heval := congrArg (fun w : ℕ →₀ 𝕜 ↦ w (s m)) hv
      have hnot : s m ∉ v.support := fun hsm ↦
        (lt_irrefl m) (h_lt.trans_le (Finset.le_max' _ _ hsm))
      have hv_sm : v (s m) = 0 := Finsupp.notMem_support_iff.1 hnot
      have hmap : Finsupp.mapDomain s v (s m) = v m :=
        Finsupp.mapDomain_apply_of_injective hs.injective v m
      simp only [shiftInterp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finsupp.zero_apply, Finsupp.lmapDomain_apply, hv_sm, mul_zero, zero_add, hmap] at heval
      exact (mul_ne_zero hc hvm) heval

/-- The tautological inclusion into `ℕ →₀ 𝕜` viewed as a fibrewise linear map on the pulled-back
bundle `(toInfiniteContinuousMap : _ → _) *ᵖ (Tautological 𝕜 k)` over `finiteGrassmannian 𝕜 k n`. -/
private def stageTautologicalLinearMap {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k n : ℕ}
    (V : finiteGrassmannian 𝕜 k n) :
    ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k)) V →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Tautological.subtype (finiteGrassmannian.toInfinite V)

@[simp]
private theorem stageTautologicalLinearMap_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k n : ℕ}
    (V : finiteGrassmannian 𝕜 k n)
    (v : ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k)) V) :
    stageTautologicalLinearMap V v = v.val :=
  Tautological.subtype_apply (finiteGrassmannian.toInfinite V) v

private theorem stageTautologicalLinearMap_injective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k n : ℕ} (V : finiteGrassmannian 𝕜 k n) :
    Injective (stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) V) :=
  Tautological.subtype_injective (finiteGrassmannian.toInfinite V)

@[simp]
private theorem range_stageTautologicalLinearMap {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k n : ℕ}
    (V : finiteGrassmannian 𝕜 k n) :
    LinearMap.range (stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) V) =
      (finiteGrassmannian.toInfinite V).1 :=
  Tautological.range_subtype (finiteGrassmannian.toInfinite V)

/-- On the `n`-th finite stage, the tautological inclusion defines classifying coordinates on
`(toInfiniteContinuousMap : _ → _) *ᵖ (Tautological 𝕜 k)`. -/
private theorem isClassifyingCoordinates_stageTautological
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {k n : ℕ} :
    IsClassifyingCoordinates 𝕜 (Fin k → 𝕜)
      ((finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
        (Tautological 𝕜 k))
      (stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) (n := n)) where
  continuous_coord m :=
    ((continuous_evalCoord m).comp
      (Pullback.continuous_lift (Fin k → 𝕜) (Tautological 𝕜 k)
        (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _))).congr
          fun p ↦ by rcases p with ⟨_, _⟩; simp [Pullback.lift]
  locally_supported _ :=
    ⟨n, Filter.Eventually.of_forall fun V v m hm ↦ by
      have hv : v.val ∈ (finiteGrassmannian.toInfinite V).1 := v.property
      rw [finiteGrassmannian.coe_toInfinite, Submodule.mem_map] at hv
      rcases hv with ⟨u, -, hu⟩
      rw [stageTautologicalLinearMap_apply, ← hu] at hm
      by_contra hmn
      exact (Finsupp.mem_support_iff.1 hm)
        (coordinateInclusion_apply_of_le u
          (Nat.le_of_not_gt fun hlt ↦ hmn (Finset.mem_range.2 hlt)))⟩
  injective V := stageTautologicalLinearMap_injective V

end Shifts

end infiniteGrassmannian

namespace IsClassifyingCoordinates

/-- Linearly interpolated coordinates `(1 - t) • j₀ x + t • j₁ x` on the cylinder pullback bundle
`(((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E)`. -/
@[expose] def cylinderLinearMap
    {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    (j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)) (p : I × X) :
    (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) p →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  (1 - algebraMap ℝ 𝕜 p.1.1) • j₀ p.2 + (algebraMap ℝ 𝕜 p.1.1) • j₁ p.2

@[simp]
theorem cylinderLinearMap_apply
    {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    (j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)) (p : I × X)
    (v : (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) p) :
    cylinderLinearMap j₀ j₁ p v =
      (1 - algebraMap ℝ 𝕜 p.1.1) • j₀ p.2 v + (algebraMap ℝ 𝕜 p.1.1) • j₁ p.2 v :=
  rfl

@[simp]
theorem range_cylinderLinearMap_zero
    {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    (j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)) (x : X) :
    LinearMap.range (cylinderLinearMap j₀ j₁ (0, x)) = LinearMap.range (j₀ x) := by
  change LinearMap.range ((1 - algebraMap ℝ 𝕜 (0 : I).1) • j₀ x +
    (algebraMap ℝ 𝕜 (0 : I).1) • j₁ x) = LinearMap.range (j₀ x)
  congr 1
  ext v m
  simp

@[simp]
theorem range_cylinderLinearMap_one
    {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    (j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)) (x : X) :
    LinearMap.range (cylinderLinearMap j₀ j₁ (1, x)) = LinearMap.range (j₁ x) := by
  change LinearMap.range ((1 - algebraMap ℝ 𝕜 (1 : I).1) • j₀ x +
    (algebraMap ℝ 𝕜 (1 : I).1) • j₁ x) = LinearMap.range (j₁ x)
  congr 1
  ext v m
  simp

/-- Linearly interpolating between two families of classifying coordinates `j₀` and `j₁` on the
same bundle `E` over `X` yields classifying coordinates on the cylinder bundle over `I × X`,
whenever `(1 - algebraMap ℝ 𝕜 t) • j₀ x + (algebraMap ℝ 𝕜 t) • j₁ x` is fibrewise injective for
every `(t, x) : I × X`. -/
theorem cylinderInterp
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X] {F : Type*} [TopologicalSpace F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hinj : ∀ (t : I) (x : X),
      Injective ((1 - algebraMap ℝ 𝕜 t.1) • j₀ x + (algebraMap ℝ 𝕜 t.1) • j₁ x)) :
    IsClassifyingCoordinates 𝕜 F (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E)
      (cylinderLinearMap j₀ j₁) where
  continuous_coord m := by
    let π_cyl := Pullback.continuous_proj F E ((ContinuousMap.snd : C(I × X, X)) : I × X → X)
    let lift_cyl := Pullback.continuous_lift F E ((ContinuousMap.snd : C(I × X, X)) : I × X → X)
    have ht : Continuous fun q : TotalSpace F
        (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) ↦ algebraMap ℝ 𝕜 q.proj.1.1 :=
      (continuous_algebraMap ℝ 𝕜).comp (continuous_subtype_val.comp (continuous_fst.comp π_cyl))
    have hsum : Continuous fun q : TotalSpace F
        (((ContinuousMap.snd : C(I × X, X)) : I × X → X) *ᵖ E) ↦
          (1 - algebraMap ℝ 𝕜 q.proj.1.1) * j₀ q.proj.2 q.2 m +
            algebraMap ℝ 𝕜 q.proj.1.1 * j₁ q.proj.2 q.2 m :=
      (((continuous_const (y := (1 : 𝕜))).sub ht).mul ((hj₀.continuous_coord m).comp lift_cyl)).add
        (ht.mul ((hj₁.continuous_coord m).comp lift_cyl))
    refine hsum.congr fun p ↦ ?_
    rcases p with ⟨⟨t, x⟩, v⟩
    rfl
  locally_supported p := by
    obtain ⟨N₀, hN₀⟩ := hj₀.locally_supported p.2
    obtain ⟨N₁, hN₁⟩ := hj₁.locally_supported p.2
    refine ⟨max N₀ N₁, Filter.mem_of_superset
      (continuous_snd.continuousAt.preimage_mem_nhds (Filter.inter_mem hN₀ hN₁))
      fun q hq v r hr ↦ ?_⟩
    rcases Finset.mem_union.1 (Finsupp.support_add hr) with hr₀ | hr₁
    · exact Finset.mem_range.2 ((Finset.mem_range.1
        (hq.1 v (Finsupp.support_smul hr₀))).trans_le (le_max_left N₀ N₁))
    · exact Finset.mem_range.2 ((Finset.mem_range.1
        (hq.2 v (Finsupp.support_smul hr₁))).trans_le (le_max_right N₀ N₁))
  injective p := hinj p.1 p.2

/-- If `(1 - t) • j₀ + t • j₁` is fibrewise injective for every `(t, x) : I × X`, its classifying
map on `I × X` is an explicit homotopy between `hj₀.classifyContinuousMap hk` and
`hj₁.classifyContinuousMap hk`. -/
def homotopyOfLinearCombinationInjective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hinj : ∀ (t : I) (x : X),
      Injective ((1 - algebraMap ℝ 𝕜 t.1) • j₀ x + (algebraMap ℝ 𝕜 t.1) • j₁ x))
    (hk : Module.finrank 𝕜 F = k) :
    (hj₀.classifyContinuousMap hk).Homotopy (hj₁.classifyContinuousMap hk) where
  toContinuousMap := (hj₀.cylinderInterp hj₁ hinj).classifyContinuousMap hk
  map_zero_left x := Subtype.ext <| by
    change ((hj₀.cylinderInterp hj₁ hinj).classify hk (0, x)).1 = (hj₀.classify hk x).1
    rw [coe_classify, coe_classify, range_cylinderLinearMap_zero]
  map_one_left x := Subtype.ext <| by
    change ((hj₀.cylinderInterp hj₁ hinj).classify hk (1, x)).1 = (hj₁.classify hk x).1
    rw [coe_classify, coe_classify, range_cylinderLinearMap_one]

end IsClassifyingCoordinates

namespace infiniteGrassmannian

/-- Any strictly monotone coordinate shift `s : ℕ → ℕ` induces a self-map of
`infiniteGrassmannian 𝕜 k` homotopic to the identity. -/
theorem homotopic_id_mapContinuousMap_lmapDomain
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    {s : ℕ → ℕ} (hs : StrictMono s)
    (hφ : Function.Injective (Finsupp.lmapDomain 𝕜 𝕜 s) :=
      Finsupp.mapDomain_injective hs.injective) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (mapContinuousMap (Finsupp.lmapDomain 𝕜 𝕜 s) hφ) := by
  let H : I × infiniteGrassmannian 𝕜 k → infiniteGrassmannian 𝕜 k := fun p ↦
    map (shiftInterp 𝕜 s (algebraMap ℝ 𝕜 p.1.1)) (shiftInterp_injective hs _) p.2
  have hcont : Continuous H := by
    refine continuous_prod_left_iff.2 fun n ↦ ?_
    let E_n := (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k)
    let hj₀ := isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)
    let hj₁ := hj₀.postcomp (FiberBundle.continuous_proj (Fin k → 𝕜) E_n)
      (Finsupp.lmapDomain 𝕜 𝕜 s) hφ
    have heq (c : 𝕜) (V : finiteGrassmannian 𝕜 k n) :
        (1 - c) • stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) V +
          c • (Finsupp.lmapDomain 𝕜 𝕜 s).comp (stageTautologicalLinearMap V) =
        (shiftInterp 𝕜 s c).comp (stageTautologicalLinearMap V) := by
      ext v m
      simp [shiftInterp]
    have hinj (t : I) (V : finiteGrassmannian 𝕜 k n) :
        Injective ((1 - algebraMap ℝ 𝕜 t.1) • stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) V +
          (algebraMap ℝ 𝕜 t.1) • (Finsupp.lmapDomain 𝕜 𝕜 s).comp
            (stageTautologicalLinearMap V)) := by
      rw [heq]
      exact (shiftInterp_injective hs _).comp (stageTautologicalLinearMap_injective V)
    refine ((hj₀.cylinderInterp hj₁ hinj).continuous_classify (Module.finrank_fin_fun 𝕜)).congr
      fun q ↦ Subtype.ext ?_
    rw [IsClassifyingCoordinates.coe_classify]
    change LinearMap.range
      ((1 - algebraMap ℝ 𝕜 q.1.1) • stageTautologicalLinearMap (𝕜 := 𝕜) (k := k) q.2 +
        (algebraMap ℝ 𝕜 q.1.1) • (Finsupp.lmapDomain 𝕜 𝕜 s).comp
          (stageTautologicalLinearMap q.2)) = _
    rw [heq, LinearMap.range_comp, range_stageTautologicalLinearMap, coe_map]
  refine ⟨{
    toFun := H
    continuous_toFun := hcont
    map_zero_left W := Subtype.ext (by simp [H])
    map_one_left W := Subtype.ext (by rw [mapContinuousMap_apply]; simp [H]) }⟩

/-- The even-coordinate shift `m ↦ 2 * m` on `ℕ →₀ 𝕜`. -/
private def evenLinear (𝕜 : Type*) [Semiring 𝕜] : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m)

/-- The odd-coordinate shift `m ↦ 2 * m + 1` on `ℕ →₀ 𝕜`. -/
private def oddLinear (𝕜 : Type*) [Semiring 𝕜] : (ℕ →₀ 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Finsupp.lmapDomain 𝕜 𝕜 (fun m ↦ 2 * m + 1)

private theorem strictMono_even : StrictMono (fun m : ℕ ↦ 2 * m) :=
  fun _ _ h ↦ Nat.mul_lt_mul_of_pos_left h Nat.two_pos

private theorem strictMono_odd : StrictMono (fun m : ℕ ↦ 2 * m + 1) :=
  fun _ _ h ↦ Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left h Nat.two_pos)

private theorem evenLinear_injective (𝕜 : Type*) [Semiring 𝕜] :
    Function.Injective (evenLinear 𝕜) :=
  Finsupp.mapDomain_injective strictMono_even.injective

private theorem oddLinear_injective (𝕜 : Type*) [Semiring 𝕜] :
    Function.Injective (oddLinear 𝕜) :=
  Finsupp.mapDomain_injective strictMono_odd.injective

private theorem evenLinear_apply_even {𝕜 : Type*} [Semiring 𝕜] (v : ℕ →₀ 𝕜) (m : ℕ) :
    evenLinear 𝕜 v (2 * m) = v m :=
  Finsupp.mapDomain_apply_of_injective strictMono_even.injective v m

private theorem oddLinear_apply_odd {𝕜 : Type*} [Semiring 𝕜] (v : ℕ →₀ 𝕜) (m : ℕ) :
    oddLinear 𝕜 v (2 * m + 1) = v m :=
  Finsupp.mapDomain_apply_of_injective strictMono_odd.injective v m

private theorem evenLinear_apply_odd {𝕜 : Type*} [Semiring 𝕜] (v : ℕ →₀ 𝕜) (m : ℕ) :
    evenLinear 𝕜 v (2 * m + 1) = 0 :=
  Finsupp.mapDomain_of_notMem_range v _ (by rintro ⟨r, hr⟩; dsimp only at hr; omega)

/-- Interleaving any two injective maps into `ℕ →₀ 𝕜` via `evenLinear` and `oddLinear` produces an
injective linear combination `(1 - c) • (evenLinear ∘ f₀) + c • (oddLinear ∘ f₁)` for every scalar
`c` in an integral domain `𝕜` (since `1 - c` and `c` cannot both vanish). -/
private theorem even_odd_interp_injective {𝕜 M : Type*} [CommRing 𝕜] [IsDomain 𝕜]
    [AddCommMonoid M] [Module 𝕜 M] {f₀ f₁ : M →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hf₀ : Function.Injective f₀) (hf₁ : Function.Injective f₁) (c : 𝕜) :
    Function.Injective ((1 - c) • (evenLinear 𝕜).comp f₀ + c • (oddLinear 𝕜).comp f₁) := by
  intro v w hvw
  by_cases hc : c = 0
  · subst hc
    refine hf₀ <| Finsupp.ext fun m ↦ ?_
    have hev := congrArg (fun z : ℕ →₀ 𝕜 ↦ z (2 * m)) hvw
    simpa [evenLinear_apply_even] using hev
  · refine hf₁ <| Finsupp.ext fun m ↦ ?_
    have hod := congrArg (fun z : ℕ →₀ 𝕜 ↦ z (2 * m + 1)) hvw
    simp [evenLinear_apply_odd, oddLinear_apply_odd] at hod
    exact hod.resolve_right hc

end infiniteGrassmannian

/-- Any two families of classifying coordinates on the *same* vector bundle `E` over an arbitrary
topological space `X` induce homotopic classifying maps to `infiniteGrassmannian 𝕜 k`. -/
theorem IsClassifyingCoordinates.homotopic_classifyContinuousMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {X : Type*} [TopologicalSpace X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : X → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    {j₀ j₁ : ∀ x, E x →ₗ[𝕜] (ℕ →₀ 𝕜)} {k : ℕ}
    (hj₀ : IsClassifyingCoordinates 𝕜 F E j₀) (hj₁ : IsClassifyingCoordinates 𝕜 F E j₁)
    (hk : Module.finrank 𝕜 F = k) :
    (hj₀.classifyContinuousMap hk).Homotopic (hj₁.classifyContinuousMap hk) := by
  have hπ : Continuous (π F E) := FiberBundle.continuous_proj F E
  let hev := hj₀.postcomp hπ (infiniteGrassmannian.evenLinear 𝕜)
    (infiniteGrassmannian.evenLinear_injective 𝕜)
  let hod := hj₁.postcomp hπ (infiniteGrassmannian.oddLinear 𝕜)
    (infiniteGrassmannian.oddLinear_injective 𝕜)
  have hmid : (hev.classifyContinuousMap hk).Homotopic (hod.classifyContinuousMap hk) :=
    ⟨hev.homotopyOfLinearCombinationInjective hod
      (fun t x ↦ infiniteGrassmannian.even_odd_interp_injective
        (hj₀.injective x) (hj₁.injective x) (algebraMap ℝ 𝕜 t.1)) hk⟩
  rw [hj₀.classifyContinuousMap_postcomp (infiniteGrassmannian.evenLinear 𝕜)
        (infiniteGrassmannian.evenLinear_injective 𝕜) hk,
      hj₁.classifyContinuousMap_postcomp (infiniteGrassmannian.oddLinear 𝕜)
        (infiniteGrassmannian.oddLinear_injective 𝕜) hk] at hmid
  have hid_ev := ContinuousMap.Homotopic.comp
    (infiniteGrassmannian.homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k)
      infiniteGrassmannian.strictMono_even)
    (ContinuousMap.Homotopic.refl (hj₀.classifyContinuousMap hk))
  have hid_od := ContinuousMap.Homotopic.comp
    (infiniteGrassmannian.homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k)
      infiniteGrassmannian.strictMono_odd)
    (ContinuousMap.Homotopic.refl (hj₁.classifyContinuousMap hk))
  exact hid_ev.trans (hmid.trans hid_od.symm)

namespace infiniteGrassmannian

/-- Any family of classifying coordinates on `Tautological 𝕜 k` itself induces a classifying map
homotopic to the identity of `infiniteGrassmannian 𝕜 k`. On each finite coordinate stage
`finiteGrassmannian 𝕜 k n`, `Tautological.subtype` is locally finitely supported, so even/odd
interleaving supplies compatible stagewise homotopies descending along `sigmaToInfinite`. -/
theorem homotopic_id_classifyContinuousMap_tautological
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] {k : ℕ}
    {j : ∀ W, Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) j) :
    (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic
      (hj.classifyContinuousMap (Module.finrank_fin_fun 𝕜)) := by
  let c := hj.classifyContinuousMap (Module.finrank_fin_fun 𝕜)
  let J (t : I) (W : infiniteGrassmannian 𝕜 k) : Tautological 𝕜 k W →ₗ[𝕜] (ℕ →₀ 𝕜) :=
    (1 - algebraMap ℝ 𝕜 t.1) • (evenLinear 𝕜).comp (Tautological.subtype W) +
      (algebraMap ℝ 𝕜 t.1) • (oddLinear 𝕜).comp (j W)
  have hJ_inj (t : I) (W : infiniteGrassmannian 𝕜 k) : Injective (J t W) :=
    even_odd_interp_injective (Tautological.subtype_injective W) (hj.injective W)
      (algebraMap ℝ 𝕜 t.1)
  let H : I × infiniteGrassmannian 𝕜 k → infiniteGrassmannian 𝕜 k := fun p ↦
    ⟨LinearMap.range (J p.1 p.2),
      (LinearEquiv.ofInjective (J p.1 p.2) (hJ_inj p.1 p.2)).symm.rank_eq.trans
        ((tautologicalEquiv 𝕜 k p.2).rank_eq.trans p.2.2)⟩
  have hcont : Continuous H := by
    refine continuous_prod_left_iff.2 fun n ↦ ?_
    let E_n := (finiteGrassmannian.toInfiniteContinuousMap (𝕜 := 𝕜) (k := k) (n := n) : _ → _) *ᵖ
      (Tautological 𝕜 k)
    have hπ_n : Continuous (π (Fin k → 𝕜) E_n) := FiberBundle.continuous_proj (Fin k → 𝕜) E_n
    let hj_stage := (isClassifyingCoordinates_stageTautological (𝕜 := 𝕜) (k := k) (n := n)).postcomp
      hπ_n (evenLinear 𝕜) (evenLinear_injective 𝕜)
    let hj_pull := (hj.pullback finiteGrassmannian.toInfiniteContinuousMap).postcomp
      hπ_n (oddLinear 𝕜) (oddLinear_injective 𝕜)
    refine ((hj_stage.cylinderInterp hj_pull fun t V ↦ hJ_inj t _).continuous_classify
      (Module.finrank_fin_fun 𝕜)).congr fun _ ↦ Subtype.ext rfl
  have hmid : (mapContinuousMap (evenLinear 𝕜) (evenLinear_injective 𝕜)).Homotopic
      ((mapContinuousMap (oddLinear 𝕜) (oddLinear_injective 𝕜)).comp c) :=
    ⟨{ toFun := H
       continuous_toFun := hcont
       map_zero_left W := Subtype.ext <| by
         have h0 : J 0 W = (evenLinear 𝕜).comp (Tautological.subtype W) := by
           ext v m; simp [J]
         simp [H, h0, LinearMap.range_comp]
       map_one_left W := Subtype.ext <| by
         have h1 : J 1 W = (oddLinear 𝕜).comp (j W) := by
           ext v m; simp [J]
         simp [H, c, h1, LinearMap.range_comp] }⟩
  have hid_ev := homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k) strictMono_even
  have hid_od := ContinuousMap.Homotopic.comp
    (homotopic_id_mapContinuousMap_lmapDomain (𝕜 := 𝕜) (k := k) strictMono_odd)
    (ContinuousMap.Homotopic.refl c)
  exact hid_ev.trans (hmid.trans hid_od.symm)

/-- Over `RCLike 𝕜` and an *arbitrary* topological space `X` (no paracompactness or separation on
`X` is needed here), if the pullbacks of `Tautological 𝕜 k` along `f₀, f₁ : C(X, _)` admit a
continuous fibrewise linear equivalence, then `f₀` and `f₁` are homotopic. -/
theorem homotopic_of_pullback_equiv {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
        p.proj (Φ p.proj p.2)) :
    f₀.Homotopic f₁ := by
  obtain ⟨j_univ, hj_univ⟩ :=
    exists_isClassifyingCoordinates (𝕜 := 𝕜) (X := infiniteGrassmannian 𝕜 k)
      (F := Fin k → 𝕜) (E := Tautological 𝕜 k)
  have hk := Module.finrank_fin_fun (R := 𝕜) (n := k)
  let c := hj_univ.classifyContinuousMap hk
  have hc : (ContinuousMap.id (infiniteGrassmannian 𝕜 k)).Homotopic c :=
    homotopic_id_classifyContinuousMap_tautological hj_univ
  let hj₀ := hj_univ.pullback f₀
  let hj₁ := hj_univ.pullback f₁
  let hj₁' := hj₁.compLinearMap (G := Fin k → 𝕜)
    (E' := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k))
    (fun x ↦ (Φ x).toLinearMap) (fun x ↦ (Φ x).injective) hΦ
  have h_eq : hj₁'.classifyContinuousMap hk = c.comp f₁ :=
    (hj₁.classifyContinuousMap_compLinearEquiv (G := Fin k → 𝕜)
      (E' := (f₀ : _ → _) *ᵖ (Tautological 𝕜 k))
      (fun x ↦ (Φ x).toLinearEquiv) hΦ hk hk).trans
        (hj_univ.classifyContinuousMap_pullback f₁ hk)
  have hmid : (c.comp f₀).Homotopic (c.comp f₁) := by
    rw [← hj_univ.classifyContinuousMap_pullback f₀ hk, ← h_eq]
    exact hj₀.homotopic_classifyContinuousMap hj₁' hk
  exact (ContinuousMap.Homotopic.comp hc (.refl f₀)).trans
    (hmid.trans (ContinuousMap.Homotopic.comp hc (.refl f₁)).symm)

/-- Over `RCLike 𝕜` and a paracompact `R₁` base `X` (for instance any paracompact Hausdorff space),
two continuous maps `f₀, f₁ : C(X, infiniteGrassmannian 𝕜 k)` are homotopic if and only if the
pullbacks of `Tautological 𝕜 k` along `f₀` and `f₁` are isomorphic as vector bundles. -/
theorem homotopic_iff_exists_pullbackEquiv
    {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X] [ParacompactSpace X] [R1Space X]
    {k : ℕ} {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)} :
    f₀.Homotopic f₁ ↔
      ∃ Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x),
        Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
          TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
            p.proj (Φ p.proj p.2) :=
  ⟨fun h ↦
    let ⟨Φ, hΦ, _⟩ := h.exists_continuousLinearEquiv_pullback (F := Fin k → 𝕜)
      (E := Tautological 𝕜 k)
    ⟨Φ, hΦ⟩,
   fun ⟨Φ, hΦ⟩ ↦ homotopic_of_pullback_equiv Φ hΦ⟩

end infiniteGrassmannian

end HomotopyUniqueness

section SmallClassification

namespace infiniteGrassmannian

section CoreComparisons

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]

variable (𝕜) in
/-- The universal tautological bundle over `infiniteGrassmannian 𝕜 k` packaged as a point-indexed
finite-rank coordinate core in `FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k)`. -/
@[expose, implicit_reducible]
def tautologicalCore (k : ℕ) : FiniteRankBundleCore 𝕜 (infiniteGrassmannian 𝕜 k) where
  rank := k
  core := pointIndexedCore 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  indexAt_eq := pointIndexedCore_indexAt 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)

@[simp]
theorem rank_tautologicalCore (k : ℕ) : (tautologicalCore 𝕜 k).rank = k := (rfl)

@[simp]
theorem core_tautologicalCore (k : ℕ) :
    (tautologicalCore 𝕜 k).core = pointIndexedCore 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k) := (rfl)

theorem tautologicalCore_eq_ofBundle (k : ℕ) :
    tautologicalCore 𝕜 k = .ofBundle 𝕜 k (Tautological 𝕜 k) := (rfl)

/-- Point-indexed finite-rank coordinate core associated to the pullback of `Tautological 𝕜 k`
along `f : C(X, infiniteGrassmannian 𝕜 k)`. -/
private def tautologicalPullbackPointCore {k : ℕ} (f : C(X, infiniteGrassmannian 𝕜 k)) :
    FiniteRankBundleCore 𝕜 X where
  rank := k
  core := pointIndexedCore 𝕜 (Fin k → 𝕜) ((f : _ → _) *ᵖ (Tautological 𝕜 k))
  indexAt_eq := pointIndexedCore_indexAt 𝕜 (Fin k → 𝕜) ((f : _ → _) *ᵖ (Tautological 𝕜 k))

/-- Helper constructing a categorical isomorphism `A ≅ D` in `FiniteRankBundleCore 𝕜 X` from a
family of coordinate equivalences whose induced map on core total spaces is continuous. -/
private def coreIsoOfContinuousEquiv [CompleteSpace 𝕜]
    {A D : FiniteRankBundleCore 𝕜 X}
    (ψ : X → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hψ : Continuous fun p : A.core.TotalSpace ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) p.proj (ψ p.proj p.2)) :
    A ≅ D := by
  let hom : A ⟶ D := VectorBundleCore.CoordinateHom.ofContinuous
    (fun x ↦ (ψ x).toContinuousLinearMap)
    ((continuous_hom_bundle_iff (E₁ := A.core.Fiber) (E₂ := D.core.Fiber) _).2 hψ)
  have hbij : ∀ x, Bijective (hom.fiberMap x) := fun x ↦ by
    rw [congrFun (VectorBundleCore.CoordinateHom.fiberMap_ofContinuous _ _) x]
    exact (ψ x).bijective
  have : IsIso hom := (FiniteRankBundleCore.isIso_iff_bijective hom).2 hbij
  exact asIso hom

/-- Over a complete scalar field, `(tautologicalCore 𝕜 k).pullback f` is canonically isomorphic in
`FiniteRankBundleCore 𝕜 X` to `tautologicalPullbackPointCore f`. -/
private def tautologicalPullbackIso [CompleteSpace 𝕜] {k : ℕ}
    (f : C(X, infiniteGrassmannian 𝕜 k)) :
    (tautologicalCore 𝕜 k).pullback f ≅ tautologicalPullbackPointCore f := by
  let eT := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  let eP := pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) ((f : _ → _) *ᵖ (Tautological 𝕜 k))
  let hT := pointIndexedCoreHomeomorph 𝕜 (Fin k → 𝕜) (Tautological 𝕜 k)
  let hP := pointIndexedCoreHomeomorph 𝕜 (Fin k → 𝕜) ((f : _ → _) *ᵖ (Tautological 𝕜 k))
  let hp := (tautologicalCore 𝕜 k).pullbackHomeomorph f
  have hmid : Continuous fun p : TotalSpace (Fin k → 𝕜)
      ((f : _ → _) *ᵖ (tautologicalCore 𝕜 k).core.Fiber) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (eT (f p.proj) p.2) :=
    Bundle.Pullback.continuous_iff (F := Fin k → 𝕜) (E := Tautological 𝕜 k)
      (f := (f : X → infiniteGrassmannian 𝕜 k)).2
        ⟨Pullback.continuous_proj (Fin k → 𝕜) (tautologicalCore 𝕜 k).core.Fiber f, by
          refine (hT.continuous.comp
            (Pullback.continuous_lift (Fin k → 𝕜) (tautologicalCore 𝕜 k).core.Fiber f)).congr
              fun p ↦ ?_
          rcases p with ⟨x, v⟩
          simp [hT, eT, Pullback.lift]⟩
  exact coreIsoOfContinuousEquiv (fun x ↦ (eT (f x)).trans (eP x).symm)
    ((hP.symm.continuous.comp (hmid.comp hp.continuous)).congr fun p ↦ by
      rcases p with ⟨x, v⟩
      dsimp only [Function.comp_def, hP, hp]
      rw [FiniteRankBundleCore.pullbackHomeomorph_apply, pointIndexedCoreHomeomorph_symm_apply]
      rfl)

/-- Two pullbacks of `Tautological 𝕜 k` with a continuous fibrewise linear equivalence have
isomorphic `tautologicalCore` pullbacks in `FiniteRankBundleCore 𝕜 X`. -/
theorem nonempty_pullbackIso_of_pullbackEquiv [CompleteSpace 𝕜] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x))
    (hΦ : Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
      TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
        p.proj (Φ p.proj p.2)) :
    Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) := by
  let φ_pair : {φ : ∀ x, ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) x →L[𝕜]
      ((f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) x //
      Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (φ p.proj p.2)} :=
    ⟨fun x ↦ (Φ x).toContinuousLinearMap, hΦ⟩
  let hom₀ : VectorBundleCore.CoordinateHom
      (pointIndexedCore 𝕜 (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)))
      (pointIndexedCore 𝕜 (Fin k → 𝕜) ((f₁ : _ → _) *ᵖ (Tautological 𝕜 k))) :=
    pointIndexedCoreHomEquiv.symm φ_pair
  let hom : tautologicalPullbackPointCore f₀ ⟶ tautologicalPullbackPointCore f₁ := hom₀
  have hbij : ∀ x, Bijective (hom₀.fiberMap x) := fun x ↦ by
    let ψ_x :=
      (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) x).trans
        ((Φ x).trans
          (pointIndexedCoreFiberEquiv 𝕜 (Fin k → 𝕜)
            ((f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) x).symm)
    have hfib : ⇑(hom₀.fiberMap x) = ⇑ψ_x :=
      funext (pointIndexedCoreHomEquiv_symm_fiberMap φ_pair x)
    rw [hfib]
    exact ψ_x.bijective
  have : IsIso hom := (FiniteRankBundleCore.isIso_iff_bijective hom).2 hbij
  exact ⟨(tautologicalPullbackIso f₀).trans ((asIso hom).trans (tautologicalPullbackIso f₁).symm)⟩

/-- Conversely, an isomorphism in `FiniteRankBundleCore 𝕜 X` between two pullbacks of
`tautologicalCore 𝕜 k` yields a continuous fibrewise linear equivalence between the actual pullback
bundles. -/
theorem exists_pullbackEquiv_of_pullbackIso [CompleteSpace 𝕜] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)}
    (α : (tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :
    ∃ Φ : ∀ x, Tautological 𝕜 k (f₀ x) ≃L[𝕜] Tautological 𝕜 k (f₁ x),
      Continuous fun p : TotalSpace (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) ↦
        TotalSpace.mk' (Fin k → 𝕜) (E := (f₁ : _ → _) *ᵖ (Tautological 𝕜 k))
          p.proj (Φ p.proj p.2) := by
  let β : tautologicalPullbackPointCore f₀ ≅ tautologicalPullbackPointCore f₁ :=
    (tautologicalPullbackIso f₀).symm.trans (α.trans (tautologicalPullbackIso f₁))
  let β_hom : VectorBundleCore.CoordinateHom
      (pointIndexedCore 𝕜 (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)))
      (pointIndexedCore 𝕜 (Fin k → 𝕜) ((f₁ : _ → _) *ᵖ (Tautological 𝕜 k))) := β.hom
  let β_inv : VectorBundleCore.CoordinateHom
      (pointIndexedCore 𝕜 (Fin k → 𝕜) ((f₁ : _ → _) *ᵖ (Tautological 𝕜 k)))
      (pointIndexedCore 𝕜 (Fin k → 𝕜) ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k))) := β.inv
  let g := pointIndexedCoreHomEquiv β_hom
  let g_inv := pointIndexedCoreHomEquiv β_inv
  have hleft (x : X) (v : ((f₀ : _ → _) *ᵖ (Tautological 𝕜 k)) x) :
      g_inv.1 x (g.1 x v) = v := by
    change ((g_inv.1 x).comp (g.1 x)) v = v
    rw [← pointIndexedCoreHomEquiv_comp β_inv β_hom x]
    have hid : β_inv.comp β_hom = VectorBundleCore.CoordinateHom.id _ := β.hom_inv_id
    rw [hid, pointIndexedCoreHomEquiv_id, ContinuousLinearMap.id_apply]
  have hright (x : X) (w : ((f₁ : _ → _) *ᵖ (Tautological 𝕜 k)) x) :
      g.1 x (g_inv.1 x w) = w := by
    change ((g.1 x).comp (g_inv.1 x)) w = w
    rw [← pointIndexedCoreHomEquiv_comp β_hom β_inv x]
    have hid : β_hom.comp β_inv = VectorBundleCore.CoordinateHom.id _ := β.inv_hom_id
    rw [hid, pointIndexedCoreHomEquiv_id, ContinuousLinearMap.id_apply]
  exact ⟨fun x ↦ ContinuousLinearEquiv.equivOfInverse (g.1 x) (g_inv.1 x) (hleft x) (hright x),
    g.2⟩

/-- Over a complete scalar field, any family of classifying coordinates `j` on `A.core.Fiber` for a
rank-`k` core `A : FiniteRankBundleCore 𝕜 X` canonically identifies the pulled-back universal core
`(tautologicalCore 𝕜 k).pullback (hj.classifyContinuousMap hk)` with `A`. -/
def tautologicalPullbackIsoOfClassifyingCoordinates [CompleteSpace 𝕜] {k : ℕ}
    {A : FiniteRankBundleCore 𝕜 X} (hA : A.rank = k)
    {j : ∀ x, A.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.rank → 𝕜) A.core.Fiber j)
    (hk : Module.finrank 𝕜 (Fin A.rank → 𝕜) = k := (Module.finrank_fin_fun 𝕜).trans hA) :
    (tautologicalCore 𝕜 k).pullback (hj.classifyContinuousMap hk) ≅ A := by
  subst hA
  let f := hj.classifyContinuousMap hk
  let hclass := hj.classifyTautologicalHomeomorph hk
  let hP := pointIndexedCoreHomeomorph 𝕜 (Fin A.rank → 𝕜)
    ((f : _ → _) *ᵖ (Tautological 𝕜 A.rank))
  let eP := pointIndexedCoreFiberEquiv 𝕜 (Fin A.rank → 𝕜)
    ((f : _ → _) *ᵖ (Tautological 𝕜 A.rank))
  let isoA : A ≅ tautologicalPullbackPointCore f :=
    coreIsoOfContinuousEquiv
      (fun x ↦ (hj.classifyTautologicalEquiv hk x).trans (eP x).symm)
      ((hP.symm.continuous.comp hclass.continuous).congr fun p ↦ by
        rcases p with ⟨x, v⟩
        dsimp only [Function.comp_def, hP, hclass]
        rw [hj.classifyTautologicalHomeomorph_apply hk, pointIndexedCoreHomeomorph_symm_apply]
        rfl)
  exact (tautologicalPullbackIso f).trans isoA.symm

/-- Over a complete normed `ℝ`-algebra field and a paracompact normal base `X`, every object
`A : FiniteRankBundleCore 𝕜 X` of rank `k` is isomorphic to `(tautologicalCore 𝕜 k).pullback f` for
some continuous map `f : C(X, infiniteGrassmannian 𝕜 k)`. -/
theorem exists_tautologicalPullbackIso [CompleteSpace 𝕜] [NormedAlgebra ℝ 𝕜]
    [ParacompactSpace X] [NormalSpace X] {k : ℕ}
    (A : FiniteRankBundleCore 𝕜 X) (hA : A.rank = k) :
    ∃ f : C(X, infiniteGrassmannian 𝕜 k),
      Nonempty ((tautologicalCore 𝕜 k).pullback f ≅ A) :=
  let ⟨_, hj⟩ := exists_isClassifyingCoordinates (𝕜 := 𝕜) (X := X)
    (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  ⟨_, ⟨tautologicalPullbackIsoOfClassifyingCoordinates hA hj⟩⟩

end CoreComparisons

section Bijection

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [TopologicalSpace X]

/-- Over `RCLike 𝕜` and a paracompact `R₁` space `X` (in particular any paracompact Hausdorff
space), two continuous maps `f₀, f₁ : C(X, infiniteGrassmannian 𝕜 k)` are homotopic if and only if
the pulled-back cores `(tautologicalCore 𝕜 k).pullback f₀` and `(tautologicalCore 𝕜 k).pullback f₁`
are isomorphic in `FiniteRankBundleCore 𝕜 X`. -/
theorem homotopic_iff_nonempty_pullbackIso [ParacompactSpace X] [R1Space X] {k : ℕ}
    {f₀ f₁ : C(X, infiniteGrassmannian 𝕜 k)} :
    f₀.Homotopic f₁ ↔
      Nonempty ((tautologicalCore 𝕜 k).pullback f₀ ≅ (tautologicalCore 𝕜 k).pullback f₁) :=
  homotopic_iff_exists_pullbackEquiv.trans
    ⟨fun ⟨Φ, hΦ⟩ ↦ nonempty_pullbackIso_of_pullbackEquiv Φ hΦ,
     fun ⟨α⟩ ↦ exists_pullbackEquiv_of_pullbackIso α⟩

variable (𝕜 X) in
/-- **Universal vector bundle classification (`BO(k)` / `BU(k)`).**
Over `ℝ` or `ℂ` (more generally any `RCLike 𝕜`) and a paracompact `R₁` base `X` (for instance any
paracompact Hausdorff space, since `ParacompactSpace` + `R1Space` implies `NormalSpace`), pulling
back `tautologicalCore 𝕜 k` induces a bijection from homotopy classes of maps
`C(X, infiniteGrassmannian 𝕜 k)` to isomorphism classes of rank-`k` vector bundles in
`FiniteRankBundleCore 𝕜 X`. Both `X = Empty` and `k = 0` are included without side conditions. -/
def classificationEquiv [ParacompactSpace X] [R1Space X] (k : ℕ) :
    Quotient ⟨ContinuousMap.Homotopic (X := X) (Y := infiniteGrassmannian 𝕜 k),
        ContinuousMap.Homotopic.equivalence⟩ ≃
      Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _)) :=
  Equiv.ofBijective
    (Quotient.map
      (sa := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
      (sb := (CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap Subtype.val)
      (fun f : C(X, infiniteGrassmannian 𝕜 k) ↦
        (⟨(tautologicalCore 𝕜 k).pullback f, rfl⟩ : {A : FiniteRankBundleCore 𝕜 X // A.rank = k}))
      fun _ _ h ↦ homotopic_iff_nonempty_pullbackIso.1 h)
    ⟨Quotient.ind₂ fun _ _ h ↦
        Quotient.sound (homotopic_iff_nonempty_pullbackIso.2 (Quotient.exact h)),
     Quotient.ind fun A ↦
        let ⟨f, hf⟩ := exists_tautologicalPullbackIso A.1 A.2
        ⟨Quotient.mk _ f, Quotient.sound hf⟩⟩

@[simp]
theorem classificationEquiv_mk [ParacompactSpace X] [R1Space X] (k : ℕ)
    (f : C(X, infiniteGrassmannian 𝕜 k)) :
    classificationEquiv 𝕜 X k (Quotient.mk _ f) =
      Quotient.mk _ ⟨(tautologicalCore 𝕜 k).pullback f, rfl⟩ := (rfl)

/-- Inverse characterization of `classificationEquiv`: the inverse sends the isomorphism class of a
rank-`k` bundle core `A` to the homotopy class of the classifying map associated to any classifying
coordinates `j` on `A.core.Fiber`. -/
theorem classificationEquiv_symm_mk_of_isClassifyingCoordinates [ParacompactSpace X] [R1Space X]
    {k : ℕ} (A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k})
    {j : ∀ x, A.1.core.Fiber x →ₗ[𝕜] (ℕ →₀ 𝕜)}
    (hj : IsClassifyingCoordinates 𝕜 (Fin A.1.rank → 𝕜) A.1.core.Fiber j)
    (hk : Module.finrank 𝕜 (Fin A.1.rank → 𝕜) = k := (Module.finrank_fin_fun 𝕜).trans A.2) :
    (classificationEquiv 𝕜 X k).symm (Quotient.mk _ A) =
      Quotient.mk _ (hj.classifyContinuousMap hk) := by
  apply (classificationEquiv 𝕜 X k).injective
  rw [Equiv.apply_symm_apply, classificationEquiv_mk]
  exact Quotient.sound ⟨(tautologicalPullbackIsoOfClassifyingCoordinates A.2 hj hk).symm⟩

/-- Pullback of isomorphism classes of rank-`k` vector-bundle cores along a continuous map
`g : C(X', X)`. -/
def pullbackRankClass {X' : Type*} [TopologicalSpace X'] (g : C(X', X)) (k : ℕ) :
    Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _)) →
      Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X')).comap
        (Subtype.val : {A : FiniteRankBundleCore 𝕜 X' // A.rank = k} → _)) :=
  Quotient.map
    (sa := (CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap Subtype.val)
    (sb := (CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X')).comap Subtype.val)
    (fun A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} ↦
      (⟨A.1.pullback g, A.2⟩ : {A : FiniteRankBundleCore 𝕜 X' // A.rank = k}))
    fun _ _ ⟨α⟩ ↦ ⟨(FiniteRankBundleCore.pullbackFunctor g).mapIso α⟩

@[simp]
theorem pullbackRankClass_mk {X' : Type*} [TopologicalSpace X'] (g : C(X', X)) (k : ℕ)
    (A : {A : FiniteRankBundleCore 𝕜 X // A.rank = k}) :
    pullbackRankClass g k (Quotient.mk _ A) = Quotient.mk _ ⟨A.1.pullback g, A.2⟩ := (rfl)

/-- Naturality of `classificationEquiv`: precomposing a classifying map with `g : C(X', X)`
corresponds to pulling back the classified rank-`k` bundle core along `g`. -/
theorem classificationEquiv_comp {X' : Type*} [TopologicalSpace X']
    [ParacompactSpace X] [R1Space X] [ParacompactSpace X'] [R1Space X']
    (g : C(X', X)) (k : ℕ) (f : C(X, infiniteGrassmannian 𝕜 k)) :
    classificationEquiv 𝕜 X' k (Quotient.mk _ (f.comp g)) =
      pullbackRankClass g k (classificationEquiv 𝕜 X k (Quotient.mk _ f)) := (rfl)

/-- Contravariant naturality of `(classificationEquiv 𝕜 X k).symm`: pulling back a rank-`k` bundle
class along `g : C(X', X)` corresponds to precomposing its classifying homotopy class with `g`. -/
theorem classificationEquiv_symm_pullbackRankClass {X' : Type*} [TopologicalSpace X']
    [ParacompactSpace X] [R1Space X] [ParacompactSpace X'] [R1Space X']
    (g : C(X', X)) (k : ℕ)
    (c : Quotient ((CategoryTheory.isIsomorphicSetoid (FiniteRankBundleCore 𝕜 X)).comap
      (Subtype.val : {A : FiniteRankBundleCore 𝕜 X // A.rank = k} → _))) :
    (classificationEquiv 𝕜 X' k).symm (pullbackRankClass g k c) =
      Quotient.map
        (sa := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
        (sb := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩)
        (fun f : C(X, infiniteGrassmannian 𝕜 k) ↦ f.comp g)
        (fun _ _ h ↦ h.comp (.refl g))
        ((classificationEquiv 𝕜 X k).symm c) := by
  rcases (classificationEquiv 𝕜 X k).surjective c with ⟨q, rfl⟩
  revert q
  refine Quotient.ind fun f ↦ ?_
  rw [← classificationEquiv_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

end Bijection

end infiniteGrassmannian

end SmallClassification

end TauCeti
