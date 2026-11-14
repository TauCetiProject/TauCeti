/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import Mathlib.Geometry.Manifold.HasGroupoid
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology

/-!
# Top and higher singular homology of noncompact manifolds

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary, and let `N` be a module over a ring `Λ`. This file
proves that `Hₖ(M; N)` vanishes for every `k > n` without any compactness hypothesis on `M`
(`TauCeti.isZero_singularHomology_of_finrank_lt`), and that `Hₙ(M; N)` vanishes whenever no
connected component of `M` is compact
(`TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`). In particular, if
`M` is connected and noncompact then `Hₖ(M; N) = 0` for all `k ≥ n`
(`TauCeti.isZero_singularHomology_of_not_compactSpace`), so a connected boundaryless `n`-manifold
with nonzero homology in some degree `k ≥ n` is compact
(`TauCeti.compactSpace_of_not_isZero_singularHomology`). Likewise every proper open subset of a
connected `n`-manifold has vanishing homology in degrees `k ≥ n`
(`TauCeti.isZero_singularHomology_of_isOpen_ne_univ`).

The proof follows Hatcher's compact-exhaustion argument using local homology along compact sets:

* **Detection on compact subsets.** Suppose `Hₖ₊₁(M, M ∖ D; N) = 0` for every compact `D ⊆ M`. Any
  class `α ∈ Hₖ(M; N)` comes from `Hₖ(K; N)` for some compact `K ⊆ M`
  (`TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq`). Choosing a compact neighbourhood
  `L` of `K` with interior `U ⊇ K`, if the image of `α` in `Hₖ(M, M ∖ L; N)` vanishes then `α`
  also comes from `Hₖ(M ∖ L; N)`. Inside `M ∖ (L ∖ U)`, the disjoint open sets `U` and `M ∖ L`
  cover the space, so Mayer–Vietoris makes `Hₖ(U; N) ⊞ Hₖ(M ∖ L; N) ⟶ Hₖ(M ∖ (L ∖ U); N)` a
  monomorphism, while `Hₖ₊₁(M, M ∖ (L ∖ U); N) = 0` makes `Hₖ(M ∖ (L ∖ U); N) ⟶ Hₖ(M; N)` a
  monomorphism. Comparing the lifts of `α` to `U` and to `M ∖ L` forces `α = 0`
  (`TauCeti.eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero`).
* **Degrees above `n`.** By `TauCeti.isZero_localHomology_of_isCompact`, `Hₖ(M, M ∖ L; N)` and
  `Hₖ₊₁(M, M ∖ D; N)` both vanish for `k > n`, giving `Hₖ(M; N) = 0`.
* **Top degree on noncompact components.** A class `α` pushed forward from compact `K` vanishes in
  `Hₙ(M, M ∖ {x₀}; N)` at every point `x₀ ∉ K`
  (`TauCeti.singularHomologyToLocalHomology_map_subtypeVal_eq_zero_of_notMem`). If the connected
  component of `x` is noncompact, then since `M` is locally path-connected that component is a
  closed path component, so it cannot lie inside `K`; transporting vanishing along a path from a
  point `x₀ ∉ K` of the component to `x` via `TauCeti.localHomologySystemCone` shows that `α`
  vanishes in `Hₙ(M, M ∖ {x}; N)` for every `x ∈ M`. Pointwise detection along compact sets
  (`TauCeti.eq_zero_of_forall_localHomologyRestriction_eq_zero`) then kills the image of `α` in
  `Hₙ(M, M ∖ L; N)` for every compact `L`, and the first step concludes `α = 0`.

## Main results

* `TauCeti.eq_zero_of_disjoint_isOpen_of_isZero_localHomology`: if `M ∖ D = U ∪ V` is a union of
  disjoint open subsets `U, V ⊆ M` and `Hₖ₊₁(M, M ∖ D; N) = 0`, any class in `Hₖ(M; N)` coming
  from both `Hₖ(U; N)` and `Hₖ(V; N)` is zero.
* `TauCeti.eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero`: in a locally compact Hausdorff
  space whose compact subsets have vanishing local homology in degree `k + 1`, a class in
  `Hₖ(M; N)` vanishing in `Hₖ(M, M ∖ L; N)` for all compact `L` is zero.
* `TauCeti.isZero_singularHomology_of_finrank_lt`: `Hₖ(M; N) = 0` for `k > n` on any Hausdorff
  boundaryless `n`-manifold.
* `TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`: `Hₖ(M; N) = 0` for
  `k ≥ n` when every connected component of `M` is noncompact.
* `TauCeti.isZero_singularHomology_of_not_compactSpace` and
  `TauCeti.compactSpace_of_not_isZero_singularHomology`: for connected `M`, noncompactness implies
  `Hₖ(M; N) = 0` for `k ≥ n`, and nonvanishing in some degree `k ≥ n` implies `CompactSpace M`.
* `TauCeti.isZero_singularHomology_of_isOpen_ne_univ`: for connected `M` and proper open `U ⊂ M`,
  `Hₖ(U; N) = 0` for `k ≥ n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology

universe w

namespace TauCeti

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)

section TopologicalSpace

variable {M : Type w} [TopologicalSpace M]

/-- `TauCeti.singularHomologyToLocalHomology` at `x` agrees pointwise with the relative quotient
map from `Hₖ(M; N)` to `Hₖ(M, M ∖ {x}; N)`. -/
theorem singularHomologyToLocalHomology_apply_eq_singularHomologyπ (x : M) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)) :
    singularHomologyToLocalHomology N x k α =
      (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} Λ) N k α := by
  have h := TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id
    N (X := TopCat.of M) (S := ({x} : Set M)ᶜ) (S' := univᶜ)
    (compl_subset_compl.2 (subset_univ {x})) k
  rw [← localHomologyRestriction_def N (subset_univ {x}) k] at h
  exact (singularHomologyToLocalHomology_apply N x α).trans
    ((ConcreteCategory.comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom h α))

/-- Restricting the image of `α ∈ Hₖ(M; N)` in `Hₖ(M, M ∖ S; N)` to a point `x ∈ S` agrees with
`TauCeti.singularHomologyToLocalHomology` at `x`. -/
theorem localHomologyRestriction_singularHomologyπ_apply {S : Set M} {x : M} (hx : x ∈ S) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)) :
    localHomologyRestriction N (singleton_subset_iff.2 hx) k
        ((TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ
          (C := ModuleCat.{w} Λ) N k α) =
      singularHomologyToLocalHomology N x k α := by
  have h := TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id
    N (X := TopCat.of M) (S := ({x} : Set M)ᶜ) (S' := Sᶜ)
    (compl_subset_compl.2 (singleton_subset_iff.2 hx)) k
  rw [← localHomologyRestriction_def] at h
  exact ((ConcreteCategory.comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom h α)).trans
    (singularHomologyToLocalHomology_apply_eq_singularHomologyπ N x α).symm

/-- A class pushed forward from a subset `K ⊆ M` vanishes in the local homology at every point
outside `K`. -/
theorem singularHomologyToLocalHomology_map_subtypeVal_eq_zero_of_notMem {K : Set M} {x : M}
    (hx : x ∉ K) {k : ℕ}
    (α : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of K)) :
    singularHomologyToLocalHomology N x k
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
          (TopCat.ofHom (ContinuousMap.subtypeVal K)) α) = 0 := by
  let P := TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))
  let j : TopCat.of K ⟶ P.snd := TopCat.ofHom ⟨fun y ↦ ⟨y.1, fun h ↦ hx (h ▸ y.2)⟩, by fun_prop⟩
  have hj : j ≫ P.map = TopCat.ofHom (ContinuousMap.subtypeVal K) := by ext; rfl
  have hmap : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal K)))
        N k =
      SSet.homologyMap (TopCat.toSSet.map j) N k ≫
        SSet.homologyMap (TopCat.toSSet.map P.map) N k :=
    (congrArg (fun f : TopCat.of K ⟶ P.fst ↦ SSet.homologyMap (TopCat.toSSet.map f) N k)
      hj.symm).trans (by rw [TopCat.toSSet.map_comp, SSet.homologyMap_comp])
  have hzero : (SSet.homologyMap (TopCat.toSSet.map j) N k ≫
      SSet.homologyMap (TopCat.toSSet.map P.map) N k ≫
        P.singularHomologyπ (C := ModuleCat.{w} Λ) N k) α = 0 := by
    rw [P.homologyMap_comp_singularHomologyπ, Limits.comp_zero]
    rfl
  have hcomp : (SSet.homologyMap
        (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal K))) N k ≫
      P.singularHomologyπ (C := ModuleCat.{w} Λ) N k) α = 0 :=
    (ConcreteCategory.congr_hom (hmap =≫ P.singularHomologyπ (C := ModuleCat.{w} Λ) N k) α).trans
      ((ConcreteCategory.congr_hom (Category.assoc _ _ _) α).trans hzero)
  exact (singularHomologyToLocalHomology_apply_eq_singularHomologyπ N x _).trans
    ((ConcreteCategory.comp_apply _ _ _).symm.trans hcomp)

/-- If `M ∖ D = U ∪ V` is decomposed into disjoint open subsets `U` and `V` of `M` and
`Hₖ₊₁(M, M ∖ D; N) = 0`, then any class `α ∈ Hₖ(M; N)` lying in the images of both
`Hₖ(U; N) ⟶ Hₖ(M; N)` and `Hₖ(V; N) ⟶ Hₖ(M; N)` is zero. -/
theorem eq_zero_of_disjoint_isOpen_of_isZero_localHomology {D U V : Set M}
    (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V) (hUVD : U ∪ V = Dᶜ) {k : ℕ}
    (hhigh : IsZero (localHomology N D (k + 1)))
    {α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hU : ∃ γU, SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U))) N k γU = α)
    (hV : ∃ γV, SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V))) N k γV = α) :
    α = 0 := by
  obtain ⟨γU, hγU⟩ := hU
  obtain ⟨γV, hγV⟩ := hV
  set W : Set M := Dᶜ
  set U' : Set (TopCat.of W) := Subtype.val ⁻¹' U
  set V' : Set (TopCat.of W) := Subtype.val ⁻¹' V
  have hU'o : IsOpen U' := hUo.preimage continuous_subtype_val
  have hV'o : IsOpen V' := hVo.preimage continuous_subtype_val
  have hUV' : U' ∪ V' = univ := eq_univ_of_forall fun x ↦ hUVD.symm.subset x.2
  have : IsEmpty (TopCat.of ↥(U' ∩ V')) := ⟨fun ⟨_, hxU, hxV⟩ ↦ hUV.le_bot ⟨hxU, hxV⟩⟩
  have : (TopCat.toSSet.obj (TopCat.of ↥(U' ∩ V'))).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).mp fun ⟨σ⟩ ↦
      isEmptyElim (TopCat.toSSetObj₀Equiv σ)
  have hZeroUV : IsZero ((TopCat.toSSet.obj (TopCat.of ↥(U' ∩ V'))).homology N k) :=
    SSet.isZero_homology_of_hasDimensionLT (TopCat.toSSet.obj (TopCat.of ↥(U' ∩ V'))) N k 0
  have hMV := (TopCat.mayerVietoris_exact₂ N hU'o hV'o hUV' k).mono_g (hZeroUV.eq_of_src _ _)
  let HU := (TopCat.toSSet.obj (TopCat.of ↥U')).homology N k
  let HV := (TopCat.toSSet.obj (TopCat.of ↥V')).homology N k
  let jU : TopCat.of ↥U ⟶ TopCat.of ↥U' :=
    TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, hUVD.subset (subset_union_left x.2)⟩, x.2⟩, by fun_prop⟩
  let jV : TopCat.of ↥V ⟶ TopCat.of ↥V' :=
    TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, hUVD.subset (subset_union_right x.2)⟩, x.2⟩, by fun_prop⟩
  let δU : HU := SSet.homologyMap (TopCat.toSSet.map jU) N k γU
  let δV : HV := SSet.homologyMap (TopCat.toSSet.map jV) N k γV
  have hfacU : jU ≫ TopCat.ofHom (ContinuousMap.subtypeVal U') ≫
      TopCat.ofHom (ContinuousMap.subtypeVal W) = TopCat.ofHom (ContinuousMap.subtypeVal U) := by
    ext; rfl
  have hfacV : jV ≫ TopCat.ofHom (ContinuousMap.subtypeVal V') ≫
      TopCat.ofHom (ContinuousMap.subtypeVal W) = TopCat.ofHom (ContinuousMap.subtypeVal V) := by
    ext; rfl
  have hU'α : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal W))) N k
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U')))
        N k δU) = α := by
    dsimp only [δU]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp,
      ← SSet.homologyMap_comp, ← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, hfacU]
    exact hγU
  have hV'α : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal W))) N k
      (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V')))
        N k δV) = α := by
    dsimp only [δV]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp,
      ← SSet.homologyMap_comp, ← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, hfacV]
    exact hγV
  have hMonoW : Mono (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal W))) N k) :=
    (TopPair.ofSubset (Dᶜ : Set (TopCat.of M))).mono_homologyMap_map_of_isZero N hhigh
  have hEqW := (ModuleCat.mono_iff_injective _).1 hMonoW (hU'α.trans hV'α.symm)
  have hMVzero : SSet.mayerVietorisFromBiprod N
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U')))
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V'))) k
      ((biprod.inl : HU ⟶ HU ⊞ HV) δU - (biprod.inr : HV ⟶ HU ⊞ HV) δV) = 0 := by
    rw [map_sub, ← ConcreteCategory.comp_apply biprod.inl, SSet.inl_mayerVietorisFromBiprod,
      ← ConcreteCategory.comp_apply biprod.inr, SSet.inr_mayerVietorisFromBiprod]
    exact sub_eq_zero.2 hEqW
  have hbiprod := (ModuleCat.mono_iff_injective _).1 hMV (hMVzero.trans (map_zero _).symm)
  have hδU : δU = 0 := by
    have h := congrArg (biprod.fst : HU ⊞ HV ⟶ HU) hbiprod
    rw [map_sub, map_zero, ← ConcreteCategory.comp_apply biprod.inl, biprod.inl_fst,
      ConcreteCategory.id_apply, ← ConcreteCategory.comp_apply biprod.inr, biprod.inr_fst] at h
    exact sub_eq_zero.1 h
  rw [← hU'α, hδU, map_zero, map_zero]

/-- **Compact-exhaustion vanishing criterion.** In a locally compact Hausdorff space `M` where
`Hₖ₊₁(M, M ∖ D; N) = 0` for every compact `D ⊆ M`, a class `α ∈ Hₖ(M; N)` whose image in
`Hₖ(M, M ∖ L; N)` vanishes for every compact `L ⊆ M` is zero. -/
theorem eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero
    [T2Space M] [WeaklyLocallyCompactSpace M] {k : ℕ}
    (hhigh : ∀ D : Set M, IsCompact D → IsZero (localHomology N D (k + 1)))
    (α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ))
    (hπ : ∀ L : Set M, IsCompact L →
      (TopPair.ofSubset (Lᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} Λ) N k α = 0) :
    α = 0 := by
  obtain ⟨K, hK, αK, hαK⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq N k α
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  have hDc : IsCompact (L \ interior L) := hL.inter_right isOpen_interior.isClosed_compl
  have hUVD : interior L ∪ Lᶜ = (L \ interior L)ᶜ := by
    rw [sdiff_eq, compl_inter, compl_compl, union_comm]
  obtain ⟨β, hβ⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset (Lᶜ : Set (TopCat.of M))).singularHomology_exact_space N k) α (hπ L hL)
  let αK' : ((TopCat.toSSet.obj (TopCat.of ↥K)).homology N k : ModuleCat.{w} Λ) := αK
  refine eq_zero_of_disjoint_isOpen_of_isZero_localHomology N isOpen_interior
    hL.isClosed.isOpen_compl
    (disjoint_left.2 fun _ hxU hxLc ↦ hxLc (interior_subset hxU)) hUVD (hhigh _ hDc)
    ⟨SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion hKL))) N k αK', ?_⟩
    ⟨β, hβ⟩
  refine (?_ : _ = SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal K))) N k αK').trans hαK
  rw [← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← TopCat.toSSet.map_comp]
  rfl

end TopologicalSpace

section SameUniverseModel

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

private theorem singularHomologyToLocalHomology_eq_zero_of_joined_aux (E : Type w)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {x y : M}
    (hxy : Joined x y) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hα : singularHomologyToLocalHomology N x k α = 0) :
    singularHomologyToLocalHomology N y k α = 0 := by
  let f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y :=
    Path.Homotopic.Quotient.mk hxy.somePath
  let β₀ := ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
    (C := ModuleCat.{w} Λ) N k).hom α
  have hx₀ : (localHomologySystemCone N M E k).π.app (.mk x) β₀ = 0 :=
    (singularHomologyToLocalHomology_apply N x α).symm.trans hα
  have hw := ConcreteCategory.congr_hom ((localHomologySystemCone N M E k).w f) β₀
  exact (singularHomologyToLocalHomology_apply N y α).trans
    (hw.symm.trans ((ConcreteCategory.comp_apply _ _ _).trans
      ((congrArg ((localHomologySystem N M E k).map f) hx₀).trans (map_zero _))))

private theorem isZero_singularHomology_of_finrank_lt_aux {n k : ℕ} (hn : finrank ℝ E = n)
    (hk : n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun α β ↦ sub_eq_zero.1 ?_⟩
  refine eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero N
    (fun D hD ↦ isZero_localHomology_of_isCompact N hn hD (Nat.lt_succ_of_lt hk)) (α - β)
    fun L hL ↦ (ModuleCat.subsingleton_of_isZero
      (isZero_localHomology_of_isCompact N hn hL hk)).elim _ _

private theorem isZero_singularHomology_top_of_forall_not_isCompact_connectedComponent_aux {n : ℕ}
    (hn : finrank ℝ E = n) (hcomp : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) n).obj N).obj
      (TopCat.of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  have := ChartedSpace.locallyPathConnectedSpace E M
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun α β ↦ sub_eq_zero.1 ?_⟩
  set γ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ) := α - β
  obtain ⟨K, hK, γK, hγK⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq N n γ
  -- Every point `x` can be joined to a point `x₀ ∉ K` because its closed path component is not
  -- compact, hence not contained in `K`.
  have hloc (x : M) : singularHomologyToLocalHomology N x n γ = 0 := by
    have hnotSub : ¬ connectedComponent x ⊆ K :=
      fun hsub ↦ hcomp x (hK.of_isClosed_subset isClosed_connectedComponent hsub)
    obtain ⟨x₀, hx₀c, hx₀K⟩ := not_subset.1 hnotSub
    have hjoined : Joined x₀ x :=
      (mem_pathComponent_iff.1 (pathComponent_eq_connectedComponent x ▸ hx₀c)).symm
    refine singularHomologyToLocalHomology_eq_zero_of_joined_aux N E hjoined ?_
    rw [← hγK]
    exact singularHomologyToLocalHomology_map_subtypeVal_eq_zero_of_notMem N hx₀K γK
  refine eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero N
    (fun D hD ↦ isZero_localHomology_of_isCompact N hn hD (Nat.lt_succ_self n)) γ fun L hL ↦ ?_
  refine eq_zero_of_forall_localHomologyRestriction_eq_zero N hn hL _ fun x hx ↦ ?_
  rw [localHomologyRestriction_singularHomologyπ_apply N hx]
  exact hloc x

end SameUniverseModel

section Manifold

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **Vanishing in local homology transports along paths.** On a Hausdorff boundaryless manifold,
if `α ∈ Hₖ(M; N)` vanishes in the local homology `Hₖ(M, M ∖ {x}; N)`, then it vanishes in
`Hₖ(M, M ∖ {y}; N)` for every point `y` in the path component of `x`. -/
theorem singularHomologyToLocalHomology_eq_zero_of_joined (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {x y : M} (hxy : Joined x y) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hα : singularHomologyToLocalHomology N x k α = 0) :
    singularHomologyToLocalHomology N y k α = 0 := by
  let E' := EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ E)))
  let L : E ≃L[ℝ] E' :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_ulift_fin.{w} (finrank ℝ E)).symm
  let _ : ChartedSpace E' E := L.toHomeomorph.isOpenEmbedding.singletonChartedSpace
  let _ : ChartedSpace E' M := ChartedSpace.comp E' E M
  exact singularHomologyToLocalHomology_eq_zero_of_joined_aux N E' hxy hα

/-- **Singular homology of a boundaryless manifold vanishes above the dimension.** For any
Hausdorff space `M` modelled on a real normed space `E` of finite dimension `n`, compact or not,
`Hₖ(M; N) = 0` for `k > n`. -/
theorem isZero_singularHomology_of_finrank_lt {n k : ℕ} (hn : finrank ℝ E = n) (hk : n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  let E' := EuclideanSpace ℝ (ULift.{w} (Fin n))
  let L : E ≃L[ℝ] E' :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_ulift_fin.{w} n).symm)
  let _ : ChartedSpace E' E := L.toHomeomorph.isOpenEmbedding.singletonChartedSpace
  let _ : ChartedSpace E' M := ChartedSpace.comp E' E M
  exact isZero_singularHomology_of_finrank_lt_aux (E := E') N
    (finrank_euclideanSpace_ulift_fin.{w} n) hk

/-- **Top and higher homology vanish when every connected component is noncompact**
(Hatcher, Proposition 3.29). Let `M` be a Hausdorff space modelled on a real normed space of
dimension `n`. If no connected component of `M` is compact, then `Hₖ(M; N) = 0` for all `k ≥ n`. -/
theorem isZero_singularHomology_of_forall_not_isCompact_connectedComponent {n : ℕ}
    (hn : finrank ℝ E = n) (hcomp : ∀ x : M, ¬ IsCompact (connectedComponent x)) {k : ℕ}
    (hk : n ≤ k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  obtain rfl | hk := hk.eq_or_lt
  · let E' := EuclideanSpace ℝ (ULift.{w} (Fin n))
    let L : E ≃L[ℝ] E' :=
      ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_ulift_fin.{w} n).symm)
    let _ : ChartedSpace E' E := L.toHomeomorph.isOpenEmbedding.singletonChartedSpace
    let _ : ChartedSpace E' M := ChartedSpace.comp E' E M
    exact isZero_singularHomology_top_of_forall_not_isCompact_connectedComponent_aux (E := E') N
      (finrank_euclideanSpace_ulift_fin.{w} n) hcomp
  · exact isZero_singularHomology_of_finrank_lt N hn hk

/-- **Top and higher homology of a connected noncompact manifold vanish** (Hatcher,
Proposition 3.29). For a connected noncompact Hausdorff space `M` modelled on a real normed space
of dimension `n`, `Hₖ(M; N) = 0` for every `k ≥ n`. -/
theorem isZero_singularHomology_of_not_compactSpace [ConnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (hM : ¬ CompactSpace M) {k : ℕ} (hk : n ≤ k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  refine isZero_singularHomology_of_forall_not_isCompact_connectedComponent N hn (fun x hc ↦ hM ?_)
    hk
  rw [← isCompact_univ_iff, ← PreconnectedSpace.connectedComponent_eq_univ x]
  exact hc

/-- **Nonzero homology in degree at least the dimension forces compactness.** If a connected
Hausdorff space `M` modelled on a real normed space of dimension `n` has `Hₖ(M; N) ≠ 0` for some
`k ≥ n` and some module `N`, then `M` is compact. -/
theorem compactSpace_of_not_isZero_singularHomology [ConnectedSpace M] {n k : ℕ}
    (hn : finrank ℝ E = n) (hk : n ≤ k)
    (h : ¬ IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M))) :
    CompactSpace M :=
  Classical.byContradiction fun hM ↦ h (isZero_singularHomology_of_not_compactSpace N hn hM hk)

/-- **Homology of a proper open subset of a connected manifold vanishes from the dimension on.**
Let `M` be a connected Hausdorff space modelled on a real normed space of dimension `n`, and let
`U ⊆ M` be a proper open subset (`U ≠ univ`). Then `Hₖ(U; N) = 0` for every `k ≥ n`, even if `U` is
disconnected. -/
theorem isZero_singularHomology_of_isOpen_ne_univ [ConnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) {U : Set M} (hUo : IsOpen U) (hU : U ≠ univ) {k : ℕ} (hk : n ≤ k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of U)) := by
  rcases isEmpty_or_nonempty U with hEmpty | hNonempty
  · have : (TopCat.toSSet.obj (TopCat.of U)).HasDimensionLT 0 :=
      (SSet.notNonempty_iff_hasDimensionLT_zero _).mp fun ⟨σ⟩ ↦
        isEmptyElim (TopCat.toSSetObj₀Equiv σ)
    exact SSet.isZero_homology_of_hasDimensionLT (TopCat.toSSet.obj (TopCat.of U)) N k 0
  · let _ : ChartedSpace M U := hUo.isOpenEmbedding_subtypeVal.singletonChartedSpace
    let _ : ChartedSpace E U := ChartedSpace.comp E M U
    have := ChartedSpace.locallyPathConnectedSpace E U
    refine isZero_singularHomology_of_forall_not_isCompact_connectedComponent (E := E) N hn
      (fun x hc ↦ hU ?_) hk
    have hOpenU : IsOpen (connectedComponent x) := by
      rw [← pathComponent_eq_connectedComponent]
      exact IsOpen.pathComponent x
    have hOpenM : IsOpen (Subtype.val '' connectedComponent x) :=
      hUo.isOpenEmbedding_subtypeVal.isOpenMap _ hOpenU
    have hClosedM : IsClosed (Subtype.val '' connectedComponent x) :=
      (hc.image continuous_subtype_val).isClosed
    have hClopen : IsClopen (Subtype.val '' connectedComponent x) := ⟨hClosedM, hOpenM⟩
    have hUniv : Subtype.val '' connectedComponent x = univ :=
      hClopen.eq_univ ⟨x.1, x, mem_connectedComponent, rfl⟩
    exact univ_subset_iff.1 (hUniv ▸ image_subset_iff.2 fun y _ ↦ y.2)

end Manifold

end TauCeti
