/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Ring.ULift
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients

/-!
# Top and higher singular homology of noncompact manifolds

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary, and let `N` be a module over a ring `Λ`. This file
proves that `Hₖ(M; N)` vanishes for every `k > n` without any compactness hypothesis on `M`
(`TauCeti.isZero_singularHomology_of_finrank_lt`), and that `Hₙ(M; N)` vanishes whenever no
connected component of `M` is compact
(`TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`). In particular, if
`M` is preconnected and noncompact then `Hₖ(M; N) = 0` for all `k ≥ n`
(`TauCeti.isZero_singularHomology_of_not_compactSpace`), so a preconnected boundaryless
`n`-manifold with nonzero homology in some degree `k ≥ n` is compact
(`TauCeti.compactSpace_of_not_isZero_singularHomology`). Likewise every proper open subset of a
preconnected `n`-manifold has vanishing homology in degrees `k ≥ n`
(`TauCeti.isZero_singularHomology_of_isOpen_ne_univ`).

The proof follows Hatcher's compact-exhaustion argument using local homology along compact sets,
followed by restriction of scalars to `ULift ℤ` so that `Λ` can live in any universe:

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
  point `x₀ ∉ K` of the component to `x` via
  `TauCeti.localHomologyRestriction_univ_comp_localHomologyTransport` shows that `α` vanishes in
  `Hₙ(M, M ∖ {x}; N)` for every `x ∈ M`. Pointwise detection along compact sets
  (`TauCeti.eq_zero_of_forall_localHomologyRestriction_eq_zero`) then kills the image of `α` in
  `Hₙ(M, M ∖ L; N)` for every compact `L`, and the first step concludes `α = 0`.

## Main results

* `TauCeti.eq_zero_of_disjoint_isOpen_of_isZero_localHomology`: if `M ∖ D = U ∪ V` is a union of
  disjoint open subsets `U, V ⊆ M` and `Hₖ₊₁(M, M ∖ D; N) = 0`, any class in `Hₖ(M; N)` coming
  from both `Hₖ(U; N)` and `Hₖ(V; N)` is zero.
* `TauCeti.eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero`: in a locally compact Hausdorff
  space whose compact subsets have vanishing local homology in degree `k + 1`, a class in
  `Hₖ(M; N)` vanishing in `Hₖ(M, M ∖ L; N)` for all compact `L` is zero.
* `TauCeti.singularHomologyToLocalHomology_eq_zero_of_joined`: vanishing in local homology
  transports along paths on any Hausdorff boundaryless manifold.
* `TauCeti.isZero_singularHomology_of_finrank_lt`: `Hₖ(M; N) = 0` for `k > n` on any Hausdorff
  boundaryless `n`-manifold.
* `TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`: `Hₖ(M; N) = 0` for
  `k ≥ n` when every connected component of `M` is noncompact.
* `TauCeti.isZero_singularHomology_of_not_compactSpace` and
  `TauCeti.compactSpace_of_not_isZero_singularHomology`: for preconnected `M`, noncompactness
  implies `Hₖ(M; N) = 0` for `k ≥ n`, and nonvanishing in some degree `k ≥ n` implies
  `CompactSpace M`.
* `TauCeti.isZero_singularHomology_of_isOpen_ne_univ`: for preconnected `M` and proper open
  `U ⊂ M`, `Hₖ(U; N) = 0` for `k ≥ n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology

universe w

namespace TauCeti

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)

section TopologicalSpace

variable {M : Type w} [TopologicalSpace M]

/-- Pushing forward along `f : X ⟶ Y` in `singularHomologyFunctor` agrees with `SSet.homologyMap`
under the object identifications `TauCeti.singularHomologyFunctor_obj_obj`. -/
private lemma singularHomologyFunctor_map_comp_eqToHom {X Y : TopCat.{w}} (f : X ⟶ Y) (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map f ≫
        eqToHom (singularHomologyFunctor_obj_obj N k Y) =
      eqToHom (singularHomologyFunctor_obj_obj N k X) ≫
        SSet.homologyMap (TopCat.toSSet.map f) N k := by
  apply eq_of_heq
  rw [comp_eqToHom_heq_iff, heq_eqToHom_comp_iff]
  exact heq_of_eq (singularHomologyFunctor_obj_map N k f)

/-- Every class in `(TopCat.toSSet.obj (TopCat.of M)).homology N k` is pushed forward from a
compact subset, transporting `TauCeti.exists_isCompact_singularHomologyMap_subtypeVal_eq` along
`TauCeti.singularHomologyFunctor_obj_obj` and `TauCeti.singularHomologyFunctor_obj_map`. -/
private lemma exists_isCompact_homologyMap_subtypeVal_eq (k : ℕ)
    (α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)) :
    ∃ (K : Set M) (_ : IsCompact K)
      (αK : ((TopCat.toSSet.obj (TopCat.of K)).homology N k : ModuleCat.{w} Λ)),
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal K))) N k αK =
        α := by
  have hM := singularHomologyFunctor_obj_obj N k (TopCat.of M)
  obtain ⟨K, hK, αK, hαK⟩ :=
    exists_isCompact_singularHomologyMap_subtypeVal_eq N k (eqToHom hM.symm α)
  refine ⟨K, hK, eqToHom (singularHomologyFunctor_obj_obj N k (TopCat.of K)) αK, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← singularHomologyFunctor_map_comp_eqToHom,
    ConcreteCategory.comp_apply, hαK, ← ConcreteCategory.comp_apply, eqToHom_trans,
    eqToHom_refl, ConcreteCategory.id_apply]

/-- If a homology class `α ∈ Hₖ(M; N)` comes from a subset `U ⊆ W`, it also comes from `W` via a
class pushed forward from `Subtype.val ⁻¹' U : Set W`. -/
private lemma exists_homologyMap_preimage_eq_of_subset {U W : Set M} (hUW : U ⊆ W) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hU : ∃ γU, SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U))) N k γU = α) :
    ∃ δU : ((TopCat.toSSet.obj (TopCat.of ↥(Subtype.val ⁻¹' U : Set (TopCat.of W)))).homology
        N k : ModuleCat.{w} Λ),
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal W))) N k
        (SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.subtypeVal
            (Subtype.val ⁻¹' U : Set (TopCat.of W))))) N k δU) = α := by
  obtain ⟨γU, hγU⟩ := hU
  let U' : Set (TopCat.of W) := Subtype.val ⁻¹' U
  let jU : TopCat.of ↥U ⟶ TopCat.of ↥U' :=
    TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, hUW x.2⟩, x.2⟩, by fun_prop⟩
  have hfac : jU ≫ TopCat.ofHom (ContinuousMap.subtypeVal U') ≫
      TopCat.ofHom (ContinuousMap.subtypeVal W) = TopCat.ofHom (ContinuousMap.subtypeVal U) := by
    ext; rfl
  refine ⟨SSet.homologyMap (TopCat.toSSet.map jU) N k γU, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp,
    ← SSet.homologyMap_comp, ← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, hfac]
  exact hγU

/-- On a space `W` covered by two disjoint open subsets `U'` and `V'`, a class in `Hₖ(W; N)`
pushed forward from `U'` and also from `V'` is zero: the Mayer–Vietoris map from the direct sum is
injective because `U' ∩ V'` is empty. -/
private lemma eq_zero_of_disjoint_isOpen_cover {W : TopCat.{w}} {U' V' : Set W}
    (hU'o : IsOpen U') (hV'o : IsOpen V') (hUV'd : Disjoint U' V') (hUV' : U' ∪ V' = univ)
    {k : ℕ}
    {δU : ((TopCat.toSSet.obj (TopCat.of ↥U')).homology N k : ModuleCat.{w} Λ)}
    {δV : ((TopCat.toSSet.obj (TopCat.of ↥V')).homology N k : ModuleCat.{w} Λ)}
    (hEq : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U'))) N k
        δU =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V'))) N k δV) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U'))) N k δU =
      0 := by
  have : IsEmpty (TopCat.of ↥(U' ∩ V')) := ⟨fun ⟨_, hxU, hxV⟩ ↦ hUV'd.le_bot ⟨hxU, hxV⟩⟩
  have hZeroUV : IsZero ((TopCat.toSSet.obj (TopCat.of ↥(U' ∩ V'))).homology N k) := by
    rw [← singularHomologyFunctor_obj_obj]
    exact isZero_singularHomologyFunctor_of_isEmpty N (TopCat.of ↥(U' ∩ V')) k
  have hMV := (TopCat.mayerVietoris_exact₂ N hU'o hV'o hUV' k).mono_g (hZeroUV.eq_of_src _ _)
  let HU := (TopCat.toSSet.obj (TopCat.of ↥U')).homology N k
  let HV := (TopCat.toSSet.obj (TopCat.of ↥V')).homology N k
  have hMVzero : SSet.mayerVietorisFromBiprod N
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U')))
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V'))) k
      ((biprod.inl : HU ⟶ HU ⊞ HV) δU - (biprod.inr : HV ⟶ HU ⊞ HV) δV) = 0 := by
    rw [map_sub, ← ConcreteCategory.comp_apply biprod.inl, SSet.inl_mayerVietorisFromBiprod,
      ← ConcreteCategory.comp_apply biprod.inr, SSet.inr_mayerVietorisFromBiprod]
    exact sub_eq_zero.2 hEq
  have hbiprod := (ModuleCat.mono_iff_injective _).1 hMV (hMVzero.trans (map_zero _).symm)
  have hδU : δU = 0 := by
    have h := congrArg (biprod.fst : HU ⊞ HV ⟶ HU) hbiprod
    rw [map_sub, map_zero, ← ConcreteCategory.comp_apply biprod.inl, biprod.inl_fst,
      ConcreteCategory.id_apply, ← ConcreteCategory.comp_apply biprod.inr, biprod.inr_fst] at h
    exact sub_eq_zero.1 h
  rw [hδU, map_zero]

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
  -- Lift the pushforwards from `U` and `V` to the disjoint open cover of `W = M \ D`.
  obtain ⟨δU, hU'α⟩ := exists_homologyMap_preimage_eq_of_subset N
    (subset_union_left.trans hUVD.subset) hU
  obtain ⟨δV, hV'α⟩ := exists_homologyMap_preimage_eq_of_subset N
    (subset_union_right.trans hUVD.subset) hV
  -- Vanishing of `Hₖ₊₁(M, W; N)` makes `Hₖ(W; N) ⟶ Hₖ(M; N)` injective, so the lifts agree on `W`.
  have hMonoW : Mono (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (Dᶜ : Set M)))) N k) :=
    (TopPair.ofSubset (Dᶜ : Set (TopCat.of M))).mono_homologyMap_map_of_isZero N hhigh
  have hEqW := (ModuleCat.mono_iff_injective _).1 hMonoW (hU'α.trans hV'α.symm)
  -- Mayer–Vietoris on the disjoint open cover of `W` then kills the class on `W`, hence `α`.
  have hZero := eq_zero_of_disjoint_isOpen_cover N (W := TopCat.of ↥(Dᶜ : Set M))
    (hUo.preimage continuous_subtype_val) (hVo.preimage continuous_subtype_val)
    (hUV.preimage _) (eq_univ_of_forall fun x ↦ hUVD.symm.subset x.2) hEqW
  rw [← hU'α, hZero, map_zero]

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
  obtain ⟨K, hK, αK, hαK⟩ := exists_isCompact_homologyMap_subtypeVal_eq N k α
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  have hDc : IsCompact (L \ interior L) := hL.inter_right isOpen_interior.isClosed_compl
  have hUVD : interior L ∪ Lᶜ = (L \ interior L)ᶜ := by
    rw [sdiff_eq, compl_inter, compl_compl, union_comm]
  obtain ⟨β, hβ⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset (Lᶜ : Set (TopCat.of M))).singularHomology_exact_space N k) α (hπ L hL)
  refine eq_zero_of_disjoint_isOpen_of_isZero_localHomology N isOpen_interior
    hL.isClosed.isOpen_compl
    (disjoint_left.2 fun _ hxU hxLc ↦ hxLc (interior_subset hxU)) hUVD (hhigh _ hDc)
    ⟨SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion hKL))) N k αK, ?_⟩
    ⟨β, hβ⟩
  rw [← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← TopCat.toSSet.map_comp,
    ← TopCat.ofHom_comp, ContinuousMap.subtypeVal_comp_inclusion]
  exact hαK

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
  have hx₀ : localHomologyRestriction N (subset_univ {x}) k β₀ = 0 :=
    (singularHomologyToLocalHomology_apply N x α).symm.trans hα
  have hw := ConcreteCategory.congr_hom
    (localHomologyRestriction_univ_comp_localHomologyTransport N (E := E) k f) β₀
  exact (singularHomologyToLocalHomology_apply N y α).trans
    (hw.symm.trans ((ConcreteCategory.comp_apply _ _ _).trans
      ((congrArg (localHomologyTransport N M E k f) hx₀).trans (map_zero _))))

private theorem isZero_singularHomology_of_finrank_lt_aux
    {Λ' : Type w} [Ring Λ'] (N' : ModuleCat.{w} Λ') {n k : ℕ} (hn : finrank ℝ E = n)
    (hk : n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ') k).obj N').obj
      (TopCat.of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  rw [singularHomologyFunctor_obj_obj, ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun α β ↦ sub_eq_zero.1 ?_⟩
  refine eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero N'
    (fun D hD ↦ isZero_localHomology_of_isCompact N' hn hD (Nat.lt_succ_of_lt hk)) (α - β)
    fun L hL ↦ (ModuleCat.subsingleton_of_isZero
      (isZero_localHomology_of_isCompact N' hn hL hk)).elim _ _

private theorem isZero_singularHomology_top_of_forall_not_isCompact_connectedComponent_aux
    {Λ' : Type w} [Ring Λ'] (N' : ModuleCat.{w} Λ') {n : ℕ}
    (hn : finrank ℝ E = n) (hcomp : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ') n).obj N').obj
      (TopCat.of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  have := ChartedSpace.locallyPathConnectedSpace E M
  rw [singularHomologyFunctor_obj_obj, ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun α β ↦ sub_eq_zero.1 ?_⟩
  let γ := α - β
  obtain ⟨K, hK, γK, hγK⟩ := exists_isCompact_homologyMap_subtypeVal_eq N' n γ
  -- Every point `x` can be joined to a point `x₀ ∉ K` because its closed path component is not
  -- compact, hence not contained in `K`.
  have hloc (x : M) : singularHomologyToLocalHomology N' x n γ = 0 := by
    have hnotSub : ¬ connectedComponent x ⊆ K :=
      fun hsub ↦ hcomp x (hK.of_isClosed_subset isClosed_connectedComponent hsub)
    obtain ⟨x₀, hx₀c, hx₀K⟩ := not_subset.1 hnotSub
    have hjoined : Joined x₀ x :=
      (mem_pathComponent_iff.1 (pathComponent_eq_connectedComponent x ▸ hx₀c)).symm
    refine singularHomologyToLocalHomology_eq_zero_of_joined_aux N' E hjoined ?_
    rw [← hγK]
    exact singularHomologyToLocalHomology_homologyMap_subtypeVal_eq_zero_of_notMem N' hx₀K γK
  refine eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero N'
    (fun D hD ↦ isZero_localHomology_of_isCompact N' hn hD (Nat.lt_succ_self n)) γ fun L hL ↦ ?_
  refine eq_zero_of_forall_localHomologyRestriction_eq_zero N' hn hL _ fun x hx ↦ ?_
  rw [localHomologyRestriction_singularHomologyπ_apply N' (singleton_subset_iff.2 hx)]
  exact hloc x

end SameUniverseModel

section Manifold

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- Re-model a space `M` charted on a real normed space `E` of finite dimension `n` onto
`EuclideanSpace ℝ (ULift.{w} (Fin n))` in the universe `w` of `M`. -/
@[instance_reducible]
private def chartedSpaceEuclideanUliftFin {M : Type w} [TopologicalSpace M] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
    (hn : finrank ℝ E = n) : ChartedSpace (EuclideanSpace ℝ (ULift.{w} (Fin n))) M :=
  let L : E ≃L[ℝ] EuclideanSpace ℝ (ULift.{w} (Fin n)) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_ulift_fin.{w} n).symm)
  let _ : ChartedSpace (EuclideanSpace ℝ (ULift.{w} (Fin n))) E :=
    L.toHomeomorph.isOpenEmbedding.singletonChartedSpace
  ChartedSpace.comp (EuclideanSpace ℝ (ULift.{w} (Fin n))) E M

/-- Restricting scalars along `ULift.{w} ℤ →+* Λ` reflects vanishing of singular homology, reducing
coefficients over a ring in any universe to `ULift.{w} ℤ : Type w`. -/
private theorem isZero_singularHomology_of_restrictScalars_ulift_int {X : TopCat.{w}} {k : ℕ}
    (h : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} (ULift.{w} ℤ)) k).obj
      ((ModuleCat.restrictScalars.{w}
        ((Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom)).obj N)).obj X)) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj X) := by
  let F := ModuleCat.restrictScalars.{w} ((Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom)
  have : ∀ T : Type w, PreservesColimitsOfShape (Discrete T) F :=
    fun _ ↦ ⟨fun {K} ↦ ModuleCat.preservesColimit_restrictScalars _ K⟩
  have hF : IsZero (F.obj
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj X)) :=
    (Iso.isZero_iff ((Functor.singularHomologyFunctorObjCompIso F N k).app X)).2 h
  rw [IsZero.iff_id_eq_zero]
  refine F.map_injective ?_
  rw [F.map_id, F.map_zero]
  exact hF.eq_of_src _ _

/-- **Vanishing in local homology transports along paths.** On a Hausdorff boundaryless manifold,
if `α ∈ Hₖ(M; N)` vanishes in the local homology `Hₖ(M, M ∖ {x}; N)`, then it vanishes in
`Hₖ(M, M ∖ {y}; N)` for every point `y` in the path component of `x`. -/
theorem singularHomologyToLocalHomology_eq_zero_of_joined (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {x y : M} (hxy : Joined x y) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hα : singularHomologyToLocalHomology N x k α = 0) :
    singularHomologyToLocalHomology N y k α = 0 := by
  let _ := chartedSpaceEuclideanUliftFin.{w} (M := M) (rfl : finrank ℝ E = finrank ℝ E)
  exact singularHomologyToLocalHomology_eq_zero_of_joined_aux N
    (EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ E)))) hxy hα

/-- **Singular homology of a boundaryless manifold vanishes above the dimension.** For any
Hausdorff space `M` modelled on a real normed space `E` of finite dimension `n`, compact or not,
`Hₖ(M; N) = 0` for `k > n`. -/
theorem isZero_singularHomology_of_finrank_lt {n k : ℕ} (hn : finrank ℝ E = n) (hk : n < k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  let _ := chartedSpaceEuclideanUliftFin.{w} (M := M) hn
  refine isZero_singularHomology_of_restrictScalars_ulift_int N ?_
  exact isZero_singularHomology_of_finrank_lt_aux
    (E := EuclideanSpace ℝ (ULift.{w} (Fin n))) _
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
  · let _ := chartedSpaceEuclideanUliftFin.{w} (M := M) hn
    refine isZero_singularHomology_of_restrictScalars_ulift_int N ?_
    exact isZero_singularHomology_top_of_forall_not_isCompact_connectedComponent_aux
      (E := EuclideanSpace ℝ (ULift.{w} (Fin n))) _
      (finrank_euclideanSpace_ulift_fin.{w} n) hcomp
  · exact isZero_singularHomology_of_finrank_lt N hn hk

/-- **Top and higher homology of a preconnected noncompact manifold vanish** (Hatcher,
Proposition 3.29). For a preconnected noncompact Hausdorff space `M` modelled on a real normed
space of dimension `n`, `Hₖ(M; N) = 0` for every `k ≥ n`. -/
theorem isZero_singularHomology_of_not_compactSpace [PreconnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) (hM : ¬ CompactSpace M) {k : ℕ} (hk : n ≤ k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) := by
  refine isZero_singularHomology_of_forall_not_isCompact_connectedComponent N hn (fun x hc ↦ hM ?_)
    hk
  rw [← isCompact_univ_iff, ← PreconnectedSpace.connectedComponent_eq_univ x]
  exact hc

/-- **Nonzero homology in degree at least the dimension forces compactness.** If a preconnected
Hausdorff space `M` modelled on a real normed space of dimension `n` has `Hₖ(M; N) ≠ 0` for some
`k ≥ n` and some module `N`, then `M` is compact. -/
theorem compactSpace_of_not_isZero_singularHomology [PreconnectedSpace M] {n k : ℕ}
    (hn : finrank ℝ E = n) (hk : n ≤ k)
    (h : ¬ IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M))) :
    CompactSpace M :=
  Classical.byContradiction fun hM ↦ h (isZero_singularHomology_of_not_compactSpace N hn hM hk)

/-- **Homology of a proper open subset of a preconnected manifold vanishes from the dimension on.**
Let `M` be a preconnected Hausdorff space modelled on a real normed space of dimension `n`, and let
`U ⊆ M` be a proper open subset (`U ≠ univ`). Then `Hₖ(U; N) = 0` for every `k ≥ n`, even if `U` is
disconnected. -/
theorem isZero_singularHomology_of_isOpen_ne_univ [PreconnectedSpace M] {n : ℕ}
    (hn : finrank ℝ E = n) {U : Set M} (hUo : IsOpen U) (hU : U ≠ univ) {k : ℕ} (hk : n ≤ k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of U)) := by
  rcases isEmpty_or_nonempty U with _ | _
  · exact isZero_singularHomologyFunctor_of_isEmpty N (TopCat.of U) k
  · let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hUo⟩
    have := ChartedSpace.locallyPathConnectedSpace E U
    refine isZero_singularHomology_of_forall_not_isCompact_connectedComponent (E := E) N hn
      (fun x hc ↦ hU ?_) hk
    have hOpenM : IsOpen (Subtype.val '' connectedComponent x) :=
      hUo.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_connectedComponent
    have hClosedM : IsClosed (Subtype.val '' connectedComponent x) :=
      (hc.image continuous_subtype_val).isClosed
    have hClopen : IsClopen (Subtype.val '' connectedComponent x) := ⟨hClosedM, hOpenM⟩
    have hUniv : Subtype.val '' connectedComponent x = univ :=
      hClopen.eq_univ ⟨x.1, x, mem_connectedComponent, rfl⟩
    exact univ_subset_iff.1 (hUniv ▸ image_subset_iff.2 fun y _ ↦ y.2)

end Manifold

end TauCeti
