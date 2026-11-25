/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.AlgebraicTopology.Singular.CompactSupport
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Ring.ULift
import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.AlgebraicTopology.Singular.Additivity
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
import TauCeti.AlgebraicTopology.Singular.LocalHomology.MayerVietoris
import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology
import TauCeti.Geometry.Manifold.ModelTransport.Finrank
import TauCeti.Topology.Compactness.Compact

/-!
# Vanishing of top singular homology on noncompact manifolds

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary, and let `N` be a module over a ring `Λ`. Combining
compact supports (Hatcher, Proposition 3.33) with local homology vanishing on compact sets
(Hatcher, Lemma 3.27(b)), this file proves:

* `Hₖ(M; N) = 0` for every `k > n`, with no compactness or connectedness assumption on `M`
  (`TauCeti.isZero_singularHomology_of_lt`), extending
  `TauCeti.isZero_singularHomology_of_compactSpace` by removing compactness;
* Hatcher's Proposition 3.29: `Hₖ(M; N) = 0` for every `k ≥ n` whenever no connected component of
  `M` is compact (`TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`),
  and in particular when `M` is preconnected and noncompact
  (`TauCeti.isZero_singularHomology_of_noncompactSpace`).

Contrapositively, if `M` is preconnected and `Hₖ(M; N)` is nonzero (or nontrivial) in some degree
`k ≥ n`, then `M` is compact (`TauCeti.compactSpace_of_not_isZero_singularHomology` and
`TauCeti.compactSpace_of_nontrivial_singularHomology`). In
`TauCeti.Geometry.Manifold.PoincareConjecture`, this forces compactness of any Hausdorff
`n`-manifold without boundary homotopy equivalent to `Sⁿ`, since for `n ≥ 1` such a manifold is
connected with nontrivial top integral homology `Hₙ(M; ℤ) ≅ ℤ`. Likewise every proper open
subset of a preconnected `n`-manifold has vanishing homology in degrees `k ≥ n`
(`TauCeti.isZero_singularHomology_of_isOpen_ne_univ`).

## Main results

* `TauCeti.eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero`: in a weakly locally compact
  Hausdorff space whose compact subsets have vanishing local homology in degree `k + 1`, a class in
  `Hₖ(M; N)` vanishing in `Hₖ(M, M ∖ L; N)` for all compact `L` is zero.
* `TauCeti.mono_singularHomologyMap_subtype_of_isCompact_closure`: on a Hausdorff `n`-manifold, the
  inclusion of an open subset with compact closure induces a monomorphism on `Hₖ` for `k ≥ n`.
* `TauCeti.isZero_singularHomology_of_lt`: `Hₖ(M; N) = 0` for `k > n` on every Hausdorff
  `n`-manifold without boundary.
* `TauCeti.isZero_singularHomology_of_forall_not_isCompact_connectedComponent`: `Hₖ(M; N) = 0` for
  `k ≥ n` when no connected component of `M` is compact.
* `TauCeti.isZero_singularHomology_of_noncompactSpace`: Hatcher's Proposition 3.29, `Hₖ(M; N) = 0`
  for `k ≥ n` on a preconnected noncompact Hausdorff `n`-manifold without boundary.
* `TauCeti.compactSpace_of_not_isZero_singularHomology` and
  `TauCeti.compactSpace_of_nontrivial_singularHomology`: nonvanishing or nontriviality of
  `Hₖ(M; N)` for some `k ≥ n` on a preconnected Hausdorff `n`-manifold forces `CompactSpace M`.
* `TauCeti.isZero_singularHomology_of_isOpen_ne_univ`,
  `TauCeti.isZero_singularHomology_of_isOpen_of_lt`, and
  `TauCeti.isZero_singularHomology_of_isOpen_of_isPreconnected_of_not_isCompact`: homology
  vanishing on open subsets `U ⊆ M`.
* `ModuleCat.finrank_singularHomology_eq_zero_of_lt`,
  `ModuleCat.finrank_singularHomology_eq_zero_of_forall_not_isCompact_connectedComponent`, and
  `ModuleCat.finrank_singularHomology_eq_zero_of_noncompactSpace`: the corresponding rank-vanishing
  statements.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.27(b) (p. 236), Proposition 3.29 (p. 239), and Proposition 3.33 (p. 244).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Module Set TopCat Topology

universe w

namespace TauCeti

/-
Proof outline for `SameUniverse` and `General`:

Every class `z ∈ Hₖ(M; N)` comes from an open subset `U` contained in a compact subset `K` of `M`
(`TauCeti.exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq`). Suppose `z` maps to zero in
the local homology `Hₖ(M, M ∖ K; N)`. By exactness of the pair `(M, M ∖ K)`, `z` also comes from a
class `v ∈ Hₖ(M ∖ K; N)`. For `k ≥ n`, the compact set `K ∖ U` satisfies
`Hₖ₊₁(M, M ∖ (K ∖ U); N) = 0` (`TauCeti.isZero_localHomology_of_isCompact`), so the inclusion of
`(K ∖ U)ᶜ = U ∪ (M ∖ K)` into `M` induces a monomorphism `Hₖ(U ∪ (M ∖ K); N) ⟶ Hₖ(M; N)`. The
classes on the disjoint open subsets `U` and `M ∖ K` therefore agree in `Hₖ(U ∪ (M ∖ K); N)`, hence
both vanish (`TauCeti.eq_zero_and_eq_zero_of_singularHomologyMap_inclusion_eq_of_disjoint`), so
`z = 0`.

When `k > n`, the local homology `Hₖ(M, M ∖ K; N)` vanishes unconditionally. When `k = n` and no
connected component of `M` is compact, for each `x ∈ K` the connected component of `x` is closed,
hence cannot lie inside `K`, so it meets `M ∖ K` at a point `x₀`. Since `M` is locally path
connected, `x₀` and `x` lie in the same path component. Because `U ⊆ K ⊆ M ∖ {x₀}`, the local class
of `z` vanishes at `x₀`, hence at `x` by transport along a path (`TauCeti.localHomologySystemCone`),
and therefore `z` maps to zero in `Hₙ(M, M ∖ K; N)`
(`TauCeti.eq_zero_of_forall_localHomologyRestriction_eq_zero`).

Finally, `ChartedSpace.ofFinrankEq` replaces an arbitrary finite-dimensional model space `E` by
`ULift.{w} (Fin n) → ℝ` in the universe `w` of `M`, and restriction of scalars along
`ULift.{w} ℤ →+* Λ` (`CategoryTheory.Functor.isZero_singularHomologyFunctor_iff`) unties the
coefficient ring universe from `w`.
-/

section TopologicalSpace

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ) {M : Type w} [TopologicalSpace M]

/-- **Compact-exhaustion vanishing criterion.** In a weakly locally compact Hausdorff space `M`
where `Hₖ₊₁(M, M ∖ D; N) = 0` for every compact `D ⊆ M`, a class `α ∈ Hₖ(M; N)` whose image in
`Hₖ(M, M ∖ L; N)` vanishes for every compact `L ⊆ M` is zero. -/
theorem eq_zero_of_forall_isCompact_singularHomologyπ_eq_zero
    [T2Space M] [WeaklyLocallyCompactSpace M] {k : ℕ}
    (hhigh : ∀ D : Set M, IsCompact D → IsZero (localHomology N D (k + 1)))
    (α : ((toSSet.obj (of M)).homology N k : ModuleCat.{w} Λ))
    (hπ : ∀ L : Set M, IsCompact L →
      (TopPair.ofSubset (Lᶜ : Set (of M))).singularHomologyπ (C := ModuleCat.{w} Λ) N k α = 0) :
    α = 0 := by
  obtain ⟨K, hK, αK, hαK⟩ := exists_isCompact_singularHomologyMap_subtypeVal_eq (Y := M) N k α
  -- `((singularHomologyFunctor _ k).obj N).obj X` and `.map f` are definitionally
  -- `(toSSet.obj X).homology N k` and `SSet.homologyMap (toSSet.map f) N k`.
  change ((toSSet.obj (of K)).homology N k : ModuleCat.{w} Λ) at αK
  change SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal K))) N k αK = α at hαK
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  have hDc : IsCompact (L \ interior L) := hL.inter_right isOpen_interior.isClosed_compl
  have hUVD : interior L ∪ Lᶜ = (L \ interior L)ᶜ := by
    rw [Set.sdiff_eq, compl_inter, compl_compl, union_comm]
  obtain ⟨β, hβ⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset (Lᶜ : Set (of M))).singularHomology_exact_space N k) α (hπ L hL)
  refine eq_zero_of_disjoint_isOpen_of_isZero_localHomology N isOpen_interior
    hL.isClosed.isOpen_compl
    (disjoint_left.2 fun _ hxU hxLc ↦ hxLc (interior_subset hxU)) hUVD (hhigh _ hDc)
    ⟨SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion hKL))) N k αK, ?_⟩
    ⟨β, hβ⟩
  rw [← hαK, ← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← toSSet.map_comp,
    TopCat.ofHom_inclusion_comp_ofHom_subtypeVal]

end TopologicalSpace

section SameUniverse

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ) {n : ℕ}
  {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- A class in `Hₖ(M; N)` supported on an open subset `U` of a compact set `K ⊆ M` vanishes once
its image in `Hₖ(M, M ∖ K; N)` vanishes, provided `k ≥ n`. -/
private lemma homologyMap_toSSet_subtypeVal_eq_zero_of_singularHomologyπ_compl_eq_zero
    (hn : finrank ℝ E = n) {k : ℕ} (hk : n ≤ k) {U K : Set M} (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (u : ((toSSet.obj (of ↥U)).homology N k : ModuleCat.{w} Λ))
    (hz : (TopPair.ofSubset (Kᶜ : Set (of M))).singularHomologyπ N k
      (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N k u) = 0) :
    SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N k u = 0 := by
  set z := SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N k u with hz_def
  -- In `singularHomology_exact_space`, the first morphism of the `ShortComplex.mk` is induced by
  -- `(TopPair.ofSubset Kᶜ).map`.
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((TopPair.ofSubset (Kᶜ : Set (of M))).singularHomology_exact_space N k) z hz
  change SSet.homologyMap (toSSet.map (TopPair.ofSubset (Kᶜ : Set (of M))).map) N k v = z at hv
  rw [TopPair.ofSubset_map] at hv
  have hLc : (U ∪ Kᶜ : Set (of M)) = ((K \ U)ᶜ : Set (of M)) := by
    rw [Set.sdiff_eq, compl_inter, compl_compl, union_comm]
  have hzeroL : IsZero ((TopPair.ofSubset (U ∪ Kᶜ : Set (of M))).singularHomology N (k + 1)) := by
    rw [hLc]
    exact isZero_localHomology_of_isCompact N hn (hK.diff hU) (by lia)
  let j := SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ Kᶜ)))) N k
  have hmono : Mono j := by
    have hm := (TopPair.ofSubset (U ∪ Kᶜ : Set (of M))).mono_homologyMap_map_of_isZero N hzeroL
    rwa [TopPair.ofSubset_map] at hm
  have hj_inc {S : Set M} (hS : S ⊆ U ∪ Kᶜ)
      (w : ((toSSet.obj (of ↥S)).homology N k : ModuleCat.{w} Λ)) :
      j (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion hS))) N k w) =
        SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal S))) N k w := by
    dsimp only [j]
    rw [← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← toSSet.map_comp,
      TopCat.ofHom_inclusion_comp_ofHom_subtypeVal]
  have huv : ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (ofHom (ContinuousMap.inclusion (subset_union_left (s := U) (t := Kᶜ)))) u =
      ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
        (ofHom (ContinuousMap.inclusion (subset_union_right (s := U) (t := Kᶜ)))) v := by
    simp only [singularHomologyFunctor_obj_map]
    exact ((ModuleCat.mono_iff_injective j).1 hmono)
      ((hj_inc subset_union_left u).trans (hv.symm.trans (hj_inc subset_union_right v).symm))
  have hu0 : u = 0 := (eq_zero_and_eq_zero_of_singularHomologyMap_inclusion_eq_of_disjoint N
    hU hK.isClosed.isOpen_compl (disjoint_compl_right.mono_left hUK) u v huv).1
  rw [hz_def, hu0, map_zero]

/-- If a class in `Hₙ(M; N)` comes from `U ⊆ K` with `K` compact and no connected component of `M`
is compact, then its image in `Hₙ(M, M ∖ K; N)` vanishes. -/
private lemma singularHomologyπ_compl_eq_zero_of_forall_not_isCompact_connectedComponent
    (hn : finrank ℝ E = n) (hnc : ∀ x : M, ¬ IsCompact (connectedComponent x))
    {U K : Set M} (hK : IsCompact K) (hUK : U ⊆ K)
    (u : ((toSSet.obj (of ↥U)).homology N n : ModuleCat.{w} Λ)) :
    (TopPair.ofSubset (Kᶜ : Set (of M))).singularHomologyπ N n
      (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N n u) = 0 := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  let z : ((toSSet.obj (of M)).homology N n : ModuleCat.{w} Λ) :=
    SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N n u
  let γ : ((localHomologySystemCone N M E n).pt : ModuleCat.{w} Λ) :=
    (TopPair.ofSubset ((univ : Set M)ᶜ : Set (of M))).singularHomologyπ N n z
  have hcone_app (y : M) :
      ((localHomologySystemCone N M E n).π.app (.mk y)) γ =
        (TopPair.ofSubset ({y}ᶜ : Set (of M))).singularHomologyπ N n z := by
    rw [localHomologySystemCone_π_app]
    exact singularHomologyπ_localHomologyRestriction_apply N (subset_univ {y}) n z
  refine eq_zero_of_forall_localHomologyRestriction_eq_zero N hn hK _ fun x hx ↦ ?_
  have hnot_sub : ¬ connectedComponent x ⊆ K :=
    fun hsub ↦ hnc x (hK.of_isClosed_subset isClosed_connectedComponent hsub)
  obtain ⟨x₀, hx₀c, hx₀K⟩ := not_subset.1 hnot_sub
  have hjoin : Joined x₀ x := by
    have hx₀p : x₀ ∈ pathComponent x := by rwa [pathComponent_eq_connectedComponent]
    exact hx₀p.symm
  let f : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x :=
    Path.Homotopic.Quotient.mk hjoin.somePath
  have hUx₀ : U ⊆ ({x₀}ᶜ : Set M) := fun y hy hxy ↦ hx₀K (mem_singleton_iff.1 hxy ▸ hUK hy)
  have hx₀_zero : (TopPair.ofSubset ({x₀}ᶜ : Set (of M))).singularHomologyπ N n z = 0 := by
    have hz' : z = SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal ({x₀}ᶜ : Set M))))
        N n (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion hUx₀))) N n u) := by
      dsimp only [z]
      rw [← ConcreteCategory.comp_apply, ← SSet.homologyMap_comp, ← toSSet.map_comp,
        TopCat.ofHom_inclusion_comp_ofHom_subtypeVal]
    have h0 := (TopPair.ofSubset ({x₀}ᶜ : Set (of M))).homologyMap_comp_singularHomologyπ N n
    rw [TopPair.ofSubset_map] at h0
    rw [hz']
    exact (ShortComplex.mk _ _ h0).zero_apply _
  have hγx₀ : ((localHomologySystemCone N M E n).π.app (.mk x₀)) γ = 0 :=
    (hcone_app x₀).trans hx₀_zero
  have hγx : ((localHomologySystemCone N M E n).π.app (.mk x)) γ = 0 := by
    rw [← (localHomologySystemCone N M E n).w f, ConcreteCategory.comp_apply, hγx₀, map_zero]
  exact (singularHomologyπ_localHomologyRestriction_apply N (singleton_subset_iff.2 hx) n z).trans
    ((hcone_app x).symm.trans hγx)

/-- Common compact-support reduction for `Hₖ(M; N) = 0` in degrees `k ≥ n`: once every class
supported on `U ⊆ K` with `K` compact vanishes in `Hₖ(M, M ∖ K; N)`, `Hₖ(M; N)` vanishes. -/
private lemma isZero_singularHomology_of_forall_singularHomologyπ_compl_eq_zero
    (hn : finrank ℝ E = n) {k : ℕ} (hk : n ≤ k)
    (hπ : ∀ ⦃U K : Set M⦄, IsOpen U → IsCompact K → U ⊆ K →
      ∀ u : ((toSSet.obj (of ↥U)).homology N k : ModuleCat.{w} Λ),
        (TopPair.ofSubset (Kᶜ : Set (of M))).singularHomologyπ N k
          (SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.subtypeVal U))) N k u) = 0) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  refine ModuleCat.isZero_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun z ↦ ?_)
  obtain ⟨U, K, hU, hK, hUK, u, rfl⟩ :=
    exists_isOpen_isCompact_singularHomologyMap_subtypeVal_eq N k z
  rw [singularHomologyFunctor_obj_map]
  exact homologyMap_toSSet_subtypeVal_eq_zero_of_singularHomologyπ_compl_eq_zero N hn hk hU hK
    hUK u (hπ hU hK hUK u)

private lemma isZero_singularHomology_of_lt_aux (hn : finrank ℝ E = n) {k : ℕ} (hk : n < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) :=
  isZero_singularHomology_of_forall_singularHomologyπ_compl_eq_zero N hn hk.le
    fun _ _ _ hK _ _ ↦
      (ModuleCat.subsingleton_of_isZero (isZero_localHomology_of_isCompact N hn hK hk)).elim _ 0

private lemma isZero_singularHomology_of_forall_not_isCompact_connectedComponent_aux
    (hn : finrank ℝ E = n) (hnc : ∀ x : M, ¬ IsCompact (connectedComponent x)) {k : ℕ}
    (hk : n ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) := by
  obtain rfl | hk := hk.eq_or_lt
  · exact isZero_singularHomology_of_forall_singularHomologyπ_compl_eq_zero N hn le_rfl
      fun _ _ _ hK hUK u ↦
        singularHomologyπ_compl_eq_zero_of_forall_not_isCompact_connectedComponent N hn hnc hK
          hUK u
  · exact isZero_singularHomology_of_lt_aux N hn hk

private lemma mono_singularHomologyMap_subtype_of_isCompact_closure_aux
    (hn : finrank ℝ E = n) {U : Set M} (hU : IsOpen U) (hcpt : IsCompact (closure U)) {k : ℕ}
    (hk : n ≤ k) :
    Mono (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (ofHom (ContinuousMap.subtypeVal U))) :=
  mono_singularHomologyMap_subtype_of_isZero_localHomology_frontier N hU
    (isZero_localHomology_of_isCompact N hn
      (hcpt.of_isClosed_subset isClosed_frontier frontier_subset_closure) (by lia))

end SameUniverse

section General

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ) {n : ℕ}
  {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- **The singular homology of a manifold vanishes above the dimension** (Hatcher, Lemma 3.27(b)
and Proposition 3.33). For any Hausdorff space `M` modelled on a real normed space of dimension
`n`, `Hₖ(M; N) = 0` for `k > n`, without assuming compactness or connectedness. -/
theorem isZero_singularHomology_of_lt (hn : finrank ℝ E = n) {k : ℕ} (hk : n < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) := by
  let _ : ChartedSpace (ULift.{w} (Fin n) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [hn])
  let φ : ULift.{w} ℤ →+* Λ := (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom
  exact ((ModuleCat.restrictScalars.{w} φ).isZero_singularHomologyFunctor_iff N k (of M)).1
    (isZero_singularHomology_of_lt_aux (E := ULift.{w} (Fin n) → ℝ) _ (by simp) hk)

/-- **Singular homology from the dimension on vanishes when no connected component is compact**
(Hatcher, Proposition 3.29). For a Hausdorff space `M` modelled on a real normed space of dimension
`n`, if no connected component of `M` is compact, then `Hₖ(M; N) = 0` for all `k ≥ n`. -/
theorem isZero_singularHomology_of_forall_not_isCompact_connectedComponent (hn : finrank ℝ E = n)
    (hnc : ∀ x : M, ¬ IsCompact (connectedComponent x)) {k : ℕ} (hk : n ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) := by
  let _ : ChartedSpace (ULift.{w} (Fin n) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [hn])
  let φ : ULift.{w} ℤ →+* Λ := (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom
  exact ((ModuleCat.restrictScalars.{w} φ).isZero_singularHomologyFunctor_iff N k (of M)).1
    (isZero_singularHomology_of_forall_not_isCompact_connectedComponent_aux
      (E := ULift.{w} (Fin n) → ℝ) _ (by simp) hnc hk)

/-- **Top singular homology of a noncompact manifold vanishes** (Hatcher, Proposition 3.29).
For a preconnected noncompact Hausdorff space `M` modelled on a real normed space of dimension
`n`, `Hₖ(M; N) = 0` for every `k ≥ n`. -/
theorem isZero_singularHomology_of_noncompactSpace [PreconnectedSpace M] [NoncompactSpace M]
    (hn : finrank ℝ E = n) {k : ℕ} (hk : n ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M)) :=
  isZero_singularHomology_of_forall_not_isCompact_connectedComponent N hn
    not_isCompact_connectedComponent hk

/-- **Nonvanishing singular homology in degree at least the dimension forces compactness.** If `M`
is a preconnected Hausdorff space modelled on a real normed space of dimension `n` and `Hₖ(M; N)`
is nonzero for some `k ≥ n`, then `M` is compact. -/
theorem compactSpace_of_not_isZero_singularHomology [PreconnectedSpace M] (hn : finrank ℝ E = n)
    {k : ℕ} (hk : n ≤ k)
    (h : ¬ IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M))) :
    CompactSpace M := by
  by_contra hnc
  have := not_compactSpace_iff.1 hnc
  exact h (isZero_singularHomology_of_noncompactSpace N hn hk)

/-- **Nontrivial singular homology in degree at least the dimension forces compactness.** If `M` is
a preconnected Hausdorff space modelled on a real normed space of dimension `n` and `Hₖ(M; N)` is
nontrivial for some `k ≥ n`, then `M` is compact. -/
theorem compactSpace_of_nontrivial_singularHomology [PreconnectedSpace M] (hn : finrank ℝ E = n)
    {k : ℕ} (hk : n ≤ k)
    [h : Nontrivial (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of M))] :
    CompactSpace M :=
  compactSpace_of_not_isZero_singularHomology N hn hk fun hz ↦
    @false_of_nontrivial_of_subsingleton _ h (ModuleCat.subsingleton_of_isZero hz)

/-- **Homology of a proper open subset of a preconnected manifold vanishes from the dimension on.**
Let `M` be a preconnected Hausdorff space modelled on a real normed space of dimension `n`, and let
`U ⊆ M` be a proper open subset (`U ≠ univ`). Then `Hₖ(U; N) = 0` for every `k ≥ n`, even if `U` is
disconnected. -/
theorem isZero_singularHomology_of_isOpen_ne_univ [PreconnectedSpace M] (hn : finrank ℝ E = n)
    {U : Set M} (hUo : IsOpen U) (hU : U ≠ univ) {k : ℕ} (hk : n ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of U)) := by
  rcases isEmpty_or_nonempty U with _ | _
  · exact isZero_singularHomology_of_isEmpty N (of U) k
  · let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hUo⟩
    have := ChartedSpace.locallyPathConnectedSpace E U
    refine isZero_singularHomology_of_forall_not_isCompact_connectedComponent (E := E) N hn
      (fun x hc ↦ hU ?_) hk
    have hOpenM : IsOpen (Subtype.val '' connectedComponent x) :=
      hUo.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_connectedComponent
    have hClosedM : IsClosed (Subtype.val '' connectedComponent x) :=
      (hc.image continuous_subtypeVal).isClosed
    have hClopen : IsClopen (Subtype.val '' connectedComponent x) := ⟨hClosedM, hOpenM⟩
    have hUniv : Subtype.val '' connectedComponent x = univ :=
      hClopen.eq_univ ⟨x.val, x, mem_connectedComponent, rfl⟩
    exact univ_subset_iff.1 (hUniv ▸ image_subset_iff.2 fun y _ ↦ y.property)

/-- **Injectivity of relatively compact open-subset homology on a manifold.** On a Hausdorff
space `M` modelled on a real normed space of dimension `n`, the inclusion `U ↪ M` of an open subset
with compact closure induces a monomorphism `Hₖ(U; N) ⟶ Hₖ(M; N)` in every degree `k ≥ n`. -/
theorem mono_singularHomologyMap_subtype_of_isCompact_closure (hn : finrank ℝ E = n)
    {U : Set M} (hU : IsOpen U) (hcpt : IsCompact (closure U)) {k : ℕ} (hk : n ≤ k) :
    Mono (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (ofHom (ContinuousMap.subtypeVal U))) := by
  let _ : ChartedSpace (ULift.{w} (Fin n) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [hn])
  let φ : ULift.{w} ℤ →+* Λ := (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom
  exact (ModuleCat.restrictScalars.{w} φ).mono_singularHomologyFunctor_map_of_mono N _ k
    (mono_singularHomologyMap_subtype_of_isCompact_closure_aux
      (E := ULift.{w} (Fin n) → ℝ) _ (by simp) hU hcpt hk)

/-- **Singular homology of an open subset of a manifold vanishes above the dimension.** For any open
subset `U ⊆ M` of a Hausdorff `n`-manifold without boundary, `Hₖ(U; N) = 0` for `k > n`. -/
theorem isZero_singularHomology_of_isOpen_of_lt (hn : finrank ℝ E = n) {U : Set M} (hU : IsOpen U)
    {k : ℕ} (hk : n < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of U)) := by
  let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hU⟩
  exact isZero_singularHomology_of_lt (E := E) N hn hk

/-- **Top singular homology of a preconnected noncompact open subset of a manifold vanishes.** For
any preconnected noncompact open subset `U ⊆ M` of a Hausdorff `n`-manifold without boundary,
`Hₖ(U; N) = 0` for every `k ≥ n`. -/
theorem isZero_singularHomology_of_isOpen_of_isPreconnected_of_not_isCompact (hn : finrank ℝ E = n)
    {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) (hK : ¬ IsCompact U) {k : ℕ}
    (hk : n ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (of U)) := by
  let _ : ChartedSpace E U := TopologicalSpace.Opens.instChartedSpace ⟨U, hU⟩
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  have : NoncompactSpace U := not_compactSpace_iff.mp (isCompact_iff_compactSpace.not.mp hK)
  exact isZero_singularHomology_of_noncompactSpace (E := E) N hn hk

end General

end TauCeti

namespace ModuleCat

open AlgebraicTopology TauCeti

variable {Λ : Type*} [Ring Λ] [Nontrivial Λ] (N : ModuleCat.{w} Λ) {n : ℕ}
  {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- Above the dimension of a Hausdorff manifold `M`, `Hₖ(M; N)` has rank zero. -/
theorem finrank_singularHomology_eq_zero_of_lt (hn : Module.finrank ℝ E = n) {k : ℕ}
    (hk : n < k) :
    Module.finrank Λ (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) = 0 := by
  have := (ModuleCat.isZero_iff_subsingleton).1 (isZero_singularHomology_of_lt (M := M) N hn hk)
  exact Module.finrank_zero_of_subsingleton

/-- On a Hausdorff `n`-manifold `M` with no compact connected component, `Hₖ(M; N)` has rank zero
for every `k ≥ n`. -/
theorem finrank_singularHomology_eq_zero_of_forall_not_isCompact_connectedComponent
    (hn : Module.finrank ℝ E = n) (hnc : ∀ x : M, ¬ IsCompact (connectedComponent x)) {k : ℕ}
    (hk : n ≤ k) :
    Module.finrank Λ (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) = 0 := by
  have := (ModuleCat.isZero_iff_subsingleton).1
    (isZero_singularHomology_of_forall_not_isCompact_connectedComponent (M := M) N hn hnc hk)
  exact Module.finrank_zero_of_subsingleton

/-- On a preconnected noncompact Hausdorff `n`-manifold `M`, `Hₖ(M; N)` has rank zero for every
`k ≥ n`. -/
theorem finrank_singularHomology_eq_zero_of_noncompactSpace [PreconnectedSpace M]
    [NoncompactSpace M] (hn : Module.finrank ℝ E = n) {k : ℕ} (hk : n ≤ k) :
    Module.finrank Λ (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of M)) = 0 :=
  finrank_singularHomology_eq_zero_of_forall_not_isCompact_connectedComponent N hn
    not_isCompact_connectedComponent hk

end ModuleCat
