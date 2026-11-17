/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import TauCeti.AlgebraicTopology.Singular.DirectedUnion
import TauCeti.Geometry.Manifold.ChartedSpace.FiniteDimension

/-!
# Singular homology of noncompact manifolds

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary. For compact `M`, `Hₖ(M)` vanishes above degree `n`
because it is the local homology `Hₖ(M, M ∖ M)` of a compact set
(`TauCeti.isZero_localHomology_of_isCompact`). This file proves that `Hₖ(M)` vanishes above degree
`n` without assuming compactness, and that in degree `n` singular homology also vanishes whenever
every path component of `M` is noncompact, in particular when `M` is connected and noncompact.
Together these are Hatcher's Proposition 3.29.

No countability, sigma-compactness or paracompactness hypothesis on `M` is needed: singular chains
have compact support, so `Hₖ(M)` is the filtered colimit of `Hₖ(U)` over the open subsets `U ⊆ M`
with compact closure (`TauCeti.exists_isOpen_isCompact_closure_singularHomologyMap_eq`). For any
open subset `U` of a topological space `M`, `(M ∖ frontier U)` is covered by the two disjoint open
sets `U` and `M ∖ closure U`, so excision identifies `Hₖ(U)` with
`Hₖ(M ∖ frontier U, M ∖ closure U)` (`TauCeti.isIso_singularHomologyMap_openToFrontierComplPair`).
In the long exact sequence of the triple `(M, M ∖ frontier U, M ∖ closure U)`, vanishing of the
local homology `Hₖ₊₁(M, M ∖ frontier U)` therefore makes the composite
`Hₖ(U) ⟶ Hₖ(M) ⟶ Hₖ(M, M ∖ closure U)`, and hence the inclusion map `Hₖ(U) ⟶ Hₖ(M)`, a monomorphism
(`TauCeti.mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isZero_localHomology_frontier`,
`TauCeti.mono_singularHomologyMap_subtype_of_isZero_localHomology_frontier`).

When `M` is an `n`-manifold and `closure U` is compact, `frontier U` is compact as well, so
`Hₖ₊₁(M, M ∖ frontier U) = 0` for `k ≥ n` (`TauCeti.isZero_localHomology_of_isCompact`). For
`k > n` the target `Hₖ(M, M ∖ closure U)` also vanishes, giving `Hₖ(U) = 0` and hence `Hₖ(M) = 0`
(`TauCeti.isZero_singularHomology_of_finrank_lt`). In degree `n`, if no path component of `M` is
compact, each `x ∈ closure U` can be joined by a path to a point `y ∉ closure U` because the path
component of `x` is closed (`ChartedSpace.locallyPathConnectedSpace`). A class coming from `Hₙ(U)`
vanishes in `Hₙ(M, M ∖ {y})` since `U ⊆ M ∖ {y}`, so parallel transport along that path kills its
local restriction at `x` (`TauCeti.localHomologyRestriction_univ_comp_localHomologyTransport`). As
local restrictions at the points of `closure U` detect `Hₙ(M, M ∖ closure U)`
(`TauCeti.eq_zero_of_forall_localHomologyRestriction_eq_zero`), the class vanishes in `Hₙ(U)` and
therefore in `Hₙ(M)` (`TauCeti.isZero_singularHomology_of_forall_not_isCompact_pathComponent`,
`TauCeti.isZero_singularHomology_of_noncompactSpace`).

Both the coefficient ring `Λ` and the model normed space `E` may live in universes independent of
`M`: `ChartedSpace.ofFinrankEq` re-charts `M` on `ULift (Fin n) → ℝ` in the universe of `M`, and
module coefficients are restricted along `ULift ℤ →+* Λ`, which preserves singular homology
(`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`).

## Main definitions and results

* `TauCeti.openToFrontierComplPair` and `TauCeti.isIso_singularHomologyMap_openToFrontierComplPair`:
  for an open set `U ⊆ M`, the inclusion `(U, ∅) ⟶ (M ∖ frontier U, M ∖ closure U)` induces
  isomorphisms on relative singular homology in every degree.
* `TauCeti.mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isZero_localHomology_frontier`
  and `TauCeti.mono_singularHomologyMap_subtype_of_isZero_localHomology_frontier`: if
  `Hₖ₊₁(M, M ∖ frontier U) = 0` for open `U`, then `Hₖ(U) ⟶ Hₖ(M) ⟶ Hₖ(M, M ∖ closure U)` and
  `Hₖ(U) ⟶ Hₖ(M)` are monomorphisms.
* `TauCeti.mono_singularHomologyMap_subtype_of_isCompact_closure`: on a Hausdorff `n`-manifold, the
  inclusion of an open subset with compact closure induces a monomorphism on `Hₖ` for `k ≥ n`.
* `TauCeti.isZero_singularHomology_of_finrank_lt`: on any Hausdorff `n`-manifold without boundary,
  `Hₖ(M; N) = 0` for `k > n`.
* `TauCeti.isZero_singularHomology_of_forall_not_isCompact_pathComponent`: if moreover no path
  component of `M` is compact, `Hₖ(M; N) = 0` for all `k ≥ n`.
* `TauCeti.isZero_singularHomology_of_noncompactSpace`: on a preconnected noncompact Hausdorff
  `n`-manifold without boundary, `Hₖ(M; N) = 0` for all `k ≥ n`.
* `TauCeti.compactSpace_of_not_isZero_singularHomology`: contrapositively, a preconnected Hausdorff
  `n`-manifold without boundary with `Hₖ(M; N) ≠ 0` for some `k ≥ n` is compact.
* `TauCeti.isZero_singularHomology_of_isOpen_of_finrank_lt` and
  `TauCeti.isZero_singularHomology_of_isOpen_of_isPreconnected_of_not_isCompact`: the corresponding
  vanishing statements for open subsets `U ⊆ M`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Module Set Topology

universe w v u

namespace TauCeti

/-! ### Excision and the frontier triple of an open subset -/

section FrontierExcision

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {M : Type w} [TopologicalSpace M] {U : Set M}

/-- For an open subset `U ⊆ M`, the inclusion of topological pairs
`(U, ∅) ⟶ (M ∖ frontier U, M ∖ closure U)`, the inner pair of the triple
`(M, M ∖ frontier U, M ∖ closure U)`. -/
def openToFrontierComplPair (hU : IsOpen U) :
    TopPair.ofSubset (∅ : Set (TopCat.of U)) ⟶
      TopPair.ofInclusion (X := TopCat.of M)
        (compl_subset_compl.2 (frontier_subset_closure (s := U))) :=
  TopPair.ofHom
    (TopCat.ofHom (ContinuousMap.inclusion (disjoint_frontier_iff_isOpen.2 hU).subset_compl_left))
    (TopCat.ofHom ⟨fun x ↦ x.2.elim, by fun_prop⟩)
    (by ext x; exact x.2.elim)

@[simp]
lemma openToFrontierComplPair_fst_apply (hU : IsOpen U) (x : U) :
    (TopPair.Hom.fst (openToFrontierComplPair hU) x).1 = x.1 :=
  (rfl)

/-- **Excision of the complement of the closure from the complement of the frontier.** For an open
subset `U ⊆ M`, the space `M ∖ frontier U` is covered by the two disjoint open subsets `U` and
`M ∖ closure U`, so `(U, ∅) ⟶ (M ∖ frontier U, M ∖ closure U)` induces isomorphisms on relative
singular homology in every degree. -/
theorem isIso_singularHomologyMap_openToFrontierComplPair (hU : IsOpen U) (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (openToFrontierComplPair hU) R k) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover R (openToFrontierComplPair hU)
    (IsEmbedding.inclusion (disjoint_frontier_iff_isOpen.2 hU).subset_compl_left)
    (fun x hx ↦ ?_)
    (fun b : Bool ↦ bif b then Subtype.val ⁻¹' U else Subtype.val ⁻¹' (closure U)ᶜ)
    (fun b ↦ by
      cases b
      · exact isClosed_closure.isOpen_compl.preimage continuous_subtype_val
      · exact hU.preimage continuous_subtype_val)
    (eq_univ_of_forall fun y ↦ by
      by_cases hy : y.1 ∈ closure U
      · refine mem_iUnion.2 ⟨true, ?_⟩
        by_contra hyU
        exact y.2 ⟨hy, by rwa [hU.interior_eq]⟩
      · exact mem_iUnion.2 ⟨false, hy⟩)
    (fun b ↦ by
      cases b
      · exact Or.inl fun y hy ↦ ⟨⟨y.1, hy⟩, rfl⟩
      · exact Or.inr fun y hy ↦ ⟨⟨y.1, hy⟩, rfl⟩)
    k
  obtain ⟨y, hy⟩ := hx
  exact (y.2 (subset_closure (congrArg Subtype.val hy ▸ x.2))).elim

/-- **Injectivity into local homology along the closure of an open subset.** Let `U ⊆ M` be open.
If the local homology `Hₖ₊₁(M, M ∖ frontier U)` along the frontier vanishes, then the composite
`Hₖ(U) ⟶ Hₖ(M) ⟶ Hₖ(M, M ∖ closure U)` is a monomorphism. -/
theorem mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isZero_localHomology_frontier
    (hU : IsOpen U) {k : ℕ} (hfr : IsZero (localHomology R (frontier U) (k + 1))) :
    Mono (((singularHomologyFunctor A k).obj R).map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M))) ≫
      (TopPair.ofSubset ((closure U)ᶜ : Set (TopCat.of M))).singularHomologyπ R k) := by
  let T := TopTriple.ofSubset (X := TopCat.of M)
    (compl_subset_compl.2 (frontier_subset_closure (s := U)))
  have hmono_inner : Mono (TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) R k) :=
    (T.singularHomology_exact_inner R (k + 1) k rfl).mono_g (hfr.eq_of_src _ _)
  have : IsEmpty (TopPair.ofSubset (∅ : Set (TopCat.of U))).snd :=
    inferInstanceAs (IsEmpty (∅ : Set U))
  have := isIso_singularHomologyMap_openToFrontierComplPair R hU k
  have hmono_comp : Mono ((TopPair.ofSubset (∅ : Set (TopCat.of U))).singularHomologyπ R k ≫
      TopPair.singularHomologyMap (openToFrontierComplPair hU ≫ TopTriple.innerToTotal.app T)
        R k) := by
    have hcomp := TopPair.singularHomologyMap_comp (openToFrontierComplPair hU) R
      (TopTriple.innerToTotal.app T) k
    let f₂ : (TopPair.ofInclusion (X := TopCat.of M)
        (compl_subset_compl.2 (frontier_subset_closure (s := U)))).singularHomology R k ⟶
        (TopTriple.totalPair.obj T).singularHomology R k :=
      TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) R k
    have : Mono f₂ := hmono_inner
    have : Mono ((TopPair.ofSubset (∅ : Set (TopCat.of U))).singularHomologyπ R k ≫
        (TopPair.singularHomologyMap (openToFrontierComplPair hU) R k ≫ f₂)) := by
      have := mono_comp (TopPair.singularHomologyMap (openToFrontierComplPair hU) R k) f₂
      exact mono_comp _ _
    rwa [hcomp]
  have hfst : TopPair.Hom.fst (openToFrontierComplPair hU ≫ TopTriple.innerToTotal.app T) =
      TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) := by
    ext x
    rfl
  rw [singularHomologyFunctor_obj_map, ← hfst]
  rwa [← TopPair.singularHomologyπ_naturality] at hmono_comp

/-- **Injectivity of open-subset homology when frontier local homology vanishes.** If `U ⊆ M` is
open and `Hₖ₊₁(M, M ∖ frontier U) = 0`, then the inclusion `U ↪ M` induces a monomorphism
`Hₖ(U; R) ⟶ Hₖ(M; R)`. -/
theorem mono_singularHomologyMap_subtype_of_isZero_localHomology_frontier
    (hU : IsOpen U) {k : ℕ} (hfr : IsZero (localHomology R (frontier U) (k + 1))) :
    Mono (((singularHomologyFunctor A k).obj R).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)))) :=
  have :=
    mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isZero_localHomology_frontier R hU
      hfr
  mono_of_mono _ ((TopPair.ofSubset ((closure U)ᶜ : Set (TopCat.of M))).singularHomologyπ R k)

end FrontierExcision

/-! ### Vanishing on topological manifolds (Hatcher's Proposition 3.29) -/

section ManifoldSameUniverse

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type w} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- On a Hausdorff manifold without boundary, for a relatively compact open subset `U ⊆ M` and
`finrank ℝ E ≤ k`, the composite `Hₖ(U; N) ⟶ Hₖ(M; N) ⟶ Hₖ(M, M ∖ closure U; N)` is a
monomorphism. -/
private lemma mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isCompact_closure_aux
    {U : Set M} (hU : IsOpen U) (hcpt : IsCompact (closure U)) {k : ℕ}
    (hk : finrank ℝ E ≤ k) :
    Mono (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M))) ≫
      (TopPair.ofSubset ((closure U)ᶜ : Set (TopCat.of M))).singularHomologyπ N k) :=
  mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isZero_localHomology_frontier N hU
    (isZero_localHomology_of_isCompact N (E := E) (n := finrank ℝ E) rfl
      (hcpt.of_isClosed_subset isClosed_frontier frontier_subset_closure) (by lia))

/-- Same-universe form of `mono_singularHomologyMap_subtype_of_isCompact_closure`. -/
private lemma mono_singularHomologyMap_subtype_of_isCompact_closure_aux
    {U : Set M} (hU : IsOpen U) (hcpt : IsCompact (closure U)) {k : ℕ}
    (hk : finrank ℝ E ≤ k) :
    Mono (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)))) :=
  have := mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isCompact_closure_aux N hU
    hcpt hk
  mono_of_mono _ ((TopPair.ofSubset ((closure U)ᶜ : Set (TopCat.of M))).singularHomologyπ N k)

/-- Same-universe form of `isZero_singularHomology_of_finrank_lt`. -/
private lemma isZero_singularHomology_of_finrank_lt_aux {k : ℕ} (hk : finrank ℝ E < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_iff_forall_eq 0 |>.2 fun γ ↦ ?_
  obtain ⟨U, hU, hcpt, γU, rfl⟩ := exists_isOpen_isCompact_closure_singularHomologyMap_eq N k γ
  have hmono :=
    mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isCompact_closure_aux N hU hcpt
      hk.le
  have hzero_tgt : IsZero (localHomology N (closure U) k) :=
    isZero_localHomology_of_isCompact N (E := E) (n := finrank ℝ E) rfl hcpt hk
  have hγU : γU = 0 :=
    (ModuleCat.mono_iff_injective _).1 hmono ((ModuleCat.subsingleton_of_isZero hzero_tgt).elim _ _)
  rw [hγU, map_zero]

/-- Same-universe form of `isZero_singularHomology_of_forall_not_isCompact_pathComponent`. -/
private lemma isZero_singularHomology_of_forall_not_isCompact_pathComponent_aux
    (hnc : ∀ x : M, ¬ IsCompact (pathComponent x)) {k : ℕ} (hk : finrank ℝ E ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M)) := by
  rcases hk.eq_or_lt with rfl | hlt
  · set n := finrank ℝ E
    have := ChartedSpace.locallyCompactSpace E M
    have := ChartedSpace.locallyPathConnectedSpace E M
    rw [ModuleCat.isZero_iff_subsingleton]
    refine subsingleton_iff_forall_eq 0 |>.2 fun γ ↦ ?_
    obtain ⟨U, hU, hcpt, γU, rfl⟩ := exists_isOpen_isCompact_closure_singularHomologyMap_eq N n γ
    have hmono :=
      mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isCompact_closure_aux (E := E)
        (k := n) N hU hcpt le_rfl
    let f : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
    -- `((singularHomologyFunctor _ n).obj N).obj (TopCat.of M)` is
    -- `(TopCat.toSSet.obj (TopCat.of M)).homology N n` by definition.
    let μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ) :=
      (((singularHomologyFunctor (ModuleCat.{w} Λ) n).obj N).map (TopCat.ofHom f)) γU
    have hγU : γU = 0 := by
      refine (ModuleCat.mono_iff_injective _).1 hmono ?_
      rw [map_zero]
      refine eq_zero_of_forall_localHomologyRestriction_eq_zero N (E := E) (n := n) rfl hcpt _
        fun x hx ↦ ?_
      have hnot_sub : ¬ pathComponent x ⊆ closure U := fun hsub ↦
        hnc x (hcpt.of_isClosed_subset (IsClosed.pathComponent x) hsub)
      obtain ⟨y, hxy, hyU⟩ := not_subset.1 hnot_sub
      have hy_range : y ∉ range f := by
        rintro ⟨z, rfl⟩
        exact hyU (subset_closure z.2)
      let p : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk x :=
        Path.Homotopic.Quotient.mk hxy.symm.somePath
      have htr :
          singularHomologyToLocalHomology N x n μ =
            localHomologyTransport N M E n p (singularHomologyToLocalHomology N y n μ) := by
        rw [singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_apply,
          ← localHomologyRestriction_univ_comp_localHomologyTransport N (M := M) (E := E) n p,
          ConcreteCategory.comp_apply]
      have hμy : singularHomologyToLocalHomology N y n μ = 0 :=
        singularHomologyToLocalHomology_singularHomologyMap_eq_zero N hy_range γU
      have hμx : singularHomologyToLocalHomology N x n μ = 0 := by
        rw [htr, hμy, map_zero]
      -- In `ModuleCat`, `(g ≫ π) γU` is `π (g γU) = π μ` by definition.
      exact (localHomologyRestriction_singularHomologyπ_apply N hx μ).trans hμx
    rw [hγU, map_zero]
  · exact isZero_singularHomology_of_finrank_lt_aux N hlt

end ManifoldSameUniverse

section Manifold

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type w} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- The canonical ring homomorphism `ULift.{w} ℤ →+* Λ` used to bring the coefficient ring into the
universe `w` of `M`. -/
private abbrev uliftIntRingHom (Λ : Type*) [Ring Λ] : ULift.{w} ℤ →+* Λ :=
  (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom

/-- **Injectivity of relatively compact open-subset homology on a manifold.** On a Hausdorff
topological `n`-manifold `M` without boundary, the inclusion `U ↪ M` of an open subset with compact
closure induces a monomorphism `Hₖ(U; N) ⟶ Hₖ(M; N)` in every degree `k ≥ n`. -/
theorem mono_singularHomologyMap_subtype_of_isCompact_closure
    {U : Set M} (hU : IsOpen U) (hcpt : IsCompact (closure U)) {k : ℕ}
    (hk : finrank ℝ E ≤ k) :
    Mono (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)))) :=
  let _ : ChartedSpace (ULift.{w} (Fin (finrank ℝ E)) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) (by simp)
  (ModuleCat.restrictScalars.{w} (uliftIntRingHom Λ)).mono_singularHomologyFunctor_map_of_mono
    N _ k (mono_singularHomologyMap_subtype_of_isCompact_closure_aux
      (E := ULift.{w} (Fin (finrank ℝ E)) → ℝ) _ hU hcpt (by simpa using hk))

/-- **Singular homology of a manifold vanishes above its dimension.** For any Hausdorff space `M`
charted on a real normed space `E` of finite dimension `n`, `Hₖ(M; N) = 0` for `k > n`, without
assuming compactness or second countability of `M`. This is the `k > n` part of Hatcher's
Proposition 3.29. -/
theorem isZero_singularHomology_of_finrank_lt {k : ℕ} (hk : finrank ℝ E < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M)) :=
  let _ : ChartedSpace (ULift.{w} (Fin (finrank ℝ E)) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) (by simp)
  ((ModuleCat.restrictScalars.{w} (uliftIntRingHom Λ)).isZero_singularHomologyFunctor_obj_iff
    N k (TopCat.of M)).mp
    (isZero_singularHomology_of_finrank_lt_aux
      (E := ULift.{w} (Fin (finrank ℝ E)) → ℝ) _ (by simpa using hk))

/-- **Top-dimensional singular homology vanishes when no path component is compact.** For a
Hausdorff space `M` charted on a real normed space `E` of finite dimension `n`, if no path component
of `M` is compact, then `Hₖ(M; N) = 0` for every `k ≥ n`. This is Hatcher's Proposition 3.29. -/
theorem isZero_singularHomology_of_forall_not_isCompact_pathComponent
    (hnc : ∀ x : M, ¬ IsCompact (pathComponent x)) {k : ℕ} (hk : finrank ℝ E ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M)) :=
  let _ : ChartedSpace (ULift.{w} (Fin (finrank ℝ E)) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) (by simp)
  ((ModuleCat.restrictScalars.{w} (uliftIntRingHom Λ)).isZero_singularHomologyFunctor_obj_iff
    N k (TopCat.of M)).mp
    (isZero_singularHomology_of_forall_not_isCompact_pathComponent_aux
      (E := ULift.{w} (Fin (finrank ℝ E)) → ℝ) _ hnc (by simpa using hk))

/-- **Top-dimensional singular homology of a connected noncompact manifold vanishes.** For a
preconnected noncompact Hausdorff space `M` charted on a real normed space `E` of finite dimension
`n`, `Hₖ(M; N) = 0` for every `k ≥ n`. -/
theorem isZero_singularHomology_of_noncompactSpace [PreconnectedSpace M] [NoncompactSpace M]
    {k : ℕ} (hk : finrank ℝ E ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M)) := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  refine isZero_singularHomology_of_forall_not_isCompact_pathComponent (E := E) N (fun x hcpt ↦ ?_)
    hk
  rw [pathComponent_eq_connectedComponent, PreconnectedSpace.connectedComponent_eq_univ,
    isCompact_univ_iff] at hcpt
  exact not_compactSpace_iff.mpr ‹NoncompactSpace M› hcpt

/-- **Nonzero top-degree singular homology forces compactness.** If a preconnected Hausdorff space
`M` charted on a real normed space `E` of finite dimension `n` has `Hₖ(M; N) ≠ 0` for some `k ≥ n`,
then `M` is compact. -/
theorem compactSpace_of_not_isZero_singularHomology [PreconnectedSpace M] {k : ℕ}
    (hk : finrank ℝ E ≤ k)
    (h : ¬ IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M))) :
    CompactSpace M := by
  by_contra hnc
  have : NoncompactSpace M := not_compactSpace_iff.mp hnc
  exact h (isZero_singularHomology_of_noncompactSpace (E := E) N hk)

/-- **Singular homology of an open subset of a manifold vanishes above the dimension.** -/
theorem isZero_singularHomology_of_isOpen_of_finrank_lt {U : Set M} (hU : IsOpen U) {k : ℕ}
    (hk : finrank ℝ E < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of U)) := by
  let _ : ChartedSpace E U := (⟨U, hU⟩ : TopologicalSpace.Opens M).instChartedSpace
  exact isZero_singularHomology_of_finrank_lt (E := E) N hk

/-- **Top-dimensional singular homology of a connected noncompact open subset of a manifold
vanishes.** -/
theorem isZero_singularHomology_of_isOpen_of_isPreconnected_of_not_isCompact
    {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) (hK : ¬ IsCompact U) {k : ℕ}
    (hk : finrank ℝ E ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of U)) := by
  let _ : ChartedSpace E U := (⟨U, hU⟩ : TopologicalSpace.Opens M).instChartedSpace
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  have : NoncompactSpace U := not_compactSpace_iff.mp (isCompact_iff_compactSpace.not.mp hK)
  exact isZero_singularHomology_of_noncompactSpace (E := E) N hk

end Manifold

end TauCeti
