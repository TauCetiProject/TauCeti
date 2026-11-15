/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Compact
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
import TauCeti.AlgebraicTopology.Singular.DirectedUnion

/-!
# Singular homology of noncompact manifolds

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary. For compact `M`, `Hₖ(M)` vanishes above degree `n`
because it is the local homology `Hₖ(M, M ∖ M)` of a compact set
(`TauCeti.isZero_singularHomology_of_compactSpace`). This file removes compactness above degree `n`
and proves that in degree `n` singular homology also vanishes whenever every path component of `M`
is noncompact, in particular when `M` is connected and noncompact. Together these are Hatcher's
Proposition 3.29.

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
`M`: charts are composed with a continuous linear equivalence onto
`EuclideanSpace ℝ (ULift (Fin n))` in the universe of `M`, and module coefficients are restricted
along `ULift ℤ →+* Λ`, which preserves singular homology
(`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`).

## Main definitions and results

* `TauCeti.openToFrontierComplPair` and `TauCeti.isIso_singularHomologyMap_openToFrontierComplPair`:
  for an open set `U ⊆ M`, the inclusion `(U, ∅) ⟶ (M ∖ frontier U, M ∖ closure U)` induces
  isomorphisms on relative singular homology in every degree.
* `TauCeti.mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isZero_localHomology_frontier`
  and `TauCeti.mono_singularHomologyMap_subtype_of_isZero_localHomology_frontier`: if
  `Hₖ₊₁(M, M ∖ frontier U) = 0` for open `U`, then `Hₖ(U) ⟶ Hₖ(M) ⟶ Hₖ(M, M ∖ closure U)` and
  `Hₖ(U) ⟶ Hₖ(M)` are monomorphisms.
* `TauCeti.exists_isOpen_isCompact_closure_singularHomologyMap_eq`: every singular homology class of
  a weakly locally compact Hausdorff space is supported on an open subset with compact closure.
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
* `TauCeti.isZero_singularHomology_isOpen_of_finrank_lt` and
  `TauCeti.isZero_singularHomology_isOpen_of_isPreconnected_of_not_isCompact`: the corresponding
  vanishing statements for open subsets `U ⊆ M`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Proposition 3.29.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Metric Module Set Topology

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

/-! ### Compact supports over relatively compact open subsets -/

section CompactSupport

/-- The open subsets of `X` with compact closure, ordered by inclusion. -/
private abbrev RelCompactOpens (X : Type w) [TopologicalSpace X] : Type w :=
  {U : TopologicalSpace.Opens X // IsCompact (closure (U : Set X))}

private instance {X : Type w} [TopologicalSpace X] : SemilatticeSup (RelCompactOpens X) where
  sup U V := ⟨U.1 ⊔ V.1, by
    change IsCompact (closure ((U.1 : Set X) ∪ (V.1 : Set X)))
    rw [closure_union]
    exact U.2.union V.2⟩
  le_sup_left _ _ := le_sup_left (α := TopologicalSpace.Opens X)
  le_sup_right _ _ := le_sup_right (α := TopologicalSpace.Opens X)
  sup_le _ _ _ := sup_le (α := TopologicalSpace.Opens X)

private instance {X : Type w} [TopologicalSpace X] : OrderBot (RelCompactOpens X) where
  bot := ⟨⊥, by simp⟩
  bot_le _ := bot_le (α := TopologicalSpace.Opens X)

/-- **Singular homology classes of a locally compact Hausdorff space live on relatively compact open
subsets.** Every class in `Hₖ(X; N)` is the image of a class in `Hₖ(U; N)` for some open subset
`U ⊆ X` whose closure is compact. -/
theorem exists_isOpen_isCompact_closure_singularHomologyMap_eq
    {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)
    {X : Type w} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X] (k : ℕ)
    (γ : (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of X) :
      ModuleCat.{w} Λ)) :
    ∃ U : Set X, IsOpen U ∧ IsCompact (closure U) ∧
      ∃ γU : (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of U) :
        ModuleCat.{w} Λ),
        ((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) γU = γ := by
  let D : RelCompactOpens X ⥤ TopCat.{w} :=
    { obj U := TopCat.of (U.1 : Set X)
      map f := TopCat.ofHom (ContinuousMap.inclusion f.le) }
  let G := D ⋙ (singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N
  have : PreservesColimit G
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} ⋙ forget AddCommGrpCat.{w}) :=
    Limits.comp_preservesColimit (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
      (forget AddCommGrpCat.{w})
  have : PreservesColimit G (forget (ModuleCat.{w} Λ)) :=
    preservesColimit_of_natIso G
      (eqToIso (HasForget₂.forget_comp (C := ModuleCat.{w} Λ) (D := AddCommGrpCat.{w})))
  let c : Cocone D :=
    { pt := TopCat.of X
      ι := { app U := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ } }
  have hK (K : Set c.pt) (hKc : IsCompact K) : ∃ U, K ⊆ range (c.ι.app U) := by
    obtain ⟨L, hLc, hKL⟩ := exists_compact_superset hKc
    refine ⟨⟨⟨interior L, isOpen_interior⟩, hLc.of_isClosed_subset isClosed_closure
        (hLc.isClosed.closure_subset_iff.2 interior_subset)⟩,
      fun x hx ↦ ⟨⟨x, hKL hx⟩, rfl⟩⟩
  obtain ⟨U, γU, hγU⟩ := Concrete.isColimit_exists_rep _
    (isColimitMapCoconeSingularHomology N k c (fun _ ↦ IsEmbedding.subtypeVal) hK) γ
  exact ⟨(U.1 : Set X), U.1.isOpen, U.2, γU, hγU⟩

end CompactSupport

/-! ### Vanishing on topological manifolds (Hatcher's Proposition 3.29) -/

section ManifoldSameUniverse

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type w} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- Same-universe form of `mono_singularHomologyMap_subtype_of_isCompact_closure`. -/
private lemma mono_singularHomologyMap_subtype_of_isCompact_closure_aux
    {U : Set M} (hU : IsOpen U) (hcpt : IsCompact (closure U)) {k : ℕ}
    (hk : finrank ℝ E ≤ k) :
    Mono (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)))) :=
  mono_singularHomologyMap_subtype_of_isZero_localHomology_frontier N hU
    (isZero_localHomology_of_isCompact N (E := E) (n := finrank ℝ E) rfl
      (hcpt.of_isClosed_subset isClosed_frontier frontier_subset_closure) (by lia))

/-- Same-universe form of `isZero_singularHomology_of_finrank_lt`. -/
private lemma isZero_singularHomology_of_finrank_lt_aux {k : ℕ} (hk : finrank ℝ E < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M)) := by
  have := ChartedSpace.locallyCompactSpace E M
  rw [ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_iff_forall_eq 0 |>.2 fun γ ↦ ?_
  obtain ⟨U, hU, hcpt, γU, rfl⟩ := exists_isOpen_isCompact_closure_singularHomologyMap_eq N k γ
  have hmono :=
    mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isZero_localHomology_frontier
      (k := k) N hU (isZero_localHomology_of_isCompact N (E := E) (n := finrank ℝ E) rfl
        (hcpt.of_isClosed_subset isClosed_frontier frontier_subset_closure) (by lia))
  have hzero_tgt : IsZero (localHomology N (closure U) k) :=
    isZero_localHomology_of_isCompact N (E := E) (n := finrank ℝ E) rfl hcpt hk
  have hγU : γU = 0 := by
    refine (ModuleCat.mono_iff_injective _).1 hmono ?_
    exact (ModuleCat.subsingleton_of_isZero hzero_tgt).elim _ _
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
      mono_singularHomologyMap_subtype_comp_singularHomologyπ_of_isZero_localHomology_frontier
        (k := n) N hU (isZero_localHomology_of_isCompact N (E := E) (n := n) rfl
          (hcpt.of_isClosed_subset isClosed_frontier frontier_subset_closure) (by lia))
    let ι : TopCat.of U ⟶ TopCat.of M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    -- Show that the image of `γU` in `Hₙ(M, M ∖ closure U)` vanishes at every `x ∈ closure U`.
    have hγU : γU = 0 := by
      refine (ModuleCat.mono_iff_injective _).1 hmono ?_
      rw [map_zero]
      refine eq_zero_of_forall_localHomologyRestriction_eq_zero N (E := E) (n := n) rfl hcpt _
        fun x hx ↦ ?_
      -- Since `pathComponent x` is closed and noncompact while `closure U` is compact,
      -- `pathComponent x` contains a point `y` outside `closure U`.
      have hpc_closed : IsClosed (pathComponent x) := by
        rw [pathComponent_eq_connectedComponent]
        exact isClosed_connectedComponent
      have hnot_sub : ¬ pathComponent x ⊆ closure U := fun hsub ↦
        hnc x (hcpt.of_isClosed_subset hpc_closed hsub)
      obtain ⟨y, hxy, hyU⟩ := not_subset.1 hnot_sub
      -- The inclusion `U ↪ M` factors through `M ∖ {y}`, and parallel transport from `y` to `x`
      -- along a path in `pathComponent x` identifies the local restrictions at `y` and `x`.
      have hUy : U ⊆ ({y} : Set M)ᶜ := fun z hz hzy ↦ hyU (hzy ▸ subset_closure hz)
      let Py := TopPair.ofSubset (({y} : Set M)ᶜ : Set (TopCat.of M))
      let j : TopCat.of U ⟶ Py.snd := TopCat.ofHom (ContinuousMap.inclusion hUy)
      let μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} Λ) :=
        SSet.homologyMap (TopCat.toSSet.map ι) N n γU
      have hμ_cl :
          localHomologyRestriction N (singleton_subset_iff.2 hx) n
            ((((singularHomologyFunctor (ModuleCat.{w} Λ) n).obj N).map ι ≫
              (TopPair.ofSubset ((closure U)ᶜ : Set (TopCat.of M))).singularHomologyπ N n) γU) =
            singularHomologyToLocalHomology N x n μ := by
        have hπ_cl :=
          TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id_assoc N
            (X := TopCat.of M) (S := ((closure U)ᶜ : Set M)) (S' := ((univ : Set M)ᶜ : Set M))
            (compl_subset_compl.2 (subset_univ (closure U))) n
            (localHomologyRestriction N (singleton_subset_iff.2 hx) n)
        rw [← localHomologyRestriction_def _ (subset_univ (closure U)),
          localHomologyRestriction_comp] at hπ_cl
        exact ((ConcreteCategory.comp_apply
          ((TopPair.ofSubset ((closure U)ᶜ : Set (TopCat.of M))).singularHomologyπ N n)
          (localHomologyRestriction N (singleton_subset_iff.2 hx) n) μ).symm.trans
            (ConcreteCategory.congr_hom hπ_cl.symm μ)).trans
              ((ConcreteCategory.comp_apply _ _ μ).trans
                (singularHomologyToLocalHomology_apply N x μ).symm)
      have hμ_y : singularHomologyToLocalHomology N y n μ = 0 := by
        have hπ_y :=
          TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id N
            (X := TopCat.of M) (S := (({y} : Set M)ᶜ : Set M)) (S' := ((univ : Set M)ᶜ : Set M))
            (compl_subset_compl.2 (subset_univ {y})) n
        rw [← localHomologyRestriction_def _ (subset_univ {y})] at hπ_y
        have hPy : Py.singularHomologyπ N n μ = 0 := by
          have h : SSet.homologyMap (TopCat.toSSet.map (j ≫ Py.map)) N n =
              SSet.homologyMap (TopCat.toSSet.map j) N n ≫
                SSet.homologyMap (TopCat.toSSet.map Py.map) N n := by
            rw [Functor.map_comp, SSet.homologyMap_comp]
          have hmor :
              SSet.homologyMap (TopCat.toSSet.map (j ≫ Py.map)) N n ≫
                Py.singularHomologyπ N n = 0 :=
            (h =≫ Py.singularHomologyπ N n).trans ((Category.assoc _ _ _).trans
              ((SSet.homologyMap (TopCat.toSSet.map j) N n ≫=
                Py.homologyMap_comp_singularHomologyπ N n).trans comp_zero))
          exact (ConcreteCategory.comp_apply _ _ γU).symm.trans
            ((ConcreteCategory.congr_hom hmor γU).trans rfl)
        exact (singularHomologyToLocalHomology_apply N y μ).trans
          (((ConcreteCategory.comp_apply _ _ μ).symm.trans
            (ConcreteCategory.congr_hom hπ_y μ)).trans hPy)
      let p : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk x :=
        Path.Homotopic.Quotient.mk hxy.symm.somePath
      have htr :
          singularHomologyToLocalHomology N x n μ =
            localHomologyTransport N M E n p (singularHomologyToLocalHomology N y n μ) := by
        have hp := localHomologyRestriction_univ_comp_localHomologyTransport
          N (M := M) (E := E) n p
        rw [singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_apply, ← hp,
          ConcreteCategory.comp_apply]
      rw [hμ_cl, htr, hμ_y, map_zero]
    rw [hγU, map_zero]
  · exact isZero_singularHomology_of_finrank_lt_aux N hlt

end ManifoldSameUniverse

section Manifold

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type w} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- Restricting scalars along `ULift.{w} ℤ →+* Λ` preserves coproducts without universe
restrictions, since composing with `forget₂ _ AddCommGrpCat` gives
`forget₂ (ModuleCat Λ) AddCommGrpCat`. -/
private lemma preservesColimitsOfShape_restrictScalars_uliftInt (T : Type w) :
    PreservesColimitsOfShape (Discrete T)
      (ModuleCat.restrictScalars.{w}
        ((Int.castRingHom Λ).comp (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).toRingHom)) := by
  let F := ModuleCat.restrictScalars.{w}
    ((Int.castRingHom Λ).comp (ULift.ringEquiv : ULift.{w} ℤ ≃+* ℤ).toRingHom)
  let G := forget₂ (ModuleCat.{w} (ULift.{w} ℤ)) AddCommGrpCat.{w}
  have : PreservesColimitsOfShape (Discrete T) (F ⋙ G) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete T)
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
  exact preservesColimitsOfShape_of_reflects_of_preserves (J := Discrete T) F G

/-- Restricting scalars along `ULift.{w} ℤ →+* Λ` identifies singular homology over `Λ` with
singular homology over `ULift.{w} ℤ` on the underlying types, so monomorphisms are reflected. -/
private lemma mono_of_mono_restrictScalars_uliftInt {X Y : TopCat.{w}} (f : X ⟶ Y) (k : ℕ)
    (h : Mono (((singularHomologyFunctor (ModuleCat.{w} (ULift.{w} ℤ)) k).obj
        ((ModuleCat.restrictScalars.{w}
          ((Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom)).obj N)).map f)) :
    Mono (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map f) := by
  have := preservesColimitsOfShape_restrictScalars_uliftInt (Λ := Λ)
  let φ : ULift.{w} ℤ →+* Λ := (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom
  let F := ModuleCat.restrictScalars.{w} φ
  let e := Functor.singularHomologyFunctorObjCompIso F N k
  have hnat : F.map (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map f) ≫ e.hom.app Y =
      e.hom.app X ≫
        ((singularHomologyFunctor (ModuleCat.{w} (ULift.{w} ℤ)) k).obj (F.obj N)).map f :=
    e.hom.naturality f
  have hmono_F : Mono (F.map (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map f)) := by
    have : Mono (F.map (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map f) ≫
        e.hom.app Y) := by
      rw [hnat]
      exact mono_comp _ _
    exact mono_of_mono _ (e.hom.app Y)
  rw [ModuleCat.mono_iff_injective] at hmono_F ⊢
  exact hmono_F

/-- Restricting scalars along `ULift.{w} ℤ →+* Λ` reflects vanishing of singular homology. -/
private lemma isZero_of_isZero_restrictScalars_uliftInt (X : TopCat.{w}) (k : ℕ)
    (h : IsZero (((singularHomologyFunctor (ModuleCat.{w} (ULift.{w} ℤ)) k).obj
        ((ModuleCat.restrictScalars.{w}
          ((Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom)).obj N)).obj X)) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj X) := by
  have := preservesColimitsOfShape_restrictScalars_uliftInt (Λ := Λ)
  let φ : ULift.{w} ℤ →+* Λ := (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom
  let F := ModuleCat.restrictScalars.{w} φ
  have hF : IsZero (F.obj (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj X)) :=
    h.of_iso ((Functor.singularHomologyFunctorObjCompIso F N k).app X)
  rw [ModuleCat.isZero_iff_subsingleton] at hF ⊢
  exact hF

/-- **Injectivity of relatively compact open-subset homology on a manifold.** On a Hausdorff
topological `n`-manifold `M` without boundary, the inclusion `U ↪ M` of an open subset with compact
closure induces a monomorphism `Hₖ(U; N) ⟶ Hₖ(M; N)` in every degree `k ≥ n`. -/
theorem mono_singularHomologyMap_subtype_of_isCompact_closure
    {U : Set M} (hU : IsOpen U) (hcpt : IsCompact (closure U)) {k : ℕ}
    (hk : finrank ℝ E ≤ k) :
    Mono (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)))) := by
  set n := finrank ℝ E with hn
  let E' := EuclideanSpace ℝ (ULift.{w} (Fin n))
  have hEE' : finrank ℝ E = finrank ℝ E' :=
    hn.symm.trans (finrank_euclideanSpace_ulift_fin.{w} n).symm
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq hEE'
  let := L.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp E' E M
  refine mono_of_mono_restrictScalars_uliftInt N _ k ?_
  exact mono_singularHomologyMap_subtype_of_isCompact_closure_aux (E := E') _ hU hcpt
    (hEE' ▸ hk)

/-- **Singular homology of a manifold vanishes above its dimension.** For any Hausdorff space `M`
charted on a real normed space `E` of finite dimension `n`, `Hₖ(M; N) = 0` for `k > n`, without
assuming compactness or second countability of `M`. This is the `k > n` part of Hatcher's
Proposition 3.29. -/
theorem isZero_singularHomology_of_finrank_lt {k : ℕ} (hk : finrank ℝ E < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M)) := by
  set n := finrank ℝ E with hn
  let E' := EuclideanSpace ℝ (ULift.{w} (Fin n))
  have hEE' : finrank ℝ E = finrank ℝ E' :=
    hn.symm.trans (finrank_euclideanSpace_ulift_fin.{w} n).symm
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq hEE'
  let := L.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp E' E M
  refine isZero_of_isZero_restrictScalars_uliftInt N (TopCat.of M) k ?_
  exact isZero_singularHomology_of_finrank_lt_aux (E := E') _ (hEE' ▸ hk)

/-- **Top-dimensional singular homology vanishes when no path component is compact.** For a
Hausdorff space `M` charted on a real normed space `E` of finite dimension `n`, if no path component
of `M` is compact, then `Hₖ(M; N) = 0` for every `k ≥ n`. This is Hatcher's Proposition 3.29. -/
theorem isZero_singularHomology_of_forall_not_isCompact_pathComponent
    (hnc : ∀ x : M, ¬ IsCompact (pathComponent x)) {k : ℕ} (hk : finrank ℝ E ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of M)) := by
  set n := finrank ℝ E with hn
  let E' := EuclideanSpace ℝ (ULift.{w} (Fin n))
  have hEE' : finrank ℝ E = finrank ℝ E' :=
    hn.symm.trans (finrank_euclideanSpace_ulift_fin.{w} n).symm
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq hEE'
  let := L.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp E' E M
  refine isZero_of_isZero_restrictScalars_uliftInt N (TopCat.of M) k ?_
  exact isZero_singularHomology_of_forall_not_isCompact_pathComponent_aux (E := E') _ hnc
    (hEE' ▸ hk)

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
theorem isZero_singularHomology_isOpen_of_finrank_lt {U : Set M} (hU : IsOpen U) {k : ℕ}
    (hk : finrank ℝ E < k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of U)) := by
  let _ : ChartedSpace E U := (⟨U, hU⟩ : TopologicalSpace.Opens M).instChartedSpace
  exact isZero_singularHomology_of_finrank_lt (E := E) N hk

/-- **Top-dimensional singular homology of a connected noncompact open subset of a manifold
vanishes.** -/
theorem isZero_singularHomology_isOpen_of_isPreconnected_of_not_isCompact
    {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) (hK : ¬ IsCompact U) {k : ℕ}
    (hk : finrank ℝ E ≤ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj (TopCat.of U)) := by
  let _ : ChartedSpace E U := (⟨U, hU⟩ : TopologicalSpace.Opens M).instChartedSpace
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  have : NoncompactSpace U := not_compactSpace_iff.mp (isCompact_iff_compactSpace.not.mp hK)
  exact isZero_singularHomology_of_noncompactSpace (E := E) N hk

end Manifold

end TauCeti
