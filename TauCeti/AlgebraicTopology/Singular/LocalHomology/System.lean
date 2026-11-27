/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
public import TauCeti.Topology.OpenPartialHomeomorph.Basic
import TauCeti.Geometry.Manifold.ModelTransport.Finrank

/-!
# The local homology system of a manifold

Let `M` be a Hausdorff space modelled on a finite-dimensional real normed space `E`, that is,
a topological manifold without boundary. This file assembles the local homology groups
`Hₖ(M, M ∖ {x})` into a functor out of the fundamental groupoid of `M`,
`TauCeti.localHomologySystem R M E k`. For `k = dim E` and integer coefficients this is the
orientation local system of `M`: a local orientation at `x` is a generator of
`Hₙ(M, M ∖ {x}; ℤ)`, and the functor transports local orientations along paths. With
`A = ModuleCat S` for a ring `S` it is a `TauCeti.LocalCoefficientSystem`.

The transport is determined by compact convex sets in charts. Let `φ : M → E` be an open
partial homeomorphism and let `K ⊆ φ.target` be compact and convex. For every `x` with
`φ x ∈ K`, the restriction `Hₖ(M, M ∖ φ.symm '' K) ⟶ Hₖ(M, M ∖ {x})` is an isomorphism
(`TauCeti.isIso_localHomologyRestriction_symm_image`). The transport along a path inside
`φ.symm '' K` is the unique map compatible with these restrictions at its two endpoints
(`TauCeti.localHomologyRestriction_comp_localHomologyTransport`), and this property together with
compatibility with composition characterizes the transport
(`TauCeti.eq_localHomologyTransport`).

## Main definitions and results

* `TauCeti.localHomology R S k`: the relative singular homology `Hₖ(M, M ∖ S)`.
* `TauCeti.localHomologyRestriction`: for `S ⊆ T`, the map `Hₖ(M, M ∖ T) ⟶ Hₖ(M, M ∖ S)`
  induced by the identity of `M`.
* `TauCeti.singularHomologyToLocalHomology`: with module coefficients, the map
  `Hₖ(M; N) → Hₖ(M, M ∖ {x}; N)` from singular homology to the local homology at `x`, the map of
  the long exact sequence of the pair `(M, M ∖ {x})`
  (`TauCeti.singularHomologyToLocalHomology_eq_singularHomologyπ`), vanishing on classes pushed
  forward from subsets avoiding `x`
  (`TauCeti.singularHomologyToLocalHomology_map_subtypeVal_eq_zero_of_notMem`). For `x ∈ S` it
  factors through the local homology along `S`
  (`TauCeti.singularHomologyToLocalHomology_eq_localHomologyRestriction`).
* `TauCeti.singularHomologyπ_compl_univ_bijective`: the quotient map `Hₖ(M) → Hₖ(M, M ∖ M)` is
  bijective.
* `TauCeti.localHomologySingletonLinearEquiv`: with coefficients `N ≃ₗ[Λ] Λ`, the local homology
  `Hₙ(M, M ∖ {x}; N)` of an `n`-manifold is a copy of `Λ`.
* `TauCeti.localHomologyMap`: for a continuous map `j : M → N` with `j ⁻¹' T ⊆ S`, the map
  `Hₖ(M, M ∖ S) ⟶ Hₖ(N, N ∖ T)` induced by `j`. It is functorial, is the restriction map for `j`
  the identity, and is compatible with restriction on both sides. Restricted to a point of `T`
  outside the range of `j` it is zero
  (`TauCeti.localHomologyMap_comp_localHomologyRestriction_eq_zero_of_notMem_range`).
* `TauCeti.homologyMap_comp_singularHomologyπ_ofSubset`: passing from `Hₖ(M)` to `Hₖ(M, M ∖ S)`
  is natural in continuous maps.
* `TauCeti.singularHomologyπ_univ_singularHomologyMap`: its element-level form for
  `Hₖ(M, M ∖ M)`.
* `TauCeti.singularHomologyToLocalHomology_singularHomologyMap`: passing to local homology is
  natural in maps `j` for which `x` is the only preimage of `j x`.
* `TauCeti.localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom`: the
  local homology isomorphism of a chart is the map induced by the chart on its source.
* `TauCeti.isZero_localHomology_empty`: `Hₖ(M, M) = 0`.
* `TauCeti.isIso_singularHomologyδ_ofSubset_compl`: the connecting morphism of the triple
  `(M, M ∖ T, M ∖ S)` is an isomorphism when the local homology along `S` vanishes.
* `TauCeti.isIso_localHomologyRestriction_symm_image`: the restriction from a compact set in a
  chart, star-convex about one of its points, to that point is an isomorphism.
* `TauCeti.exists_isCompact_subset_mem_nhds_isIso_localHomologyRestriction`: inside every
  neighbourhood of a point there is a compact neighbourhood `B` from which the restriction to each
  of its points is an isomorphism.
* `TauCeti.localHomologyTransport`: the transport of local homology along a path class.
* `TauCeti.localHomologySystem`: the local homology groups as a functor out of the fundamental
  groupoid, with these transport maps.
* `TauCeti.localHomologyRestriction_comp_localHomologyTransport`: the transport along a path
  inside a compact convex set in a chart.
* `TauCeti.eq_localHomologyTransport`: the transport is the only family of maps compatible with
  composition that has this property.
* `TauCeti.singularHomologyToLocalHomology_eq_zero_of_joined`: vanishing in local homology
  transports along paths on any Hausdorff boundaryless manifold.

## Implementation notes

On each open convex patch of a chart there is a functor sending a path to the comparison of its
endpoints through the closure of the patch. Two patches give the same comparison near each point
of their overlap, since both factor through a small ball in one chart. So the local functors
agree on overlaps, and they glue (`TauCeti.FundamentalGroupoid.glue`) to a functor out of the
fundamental groupoid of `M`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, the local homology groups `Hₙ(M | x)`, local
  orientations, and the comparison through `Hₙ(M | B)` for balls `B` in charts, which Hatcher
  uses to topologize the orientation covering `M_R`.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section Restriction

variable {M : Type w} [TopologicalSpace M]

/-- The relative singular homology `Hₖ(M, M ∖ S)` of `M` modulo the complement of `S`. For
`S = {x}` it is the local homology of `M` at `x`. -/
abbrev localHomology (S : Set M) (k : ℕ) : A :=
  (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomology R k

/-- The degree-zero relative class of a point, as the coefficient morphism into local homology
along a set. This is the actual point section followed by the quotient map. -/
def localHomologyPointClass (S : Set M) (x : M) : R ⟶ localHomology R S 0 :=
  singularHomology₀Section R (X := TopCat.of M) x ≫
    (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ R 0

/-- The point class is the image of the absolute point section under the relative quotient. -/
@[elementwise]
lemma localHomologyPointClass_def (S : Set M) (x : M) :
    localHomologyPointClass R S x = singularHomology₀Section R (X := TopCat.of M) x ≫
      (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ R 0 := by rfl

/-- The inverse of a rank-zero chart's homology coordinate is the actual relative point class. -/
@[elementwise nosimp]
lemma singularHomologyComplSingletonIsoOfFinrankEqZero_inv_eq_localHomologyPointClass
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [T1Space M] (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source)
    (h : Module.finrank ℝ E = 0) :
    (singularHomologyComplSingletonIsoOfFinrankEqZero R φ hx h).inv =
      localHomologyPointClass R {x} x := by
  rw [localHomologyPointClass_def]
  apply (cancel_mono (singularHomologyComplSingletonIsoOfChart R φ hx 0).hom).1
  calc
    _ = singularHomology₀Section R (φ x) ≫
        (TopPair.ofSubset ({φ x}ᶜ : Set (TopCat.of E))).singularHomologyπ R 0 := by
      rw [singularHomologyComplSingletonIsoOfFinrankEqZero_inv]
      -- The point section uses the singular functor's object, whereas the projection uses
      -- simplicial homology; `erw` unfolds these equal presentations before reassociating.
      erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
    _ = _ := (singularHomology₀Section_comp_singularHomologyComplSingletonIsoOfChart_hom
      R φ hx).symm

/-- The subspace `M ∖ M` of the pair `(M, M ∖ M)` is empty, so `Hₖ(M, M ∖ M)` is the singular
homology of `M`. -/
instance isEmpty_ofSubset_compl_univ_snd :
    IsEmpty (TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).snd := by
  simp only [compl_univ]
  exact inferInstanceAs (IsEmpty (∅ : Set M))

/-- For `S ⊆ T`, the map `Hₖ(M, M ∖ T) ⟶ Hₖ(M, M ∖ S)` on relative singular homology induced by
the identity of `M`. -/
def localHomologyRestriction {S T : Set M} (h : S ⊆ T) (k : ℕ) :
    localHomology R T k ⟶ localHomology R S k :=
  TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (compl_subset_compl.2 h)) R k

lemma localHomologyRestriction_def {S T : Set M} (h : S ⊆ T) (k : ℕ) :
    localHomologyRestriction R h k =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M))
        (compl_subset_compl.2 h)) R k :=
  (rfl)

@[simp]
lemma localHomologyRestriction_refl (S : Set M) (k : ℕ) :
    localHomologyRestriction R (subset_refl S) k = 𝟙 _ :=
  (congrArg (TopPair.singularHomologyMap · R k) (TopPair.ofSubsetMap_id _)).trans
    (TopPair.singularHomologyMap_id _ R k)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma localHomologyRestriction_comp {S T W : Set M} (h₁ : S ⊆ T) (h₂ : T ⊆ W) (k : ℕ) :
    localHomologyRestriction R h₂ k ≫ localHomologyRestriction R h₁ k =
      localHomologyRestriction R (h₁.trans h₂) k := by
  rw [localHomologyRestriction, localHomologyRestriction, localHomologyRestriction,
    ← TopPair.singularHomologyMap_comp]
  -- `𝟙 ≫ 𝟙` is definitionally `𝟙` in `TopCat`, so `ofSubsetMap_comp` applies up to the `MapsTo`
  -- proofs; rewriting with `Category.id_comp` is blocked because those proofs depend on the map.
  exact congrArg (TopPair.singularHomologyMap · R k)
    (TopPair.ofSubsetMap_comp (𝟙 (TopCat.of M)) (𝟙 (TopCat.of M)) _ _ _).symm

/-- Restricting the quotient map `Hₖ(M; R) ⟶ Hₖ(M, M ∖ T; R)` along `S ⊆ T` gives the quotient map
`Hₖ(M; R) ⟶ Hₖ(M, M ∖ S; R)`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma singularHomologyπ_localHomologyRestriction {S T : Set M} (h : S ⊆ T) (k : ℕ) :
    (TopPair.ofSubset (Tᶜ : Set (TopCat.of M))).singularHomologyπ R k ≫
        localHomologyRestriction R h k =
      (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ R k := by
  rw [localHomologyRestriction_def]
  exact TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id R
    (compl_subset_compl.2 h) k

/-- Restricting the relative point class is the point class in the smaller pair. -/
@[reassoc, elementwise]
lemma localHomologyPointClass_restriction {S T : Set M} (h : S ⊆ T) (x : M) :
    localHomologyPointClass R T x ≫ localHomologyRestriction R h 0 =
      localHomologyPointClass R S x := by
  rw [localHomologyPointClass_def, localHomologyPointClass_def]
  exact (Category.assoc _ _ _).trans
    (singularHomology₀Section R x ≫= singularHomologyπ_localHomologyRestriction R h 0)

/-- **Local homology along the empty set vanishes**: `Hₖ(M, M) = 0`. -/
theorem isZero_localHomology_empty (k : ℕ) : IsZero (localHomology R (∅ : Set M) k) := by
  rw [IsZero.iff_id_eq_zero, ← TopPair.singularHomologyMap_id]
  exact TopPair.singularHomologyMap_eq_zero_of_fac _ R
    (TopCat.ofHom (⟨fun x ↦ ⟨x, by simp⟩, by fun_prop⟩ : C(M, ((∅ : Set M)ᶜ : Set M)))) rfl k

/-- The connecting morphism `Hₖ₊₁(M, M ∖ T) ⟶ Hₖ(M ∖ T, M ∖ S)` of the triple
`(M, M ∖ T, M ∖ S)` for `T ⊆ S` is an isomorphism when the local homology along `S` vanishes in
the two adjacent degrees. -/
theorem isIso_singularHomologyδ_ofSubset_compl {S T : Set M} (h : T ⊆ S) (k : ℕ)
    (hk : IsZero (localHomology R S (k + 1))) (hk' : IsZero (localHomology R S k)) :
    IsIso ((TopTriple.ofSubset (X := TopCat.of M) (compl_subset_compl.2 h)).singularHomologyδ R
      (k + 1) k) :=
  -- `localHomology R S` is by definition the homology of the pair `TopPair.ofSubset Sᶜ`.
  TopTriple.isIso_singularHomologyδ_of_isZero _ R (k + 1) k
    (hk.of_iso (TopPair.singularHomologyMapIso R (TopTriple.ofSubsetTotalPairIso _) _).symm)
    (hk'.of_iso (TopPair.singularHomologyMapIso R (TopTriple.ofSubsetTotalPairIso _) _).symm)

/-- Let `S ⊆ T` contain `x` and `y`, and let the restrictions from `S` and from `T` to `x` be
isomorphisms. Then comparing `x` with `y` through `T` and restricting from `S` to `x` gives the
restriction from `S` to `y`. -/
private lemma localHomologyRestriction_comp_inv_comp {S T : Set M} (hST : S ⊆ T) {x y : M}
    (hx : {x} ⊆ S) (hy : {y} ⊆ S) (k : ℕ) [IsIso (localHomologyRestriction R hx k)]
    [IsIso (localHomologyRestriction R (Set.Subset.trans hx hST) k)] :
    localHomologyRestriction R hx k ≫
        inv (localHomologyRestriction R (Set.Subset.trans hx hST) k) ≫
          localHomologyRestriction R (Set.Subset.trans hy hST) k =
      localHomologyRestriction R hy k := by
  have hfac := localHomologyRestriction_comp R hx hST k
  have := IsIso.of_isIso_fac_right hfac
  have hinv : localHomologyRestriction R hx k ≫
      inv (localHomologyRestriction R (Set.Subset.trans hx hST) k) =
        inv (localHomologyRestriction R hST k) :=
    IsIso.eq_inv_of_hom_inv_id (by rw [← Category.assoc, hfac, IsIso.hom_inv_id])
  rw [← Category.assoc, hinv, ← localHomologyRestriction_comp R hy hST, IsIso.inv_hom_id_assoc]

end Restriction

section SingularHomology

variable {M : Type w} [TopologicalSpace M] {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)

/-- The map `Hₖ(M; N) → Hₖ(M, M ∖ {x}; N)` from the singular homology of `M` to its local
homology at `x`: the quotient map to `Hₖ(M, M ∖ M; N)` followed by restriction to `{x}`. -/
def singularHomologyToLocalHomology (x : M) (k : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ) →ₗ[Λ]
      (localHomology N ({x} : Set M) k : ModuleCat.{w} Λ) :=
  ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ (C := ModuleCat.{w} Λ) N k ≫
    localHomologyRestriction N (subset_univ {x}) k).hom

theorem singularHomologyToLocalHomology_apply (x : M) {k : ℕ}
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)) :
    singularHomologyToLocalHomology N x k μ =
      localHomologyRestriction N (subset_univ {x}) k
        (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
          (C := ModuleCat.{w} Λ) N k).hom μ) :=
  (rfl)

/-- The map to the local homology at `x` is the map `Hₖ(M; N) → Hₖ(M, M ∖ {x}; N)` of the long exact
sequence of the pair `(M, M ∖ {x})`. -/
theorem singularHomologyToLocalHomology_eq_singularHomologyπ (x : M) {k : ℕ}
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)) :
    singularHomologyToLocalHomology N x k μ =
      ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (C := ModuleCat.{w} Λ) N k).hom μ := by
  rw [singularHomologyToLocalHomology_apply, localHomologyRestriction_def]
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ μ)
    (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id N
      (fun _ h ↦ absurd h (by simp)) k)

private lemma homologyMap_subtypeVal_comp_singularHomologyπ_eq_zero {K : Set M} {x : M}
    (hx : x ∉ K) (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal K))) N k ≫
      (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ (C := ModuleCat.{w} Λ) N k =
        0 := by
  let P := TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))
  let j : TopCat.of K ⟶ P.snd := TopCat.ofHom ⟨fun y ↦ ⟨y.val, fun h ↦ hx (h ▸ y.property)⟩,
      by fun_prop⟩
  have hj : (TopCat.ofHom (ContinuousMap.subtypeVal K) : TopCat.of K ⟶ P.fst) = j ≫ P.map := by
    ext; rfl
  -- `P.fst` is definitionally `TopCat.of M`.
  change SSet.homologyMap (TopCat.toSSet.map (Y := P.fst)
      (TopCat.ofHom (ContinuousMap.subtypeVal K))) N k ≫
    P.singularHomologyπ (C := ModuleCat.{w} Λ) N k = 0
  rw [hj, TopCat.toSSet.map_comp, SSet.homologyMap_comp]
  exact (Category.assoc _ _ _).trans (by simp)

/-- A class pushed forward from a subset `K ⊆ M` vanishes in the local homology at every point
outside `K`. -/
theorem singularHomologyToLocalHomology_map_subtypeVal_eq_zero_of_notMem {K : Set M} {x : M}
    (hx : x ∉ K) {k : ℕ}
    (α : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).obj
      (TopCat.of K)) :
    singularHomologyToLocalHomology N x k
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) k).obj N).map
          (TopCat.ofHom (ContinuousMap.subtypeVal K)) α) = 0 := by
  -- `((singularHomologyFunctor _ k).obj N).obj X` and `.map f` are definitionally
  -- `(TopCat.toSSet.obj X).homology N k` and `SSet.homologyMap (TopCat.toSSet.map f) N k`.
  let α' : ((TopCat.toSSet.obj (TopCat.of K)).homology N k : ModuleCat.{w} Λ) := α
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (homologyMap_subtypeVal_comp_singularHomologyπ_eq_zero N hx k)) α'
  rw [ModuleCat.hom_zero, LinearMap.zero_apply] at h
  exact (singularHomologyToLocalHomology_eq_singularHomologyπ N x _).trans
    ((ConcreteCategory.comp_apply _ _ α').symm.trans h)

variable (M) in
/-- The quotient map `Hₖ(M) → Hₖ(M, M ∖ M)` is bijective, the subspace `M ∖ M` being empty. -/
theorem singularHomologyπ_compl_univ_bijective (k : ℕ) :
    Function.Bijective ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
      (C := ModuleCat.{w} Λ) N k) :=
  (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- With coefficients `N ≃ₗ[Λ] Λ`, the local homology `Hₙ(M, M ∖ {x}; N)` of a manifold of
dimension `n` at a point `x` is a copy of `Λ`, through the computation of local homology in the
chart at `x` (`TauCeti.singularHomologyComplSingletonFinrankIso`). -/
def localHomologySingletonLinearEquiv [T1Space M] {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
    (hn : Module.finrank ℝ E = n) (eN : N ≃ₗ[Λ] Λ) (x : M) :
    (localHomology N ({x} : Set M) n : ModuleCat.{w} Λ) ≃ₗ[Λ] Λ :=
  ((hn ▸ singularHomologyComplSingletonFinrankIso N (chartAt E x) (mem_chart_source E x) :
    localHomology N ({x} : Set M) n ≅ N).toLinearEquiv).trans eN

/-- The local class of `μ` at a point `x` of a set `S` is the restriction to `x` of the image of
`μ` in the local homology `Hₖ(M, M ∖ S; N)` along `S`. -/
theorem singularHomologyToLocalHomology_eq_localHomologyRestriction {S : Set M} {x : M}
    (hx : x ∈ S) {k : ℕ}
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)) :
    singularHomologyToLocalHomology N x k μ =
      localHomologyRestriction N (singleton_subset_iff.2 hx) k
        (((TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ
          (C := ModuleCat.{w} Λ) N k).hom μ) := by
  rw [singularHomologyToLocalHomology_eq_singularHomologyπ]
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ μ)
    (singularHomologyπ_localHomologyRestriction N (singleton_subset_iff.2 hx) k).symm

end SingularHomology

section Map

variable {M N P : Type w} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  (j : C(M, N))

/-- For a continuous map `j : M → N` and sets `S ⊆ M`, `T ⊆ N` with `j ⁻¹' T ⊆ S`, the map
`Hₖ(M, M ∖ S) ⟶ Hₖ(N, N ∖ T)` of local homology induced by the map of pairs
`j : (M, M ∖ S) ⟶ (N, N ∖ T)`. -/
def localHomologyMap {S : Set M} {T : Set N} (h : j ⁻¹' T ⊆ S) (k : ℕ) :
    localHomology R S k ⟶ localHomology R T k :=
  TopPair.singularHomologyMap
    (TopPair.ofSubsetMap (X := TopCat.of M) (Y := TopCat.of N) (B := Sᶜ) (B' := Tᶜ)
      (TopCat.ofHom j) ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h))) R k

lemma localHomologyMap_def {S : Set M} {T : Set N} (h : j ⁻¹' T ⊆ S) (k : ℕ) :
    localHomologyMap R j h k =
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of M) (Y := TopCat.of N) (B := Sᶜ) (B' := Tᶜ)
          (TopCat.ofHom j) ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h))) R k :=
  (rfl)

/-- A map of local homology carries the actual relative point class to its image point. -/
@[reassoc, elementwise]
lemma localHomologyPointClass_map {S : Set M} {T : Set N} (h : j ⁻¹' T ⊆ S) (x : M) :
    localHomologyPointClass R S x ≫ localHomologyMap R j h 0 =
      localHomologyPointClass R T (j x) := by
  let hf : Set.MapsTo (TopCat.ofHom j) Sᶜ Tᶜ :=
    (mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h)
  let f := TopPair.ofSubsetMap (X := TopCat.of M) (Y := TopCat.of N)
    (B := Sᶜ) (B' := Tᶜ) (TopCat.ofHom j) hf
  rw [localHomologyPointClass_def, localHomologyPointClass_def, localHomologyMap_def]
  exact TopPair.singularHomology₀Section_singularHomologyMap _ R f x (j x)
    (TopPair.ofSubsetMap_fst_apply (X := TopCat.of M) (Y := TopCat.of N)
      (TopCat.ofHom j) hf x)

/-- Equal continuous maps induce equal maps of local homology, with the preimage hypothesis
transported along the equality. -/
lemma localHomologyMap_congr {j₁ j₂ : C(M, N)} (hj : j₁ = j₂) {S : Set M} {T : Set N}
    (h : j₁ ⁻¹' T ⊆ S) (k : ℕ) :
    localHomologyMap R j₁ h k = localHomologyMap R j₂ (hj ▸ h) k := by
  subst hj
  rfl

/-- The map of local homology induced by the identity is the restriction map. -/
@[simp]
lemma localHomologyMap_id {S T : Set M} (h : ContinuousMap.id M ⁻¹' T ⊆ S) (k : ℕ) :
    localHomologyMap R (ContinuousMap.id M) h k = localHomologyRestriction R h k := by
  rw [localHomologyMap, localHomologyRestriction_def]
  exact congrArg (TopPair.singularHomologyMap · R k) (TopPair.hom_ext_of_fst _ (rfl))

/-- A continuous self-map equal to the identity induces the identity on the local homology at any
set whose preimage it keeps inside the set. -/
lemma localHomologyMap_eq_id {j : C(M, M)} (hj : j = ContinuousMap.id M) {S : Set M}
    (h : j ⁻¹' S ⊆ S) (k : ℕ) : localHomologyMap R j h k = 𝟙 _ := by
  subst hj
  rw [localHomologyMap_id]
  exact localHomologyRestriction_refl R S k

/-- The maps of local homology are functorial. -/
@[reassoc (attr := simp)]
lemma localHomologyMap_comp (j' : C(N, P)) {S : Set M} {T : Set N} {W : Set P}
    (h : j ⁻¹' T ⊆ S) (h' : j' ⁻¹' W ⊆ T) (k : ℕ) :
    localHomologyMap R j h k ≫ localHomologyMap R j' h' k =
      localHomologyMap R (j'.comp j) ((preimage_mono h').trans h) k := by
  rw [localHomologyMap, localHomologyMap, localHomologyMap, ← TopPair.singularHomologyMap_comp]
  exact congrArg (TopPair.singularHomologyMap · R k)
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (rfl))

/-- Restricting before the map of local homology is the map from the larger set. -/
@[reassoc (attr := simp)]
lemma localHomologyRestriction_comp_localHomologyMap {S S' : Set M} {T : Set N} (hS : S ⊆ S')
    (h : j ⁻¹' T ⊆ S) (k : ℕ) :
    localHomologyRestriction R hS k ≫ localHomologyMap R j h k =
      localHomologyMap R j (h.trans hS) k := by
  rw [localHomologyRestriction_def, localHomologyMap, localHomologyMap,
    ← TopPair.singularHomologyMap_comp]
  exact congrArg (TopPair.singularHomologyMap · R k)
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (Category.id_comp _))

/-- Restricting after the map of local homology is the map to the smaller set. -/
@[reassoc (attr := simp)]
lemma localHomologyMap_comp_localHomologyRestriction {S : Set M} {T T' : Set N} (hT : T ⊆ T')
    (h : j ⁻¹' T' ⊆ S) (k : ℕ) :
    localHomologyMap R j h k ≫ localHomologyRestriction R hT k =
      localHomologyMap R j ((preimage_mono hT).trans h) k := by
  rw [localHomologyRestriction_def, localHomologyMap, localHomologyMap,
    ← TopPair.singularHomologyMap_comp]
  exact congrArg (TopPair.singularHomologyMap · R k)
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (Category.comp_id _))

/-- Restricting the map of local homology `Hₖ(M, M ∖ S) ⟶ Hₖ(N, N ∖ T)` to a point `y ∈ T` outside
the range of `j` gives zero: no point of `M` lies over `y`, so the composite factors through
`Hₖ(M, M) = 0`. -/
theorem localHomologyMap_comp_localHomologyRestriction_eq_zero_of_notMem_range {S : Set M}
    {T : Set N} (h : j ⁻¹' T ⊆ S) {y : N} (hy : y ∈ T) (hyj : y ∉ range j) (k : ℕ) :
    localHomologyMap R j h k ≫ localHomologyRestriction R (singleton_subset_iff.2 hy) k = 0 := by
  have h' : j ⁻¹' {y} ⊆ ∅ := fun z hz ↦ hyj ⟨z, hz⟩
  rw [localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_comp_localHomologyMap R j (empty_subset S) h',
    (isZero_localHomology_empty R k).eq_zero_of_tgt (localHomologyRestriction R _ k), zero_comp]

/-- **Homotopy invariance of the maps of local homology.** Maps `j₀, j₁ : M → N` joined by a
homotopy that never sends a point outside `S` into `T` induce the same map
`Hₖ(M, M ∖ S) ⟶ Hₖ(N, N ∖ T)`. -/
theorem localHomologyMap_eq_of_homotopy {j₀ j₁ : C(M, N)} (F : j₀.Homotopy j₁) {S : Set M}
    {T : Set N} (hF : ∀ (τ : unitInterval) (y : M), y ∉ S → F (τ, y) ∉ T)
    (h₀ : j₀ ⁻¹' T ⊆ S) (h₁ : j₁ ⁻¹' T ⊆ S) (k : ℕ) :
    localHomologyMap R j₀ h₀ k = localHomologyMap R j₁ h₁ k :=
  (TopPair.ofSubsetHomotopy (g₀ := TopCat.ofHom j₀) (g₁ := TopCat.ofHom j₁)
    (B := (Sᶜ : Set (TopCat.of M))) (B' := (Tᶜ : Set (TopCat.of N))) F
    fun τ y hy ↦ hF τ y hy).congr_singularHomologyMap R k

/-- **Naturality of the passage to relative homology.** For `j : M → N` with `j ⁻¹' T ⊆ S`,
mapping `Hₖ(M) ⟶ Hₖ(N)` by `j` and then passing to `Hₖ(N, N ∖ T)` is passing to
`Hₖ(M, M ∖ S)` followed by the map of local homology induced by `j`. -/
@[reassoc]
theorem homologyMap_comp_singularHomologyπ_ofSubset {S : Set M} {T : Set N} (h : j ⁻¹' T ⊆ S)
    (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom j)) R k ≫
        (TopPair.ofSubset (Tᶜ : Set (TopCat.of N))).singularHomologyπ R k =
      (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomologyπ R k ≫
        localHomologyMap R j h k := by
  have h' := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap (X := TopCat.of M) (Y := TopCat.of N) (B := Sᶜ) (B' := Tᶜ)
      (TopCat.ofHom j) ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h))) R k
  simp only [TopPair.ofSubsetMap_fst] at h'
  rw [localHomologyMap_def]
  exact h'

end Map

section SingularHomologyMap

variable {M N : Type w} [TopologicalSpace M] [TopologicalSpace N] {Λ : Type*} [Ring Λ]
  (L : ModuleCat.{w} Λ)

/-- The image of `j_* μ ∈ Hₖ(N; L)` in `Hₖ(N, N ∖ N; L)` is the image of `μ` in `Hₖ(M, M ∖ M; L)`
under the map of local homology induced by `j`, the map of pairs `j : (M, M ∖ M) → (N, N ∖ N)`. -/
theorem singularHomologyπ_univ_singularHomologyMap (j : C(M, N)) {k : ℕ}
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology L k : ModuleCat.{w} Λ)) :
    ((TopPair.ofSubset ((univ : Set (TopCat.of N))ᶜ)).singularHomologyπ
        (C := ModuleCat.{w} Λ) L k).hom
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom j)) L k).hom μ) =
      localHomologyMap L j (subset_univ _) k
        (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
          (C := ModuleCat.{w} Λ) L k).hom μ) :=
  congrArg (fun φ ↦ φ.hom μ)
    (homologyMap_comp_singularHomologyπ_ofSubset L j (T := univ) (subset_univ _) k)

/-- **Naturality of the passage to local homology.** If `x` is the only preimage of `j x` under
`j : M → N`, the image in the local homology at `j x` of `j_* μ ∈ Hₖ(N; L)` is the image of the
local class of `μ` at `x` under the map of local homology `Hₖ(M, M ∖ {x}) ⟶ Hₖ(N, N ∖ {j x})`
induced by `j`. -/
theorem singularHomologyToLocalHomology_singularHomologyMap (j : C(M, N)) {x : M}
    (hx : j ⁻¹' {j x} ⊆ {x}) {k : ℕ}
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology L k : ModuleCat.{w} Λ)) :
    singularHomologyToLocalHomology L (j x) k
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom j)) L k).hom μ) =
      localHomologyMap L j hx k (singularHomologyToLocalHomology L x k μ) := by
  -- On local homology, `j` followed by restriction to `{j x}` is restriction to `{x}` followed by
  -- `j`: both are the map of pairs `(M, ∅) ⟶ (N, N ∖ {j x})`.
  have key : localHomologyMap L j (S := univ) (T := univ) (subset_univ _) k ≫
      localHomologyRestriction L (subset_univ {j x}) k =
        localHomologyRestriction L (subset_univ {x}) k ≫ localHomologyMap L j hx k := by
    rw [localHomologyMap_comp_localHomologyRestriction,
      localHomologyRestriction_comp_localHomologyMap]
  have h' := congrArg (fun φ ↦ φ.hom
    (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
      (C := ModuleCat.{w} Λ) L k).hom μ)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  rw [singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_apply,
    singularHomologyπ_univ_singularHomologyMap]
  exact h'

end SingularHomologyMap

section ChartIso

variable {M : Type w} [TopologicalSpace M] [T1Space M] {E : Type w} [TopologicalSpace E]
  [T1Space E] (φ : OpenPartialHomeomorph M E)

/-- **The chart isomorphism through the source.** The local homology isomorphism of a chart `φ`
at `a` (`TauCeti.singularHomologyComplSingletonIsoOfChart`) is the inverse of the excision
isomorphism of the source of `φ`, followed by the map induced by its canonical source
restriction `φ.sourceRestrict`. -/
theorem localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom
    {a : M} (ha : a ∈ φ.source)
    (h : φ.sourceRestrict ⁻¹' {φ a} ⊆ ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (k : ℕ) :
    localHomologyMap R (ContinuousMap.subtypeVal φ.source)
        (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl k ≫
          (singularHomologyComplSingletonIsoOfChart R φ ha k).hom =
      localHomologyMap R φ.sourceRestrict h k := by
  have h₁ : localHomologyMap R (ContinuousMap.subtypeVal φ.source)
      (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl k =
        TopPair.singularHomologyMap
        (TopPair.excisionMap (X := TopCat.of M) φ.source {a}ᶜ) R k := by
    -- The pairs agree only after unfolding the preimages of complements.
    erw [localHomologyMap_def]
    congr 1
    apply TopPair.hom_ext_of_fst
    ext z
    erw [TopPair.excisionMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    rfl
  have h₂ : localHomologyMap R φ.sourceRestrict h k =
      TopPair.singularHomologyMap ((TopPair.ofSubsetIso (X := TopCat.of φ.source)
          (Y := TopCat.of φ.target) φ.toHomeomorphSourceTarget
          (B := Subtype.val ⁻¹' {a}ᶜ) (B' := Subtype.val ⁻¹' {φ a}ᶜ)
          fun z ↦ (φ.injOn.eq_iff z.property ha).not.symm).hom ≫
        TopPair.excisionMap (X := TopCat.of E) φ.target {φ a}ᶜ) R k := by
    -- The pairs agree only after unfolding the preimages of complements.
    erw [localHomologyMap_def]
    congr 1
    apply TopPair.hom_ext_of_fst
    ext z
    rw [TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, TopPair.excisionMap_fst_apply, TopPair.ofSubsetIso_hom,
      TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply]
    exact φ.sourceRestrict_apply z
  rw [h₁, h₂, TopPair.singularHomologyMap_comp]
  exact singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom R φ ha k

end ChartIso

section Chart

variable {M : Type w} [TopologicalSpace M] {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Local homology is constant along a compact star-convex set in a chart.** If
`K ⊆ φ.target` is compact and star-convex about `φ x ∈ K`, then the restriction
`Hₖ(M, M ∖ φ.symm '' K) ⟶ Hₖ(M, M ∖ {x})` is an isomorphism. -/
theorem isIso_localHomologyRestriction_symm_image [T2Space M] (φ : OpenPartialHomeomorph M E)
    {K : Set E} {x : M} (hK : StarConvex ℝ (φ x) K) (hKc : IsCompact K) (hKφ : K ⊆ φ.target)
    (hx : x ∈ φ.source) (hxK : φ x ∈ K) (k : ℕ) :
    IsIso (localHomologyRestriction R
      (singleton_subset_iff.2 ⟨φ x, hxK, φ.left_inv hx⟩ : {x} ⊆ φ.symm '' K) k) :=
  isIso_singularHomologyMap_compl_of_chart R φ hx hK hxK hKc.isBounded
    hKc.isClosed (φ.isClosed_image_symm_of_isCompact hKc hKφ) hKφ k

/-- **Every neighbourhood of a point of a manifold contains a compact neighbourhood along which
local homology is constant.** If `M` is a Hausdorff space modelled on a finite-dimensional real
normed space and `U` is a neighbourhood of `x ∈ M`, there is a compact neighbourhood `B ⊆ U` of
`x`, the image under a chart of a closed ball, such that the restriction
`Hₖ(M, M ∖ B) ⟶ Hₖ(M, M ∖ {y})` is an isomorphism for every `y ∈ B`. -/
theorem exists_isCompact_subset_mem_nhds_isIso_localHomologyRestriction [T2Space M]
    [ChartedSpace E M] [FiniteDimensional ℝ E] {x : M} {U : Set M} (hU : U ∈ 𝓝 x) (k : ℕ) :
    ∃ B ∈ 𝓝 x, IsCompact B ∧ B ⊆ U ∧
      ∀ y (hy : y ∈ B), IsIso (localHomologyRestriction R (singleton_subset_iff.2 hy) k) := by
  let φ := chartAt E x
  have hx := mem_chart_source E x
  -- A ball about `φ x` inside the target whose image under `φ.symm` lies in `U`.
  have hV : φ.target ∩ φ.symm ⁻¹' U ∈ 𝓝 (φ x) := by
    refine Filter.inter_mem (φ.open_target.mem_nhds (φ.map_source hx)) ?_
    exact φ.continuousAt_symm (φ.map_source hx) (by rwa [φ.left_inv hx])
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  have hKV : closedBall (φ x) (ε / 2) ⊆ φ.target ∩ φ.symm ⁻¹' U :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεV
  have hKφ : closedBall (φ x) (ε / 2) ⊆ φ.target := hKV.trans inter_subset_left
  have hKc : IsCompact (closedBall (φ x) (ε / 2)) := isCompact_closedBall _ _
  refine ⟨φ.symm '' closedBall (φ x) (ε / 2), ?_,
    hKc.image_of_continuousOn (φ.continuousOn_symm.mono hKφ),
    image_subset_iff.2 (hKV.trans inter_subset_right), ?_⟩
  · have h := φ.symm.image_mem_nhds (φ.map_source hx) (closedBall_mem_nhds (φ x) (half_pos hε))
    rwa [φ.left_inv hx] at h
  · rintro y ⟨w, hw, rfl⟩
    have hw' : w ∈ φ.target := hKφ hw
    have hw'' : φ (φ.symm w) ∈ closedBall (φ x) (ε / 2) := by rwa [φ.right_inv hw']
    exact isIso_localHomologyRestriction_symm_image R φ ((convex_closedBall _ _).starConvex hw'')
      hKc hKφ (φ.map_target hw') hw'' k

/-- **Every point of a manifold has a compact neighbourhood along which local homology is
constant.** If `M` is a Hausdorff space modelled on a finite-dimensional real normed space, every
`x ∈ M` has a compact neighbourhood `B`, the image under a chart of a closed ball, such that the
restriction `Hₖ(M, M ∖ B) ⟶ Hₖ(M, M ∖ {y})` is an isomorphism for every `y ∈ B`. -/
theorem exists_isCompact_mem_nhds_isIso_localHomologyRestriction [T2Space M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] (x : M) (k : ℕ) :
    ∃ B ∈ 𝓝 x, IsCompact B ∧
      ∀ y (hy : y ∈ B), IsIso (localHomologyRestriction R (singleton_subset_iff.2 hy) k) := by
  obtain ⟨B, hB, hBc, -, hiso⟩ :=
    exists_isCompact_subset_mem_nhds_isIso_localHomologyRestriction (E := E) R
      (Filter.univ_mem : univ ∈ 𝓝 x) k
  exact ⟨B, hB, hBc, hiso⟩

/-- An open, bounded, convex subset of the target of a chart whose closure also lies in the
target. These patches index the cover over which the local homology system is glued. -/
private structure Patch (M E : Type w) [TopologicalSpace M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  chart : OpenPartialHomeomorph M E
  set : Set E
  isOpen : IsOpen set
  convex : Convex ℝ set
  isBounded : Bornology.IsBounded set
  closure_subset : closure set ⊆ chart.target

/-- The part of `M` lying over a patch. -/
private def Patch.domain (P : Patch M E) : Set M := P.chart.source ∩ P.chart ⁻¹' P.set

/-- The image in `M` of the closure of a patch. -/
private def Patch.closedImage (P : Patch M E) : Set M := P.chart.symm '' closure P.set

private lemma Patch.isOpen_domain (P : Patch M E) : IsOpen P.domain :=
  P.chart.isOpen_inter_preimage P.isOpen

private lemma Patch.singleton_subset_closedImage (P : Patch M E) {x : M} (hx : x ∈ P.domain) :
    {x} ⊆ P.closedImage :=
  singleton_subset_iff.2 ⟨P.chart x, subset_closure hx.2, P.chart.left_inv hx.1⟩

private lemma Patch.domain_subset_closedImage (P : Patch M E) : P.domain ⊆ P.closedImage :=
  fun _ hx ↦ P.singleton_subset_closedImage hx rfl

omit [NormedSpace ℝ E] in
private lemma closure_ball_half_subset_ball (c : E) {ε : ℝ} (hε : 0 < ε) :
    closure (ball c (ε / 2)) ⊆ ball c ε :=
  closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))

/-- The patch of `φ` given by the ball of radius `ε / 2` about `c`, where the ball of radius `ε`
lies in the target of `φ`. -/
private def Patch.ofBall (φ : OpenPartialHomeomorph M E) (c : E) {ε : ℝ} (hε : 0 < ε)
    (h : ball c ε ⊆ φ.target) : Patch M E where
  chart := φ
  set := ball c (ε / 2)
  isOpen := isOpen_ball
  convex := convex_ball _ _
  isBounded := isBounded_ball
  closure_subset := (closure_ball_half_subset_ball c hε).trans h

private lemma Patch.mem_domain_ofBall (φ : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ φ.source) {ε : ℝ} (hε : 0 < ε) (h : ball (φ x) ε ⊆ φ.target) :
    x ∈ (Patch.ofBall φ (φ x) hε h).domain :=
  ⟨hx, mem_ball_self (by linarith)⟩

/-- Every point of `M` lies in the domain of a patch of a chart at that point. -/
private lemma Patch.exists_domain_mem_nhds [ChartedSpace E M] (x : M) :
    ∃ P : Patch M E, P.domain ∈ 𝓝 x := by
  let φ := chartAt E x
  obtain ⟨ε, hε, hεφ⟩ := Metric.isOpen_iff.1 φ.open_target (φ x) (φ.map_source
    (mem_chart_source E x))
  let P := Patch.ofBall φ (φ x) hε hεφ
  exact ⟨P, P.isOpen_domain.mem_nhds (Patch.mem_domain_ofBall φ (mem_chart_source E x) hε hεφ)⟩

/-- Near a point `z` of the domain of `P` lying in an open set `U`, there is a patch of the same
chart whose closed image lies in `U`. -/
private lemma Patch.exists_closedImage_subset (P : Patch M E) {z : M} (hz : z ∈ P.domain)
    {U : Set M} (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ Q : Patch M E, z ∈ Q.domain ∧ Q.closedImage ⊆ U := by
  have hopen : IsOpen (P.chart.target ∩ P.chart.symm ⁻¹' U) :=
    P.chart.isOpen_inter_preimage_symm hU
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hopen (P.chart z)
    ⟨P.chart.map_source hz.1, by rwa [Set.mem_preimage, P.chart.left_inv hz.1]⟩
  have hεφ := hεU.trans inter_subset_left
  refine ⟨Patch.ofBall P.chart (P.chart z) hε hεφ, Patch.mem_domain_ofBall _ hz.1 hε hεφ, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (hεU (closure_ball_half_subset_ball _ hε hy)).2

variable [FiniteDimensional ℝ E]

private lemma Patch.isCompact_closure (P : Patch M E) : IsCompact (closure P.set) :=
  isCompact_of_isClosed_isBounded isClosed_closure P.isBounded.closure

variable [T2Space M]

private lemma Patch.isIso_localHomologyRestriction (P : Patch M E) {x : M}
    (hx : x ∈ P.domain) (k : ℕ) :
    IsIso (localHomologyRestriction R (P.singleton_subset_closedImage hx) k) :=
  isIso_localHomologyRestriction_symm_image R P.chart
    (P.convex.closure.starConvex (subset_closure hx.2)) P.isCompact_closure P.closure_subset
    hx.1 (subset_closure hx.2) k

/-- The restriction from the closed image of a patch to a point of its domain, as an
isomorphism. -/
private def Patch.iso (P : Patch M E) {x : M} (hx : x ∈ P.domain) (k : ℕ) :
    localHomology R P.closedImage k ≅ localHomology R {x} k :=
  haveI := P.isIso_localHomologyRestriction R hx k
  asIso (localHomologyRestriction R (P.singleton_subset_closedImage hx) k)

private lemma Patch.iso_hom (P : Patch M E) {x : M} (hx : x ∈ P.domain) (k : ℕ) :
    (P.iso R hx k).hom = localHomologyRestriction R (P.singleton_subset_closedImage hx) k :=
  rfl

private lemma Patch.iso_inv (P : Patch M E) {x : M} (hx : x ∈ P.domain) (k : ℕ)
    [IsIso (localHomologyRestriction R (P.singleton_subset_closedImage hx) k)] :
    (P.iso R hx k).inv = inv (localHomologyRestriction R (P.singleton_subset_closedImage hx) k) :=
  asIso_inv _

/-- The functor on the fundamental groupoid of the domain of a patch: a path is sent to the
comparison of the local homology groups at its endpoints through `Hₖ(M, M ∖ P.closedImage)`. -/
private def Patch.functor (P : Patch M E) (k : ℕ) : FundamentalGroupoid P.domain ⥤ A where
  obj a := localHomology R {a.as.val} k
  map {a b} _ := (P.iso R a.as.property k).inv ≫ (P.iso R b.as.property k).hom
  map_id _ := Iso.inv_hom_id _
  map_comp _ _ := by simp

/-- Comparing two points through a patch `P` agrees with comparing them through a patch `S`
whose closed image lies in that of `P`. -/
private lemma Patch.iso_inv_comp_iso_hom (P S : Patch M E) {x y : M} (hxP : x ∈ P.domain)
    (hyP : y ∈ P.domain) (hxS : x ∈ S.domain) (hyS : y ∈ S.domain)
    (hSP : S.closedImage ⊆ P.closedImage) (k : ℕ) :
    (P.iso R hxP k).inv ≫ (P.iso R hyP k).hom = (S.iso R hxS k).inv ≫ (S.iso R hyS k).hom := by
  have : IsIso (localHomologyRestriction R (S.singleton_subset_closedImage hxS) k) :=
    (S.iso R hxS k).isIso_hom
  have : IsIso (localHomologyRestriction R
      (Set.Subset.trans (S.singleton_subset_closedImage hxS) hSP) k) :=
    (P.iso R hxP k).isIso_hom
  rw [Iso.eq_inv_comp]
  simp only [Patch.iso_hom, Patch.iso_inv]
  exact localHomologyRestriction_comp_inv_comp R hSP (S.singleton_subset_closedImage hxS)
    (S.singleton_subset_closedImage hyS) k

/-- The local functors of two patches agree on the fundamental groupoid of the intersection of
their domains. -/
private lemma Patch.map_inclusion_comp_functor (P Q : Patch M E) (k : ℕ) :
    FundamentalGroupoid.map (ContinuousMap.inclusion
        (inter_subset_left : P.domain ∩ Q.domain ⊆ P.domain)) ⋙ P.functor R k =
      FundamentalGroupoid.map (ContinuousMap.inclusion
        (inter_subset_right : P.domain ∩ Q.domain ⊆ Q.domain)) ⋙ Q.functor R k := by
  -- Near each point of the overlap, a small patch of the chart of `P` has closed image inside
  -- the overlap, and both local functors agree with its comparison maps.
  let W : {S : Patch M E // S.closedImage ⊆ P.domain ∩ Q.domain} → Set ↥(P.domain ∩ Q.domain) :=
    fun S ↦ Subtype.val ⁻¹' S.val.domain
  refine FundamentalGroupoid.functor_ext (U := W) (fun z ↦ ?_) fun S ↦ ?_
  · obtain ⟨S, hzS, hS⟩ := P.exists_closedImage_subset z.property.1
      (P.isOpen_domain.inter Q.isOpen_domain) z.property
    exact ⟨⟨S, hS⟩, continuous_subtypeVal.continuousAt.preimage_mem_nhds
      (S.isOpen_domain.mem_nhds hzS)⟩
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) fun a b _ ↦ heq_of_eq ?_
  exact (P.iso_inv_comp_iso_hom R S.val _ _ a.as.property b.as.property
    (S.property.trans (inter_subset_left.trans P.domain_subset_closedImage)) k).trans
    (Q.iso_inv_comp_iso_hom R S.val _ _ a.as.property b.as.property
      (S.property.trans (inter_subset_right.trans Q.domain_subset_closedImage)) k).symm

variable (M E) [ChartedSpace E M]

/-- The functor out of the fundamental groupoid of `M` glued from the local functors of the
patches. Its object at `x` is only propositionally `Hₖ(M, M ∖ {x})`. -/
private def gluedSystem (k : ℕ) : FundamentalGroupoid M ⥤ A :=
  FundamentalGroupoid.glue Patch.exists_domain_mem_nhds (fun P : Patch M E ↦ P.functor R k)
    fun P Q ↦ P.map_inclusion_comp_functor R Q k

private lemma gluedSystem_obj (k : ℕ) (x : FundamentalGroupoid M) :
    (gluedSystem R M E k).obj x = localHomology R {x.as} k := by
  obtain ⟨P, hP⟩ := Patch.exists_domain_mem_nhds (E := E) x.as
  exact FundamentalGroupoid.glue_obj_mk _ _ _ P (mem_of_mem_nhds hP)

/-- The transport `Hₖ(M, M ∖ {x}) ⟶ Hₖ(M, M ∖ {y})` of local homology along a path class from
`x` to `y`, for a Hausdorff space `M` modelled on a finite-dimensional real normed space `E`.
Along a path inside a compact convex set of a chart it is described by
`TauCeti.localHomologyRestriction_comp_localHomologyTransport`. -/
def localHomologyTransport (k : ℕ) {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomology R {x.as} k ⟶ localHomology R {y.as} k :=
  eqToHom (gluedSystem_obj R M E k x).symm ≫ (gluedSystem R M E k).map f ≫
    eqToHom (gluedSystem_obj R M E k y)

@[simp]
theorem localHomologyTransport_id (k : ℕ) (x : FundamentalGroupoid M) :
    localHomologyTransport R M E k (𝟙 x) = 𝟙 _ := by
  simp [localHomologyTransport]

@[simp]
theorem localHomologyTransport_comp (k : ℕ) {x y z : FundamentalGroupoid M} (f : x ⟶ y)
    (g : y ⟶ z) :
    localHomologyTransport R M E k (f ≫ g) =
      localHomologyTransport R M E k f ≫ localHomologyTransport R M E k g := by
  simp [localHomologyTransport]

/-- **The local homology system.** For a Hausdorff space `M` modelled on a finite-dimensional
real normed space `E`, the local homology groups `Hₖ(M, M ∖ {x})` form a functor out of the
fundamental groupoid of `M`, with the transport maps `TauCeti.localHomologyTransport`. For
`k = dim E` and integer coefficients it is the orientation local system of `M`. -/
@[expose, simps]
def localHomologySystem (k : ℕ) : FundamentalGroupoid M ⥤ A where
  obj x := localHomology R {x.as} k
  map f := localHomologyTransport R M E k f
  map_id := localHomologyTransport_id R M E k
  map_comp := localHomologyTransport_comp R M E k

variable {M E}

/-- Along a path inside the domain of a patch, the transport is the comparison of the endpoints
through the closed image of the patch. -/
private lemma Patch.localHomologyTransport_mk (P : Patch M E) {x y : M} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ P.domain) (k : ℕ) :
    localHomologyTransport R M E k
        (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
      (P.iso R (γ.source ▸ hγ 0) k).inv ≫ (P.iso R (γ.target ▸ hγ 1) k).hom := by
  let γ' : Path (⟨x, γ.source ▸ hγ 0⟩ : P.domain) ⟨y, γ.target ▸ hγ 1⟩ := γ.codRestrict hγ
  have hγ' : (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
      (FundamentalGroupoid.map (ContinuousMap.subtypeVal P.domain)).map
        (Path.Homotopic.Quotient.mk γ') :=
    congrArg Path.Homotopic.Quotient.mk
      (Path.map_codRestrict (x := ⟨x, γ.source ▸ hγ 0⟩) (y := ⟨y, γ.target ▸ hγ 1⟩) γ hγ).symm
  have h := Functor.hcongr_hom (FundamentalGroupoid.map_subtypeVal_comp_glue
    Patch.exists_domain_mem_nhds (fun P : Patch M E ↦ P.functor R k)
    (fun P Q ↦ P.map_inclusion_comp_functor R Q k) P) (Path.Homotopic.Quotient.mk γ')
  apply eq_of_heq
  rw [localHomologyTransport, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, hγ']
  -- `gluedSystem` is the glued functor, and the local functor of `P` sends a path to the
  -- comparison through `P`.
  exact h

/-- **Transport of local homology along a path in a chart.** Let `K ⊆ φ.target` be compact and
convex, and let `γ` be a path from `x` to `y` inside `φ.symm '' K`. Then the transport along `γ`
is compatible with the restrictions `Hₖ(M, M ∖ φ.symm '' K) ⟶ Hₖ(M, M ∖ {x})` and
`Hₖ(M, M ∖ φ.symm '' K) ⟶ Hₖ(M, M ∖ {y})`. Since the first of these is an isomorphism
(`TauCeti.isIso_localHomologyRestriction_symm_image`), this determines the transport. -/
theorem localHomologyRestriction_comp_localHomologyTransport (φ : OpenPartialHomeomorph M E)
    {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K) (hKφ : K ⊆ φ.target) {x y : M}
    (γ : Path x y) (hγ : ∀ t, γ t ∈ φ.symm '' K) (k : ℕ) :
    localHomologyRestriction R (singleton_subset_iff.2 (γ.source ▸ hγ 0)) k ≫
        localHomologyTransport R M E k
          (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
      localHomologyRestriction R (singleton_subset_iff.2 (γ.target ▸ hγ 1)) k := by
  -- A thickening of `K` is a patch of `φ` containing `γ`; compare through its closed image.
  obtain ⟨δ, hδ, hδK⟩ := hKc.exists_cthickening_subset_open φ.open_target hKφ
  let P : Patch M E :=
    { chart := φ
      set := thickening δ K
      isOpen := isOpen_thickening
      convex := hK.thickening δ
      isBounded := hKc.isBounded.thickening
      closure_subset := (closure_thickening_subset_cthickening δ K).trans hδK }
  have hγP (t : unitInterval) : γ t ∈ P.domain := by
    obtain ⟨z, hz, hzt⟩ := hγ t
    refine hzt ▸ ⟨φ.map_target (hKφ hz), ?_⟩
    rw [Set.mem_preimage, φ.right_inv (hKφ hz)]
    exact self_subset_thickening hδ K hz
  have hKP : φ.symm '' K ⊆ P.closedImage :=
    image_mono fun z hz ↦ subset_closure (self_subset_thickening hδ K hz)
  rw [P.localHomologyTransport_mk R γ hγP k]
  obtain ⟨z, hz, hzx⟩ := γ.source ▸ hγ 0
  have : IsIso (localHomologyRestriction R (singleton_subset_iff.2 (γ.source ▸ hγ 0)) k) := by
    subst hzx
    exact isIso_localHomologyRestriction_symm_image R φ
      (hK.starConvex ((φ.right_inv (hKφ hz)).symm ▸ hz)) hKc hKφ (φ.map_target (hKφ hz))
      ((φ.right_inv (hKφ hz)).symm ▸ hz) k
  have : IsIso (localHomologyRestriction R
      (Set.Subset.trans (singleton_subset_iff.2 (γ.source ▸ hγ 0)) hKP) k) :=
    (P.iso R (γ.source ▸ hγP 0) k).isIso_hom
  rw [Patch.iso_inv, Patch.iso_hom]
  exact localHomologyRestriction_comp_inv_comp R hKP _ _ k

/-- **Uniqueness of the transport.** A family of maps `Hₖ(M, M ∖ {x}) ⟶ Hₖ(M, M ∖ {y})` indexed by
path classes from `x` to `y`, compatible with composition and satisfying the conclusion of
`TauCeti.localHomologyRestriction_comp_localHomologyTransport` along paths inside compact convex
sets of charts, is the transport `TauCeti.localHomologyTransport`. -/
theorem eq_localHomologyTransport (k : ℕ)
    (t : ∀ {x y : FundamentalGroupoid M}, (x ⟶ y) →
      (localHomology R {x.as} k ⟶ localHomology R {y.as} k))
    (ht : ∀ {x y z : FundamentalGroupoid M} (f : x ⟶ y) (g : y ⟶ z), t (f ≫ g) = t f ≫ t g)
    (hchart : ∀ (φ : OpenPartialHomeomorph M E) {K : Set E}, Convex ℝ K → IsCompact K →
      K ⊆ φ.target → ∀ {x y : M} (γ : Path x y) (hγ : ∀ s, γ s ∈ φ.symm '' K),
        localHomologyRestriction R (singleton_subset_iff.2 (γ.source ▸ hγ 0)) k ≫
            t (Path.Homotopic.Quotient.mk γ :
              FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
          localHomologyRestriction R (singleton_subset_iff.2 (γ.target ▸ hγ 1)) k)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) : t f = localHomologyTransport R M E k f := by
  -- Along a path in the domain of a patch, `t` is the comparison through the patch.
  have hpatch (P : Patch M E) {a b : M} (γ : Path a b) (hγ : ∀ s, γ s ∈ P.domain) :
      t (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) =
        (P.iso R (γ.source ▸ hγ 0) k).inv ≫ (P.iso R (γ.target ▸ hγ 1) k).hom := by
    rw [Iso.eq_inv_comp, Patch.iso_hom, Patch.iso_hom]
    exact hchart P.chart P.convex.closure P.isCompact_closure P.closure_subset γ
      fun s ↦ P.domain_subset_closedImage (hγ s)
  -- The maps `t` form a functor, which agrees with the local homology system on every patch.
  let G : FundamentalGroupoid M ⥤ A :=
    { obj x := localHomology R {x.as} k
      map := t
      map_id x := by
        obtain ⟨P, hP⟩ := Patch.exists_domain_mem_nhds (E := E) x.as
        have hx := mem_of_mem_nhds hP
        -- The identity of `x` is the class of the constant path, which lies in `P`.
        rw [FundamentalGroupoid.id_eq_path_refl]
        refine (hpatch P (Path.refl x.as) fun _ ↦ hx).trans ?_
        exact Iso.inv_hom_id _
      map_comp := ht }
  have hG : G = localHomologySystem R M E k := by
    refine FundamentalGroupoid.functor_ext (U := Patch.domain (M := M) (E := E))
      Patch.exists_domain_mem_nhds
      fun P ↦ CategoryTheory.Functor.hext (fun _ ↦ rfl) fun a b g ↦ heq_of_eq ?_
    induction g using Path.Homotopic.Quotient.ind with | mk γ =>
    -- The image of `γ` in `M` is `γ.map continuous_subtype_val`, a path in the domain of `P`.
    exact (hpatch P (γ.map continuous_subtypeVal) fun s ↦ (γ s).property).trans
      (P.localHomologyTransport_mk R (γ.map continuous_subtypeVal) (fun s ↦ (γ s).property) k).symm
  exact eq_of_heq (Functor.hcongr_hom hG f)

/-- **Restrictions of a global class are parallel.** The restrictions
`Hₖ(M, M ∖ M) ⟶ Hₖ(M, M ∖ {x})` to the points of `M` are compatible with the transport of local
homology along every path class, in every degree. -/
@[reassoc (attr := simp)]
theorem localHomologyRestriction_univ_comp_localHomologyTransport (k : ℕ)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyRestriction R (subset_univ {x.as}) k ≫ localHomologyTransport R M E k f =
      localHomologyRestriction R (subset_univ {y.as}) k := by
  -- Along a path in the domain of a patch, compare through the closed image of the patch.
  have hpatch (P : Patch M E) {a b : M} (γ : Path a b) (hγ : ∀ s, γ s ∈ P.domain) :
      localHomologyRestriction R (subset_univ {a}) k ≫
        localHomologyTransport R M E k
          (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) =
        localHomologyRestriction R (subset_univ {b}) k := by
    have ha : a ∈ P.domain := γ.source ▸ hγ 0
    rw [P.localHomologyTransport_mk R γ hγ k,
      ← localHomologyRestriction_comp R (P.singleton_subset_closedImage ha) (subset_univ _),
      ← P.iso_hom R ha, Category.assoc, Iso.hom_inv_id_assoc]
    simp [Patch.iso_hom]
  -- The path classes along which the restrictions are compatible form a subgroupoid.
  let S : Subgroupoid (FundamentalGroupoid M) :=
    { arrows c d := {f | localHomologyRestriction R (subset_univ {c.as}) k ≫
        localHomologyTransport R M E k f = localHomologyRestriction R (subset_univ {d.as}) k}
      inv {c d f} hf := by
        rw [Set.mem_ofPred_eq, ← hf]
        simp [← localHomologyTransport_comp]
      mul {c d e f} hf {g} hg := by
        rw [Set.mem_ofPred_eq, localHomologyTransport_comp, ← Category.assoc, hf, hg] }
  -- It contains the classes of paths inside the domains of patches, so it is everything.
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← FundamentalGroupoid.iSup_im_map_subtypeVal_eq_top
      (U := Patch.domain (M := M) (E := E)) Patch.exists_domain_mem_nhds]
    refine iSup_le fun P ↦ ?_
    rw [Subgroupoid.im, Subgroupoid.map_le_iff_le_comap]
    rintro ⟨⟨a⟩, ⟨b⟩, g⟩ -
    induction g using Path.Homotopic.Quotient.ind with | mk γ =>
    exact hpatch P (γ.map continuous_subtypeVal) fun s ↦ (γ s).property
  have hf : f ∈ S.arrows x y := hS ▸ trivial
  exact hf

end Chart

section SingularHomologyTransport

variable {M : Type w} [TopologicalSpace M] [T2Space M] {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)

private theorem singularHomologyToLocalHomology_eq_zero_of_joined_aux (E : Type w)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {x y : M} (hxy : Joined x y) {k : ℕ}
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

/-- **Vanishing in local homology transports along paths.** On a Hausdorff boundaryless manifold,
if `α ∈ Hₖ(M; N)` vanishes in the local homology `Hₖ(M, M ∖ {x}; N)`, then it vanishes in
`Hₖ(M, M ∖ {y}; N)` for every point `y` in the path component of `x`. -/
theorem singularHomologyToLocalHomology_eq_zero_of_joined (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    {x y : M} (hxy : Joined x y) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hα : singularHomologyToLocalHomology N x k α = 0) :
    singularHomologyToLocalHomology N y k α = 0 := by
  let _ : ChartedSpace (ULift.{w} (Fin (Module.finrank ℝ E)) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp)
  exact singularHomologyToLocalHomology_eq_zero_of_joined_aux N
    (ULift.{w} (Fin (Module.finrank ℝ E)) → ℝ) hxy hα

end SingularHomologyTransport

end TauCeti
