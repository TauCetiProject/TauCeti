/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Singular.CompactSupport
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# The duality map of an oriented manifold

Let `M` be an `n`-manifold without boundary with an orientation `o`
(`TauCeti.HomologicalOrientation M E n`), and let `L` be an abelian group. For every compact
`K ⊆ M` the orientation has a fundamental class `μ_K ∈ Hₙ(M, M ∖ K; ℤ)`
(`TauCeti.HomologicalOrientation.fundamentalClassOn`), and capping with it is a map
`Hᵖ(M, M ∖ K; L) ⟶ H_q(M; L)` for `p + q = n`
(`TauCeti.HomologicalOrientation.capFundamentalClassOn`). For compact `K ⊆ K'` the class `μ_K'`
restricts to `μ_K`, so by naturality of the relative cap product these maps are compatible with
the maps `Hᵖ(M, M ∖ K; L) ⟶ Hᵖ(M, M ∖ K'; L)` of the diagram defining cohomology with compact
supports. They therefore induce the **duality map**

`D_M : Hᵖ_c(M; L) ⟶ H_q(M; L)`

(`TauCeti.HomologicalOrientation.dualityMap`), which Poincaré duality asserts is an isomorphism.

For compact `M`, cohomology with compact supports is ordinary cohomology, and the duality map is
the cap product with the fundamental class `[M]`
(`TauCeti.HomologicalOrientation.dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv`).
Reversing the orientation negates the duality map. For an open embedding `j : U → M`, with `U`
carrying the pulled-back orientation, `j` carries the fundamental classes of `U` along compact
sets to those of `M` (`TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_comap`),
and the duality maps commute with the extension `j_! : Hᵖ_c(U; L) ⟶ Hᵖ_c(M; L)` and the
pushforward `j_* : H_q(U; L) ⟶ H_q(M; L)`: `D_M ∘ j_! = j_* ∘ D_U`
(`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_dualityMap`).
This is the naturality along which the duality maps of open subsets are compared in the proof of
Poincaré duality. Restricted to a compact `K ⊆ U`, it says that capping along `K` followed by `j_*`
is the inverse of the excision isomorphism `Hᵖ(M, M ∖ j(K); L) ≅ Hᵖ(U, U ∖ K; L)` followed by
capping along `j(K)`
(`TauCeti.HomologicalOrientation.capFundamentalClassOn_comap_comp_singularHomologyMap`), so when
`j_*` is bijective, capping along `K` is bijective exactly when capping along `j(K)` is
(`TauCeti.HomologicalOrientation.bijective_capFundamentalClassOn_comap_iff`).

Every class with compact support comes from some `Hᵖ(M, M ∖ K; L)`, on which the duality map is
capping with `μ_K`. Hence the duality map is bijective as soon as every compact set lies in a
compact `K` along which capping with `μ_K` is bijective
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_cofinal`). It is also bijective for an
empty manifold, where both groups vanish
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_isEmpty`).

Bijectivity of the duality map passes to unions of open sets in two cases that need no comparison
of connecting maps. Throughout, an open subset `U` of `M` carries the orientation pulled back
along its inclusion, and whether its duality map is bijective depends only on `U` as a subset of
`M`, not on how it is embedded
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iff_of_range_eq`).

* **Disjoint unions.** If `M = U ∪ V` with `U ∩ V = ∅`, the middle maps
  `Hᵖ_c(U) ⊞ Hᵖ_c(V) ⟶ Hᵖ_c(M)` and `H_q(U) ⊞ H_q(V) ⟶ H_q(M)` of the two Mayer–Vietoris sequences
  are isomorphisms, since both theories vanish on the empty intersection, and the duality maps
  commute with them by naturality. So duality on `U` and `V` gives duality on `M`
  (`TauCeti.HomologicalOrientation.bijective_dualityMap_of_disjoint`).
* **Directed unions.** If `M` is the union of a directed family of open sets `U i`, then
  `Hᵖ_c(M)` and `H_q(M)` are the colimits of the groups of the `U i`, because compact sets lie in
  some `U i`, and duality on every `U i` gives duality on `M`
  (`TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`).

Combining the two over the finite partial unions, duality on pairwise disjoint open subsets `s i` of
`M` gives duality on their union
(`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iSup_of_pairwise_disjoint`). This is the
disjoint-union hypothesis of the Mayer–Vietoris induction `TauCeti.mayerVietoris_induction` for the
property of an open subset that its duality map is bijective.

## Main definitions

* `TauCeti.HomologicalOrientation.capFundamentalClassOn`: capping with the fundamental class along
  a compact set, `Hᵖ(M, M ∖ K; L) ⟶ H_q(M; L)`.
* `TauCeti.HomologicalOrientation.dualityMap`: the duality map `Hᵖ_c(M; L) ⟶ H_q(M; L)`.

## Main results

* `TauCeti.HomologicalOrientation.compactSupportCohomologyι_dualityMap`: the duality map on a
  class supported in a compact `K` is the cap product with `μ_K`.
* `TauCeti.HomologicalOrientation.dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv`: for
  compact `M`, the duality map is the cap product with the fundamental class.
* `TauCeti.HomologicalOrientation.dualityMap_neg`: reversing the orientation negates the duality
  map.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_dualityMap`: naturality along open
  embeddings.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_inclusion'_dualityMap` and
  `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_toTopCat_map_dualityMap`: its
  instances for an open subset of `M` and for nested open subsets, with the restricted
  orientations.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_inclusion'_dualityMap_apply` and
  `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_toTopCat_map_dualityMap_apply`:
  their elementwise forms.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_cofinal`: the duality map is bijective
  if capping is bijective along cofinally many compact sets.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iff_of_range_eq`: bijectivity of the
  duality map of an open subset depends only on the subset.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_disjoint`,
  `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup_of_disjoint`: duality for the
  union of two disjoint open sets.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`,
  `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iSup_of_monotone`: duality for a
  directed union of open sets.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iSup_of_pairwise_disjoint`: duality
  for a union of pairwise disjoint open sets.

## Implementation notes

All groups are abelian groups, that is, objects of `ModuleCat ℤ`, and `M` lives in `Type`, as for
`TauCeti.HomologicalOrientation.fundamentalClassOn`. Cohomology and homology follow the convention
of `TauCeti.HomologicalOrientation.evalFundamentalClass`: singular chains have the integral
coefficients `ModuleCat.of ℤ (ULift ℤ)` of the fundamental classes, and `Hᵖ(-; L)` is computed from
cochains on them with values in `L`. The cap product pairs the two along the right unitors
`ℤ ⟶ ℤ ⊗ 𝟙` and `L ⊗ 𝟙 ⟶ L`, so that a cochain `φ` and a simplex `σ` give
`φ(σ|[0, …, p]) • σ|[p, …, n]`. A module over a ring enters through its underlying abelian group.

Instance search finds the `ℤ`-linear structure of `ModuleCat ℤ` as a preadditive category, for
which Mathlib's `MonoidalLinear ℤ` instance does not apply. The declaration
`CategoryTheory.MonoidalPreadditive.monoidalLinearInt` supplies it as a local instance, as for
`TopCat.integralCup`.

The naturality along inclusions of open sets is stated through `TopologicalSpace.Opens.inclusion'`
and `TopologicalSpace.Opens.toTopCat`, the form of the colimit descriptions over open covers, whose
spaces agree with the subtypes only by definition; hence its elementwise forms are stated
separately rather than by `@[elementwise]`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the duality map `D_M : Hᵖ_c(M; R) ⟶ H_{n-p}(M; R)` defined before Theorem 3.35, and
  its naturality for inclusions of open sets used in Lemma 3.36, whose step (3) is the passage to
  increasing unions.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in
  Mathematics 82, Springer, 1982, §5, the Mayer–Vietoris argument and the disjoint-union step in
  the proof of Poincaré duality.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module TopologicalSpace Topology Set

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

/-- **Capping with the fundamental class along a compact set** `K`: the map
`Hᵖ(M, M ∖ K; L) ⟶ H_q(M; L)`, `α ↦ μ_K ⌢ α`, for `p + q = n`. -/
def capFundamentalClassOn {K : Set M} (hK : IsCompact K) (p q : ℕ) (h : p + q = n) :
    (TopPair.ofSubset (Kᶜ : Set (TopCat.of M))).singularCohomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj
        (TopCat.of M) :=
  -- `AddMonoidHom.toIntLinearMap` would use the `ℤ`-module structures of the underlying additive
  -- groups rather than those of the objects of `ModuleCat ℤ`.
  let f := (LinearMap.applyₗ (R := ℤ) (o.fundamentalClassOn hn hK)).toAddMonoidHom.comp <|
    ModuleCat.homAddEquiv.toAddMonoidHom.comp
      ((TopPair.ofSubset (Kᶜ : Set (TopCat.of M))).singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q n h).toAddMonoidHom
  ModuleCat.ofHom { f with map_smul' := map_intCast_smul f ℤ ℤ }

/-- Capping with the fundamental class along `K` evaluates the relative cap product at `μ_K`. -/
lemma capFundamentalClassOn_apply {K : Set M} (hK : IsCompact K) (p q : ℕ) (h : p + q = n)
    (α : (TopPair.ofSubset (Kᶜ : Set (TopCat.of M))).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.capFundamentalClassOn hn L hK p q h α =
      ((TopPair.ofSubset (Kᶜ : Set (TopCat.of M))).singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q n h α).hom (o.fundamentalClassOn hn hK) :=
  (rfl)

/-- The maps capping with the fundamental classes are compatible with enlarging the compact set:
for compact `K ⊆ K'`, capping the restriction to `Hᵖ(M, M ∖ K'; L)` of a class with `μ_K'` is
capping the class with `μ_K`. -/
lemma singularCohomologyMap_comp_capFundamentalClassOn {K K' : Compacts (TopCat.of M)}
    (hKK' : K ≤ K') (p q : ℕ) (h : p + q = n) :
    TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M))
        (TopCat.mapsTo_id_compl_compacts hKK')) p ≫
        o.capFundamentalClassOn hn L K'.isCompact p q h =
      o.capFundamentalClassOn hn L K.isCompact p q h := by
  ext α
  have hfst : ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
      (TopPair.Hom.fst (TopPair.ofSubsetMap (𝟙 (TopCat.of M))
        (TopCat.mapsTo_id_compl_compacts hKK'))) = 𝟙 _ := by
    rw [TopPair.ofSubsetMap_fst]
    exact CategoryTheory.Functor.map_id _ _
  have hμ := o.localHomologyRestriction_fundamentalClassOn_of_subset hn K'.isCompact
    K.isCompact (SetLike.coe_subset_coe.2 hKK')
  rw [localHomologyRestriction_def] at hμ
  have := ConcreteCategory.congr_hom (TopPair.singularCap_naturality
    (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (TopCat.mapsTo_id_compl_compacts hKK')) ℤ (ρ_ _).inv
      (ρ_ L).hom p q n h α) (o.fundamentalClassOn hn K'.isCompact)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hfst, hμ] at this
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, capFundamentalClassOn_apply,
    capFundamentalClassOn_apply, ← this]
  -- The source and target of the identity from `hfst` agree only after unfolding
  -- `TopPair.ofSubset`, so `ConcreteCategory.id_apply` applies by `exact` but not by `rw`.
  exact (ConcreteCategory.id_apply _).symm

/-- **The duality map** `D_M : Hᵖ_c(M; L) ⟶ H_q(M; L)` of an oriented manifold, `p + q = n`: on a
class supported in a compact set `K`, the cap product with the fundamental class `μ_K` along `K`.
-/
def dualityMap (p q : ℕ) (h : p + q = n) :
    (TopCat.of M).compactSupportCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj
        (TopCat.of M) :=
  TopCat.compactSupportCohomologyDesc
    (fun K ↦ o.capFundamentalClassOn hn L K.isCompact p q h)
    (fun _ _ hKK' ↦ o.singularCohomologyMap_comp_capFundamentalClassOn hn L hKK' p q h)

/-- **Characterization of the duality map**: on a class of `Hᵖ(M, M ∖ K; L)`, the duality map is
the cap product with the fundamental class along `K`. -/
@[reassoc (attr := simp)]
lemma compactSupportCohomologyι_dualityMap (p q : ℕ) (h : p + q = n)
    (K : Compacts (TopCat.of M)) :
    TopCat.compactSupportCohomologyι p K ≫ o.dualityMap hn L p q h =
      o.capFundamentalClassOn hn L K.isCompact p q h :=
  TopCat.compactSupportCohomologyι_desc _ _ K

/-- The duality map on the image of a class `α` of `Hᵖ(M, M ∖ K; L)` is `μ_K ⌢ α`. -/
lemma dualityMap_compactSupportCohomologyι_apply (p q : ℕ) (h : p + q = n)
    (K : Compacts (TopCat.of M))
    (α : (TopPair.ofSubset ((K : Set (TopCat.of M))ᶜ)).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.dualityMap hn L p q h (TopCat.compactSupportCohomologyι p K α) =
      ((TopPair.ofSubset ((K : Set (TopCat.of M))ᶜ)).singularCap ℤ (ρ_ _).inv
        (ρ_ L).hom p q n h α).hom (o.fundamentalClassOn hn K.isCompact) := by
  rw [← ConcreteCategory.comp_apply, compactSupportCohomologyι_dualityMap,
    capFundamentalClassOn_apply]

/-- Reversing the orientation negates the duality map. -/
@[simp]
lemma dualityMap_neg (p q : ℕ) (h : p + q = n) :
    (-o).dualityMap hn L p q h = -o.dualityMap hn L p q h := by
  refine TopCat.compactSupportCohomology_hom_ext fun K ↦ ?_
  rw [Preadditive.comp_neg, compactSupportCohomologyι_dualityMap,
    compactSupportCohomologyι_dualityMap]
  ext α
  rw [ModuleCat.hom_neg, LinearMap.neg_apply, capFundamentalClassOn_apply,
    capFundamentalClassOn_apply, fundamentalClassOn_neg]
  exact map_neg _ _

/-- **The duality map of a compact manifold is the cap product with the fundamental class**: for
compact `M`, on `Hᵖ(M; L) ≅ Hᵖ_c(M; L)` the duality map is `α ↦ [M] ⌢ α`. -/
lemma dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv [CompactSpace M] (p q : ℕ)
    (h : p + q = n)
    (α : (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.dualityMap hn L p q h ((TopCat.compactSupportCohomologyIsoOfCompactSpace p).inv α) =
      ((TopCat.of M).singularCap ℤ (ρ_ _).inv (ρ_ L).hom p q n h α).hom
        (o.fundamentalClass hn) := by
  obtain ⟨γ, hγ⟩ : ∃ γ, TopCat.compactSupportCohomologyι p ⊤ γ =
      (TopCat.compactSupportCohomologyIsoOfCompactSpace (R := ModuleCat.of ℤ (ULift.{0} ℤ))
        (k := ℤ) (M := L) (X := TopCat.of M) p).inv α :=
    have := TopCat.isIso_compactSupportCohomologyι_top
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L) (X := TopCat.of M) p
    ⟨inv (TopCat.compactSupportCohomologyι p ⊤) _, by
      rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]⟩
  have hα := congrArg (TopCat.compactSupportCohomologyIsoOfCompactSpace p).hom hγ
  rw [Iso.inv_hom_id_apply, ← ConcreteCategory.comp_apply,
    TopCat.compactSupportCohomologyι_compactSupportCohomologyIsoOfCompactSpace_hom] at hα
  rw [← hγ, dualityMap_compactSupportCohomologyι_apply, ← hα]
  have := ConcreteCategory.congr_hom (TopPair.singularCap_singularCohomologyπ
    (TopPair.ofSubset (((⊤ : Compacts (TopCat.of M)) : Set (TopCat.of M))ᶜ)) ℤ (ρ_ _).inv
      (ρ_ L).hom p q n h γ) (o.fundamentalClass hn)
  rw [← o.singularHomologyπ_fundamentalClass hn]
  -- `rw` cannot use `ConcreteCategory.comp_apply` here: the ambient space of the pair
  -- `(M, M ∖ ⊤)` is `M` only after unfolding `TopPair.ofSubset`.
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans this.symm

section Criteria

variable {p q : ℕ} (h : p + q = n)

/-- The duality map is surjective if capping with the fundamental class along some compact set is
surjective. -/
theorem surjective_dualityMap_of_surjective_capFundamentalClassOn {K : Compacts (TopCat.of M)}
    (hK : Function.Surjective (o.capFundamentalClassOn hn L K.isCompact p q h)) :
    Function.Surjective (o.dualityMap hn L p q h) := fun z ↦ by
  obtain ⟨α, rfl⟩ := hK z
  refine ⟨TopCat.compactSupportCohomologyι p K α, ?_⟩
  rw [← ConcreteCategory.comp_apply, compactSupportCohomologyι_dualityMap]

/-- The duality map is injective if every compact set lies in a compact set `K` along which
capping with the fundamental class is injective. -/
theorem injective_dualityMap_of_cofinal
    (H : ∀ K₀ : Compacts (TopCat.of M), ∃ K, K₀ ≤ K ∧
      Function.Injective (o.capFundamentalClassOn hn L K.isCompact p q h)) :
    Function.Injective (o.dualityMap hn L p q h) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨K₀, -, α, rfl⟩ := TopCat.exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨K, hK₀K, hK⟩ := H K₀
  rw [← TopCat.singularCohomologyMap_comp_compactSupportCohomologyι_apply p hK₀K] at hx ⊢
  rw [← ConcreteCategory.comp_apply, compactSupportCohomologyι_dualityMap] at hx
  rw [(injective_iff_map_eq_zero _).1 hK _ hx, map_zero]

/-- **Criterion for Poincaré duality**: the duality map of an oriented manifold is bijective if
every compact set lies in a compact set `K` along which capping with the fundamental class,
`Hᵖ(M, M ∖ K; L) ⟶ H_q(M; L)`, is bijective. -/
theorem bijective_dualityMap_of_cofinal
    (H : ∀ K₀ : Compacts (TopCat.of M), ∃ K, K₀ ≤ K ∧
      Function.Bijective (o.capFundamentalClassOn hn L K.isCompact p q h)) :
    Function.Bijective (o.dualityMap hn L p q h) :=
  ⟨o.injective_dualityMap_of_cofinal hn L h fun K₀ ↦ (H K₀).imp fun _ hK ↦ ⟨hK.1, hK.2.1⟩,
    o.surjective_dualityMap_of_surjective_capFundamentalClassOn hn L h (H ⊥).choose_spec.2.2⟩

/-- The duality map of an empty manifold is bijective: both groups vanish. -/
theorem bijective_dualityMap_of_isEmpty [IsEmpty M] :
    Function.Bijective (o.dualityMap hn L p q h) := by
  have hc : IsZero ((TopCat.of M).compactSupportCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :=
    (isZero_singularCohomology_of_isEmpty _ ℤ L (TopCat.of M) p).of_iso
      (TopCat.compactSupportCohomologyIsoOfCompactSpace p)
  have hh : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj
      (TopCat.of M)) :=
    isZero_singularHomology_of_isEmpty L _ q
  have := hc.isIso hh (o.dualityMap hn L p q h)
  exact ConcreteCategory.bijective_of_isIso _

end Criteria

section OpenEmbedding

variable {U : Type} [TopologicalSpace U] [T2Space U] [ChartedSpace E U]

/-- **Naturality of the duality map along open embeddings**: for an open embedding `j : U → M`,
with `U` oriented by the pulled-back orientation, `D_M ∘ j_! = j_* ∘ D_U`, where
`j_! : Hᵖ_c(U; L) ⟶ Hᵖ_c(M; L)` is the extension of compactly supported classes and
`j_* : H_q(U; L) ⟶ H_q(M; L)` the pushforward. -/
theorem compactSupportCohomologyExtend_dualityMap {j : C(U, M)} (hj : IsOpenEmbedding j)
    (p q : ℕ) (h : p + q = n) :
    TopCat.compactSupportCohomologyExtend (f := TopCat.ofHom j) hj p ≫ o.dualityMap hn L p q h =
      (o.comap hj).dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (TopCat.ofHom j) := by
  refine TopCat.compactSupportCohomology_hom_ext fun K ↦ ?_
  rw [TopCat.compactSupportCohomologyι_comp_extend_assoc, compactSupportCohomologyι_dualityMap,
    compactSupportCohomologyι_dualityMap_assoc, Iso.inv_comp_eq,
    TopCat.singularCohomologyComplCompactsMapIso_hom]
  ext β
  have := ConcreteCategory.congr_hom (TopPair.singularCap_naturality
    (TopPair.ofSubsetMap (TopCat.ofHom j) (TopCat.mapsTo_compl_compacts_map hj.injective K)) ℤ
      (ρ_ _).inv (ρ_ L).hom p q n h β) ((o.comap hj).fundamentalClassOn hn K.isCompact)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst] at this
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    capFundamentalClassOn_apply, capFundamentalClassOn_apply]
  have hμ := o.localHomologyMap_fundamentalClassOn_comap hn hj K.isCompact
  rw [localHomologyMap_def] at hμ
  -- `hμ` is stated for the compact set `j '' K` and the goal for `K.map j`, which agree by
  -- definition (`Compacts.coe_map` is `rfl`). Since the set also occurs in the type of `β`, `rw`
  -- cannot change one into the other, but `exact` identifies them.
  exact (congrArg _ hμ.symm).trans this.symm

/-- **Naturality of the duality map for an open subset**: for an open `W ⊆ M`, oriented by the
restriction of `o`, extending compactly supported classes from `W` to `M` and then applying the
duality map of `M` is applying the duality map of `W` and then pushing forward along the
inclusion. -/
@[reassoc]
theorem compactSupportCohomologyExtend_inclusion'_dualityMap (W : Opens (TopCat.of M)) (p q : ℕ)
    (h : p + q = n) :
    TopCat.compactSupportCohomologyExtend W.isOpenEmbedding p ≫ o.dualityMap hn L p q h =
      (o.comap W.isOpenEmbedding).dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (Opens.inclusion' W) :=
  o.compactSupportCohomologyExtend_dualityMap hn L (j := (Opens.inclusion' W).hom)
    W.isOpenEmbedding p q h

/-- **Naturality of the duality map for nested open subsets**: for opens `V ⊆ W` of `M`, oriented
by the restrictions of `o`, extending compactly supported classes from `V` to `W` along the
inclusion `f : V ⟶ W` intertwines the duality maps of `V` and `W` with the pushforward along
`f`. -/
@[reassoc]
theorem compactSupportCohomologyExtend_toTopCat_map_dualityMap {V W : Opens (TopCat.of M)}
    (f : V ⟶ W) (p q : ℕ) (h : p + q = n) :
    TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding_toTopCat_map f) p ≫
        (o.comap W.isOpenEmbedding).dualityMap hn L p q h =
      (o.comap V.isOpenEmbedding).dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          ((Opens.toTopCat (TopCat.of M)).map f) := by
  have := (o.comap W.isOpenEmbedding).compactSupportCohomologyExtend_dualityMap hn L
    (j := ((Opens.toTopCat (TopCat.of M)).map f).hom)
    (Opens.isOpenEmbedding_toTopCat_map f) p q h
  rwa [comap_comap_toTopCat_map] at this

-- `@[elementwise]` cannot produce this from `compactSupportCohomologyExtend_inclusion'_dualityMap`:
-- the space `(Opens.toTopCat _).obj W` of the extension and the space of the duality map of `W`
-- agree only by definition, so the composite cannot be split by rewriting.
/-- Elementwise form of `compactSupportCohomologyExtend_inclusion'_dualityMap`:
`D_M (ι_! x) = ι_* (D_W x)` for the inclusion `ι` of an open `W ⊆ M`. -/
theorem compactSupportCohomologyExtend_inclusion'_dualityMap_apply (W : Opens (TopCat.of M))
    {p q : ℕ} (h : p + q = n)
    (x : ((Opens.toTopCat (TopCat.of M)).obj W).compactSupportCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.dualityMap hn L p q h (TopCat.compactSupportCohomologyExtend W.isOpenEmbedding p x) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (Opens.inclusion' W) ((o.comap W.isOpenEmbedding).dualityMap hn L p q h x) :=
  ConcreteCategory.congr_hom (o.compactSupportCohomologyExtend_inclusion'_dualityMap hn L W p q h) x

/-- Elementwise form of `compactSupportCohomologyExtend_toTopCat_map_dualityMap`:
`D_W (ι_! x) = ι_* (D_V x)` for the inclusion `ι : V ⟶ W` of nested opens of `M`. -/
theorem compactSupportCohomologyExtend_toTopCat_map_dualityMap_apply {V W : Opens (TopCat.of M)}
    (f : V ⟶ W) {p q : ℕ} (h : p + q = n)
    (x : ((Opens.toTopCat (TopCat.of M)).obj V).compactSupportCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    (o.comap W.isOpenEmbedding).dualityMap hn L p q h
        (TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding_toTopCat_map f) p x) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        ((Opens.toTopCat (TopCat.of M)).map f)
        ((o.comap V.isOpenEmbedding).dualityMap hn L p q h x) :=
  ConcreteCategory.congr_hom
    (o.compactSupportCohomologyExtend_toTopCat_map_dualityMap hn L f p q h) x

variable {j : C(U, M)} (hj : IsOpenEmbedding j) {p q : ℕ} (h : p + q = n)

/-- **Capping along a compact subset of an open subset**: for an open embedding `j : U → M` and a
compact `K ⊆ U`, capping with the fundamental class of the pulled-back orientation along `K`,
followed by `j_* : H_q(U; L) ⟶ H_q(M; L)`, is the inverse of the excision isomorphism
`Hᵖ(M, M ∖ j(K); L) ≅ Hᵖ(U, U ∖ K; L)` followed by capping with the fundamental class along
`j(K)`. -/
@[reassoc]
lemma capFundamentalClassOn_comap_comp_singularHomologyMap (K : Compacts (TopCat.of U)) :
    (o.comap hj).capFundamentalClassOn hn L K.isCompact p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (TopCat.ofHom j) =
      (TopCat.singularCohomologyComplCompactsMapIso (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L
          (f := TopCat.ofHom j) hj K p).inv ≫
        o.capFundamentalClassOn hn L
          (K.map (TopCat.ofHom j) (TopCat.ofHom j).hom.continuous).isCompact p q h := by
  have := TopCat.compactSupportCohomologyι p K ≫=
    o.compactSupportCohomologyExtend_dualityMap hn L hj p q h
  rw [TopCat.compactSupportCohomologyι_comp_extend_assoc, compactSupportCohomologyι_dualityMap,
    compactSupportCohomologyι_dualityMap_assoc] at this
  exact this.symm

/-- For an open embedding `j : U → M` inducing a bijection `j_*` on `H_q`, capping with the
fundamental class of the pulled-back orientation along a compact `K ⊆ U` is bijective exactly
when capping with the fundamental class along `j(K)` is. -/
theorem bijective_capFundamentalClassOn_comap_iff
    (hjq : Function.Bijective
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (TopCat.ofHom j)))
    (K : Compacts (TopCat.of U)) :
    Function.Bijective ((o.comap hj).capFundamentalClassOn hn L K.isCompact p q h) ↔
      Function.Bijective (o.capFundamentalClassOn hn L
        (K.map (TopCat.ofHom j) (TopCat.ofHom j).hom.continuous).isCompact p q h) := by
  rw [← Function.Bijective.of_comp_iff' hjq, ← Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (TopCat.singularCohomologyComplCompactsMapIso
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L (f := TopCat.ofHom j) hj K p).inv)]
  refine iff_of_eq (congrArg _ (funext fun α ↦ ?_))
  simpa only [ConcreteCategory.comp_apply, Function.comp_apply] using ConcreteCategory.congr_hom
    (o.capFundamentalClassOn_comap_comp_singularHomologyMap hn L hj h K) α

end OpenEmbedding

section Union

/-! ### Disjoint and directed unions of open sets -/

variable {p q : ℕ} (h : p + q = n)

/-- **The duality map of an open subset depends only on the subset.** For open embeddings
`j : U → M` and `j' : U' → M` with the same image, the duality map of the orientation pulled back
along `j` is bijective exactly when that of the orientation pulled back along `j'` is. -/
theorem bijective_dualityMap_comap_iff_of_range_eq {U U' : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace E U] [TopologicalSpace U'] [T2Space U'] [ChartedSpace E U'] {j : U → M}
    {j' : U' → M} (hj : IsOpenEmbedding j) (hj' : IsOpenEmbedding j') (hjj' : range j = range j') :
    Function.Bijective ((o.comap hj).dualityMap hn L p q h) ↔
      Function.Bijective ((o.comap hj').dualityMap hn L p q h) := by
  -- The homeomorphism `e : U ≃ₜ U'` over `M`, along which the two orientations correspond.
  let e : U ≃ₜ U' := hj.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr hjj').trans hj'.isEmbedding.toHomeomorph.symm)
  have he : j' ∘ e = j := funext fun x ↦ by
    rw [Function.comp_apply, ← hj'.isEmbedding.toHomeomorph_apply_coe]
    simp [e, Homeomorph.setCongr]
  let f : C(U, U') := ⟨e, e.continuous⟩
  have key := (o.comap hj').compactSupportCohomologyExtend_dualityMap hn L (j := f)
    e.isOpenEmbedding p q h
  rw [o.comap_comap_of_comp_eq hj' e.isOpenEmbedding hj he] at key
  have : IsIso (TopCat.ofHom f) := (TopCat.isIso_iff_isHomeomorph _).2 e.isHomeomorph
  have := TopCat.isIso_compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ))
    (k := ℤ) (M := L) (f := TopCat.ofHom f) e.isOpenEmbedding p
  have hext := ConcreteCategory.bijective_of_isIso
    (TopCat.compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (f := TopCat.ofHom f) e.isOpenEmbedding p)
  have hmap := ConcreteCategory.bijective_of_isIso
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map (TopCat.ofHom f))
  refine (Function.Bijective.of_comp_iff' hmap _).symm.trans ?_
  rw [← Function.Bijective.of_comp_iff _ hext]
  refine iff_of_eq (congrArg _ (funext fun x ↦ ?_))
  simpa only [ConcreteCategory.comp_apply, Function.comp_apply] using
    (ConcreteCategory.congr_hom key x).symm

/-- The duality maps of open subsets `U ≤ V` of `M` commute with the extension
`Hᵖ_c(U; L) ⟶ Hᵖ_c(V; L)` and the pushforward `H_q(U; L) ⟶ H_q(V; L)`. -/
private lemma compactSupportCohomologyExtend_dualityMap_of_le {U V : Opens M} (hUV : U ≤ V) :
    TopCat.compactSupportCohomologyExtend
        (f := TopCat.ofHom (⟨Set.inclusion (SetLike.coe_subset_coe.2 hUV),
          continuous_inclusion _⟩ : C(U, V))) (Opens.isOpenEmbedding_of_le hUV) p ≫
        (o.comap V.isOpenEmbedding').dualityMap hn L p q h =
      (o.comap U.isOpenEmbedding').dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (TopCat.ofHom (⟨Set.inclusion (SetLike.coe_subset_coe.2 hUV),
            continuous_inclusion _⟩ : C(U, V))) := by
  let ι : C(U, V) := ⟨Set.inclusion (SetLike.coe_subset_coe.2 hUV), continuous_inclusion _⟩
  have hι : IsOpenEmbedding ι := Opens.isOpenEmbedding_of_le hUV
  have key := (o.comap V.isOpenEmbedding').compactSupportCohomologyExtend_dualityMap hn L
    (j := ι) hι p q h
  rwa [o.comap_comap_of_comp_eq V.isOpenEmbedding' hι U.isOpenEmbedding' rfl] at key

/-- **Poincaré duality for a disjoint union of two open sets.** If `M` is the union of two
disjoint open sets `U` and `V` whose duality maps, for the pulled-back orientations, are bijective,
then the duality map `Hᵖ_c(M; L) ⟶ H_q(M; L)` is bijective. -/
theorem bijective_dualityMap_of_disjoint {U V : Opens M} (hUV : U ⊔ V = ⊤) (hd : Disjoint U V)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  -- The middle maps of the two Mayer–Vietoris sequences, which are isomorphisms.
  let Fc := biprod.desc
    (TopCat.compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (f := TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) U.isOpenEmbedding' p)
    (TopCat.compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (f := TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, M))) V.isOpenEmbedding' p)
  let Fh := biprod.desc
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))))
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, M))))
  have hFc : IsIso Fc := TopCat.isIso_biprodDesc_compactSupportCohomologyExtend_of_disjoint
    (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L (X := TopCat.of M) U V hUV hd p
  have hFh : IsIso Fh := TopCat.isIso_biprodDesc_singularHomologyFunctor_map_of_disjoint
    (X := TopCat.of M) L U.isOpen V.isOpen (by rw [← Opens.coe_sup, hUV, Opens.coe_top])
    (Opens.coe_disjoint.2 hd) q
  have := (ConcreteCategory.isIso_iff_bijective _).2 hU
  have := (ConcreteCategory.isIso_iff_bijective _).2 hV
  have := isIso_of_mono_of_epi (biprod.map ((o.comap U.isOpenEmbedding').dualityMap hn L p q h)
    ((o.comap V.isOpenEmbedding').dualityMap hn L p q h))
  -- The duality maps commute with them, by naturality along the inclusions.
  have hsq : Fc ≫ o.dualityMap hn L p q h =
      biprod.map ((o.comap U.isOpenEmbedding').dualityMap hn L p q h)
        ((o.comap V.isOpenEmbedding').dualityMap hn L p q h) ≫ Fh := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
      exact o.compactSupportCohomologyExtend_dualityMap hn L
        (j := (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) U.isOpenEmbedding' p q h
    · rw [biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc]
      exact o.compactSupportCohomologyExtend_dualityMap hn L
        (j := (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, M))) V.isOpenEmbedding' p q h
  have : IsIso (Fc ≫ o.dualityMap hn L p q h) := by
    rw [hsq]
    infer_instance
  have := IsIso.of_isIso_comp_left Fc (o.dualityMap hn L p q h)
  exact ConcreteCategory.bijective_of_isIso _

/-- **Poincaré duality for a directed union of open sets.** If `M` is the union of a directed
family of open sets `U i` whose duality maps, for the pulled-back orientations, are bijective,
then the duality map `Hᵖ_c(M; L) ⟶ H_q(M; L)` is bijective. -/
theorem bijective_dualityMap_of_iSup_eq_top {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {U : ι → Opens M} (hU : Monotone U) (hcover : ⨆ i, U i = ⊤)
    (hD : ∀ i, Function.Bijective ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  -- An empty family covers only the empty manifold.
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : IsEmpty M := ⟨fun x ↦ by simpa [← hcover] using (Opens.mem_top x)⟩
    exact o.bijective_dualityMap_of_isEmpty hn L h
  -- `H_q(M; L)` is the colimit of the `H_q(U i; L)`, since compact sets lie in some `U i`.
  have hc := TauCeti.isColimitMapCoconeSingularHomologySubset (X := TopCat.of M) L q
    (U := fun i ↦ (U i : Set M)) (fun _ _ hij ↦ hU hij) fun K hK ↦
      Compacts.exists_subset_of_iSup_eq_top hU.directed_le hcover ⟨K, hK⟩
  -- Naturality along the inclusion of `U i` into `M`; `Opens.inclusion' (U i)` is by definition
  -- `TopCat.ofHom ⟨Subtype.val, _⟩`, so `Opens.coe_inclusion'` holds by `rfl`.
  have hnat (i : ι) (z) : o.dualityMap hn L p q h
      (TopCat.compactSupportCohomologyExtend (U i).isOpenEmbedding p z) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (TopCat.ofHom (ContinuousMap.subtypeVal (U i : Set M)))
        ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h z) :=
    ConcreteCategory.congr_hom (o.compactSupportCohomologyExtend_dualityMap hn L
      (j := (⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M))) (U i).isOpenEmbedding' p q h) z
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨i, z, rfl⟩ := TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top hU hcover x
    rw [hnat] at hx
    obtain ⟨k, f, g, hf⟩ := Concrete.isColimit_exists_of_rep_eq _ hc
      ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h z) 0
      (by rw [map_zero]; exact hx)
    rw [map_zero] at hf
    let ι : C(U i, U k) := ⟨Set.inclusion (SetLike.coe_subset_coe.2 (hU f.le)),
      continuous_inclusion _⟩
    have hι : IsOpenEmbedding ι := Opens.isOpenEmbedding_of_le (hU f.le)
    -- The class `z` already vanishes in `Hᵖ_c(U k)`, by duality on `U k`.
    have hz : TopCat.compactSupportCohomologyExtend (f := TopCat.ofHom ι) hι p z = 0 :=
      (injective_iff_map_eq_zero _).1 (hD k).1 _ ((ConcreteCategory.congr_hom
        (o.compactSupportCohomologyExtend_dualityMap_of_le hn L h (hU f.le)) z).trans hf)
    have hcomp := TopCat.compactSupportCohomologyExtend_comp (R := ModuleCat.of ℤ (ULift.{0} ℤ))
      (k := ℤ) (M := L) (f := TopCat.ofHom ι) (g := Opens.inclusion' (X := TopCat.of M) (U k)) hι
      (Opens.isOpenEmbedding (X := TopCat.of M) (U k)) p
      (Opens.isOpenEmbedding (X := TopCat.of M) (U i))
    have hx : TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding (X := TopCat.of M) (U i))
        p z = TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding (X := TopCat.of M) (U k))
          p (TopCat.compactSupportCohomologyExtend (f := TopCat.ofHom ι) hι p z) :=
      ConcreteCategory.congr_hom hcomp z
    rw [hx, hz]
    exact map_zero _
  · obtain ⟨i, w, rfl⟩ := Concrete.isColimit_exists_rep _ hc y
    obtain ⟨z, rfl⟩ := (hD i).2 w
    exact ⟨_, hnat i z⟩

/-- The duality map of an open subset `U ≤ W` of `M`, with the orientation pulled back from `M`,
is bijective exactly when that of `U`, read as an open subset of `W`, with the orientation pulled
back from `W`, is. -/
private theorem bijective_dualityMap_comap_comap_iff {U W : Opens M} (hUW : U ≤ W) :
    Function.Bijective (((o.comap W.isOpenEmbedding').comap
        (Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U :
          Opens W).isOpenEmbedding').dualityMap hn L p q h) ↔
      Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h) := by
  rw [comap_comap]
  refine o.bijective_dualityMap_comap_iff_of_range_eq hn L h _ _ ?_
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.val.val, y.property⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨⟨y.val, hUW y.property⟩, y.property⟩, rfl⟩

/-- **Poincaré duality for the union of two disjoint open subsets.** If the duality maps of two
disjoint open subsets `U` and `V` of `M` are bijective, then so is that of `U ⊔ V`, for the
orientations pulled back from `M`. -/
theorem bijective_dualityMap_comap_sup_of_disjoint {U V : Opens M} (hd : Disjoint U V)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective ((o.comap (U ⊔ V).isOpenEmbedding').dualityMap hn L p q h) := by
  let i : C(↥(U ⊔ V), M) := ⟨Subtype.val, continuous_subtypeVal⟩
  refine (o.comap (U ⊔ V).isOpenEmbedding').bijective_dualityMap_of_disjoint hn L h
    (U := Opens.comap i U) (V := Opens.comap i V) ?_ ?_
    ((o.bijective_dualityMap_comap_comap_iff hn L h le_sup_left).2 hU)
    ((o.bijective_dualityMap_comap_comap_iff hn L h le_sup_right).2 hV)
  · rw [← map_sup, eq_top_iff]
    exact fun x _ ↦ x.property
  · rw [disjoint_iff, ← map_inf, disjoint_iff.1 hd, map_bot]

/-- **Poincaré duality for a directed union of open subsets.** If the duality maps of the members
of a directed family of open subsets `U i` of `M` are bijective, then so is that of their union,
for the orientations pulled back from `M`. -/
theorem bijective_dualityMap_comap_iSup_of_monotone {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {U : ι → Opens M} (hU : Monotone U)
    (hD : ∀ i, Function.Bijective ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective ((o.comap (⨆ i, U i).isOpenEmbedding').dualityMap hn L p q h) := by
  let i : C(↥(⨆ i, U i), M) := ⟨Subtype.val, continuous_subtypeVal⟩
  refine (o.comap (⨆ i, U i).isOpenEmbedding').bijective_dualityMap_of_iSup_eq_top hn L h
    (U := fun j ↦ Opens.comap i (U j)) (fun _ _ hjk ↦ Opens.comap_mono i (hU hjk)) ?_
    fun j ↦ (o.bijective_dualityMap_comap_comap_iff hn L h (le_iSup U j)).2 (hD j)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 x.property
  exact Opens.mem_iSup.2 ⟨j, hj⟩

/-- **Poincaré duality for a union of pairwise disjoint open subsets.** If the duality maps of
pairwise disjoint open subsets `s i` of `M` are bijective, then so is that of their union, for the
orientations pulled back from `M`. This is the disjoint-union step of the Mayer–Vietoris induction
for Poincaré duality (`TauCeti.mayerVietoris_induction`). -/
theorem bijective_dualityMap_comap_iSup_of_pairwise_disjoint {ι : Type} {s : ι → Opens M}
    (hs : Pairwise fun i j ↦ Disjoint (s i) (s j))
    (hD : ∀ i, Function.Bijective ((o.comap (s i).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective ((o.comap (⨆ i, s i).isOpenEmbedding').dualityMap hn L p q h) := by
  classical
  -- The finite partial unions form a directed family with the same union.
  let T : Finset ι → Opens M := fun F ↦ ⨆ i ∈ F, s i
  have hT : Monotone T := fun _ _ hFG ↦ biSup_mono fun _ hi ↦ hFG hi
  have hTD (F : Finset ι) :
      Function.Bijective ((o.comap (T F).isOpenEmbedding').dualityMap hn L p q h) := by
    induction F using Finset.induction_on with
    | empty =>
      have : IsEmpty ↥(T ∅) := ⟨fun x ↦ by simpa [T] using x.property⟩
      exact (o.comap _).bijective_dualityMap_of_isEmpty hn L h
    | insert a F ha ih =>
      have hTa : T (insert a F) = s a ⊔ T F := by
        simp only [T, Finset.iSup_insert]
      have hd : Disjoint (s a) (T F) := by
        simp only [T, disjoint_iSup_iff]
        exact fun i hi ↦ hs fun hai ↦ ha (hai ▸ hi)
      rw [hTa]
      exact o.bijective_dualityMap_comap_sup_of_disjoint hn L h hd (hD a) ih
  have hsup : ⨆ F, T F = ⨆ i, s i :=
    le_antisymm (iSup_le fun _ ↦ iSup₂_le fun i _ ↦ le_iSup s i)
      (iSup_le fun i ↦ le_iSup_of_le {i} (by simp [T]))
  rw [← hsup]
  exact o.bijective_dualityMap_comap_iSup_of_monotone hn L h hT hTD

end Union

end HomologicalOrientation

end TauCeti
