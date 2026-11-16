/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Geometry.Manifold.HasGroupoid
import TauCeti.AlgebraicTopology.Singular.DirectedUnion
import TauCeti.Topology.Sets.Opens

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

Bijectivity of the duality map passes to increasing unions of open sets
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_monotone`). If `M` is the union of an
increasing family of open sets `U i`, every compactly supported class of `M` is extended from some
`U i`, and every homology class of `M` is pushed forward from some `U i`, by compactness of the
supports; a homology class of `U i` that vanishes in `M` already vanishes in some larger `U j`.
With the naturality of the duality maps along the inclusions, bijectivity of each `D_{U i}` thus
gives bijectivity of `D_M`, and separately so for injectivity and surjectivity.

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
  embeddings, and `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_dualityMap_of_le`
  along inclusions of open subsets.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_cofinal`: the duality map is bijective
  if capping is bijective along cofinally many compact sets.
* `TauCeti.HomologicalOrientation.injective_dualityMap_of_monotone`,
  `TauCeti.HomologicalOrientation.surjective_dualityMap_of_monotone`,
  `TauCeti.HomologicalOrientation.bijective_dualityMap_of_monotone`: injectivity, surjectivity and
  bijectivity of the duality map pass from the members of an increasing open cover to the
  manifold.

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

Open subsets of `M` enter as the objects `(Opens.toTopCat (TopCat.of M)).obj V`, with their
inclusions `Opens.inclusion'`, as in the colimit descriptions of compactly supported cohomology and
of singular homology over an increasing open cover. These objects are the subtypes `V` only by
definition, so the instance `TopologicalSpace.Opens.instChartedSpaceToTopCatObj` makes them charted
spaces, as `TopologicalSpace.Opens.t2Space_toTopCat_obj` makes them Hausdorff.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the duality map `D_M : Hᵖ_c(M; R) ⟶ H_{n-p}(M; R)` defined before Theorem 3.35, its
  naturality for inclusions of open sets used in Lemma 3.36, and the step of the proof of
  Lemma 3.36 passing to increasing unions of open sets.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module TopologicalSpace Topology Set

/-- An open subset of a charted space, as an object of `TopCat`, is a charted space, like the
subtype. -/
instance TopologicalSpace.Opens.instChartedSpaceToTopCatObj {H : Type*} [TopologicalSpace H]
    {X : TopCat} [ChartedSpace H X] (V : Opens X) : ChartedSpace H ((Opens.toTopCat X).obj V) :=
  inferInstanceAs (ChartedSpace H V)

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
      (TopCat.of M)) := by
    rcases q with _ | q
    · exact isZero_singularHomologyFunctor_zero_of_isEmpty L _
    · exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ L _
        q.succ_ne_zero
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

/-- Naturality of the duality maps of two open sets `V ≤ W` of `M`, both oriented by the
pulled-back orientation, along the inclusion of `V` into `W`. -/
lemma compactSupportCohomologyExtend_dualityMap_of_le {V W : Opens (TopCat.of M)} (hVW : V ≤ W) :
    TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding_toTopCat_map (homOfLE hVW)) p ≫
        (o.comap W.isOpenEmbedding).dualityMap hn L p q h =
      (o.comap V.isOpenEmbedding).dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          ((Opens.toTopCat (TopCat.of M)).map (homOfLE hVW)) := by
  have hcomap : (o.comap W.isOpenEmbedding).comap
      (Opens.isOpenEmbedding_toTopCat_map (homOfLE hVW)) = o.comap V.isOpenEmbedding := by
    rw [comap_comap]
    refine o.comap_congr _ _ ?_
    rw [← ContinuousMap.coe_comp, ← TopCat.hom_comp, Opens.toTopCat_map_comp_inclusion']
  rw [← hcomap]
  exact (o.comap W.isOpenEmbedding).compactSupportCohomologyExtend_dualityMap hn L
    (Opens.isOpenEmbedding_toTopCat_map (homOfLE hVW)) p q h

end OpenEmbedding

section DirectedUnion

variable {p q : ℕ} (h : p + q = n)

variable {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] {U : ι → Opens (TopCat.of M)}
  (hU : Monotone U)
  (hcover : ⨆ i, U i = ⊤)

include hU hcover

/-- **Injectivity of the duality map is local for directed open covers.** If an oriented manifold
`M` is the union of an increasing family of open sets `U i`, and the duality map of each `U i`,
oriented by the pulled-back orientation, is injective, then so is the duality map of `M`. -/
theorem injective_dualityMap_of_monotone
    (H : ∀ i, Function.Injective ((o.comap (U i).isOpenEmbedding).dualityMap hn L p q h)) :
    Function.Injective (o.dualityMap hn L p q h) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain _ | _ := isEmpty_or_nonempty ι
  · have := Opens.isEmpty_of_iSup_eq_top hcover
    exact (o.bijective_dualityMap_of_isEmpty hn L h).1 (hx.trans (map_zero _).symm)
  -- `x` is extended from some `U i`, where its dual dies in a larger `U j`.
  obtain ⟨i, z, rfl⟩ :=
    TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top (X := TopCat.of M) hU hcover x
  have hi := ConcreteCategory.congr_hom
    (o.compactSupportCohomologyExtend_dualityMap hn L (U i).isOpenEmbedding p q h) z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hx, TopCat.ofHom_hom] at hi
  obtain ⟨j, hij, hj⟩ :=
    exists_singularHomologyMap_toTopCat_map_eq_zero_of_iSup_eq_top (Y := TopCat.of M) L q hU
      hcover _ hi.symm
  have hij' := ConcreteCategory.congr_hom
    (o.compactSupportCohomologyExtend_dualityMap_of_le hn L h (hU hij)) z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hj] at hij'
  -- So the extension of `z` to `U j` vanishes, and hence so does its extension to `M`, since the
  -- inclusion of `U i` into `M` factors through `U j`.
  have hiM := (U j).isOpenEmbedding.comp (Opens.isOpenEmbedding_toTopCat_map (homOfLE (hU hij)))
  rw [← TopCat.compactSupportCohomologyExtend_congr
      (Opens.toTopCat_map_comp_inclusion' (homOfLE (hU hij))) hiM,
    TopCat.compactSupportCohomologyExtend_comp
      (Opens.isOpenEmbedding_toTopCat_map (homOfLE (hU hij)))
      (U j).isOpenEmbedding p hiM, ConcreteCategory.comp_apply,
    H j (hij'.trans (map_zero _).symm), map_zero]

/-- **Surjectivity of the duality map is local for directed open covers.** If an oriented
manifold `M` is the union of an increasing family of open sets `U i`, and the duality map of each
`U i`, oriented by the pulled-back orientation, is surjective, then so is the duality map of `M`. -/
theorem surjective_dualityMap_of_monotone
    (H : ∀ i, Function.Surjective ((o.comap (U i).isOpenEmbedding).dualityMap hn L p q h)) :
    Function.Surjective (o.dualityMap hn L p q h) := fun y ↦ by
  obtain _ | _ := isEmpty_or_nonempty ι
  · have := Opens.isEmpty_of_iSup_eq_top hcover
    exact (o.bijective_dualityMap_of_isEmpty hn L h).2 y
  obtain ⟨i, y, rfl⟩ :=
    exists_singularHomologyMap_inclusion'_eq_of_iSup_eq_top (Y := TopCat.of M) L q hU hcover y
  obtain ⟨z, rfl⟩ := H i y
  refine ⟨TopCat.compactSupportCohomologyExtend (U i).isOpenEmbedding p z, ?_⟩
  rw [← ConcreteCategory.comp_apply,
    o.compactSupportCohomologyExtend_dualityMap hn L (U i).isOpenEmbedding p q h,
    ConcreteCategory.comp_apply, TopCat.ofHom_hom]

/-- **Poincaré duality is local for directed open covers.** If an oriented manifold `M` is the
union of an increasing family of open sets `U i`, and the duality map of each `U i`, oriented by
the pulled-back orientation, is bijective, then so is the duality map of `M`. -/
theorem bijective_dualityMap_of_monotone
    (H : ∀ i, Function.Bijective ((o.comap (U i).isOpenEmbedding).dualityMap hn L p q h)) :
    Function.Bijective (o.dualityMap hn L p q h) :=
  ⟨o.injective_dualityMap_of_monotone hn L h hU hcover fun i ↦ (H i).1,
    o.surjective_dualityMap_of_monotone hn L h hU hcover fun i ↦ (H i).2⟩

end DirectedUnion

end HomologicalOrientation

end TauCeti
