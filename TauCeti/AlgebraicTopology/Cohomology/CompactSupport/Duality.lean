/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
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
Poincaré duality.

## Main definitions

* `TauCeti.HomologicalOrientation.capFundamentalClassOn`: capping with the fundamental class along
  a compact set, `Hᵖ(M, M ∖ K; L) ⟶ H_q(M; L)`.
* `TauCeti.HomologicalOrientation.dualityMap`: the duality map `Hᵖ_c(M; L) ⟶ H_q(M; L)`.

## Main results

* `TauCeti.HomologicalOrientation.compactSupportCohomologyι_dualityMap`: the duality map on a
  class supported in a compact `K` is the cap product with `μ_K`.
* `TauCeti.HomologicalOrientation.dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv`: for
  compact `M`, the duality map is the cap product with the fundamental class.
* `TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_comap`: open embeddings
  carry fundamental classes along compact sets to fundamental classes.
* `TauCeti.HomologicalOrientation.dualityMap_neg`: reversing the orientation negates the duality
  map.
* `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_dualityMap`: naturality along open
  embeddings.

## Implementation notes

All groups are abelian groups, that is, objects of `ModuleCat ℤ`, and `M` lives in `Type`, as for
`TauCeti.HomologicalOrientation.fundamentalClassOn`. Cohomology and homology follow the convention
of `TauCeti.HomologicalOrientation.evalFundamentalClass`: singular chains have the integral
coefficients `ModuleCat.of ℤ (ULift ℤ)` of the fundamental classes, and `Hᵖ(-; L)` is computed from
cochains on them with values in `L`. The cap product pairs the two along the right unitors
`ℤ ⟶ ℤ ⊗ 𝟙` and `L ⊗ 𝟙 ⟶ L`, so that a cochain `φ` and a simplex `σ` give
`φ(σ|[0, …, p]) • σ|[p, …, n]`. A module over a ring enters through its underlying abelian group.

Instance search finds the `ℤ`-linear structure of `ModuleCat ℤ` as a preadditive category, for
which Mathlib's `MonoidalLinear ℤ` instance does not apply; the local instance
`TauCeti.monoidalLinearIntDuality` supplies it, as for `TopCat.integralCup`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the duality map `D_M : Hᵖ_c(M; R) ⟶ H_{n-p}(M; R)` defined before Theorem 3.35, and
  its naturality for inclusions of open sets used in Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module TopologicalSpace Topology Set

namespace TauCeti

/-- Mathlib's `MonoidalLinear ℤ` instance on `ModuleCat ℤ` is stated for its `ℤ`-linear structure
as a category of modules, while instance search finds the `ℤ`-linear structure of a preadditive
category; whiskering commutes with the integer multiples of the latter as well. -/
local instance monoidalLinearIntDuality : MonoidalLinear ℤ (ModuleCat.{0} ℤ) where
  whiskerLeft_smul X _ _ r f := whiskerLeft_zsmul r X f
  smul_whiskerRight r _ _ f X := zsmul_whiskerRight r f X

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
  ModuleCat.ofHom (X := (TopPair.ofSubset (Kᶜ : Set (TopCat.of M))).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p)
    { toFun α := ((TopPair.ofSubset (Kᶜ : Set (TopCat.of M))).singularCap ℤ (ρ_ _).inv
          (ρ_ L).hom p q n h α).hom (o.fundamentalClassOn hn hK)
      map_add' α β := by
        rw [LinearMap.map_add]
        rfl
      map_smul' c α := by
        refine (congrArg (fun f ↦ ModuleCat.Hom.hom f (o.fundamentalClassOn hn hK))
          (((TopPair.ofSubset (Kᶜ : Set (TopCat.of M))).singularCap ℤ (ρ_ _).inv
            (ρ_ L).hom p q n h).map_smul c α)).trans ?_
        simp only [ModuleCat.hom_smul, LinearMap.smul_apply, RingHom.id_apply]
        -- The two sides use `zsmul` and the given `ℤ`-module structure, respectively.
        exact (int_smul_eq_zsmul _ _ _).symm }

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
        (TopCat.mapsTo_id_compl_compacts hKK'))) = 𝟙 _ :=
    (congrArg (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map ·)
      (TopPair.ofSubsetMap_fst (g := 𝟙 (TopCat.of M)) (TopCat.mapsTo_id_compl_compacts hKK'))).trans
      (CategoryTheory.Functor.map_id _ _)
  have := ConcreteCategory.congr_hom (TopPair.singularCap_naturality
    (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (TopCat.mapsTo_id_compl_compacts hKK')) ℤ (ρ_ _).inv
      (ρ_ L).hom p q n h α) (o.fundamentalClassOn hn K'.isCompact)
  rw [hfst] at this
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, capFundamentalClassOn_apply,
    capFundamentalClassOn_apply]
  have hμ := o.localHomologyRestriction_fundamentalClassOn_of_subset hn K'.isCompact
    K.isCompact (show (K : Set M) ⊆ K' from hKK')
  rw [localHomologyRestriction_def] at hμ
  refine (Eq.trans ?_ this).trans ((ConcreteCategory.comp_apply _ _ _).trans (congrArg _ hμ))
  exact (ConcreteCategory.comp_apply _ _ _).trans (ConcreteCategory.id_apply _)

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
  ext α
  rw [Preadditive.comp_neg, compactSupportCohomologyι_dualityMap,
    compactSupportCohomologyι_dualityMap, ModuleCat.hom_neg, LinearMap.neg_apply,
    capFundamentalClassOn_apply, capFundamentalClassOn_apply, fundamentalClassOn_neg, map_neg]
  rfl

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
  refine Eq.trans ?_ this.symm
  exact (congrArg _ (o.singularHomologyπ_fundamentalClass hn).symm).trans
    (ConcreteCategory.comp_apply _ _ _).symm

section OpenEmbedding

variable {U : Type} [TopologicalSpace U] [T2Space U] [ChartedSpace E U]

/-- **Open embeddings carry fundamental classes to fundamental classes**: for an open embedding
`j : U → M` and compact `K ⊆ U`, the map `Hₙ(U, U ∖ K; ℤ) ⟶ Hₙ(M, M ∖ j(K); ℤ)` induced by `j`
carries the fundamental class along `K` of the pulled-back orientation `o.comap hj` to the
fundamental class of `o` along `j(K)`. -/
theorem localHomologyMap_fundamentalClassOn_comap {j : C(U, M)} (hj : IsOpenEmbedding j)
    {K : Set U} (hK : IsCompact K) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) j (hj.injective.preimage_image K).subset n
        ((o.comap hj).fundamentalClassOn hn hK) =
      o.fundamentalClassOn hn (hK.image j.continuous) := by
  refine o.eq_fundamentalClassOn hn _ ?_
  rintro _ ⟨x, hx, rfl⟩
  have hjx : j ⁻¹' {j x} ⊆ {x} := by
    rw [← image_singleton, hj.injective.preimage_image]
  rw [← ConcreteCategory.comp_apply, localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_comp_localHomologyMap _ j (singleton_subset_iff.2 hx) hjx,
    ConcreteCategory.comp_apply, localHomologyRestriction_fundamentalClassOn _ _ _ hx,
    ← localOrientationEquiv_comap_apply o hj x, IsOpenEmbedding.coe_localOrientationEquiv,
    localHomologyIsoOfIsOpenEmbedding_hom]
  rfl

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
  refine Eq.trans ?_ this.symm
  have hμ := o.localHomologyMap_fundamentalClassOn_comap hn hj K.isCompact
  rw [localHomologyMap_def] at hμ
  exact congrArg _ hμ.symm

end OpenEmbedding

end HomologicalOrientation

end TauCeti
