/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import TauCeti.AlgebraicTopology.Singular.Coinvariants
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Resolution

/-!
# The singular homology of the base of a contractible free cover is group homology

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G` on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`, and let `k` be a commutative ring. The singular chains of `E`
form a chain complex of representations of `G`, `TauCeti.singularChainsRep k E G`. Its
coinvariants `(k ⊗ C(E; k))_G`, with `k` the trivial representation, are the singular chains of
`B` (`IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso`): the class of `a ⊗ c` goes to
`a • p_* c`, every singular simplex of `B` lifts to `E`, and two lifts of one simplex differ by an
element of `G` (`IsQuotientCoveringMap.isColimitMapCoconeToSSet`).

If `E` is contractible, the singular chains of `E` are a projective resolution of the trivial
representation (`TauCeti.singularChainsResolution`), since `G` acts freely on `E`. Group homology
with trivial coefficients is the homology of the coinvariants of any projective resolution of
`k` (`groupHomologyIso`), so the singular homology of `B` is the group homology of `G`
(`IsQuotientCoveringMap.singularHomologyIsoGroupHomology`):

`Hₙ(B; k) ≅ Hₙ(G, k)`.

This applies to the orbit space of a contractible free `G`-space, such as a classifying space of
`G` with its universal cover.

## Main definitions

* `IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso`: the coinvariants of the
  singular chains of `E` are the singular chains of `B`.
* `IsQuotientCoveringMap.singularHomologyIsoGroupHomology`: for contractible `E`, the singular
  homology of `B` is the group homology of `G` with trivial coefficients.

## Main results

* `IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso_hom_f_coinvariantsTensorMk`: the
  comparison of chains sends the class of `a ⊗ c` to `a • p_* c`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4, Proposition 4.1, and
  Section III.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial

universe u

namespace IsQuotientCoveringMap

open TauCeti Representation MonoidalCategory

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k]

/-- Pushing chains forward to the base of a quotient covering is invariant under translation. -/
private lemma singularChains_map_comp_smul (g : G) :
    haveI := hG.toContinuousConstSMul
    (singularChains k).map (TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩) ≫
      (singularChains k).map p = (singularChains k).map p := by
  have := hG.toContinuousConstSMul
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  exact ConcreteCategory.hom_ext _ _ fun e ↦ hG.map_smul g

/-- Pushing chains forward to the base of a quotient covering forgets the action of `G`. -/
private lemma singularChains_map_f_singularChainsRepresentation (n : ℕ) (g : G)
    (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    ((singularChains k).map p).f n (singularChainsRepresentation k E G n g c) =
      ((singularChains k).map p).f n c := by
  have := hG.toContinuousConstSMul
  rw [singularChainsRepresentation_apply]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f ↦ HomologicalComplex.Hom.f f n) (singularChains_map_comp_smul hG k g)) c

/-- Pushing chains forward to the base, as a morphism to the trivial representation on the
singular `n`-chains of the base. -/
private def singularChainsPushRep (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    Rep.of (singularChainsRepresentation k E G n) ⟶
      Rep.trivial k G (((singularChains k).obj B).X n) :=
  haveI := hG.toContinuousConstSMul
  Rep.ofHom
    { toLinearMap := (((singularChains k).map p).f n).hom
      isIntertwining' g := LinearMap.ext fun c ↦
        singularChains_map_f_singularChainsRepresentation hG k n g c }

/-- The map from the coinvariants `(k ⊗ Cₙ(E))_G` to the singular `n`-chains of the base,
sending the class of `a ⊗ c` to `a • p_* c`. -/
private def coinvariantsTensorToSingularChains (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    ((Rep.coinvariantsTensor k G).obj (Rep.trivial k G k)).obj
        (Rep.of (singularChainsRepresentation k E G n)) ⟶ ((singularChains k).obj B).X n :=
  haveI := hG.toContinuousConstSMul
  Rep.desc ((λ_ _).hom ≫ singularChainsPushRep hG k n)

/-- The class of `a ⊗ c` goes to `a • p_* c`. -/
private lemma coinvariantsTensorToSingularChains_mk (n : ℕ) (a : k)
    (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    (coinvariantsTensorToSingularChains hG k n).hom (Rep.coinvariantsTensorMk (Rep.trivial k G k)
        (Rep.of (singularChainsRepresentation k E G n)) a c) =
      a • ((singularChains k).map p).f n c := by
  have := hG.toContinuousConstSMul
  rw [Rep.coinvariantsTensorMk_apply, coinvariantsTensorToSingularChains]
  simp [singularChainsPushRep]

/-- Translating a chain does not change the class of `1 ⊗ c` in the coinvariants. -/
private lemma coinvariantsTensorMk_one_singularChainsRepresentation (n : ℕ) (g : G)
    (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    Rep.coinvariantsTensorMk (Rep.trivial k G k) (Rep.of (singularChainsRepresentation k E G n)) 1
        (singularChainsRepresentation k E G n g c) =
      Rep.coinvariantsTensorMk (Rep.trivial k G k)
        (Rep.of (singularChainsRepresentation k E G n)) 1 c := by
  have := hG.toContinuousConstSMul
  rw [Rep.coinvariantsTensorMk_apply, Rep.coinvariantsTensorMk_apply]
  -- `g` acts on `1 ⊗ c` by `1 ⊗ g • c`, the action on the trivial factor being the identity.
  exact Coinvariants.mk_self_apply _ g (1 ⊗ₜ c)

/-- The map from the singular `n`-chains of the base to the coinvariants `(k ⊗ Cₙ(E))_G`,
sending a simplex to the class of `1 ⊗ σ` for a chosen lift `σ`. -/
private def singularChainsToCoinvariantsTensor (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    ((singularChains k).obj B).X n →ₗ[k] ((Rep.coinvariantsTensor k G).obj (Rep.trivial k G k)).obj
        (Rep.of (singularChainsRepresentation k E G n)) :=
  haveI := hG.toContinuousConstSMul
  chainsDesc fun τ ↦ Rep.coinvariantsTensorMk (Rep.trivial k G k)
    (Rep.of (singularChainsRepresentation k E G n)) 1
      (simplexChain (hG.toSSet_map_app_surjective _ τ).choose 1)

/-- A simplex of the base goes to the class of `1 ⊗ σ` for the chosen lift `σ`. -/
private lemma singularChainsToCoinvariantsTensor_simplexChain_one (n : ℕ)
    (τ : (TopCat.toSSet.obj B) _⦋n⦌) :
    haveI := hG.toContinuousConstSMul
    singularChainsToCoinvariantsTensor hG k n (simplexChain τ 1) =
      Rep.coinvariantsTensorMk (Rep.trivial k G k) (Rep.of (singularChainsRepresentation k E G n)) 1
        (simplexChain (hG.toSSet_map_app_surjective _ τ).choose 1) :=
  chainsDesc_simplexChain_one _ τ

/-- The comparison of `(k ⊗ Cₙ(E))_G` with the singular `n`-chains of the base is a linear
equivalence. -/
private def coinvariantsTensorLinearEquivSingularChains (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    ((Rep.coinvariantsTensor k G).obj (Rep.trivial k G k)).obj
        (Rep.of (singularChainsRepresentation k E G n)) ≃ₗ[k] ((singularChains k).obj B).X n :=
  haveI := hG.toContinuousConstSMul
  LinearEquiv.ofLinearMap (coinvariantsTensorToSingularChains hG k n).hom
    (singularChainsToCoinvariantsTensor hG k n)
    (singularChains_linearMap_ext fun τ ↦ by
      simp only [LinearMap.comp_apply, LinearMap.id_apply,
        singularChainsToCoinvariantsTensor_simplexChain_one]
      rw [coinvariantsTensorToSingularChains_mk]
      simp only [one_smul, singularChains_map_f_simplexChain,
        (hG.toSSet_map_app_surjective _ τ).choose_spec])
    (Coinvariants.hom_ext <| TensorProduct.ext <| LinearMap.ext_ring <|
      singularChains_linearMap_ext fun σ ↦ by
      -- The chosen lift of `p_* σ` is a translate `g • σ` of `σ`, and translating does not
      -- change the class of `1 ⊗ σ`.
      obtain ⟨g, hg⟩ := (hG.toSSet_map_app_eq_iff _ σ).1
        (hG.toSSet_map_app_surjective _ ((TopCat.toSSet.map p).app _ σ)).choose_spec
      simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
        LinearMap.id_apply]
      rw [← Rep.coinvariantsTensorMk_apply, coinvariantsTensorToSingularChains_mk]
      simp only [one_smul, singularChains_map_f_simplexChain,
        singularChainsToCoinvariantsTensor_simplexChain_one]
      rw [← hg, ← singularChainsRepresentation_simplexChain]
      exact coinvariantsTensorMk_one_singularChainsRepresentation hG k n g _)

/-- The comparison maps commute with the differentials. -/
private lemma coinvariantsTensorToSingularChains_comp_d (j : ℕ) :
    haveI := hG.toContinuousConstSMul
    coinvariantsTensorToSingularChains hG k (j + 1) ≫ ((singularChains k).obj B).d (j + 1) j =
      ((Rep.coinvariantsTensor k G).obj (Rep.trivial k G k)).map
          (singularChainsRepDifferential k E G j) ≫ coinvariantsTensorToSingularChains hG k j := by
  have := hG.toContinuousConstSMul
  refine Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a c ↦ ?_)
  -- On the class of `a ⊗ c`, the map induced by the differential gives the class of `a ⊗ d c`;
  -- this holds by definition of the coinvariants functor and of the tensor product of morphisms.
  have hmap : (((Rep.coinvariantsTensor k G).obj (Rep.trivial k G k)).map
      (singularChainsRepDifferential k E G j)).hom (Rep.coinvariantsTensorMk _ _ a c) =
        Rep.coinvariantsTensorMk _ _ a ((singularChainsRepDifferential k E G j).hom c) := rfl
  rw [LinearMap.compr₂_apply (Rep.coinvariantsTensorMk _ _),
    LinearMap.compr₂_apply (Rep.coinvariantsTensorMk _ _)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hmap]
  rw [coinvariantsTensorToSingularChains_mk, coinvariantsTensorToSingularChains_mk,
    singularChainsRepDifferential_hom_apply, map_smul]
  exact congrArg (a • ·) (ConcreteCategory.congr_hom (((singularChains k).map p).comm (j + 1) j) c)

/-- **The singular chains of the base of a quotient covering are the coinvariants of those of
the total space**: for the quotient covering map `p : E ⟶ B` of an action of `G`, the chain
complex `(k ⊗ C(E; k))_G` is isomorphic to `C(B; k)`, the class of `a ⊗ c` going to `a • p_* c`. -/
def singularChainsRepCoinvariantsTensorIso :
    haveI := hG.toContinuousConstSMul
    (singularChainsRep k E G).coinvariantsTensorObj (Rep.trivial k G k) ≅
      (singularChains k).obj B :=
  haveI := hG.toContinuousConstSMul
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (coinvariantsTensorLinearEquivSingularChains hG k n).toModuleIso)
    fun i j (h : j + 1 = i) ↦ by
      subst h
      rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d, singularChainsRep_d]
      exact coinvariantsTensorToSingularChains_comp_d hG k j

/-- The comparison sends the class of `a ⊗ c` to `a • p_* c`. -/
lemma singularChainsRepCoinvariantsTensorIso_hom_f_coinvariantsTensorMk (n : ℕ) (a : k)
    (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    ((hG.singularChainsRepCoinvariantsTensorIso k).hom.f n).hom
        (Rep.coinvariantsTensorMk (Rep.trivial k G k)
          (Rep.of (singularChainsRepresentation k E G n)) a c) =
      a • ((singularChains k).map p).f n c :=
  coinvariantsTensorToSingularChains_mk hG k n a c

/-- **The singular homology of the base of a contractible free covering is group homology**: for
the quotient covering map `p : E ⟶ B` of an action of `G` with contractible total space, the
singular homology `Hₙ(B; k)` is Mathlib's group homology `Hₙ(G, k)` of the trivial
representation. The singular chains of `E` form a free resolution of `k` over `k[G]`, whose
coinvariants are the singular chains of `B`. -/
def singularHomologyIsoGroupHomology [ContractibleSpace E] (n : ℕ) :
    ((singularChains k).obj B).homology n ≅ groupHomology (Rep.trivial k G k) n :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCancelSMul
  letI := Classical.decEq G
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (hG.singularChainsRepCoinvariantsTensorIso k)).symm ≪≫
    (groupHomologyIso _ n (singularChainsResolution k E G)).symm

end IsQuotientCoveringMap
