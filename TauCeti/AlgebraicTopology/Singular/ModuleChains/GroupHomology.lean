/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coinvariants
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.EquivariantMap

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

This applies to the orbit map of a free, covering-space action of `G` on a contractible space,
such as the universal cover of a classifying space of `G`.

The chain identification is natural for maps of quotient covers equivariant along arbitrary
group homomorphisms (`IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso_naturality`),
and so is the comparison with group homology: for a map `b : B ⟶ C` of bases covered by a map of
contractible total spaces equivariant along `φ : G →* H`, the map `b_*` on singular homology
corresponds to Mathlib's change-of-group map `groupHomology.map φ` on group homology with trivial
coefficients (`IsQuotientCoveringMap.singularHomologyIsoGroupHomology_hom_naturality`). No
hypothesis on `φ` is needed.

## Main definitions

* `IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso`: the coinvariants of the
  singular chains of `E` are the singular chains of `B`.
* `IsQuotientCoveringMap.singularHomologyIsoGroupHomology`: for contractible `E`, the singular
  homology of `B` is the group homology of `G` with trivial coefficients.

## Main results

* `IsQuotientCoveringMap.singularChainsRepCoinvariantsTensorIso_hom_f_coinvariantsTensorMk`: the
  comparison of chains sends the class of `a ⊗ c` to `a • p_* c`.
* `IsQuotientCoveringMap.singularHomologyIsoGroupHomology_hom_naturality`,
  `IsQuotientCoveringMap.singularHomologyIsoGroupHomology_inv_naturality`: the comparison with
  group homology is natural in the covering and the group.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4, Proposition 4.1,
  Section III.1, and Section III.8.
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

/-- **The identification of quotient-cover chains with coinvariant chains is natural.**
An equivariant map of total spaces along any group homomorphism, lying over a continuous map
of bases, commutes with the chain identification. -/
@[reassoc]
theorem singularChainsRepCoinvariantsTensorIso_naturality
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    singularChainsCoinvariantsMap k f hf ≫ (hH.singularChainsRepCoinvariantsTensorIso k).hom =
      (hG.singularChainsRepCoinvariantsTensorIso k).hom ≫ (singularChains k).map b := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  apply HomologicalComplex.hom_ext
  intro n
  refine Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun (a : k)
    (c : ((singularChains k).obj E).X n) ↦ ?_)
  -- Evaluate the chain-map composites on tensor classes; the domain objects are presented
  -- through `coinvariantsTensorObj`, so the component equations need these explicit carriers.
  change ((hH.singularChainsRepCoinvariantsTensorIso k).hom.f n)
      ((singularChainsCoinvariantsMap k f hf).f n
        (Rep.coinvariantsTensorMk (Rep.trivial k G k)
          (Rep.of (singularChainsRepresentation k E G n)) a c)) =
    ((singularChains k).map b).f n
      (((hG.singularChainsRepCoinvariantsTensorIso k).hom.f n)
        (Rep.coinvariantsTensorMk (Rep.trivial k G k)
          (Rep.of (singularChainsRepresentation k E G n)) a c))
  rw [singularChainsCoinvariantsMap_f_mk,
    singularChainsRepCoinvariantsTensorIso_hom_f_coinvariantsTensorMk,
    singularChainsRepCoinvariantsTensorIso_hom_f_coinvariantsTensorMk, map_smul]
  exact congrArg (a • ·) (by
    simpa only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply] using
      (ConcreteCategory.congr_hom
        (congrArg (fun t ↦ t.f n) (congrArg (singularChains k).map hb)) c).symm)

/-- The inverse chain identification is natural for an equivariant map of quotient covers. -/
@[reassoc]
theorem singularChainsRepCoinvariantsTensorIso_inv_naturality
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    (singularChains k).map b ≫ (hH.singularChainsRepCoinvariantsTensorIso k).inv =
      (hG.singularChainsRepCoinvariantsTensorIso k).inv ≫
        singularChainsCoinvariantsMap k f hf := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  apply (cancel_mono (hH.singularChainsRepCoinvariantsTensorIso k).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hG.singularChainsRepCoinvariantsTensorIso_naturality k hH f hf b hb,
    Iso.inv_hom_id_assoc]

/-- The comparison with group homology unfolds to the inverse of the chain identification
followed by the inverse of `groupHomologyIso`. -/
private lemma singularHomologyIsoGroupHomology_hom_eq [ContractibleSpace E] (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    haveI := hG.isCancelSMul
    letI := Classical.decEq G
    (hG.singularHomologyIsoGroupHomology k n).hom =
      HomologicalComplex.homologyMap (hG.singularChainsRepCoinvariantsTensorIso k).inv n ≫
        (groupHomologyIso _ n (singularChainsResolution k E G)).inv :=
  (rfl)

/-- **The singular homology of the base of a contractible free cover is naturally group
homology.** For quotient covers `p : E ⟶ B` and `q : F ⟶ C` with contractible total spaces, a map
`f : E ⟶ F` equivariant along any group homomorphism `φ : G →* H` and lying over `b : B ⟶ C`, the
identifications `Hₙ(B; k) ≅ Hₙ(G, k)` and `Hₙ(C; k) ≅ Hₙ(H, k)` carry `b_*` to the change-of-group
map `groupHomology.map φ`, with the identity on the trivial coefficients `k`. -/
@[reassoc]
theorem singularHomologyIsoGroupHomology_hom_naturality [ContractibleSpace E]
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) [ContractibleSpace F] {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (n : ℕ) :
    HomologicalComplex.homologyMap ((singularChains k).map b) n ≫
        (hH.singularHomologyIsoGroupHomology k n).hom =
      (hG.singularHomologyIsoGroupHomology k n).hom ≫
        groupHomology.map φ (A := Rep.trivial k G k) (B := Rep.trivial k H k)
          (𝟙 (Rep.trivial k G k)) n := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  have := hG.isCancelSMul
  have := hH.isCancelSMul
  let := Classical.decEq G
  let := Classical.decEq H
  rw [singularHomologyIsoGroupHomology_hom_eq, singularHomologyIsoGroupHomology_hom_eq]
  -- The complex of `singularChainsResolution` is `singularChainsRep` only by unfolding, so the
  -- steps below are assembled in term mode, where the two are identified.
  calc _ = HomologicalComplex.homologyMap ((hG.singularChainsRepCoinvariantsTensorIso k).inv ≫
          singularChainsCoinvariantsMap k f hf) n ≫
        (groupHomologyIso (Rep.trivial k H k) n (singularChainsResolution k F H)).inv :=
        (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).symm.trans
          (congrArg (fun t ↦ HomologicalComplex.homologyMap t n ≫ _)
            (hG.singularChainsRepCoinvariantsTensorIso_inv_naturality k hH f hf b hb))
    _ = HomologicalComplex.homologyMap (hG.singularChainsRepCoinvariantsTensorIso k).inv n ≫
          HomologicalComplex.homologyMap (φ.coinvariantsTensorChainMap (B := Rep.trivial k H k)
            (𝟙 (Rep.trivial k G k)) (singularChainsRepResMap k f hf)) n ≫
        (groupHomologyIso (Rep.trivial k H k) n (singularChainsResolution k F H)).inv := by
        rw [singularChainsCoinvariantsMap_eq_coinvariantsTensorChainMap]
        exact HomologicalComplex.homologyMap_comp_assoc _ _ _ _
    _ = _ := congrArg (_ ≫ ·) (φ.groupHomologyIso_inv_naturality (A := Rep.trivial k G k)
          (B := Rep.trivial k H k) (𝟙 (Rep.trivial k G k))
          (singularChainsResolution k E G) (singularChainsResolution k F H)
          (singularChainsRepResMap k f hf) (singularChainsRepResMap_f_zero_comp_augmentation k f hf)
          n)
    _ = _ := (Category.assoc _ _ _).symm

/-- The inverse comparison with group homology is natural in the covering and the group. -/
@[reassoc]
theorem singularHomologyIsoGroupHomology_inv_naturality [ContractibleSpace E]
    {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
    (hH : IsQuotientCoveringMap q H) [ContractibleSpace F] {φ : G →* H}
    (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
    (b : B ⟶ C) (hb : p ≫ b = f ≫ q) (n : ℕ) :
    groupHomology.map φ (A := Rep.trivial k G k) (B := Rep.trivial k H k)
          (𝟙 (Rep.trivial k G k)) n ≫ (hH.singularHomologyIsoGroupHomology k n).inv =
      (hG.singularHomologyIsoGroupHomology k n).inv ≫
        HomologicalComplex.homologyMap ((singularChains k).map b) n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    hG.singularHomologyIsoGroupHomology_hom_naturality k hH f hf b hb n, Iso.inv_hom_id_assoc]

end IsQuotientCoveringMap
